import V185TrunkScan23Chunk0249

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1479655 : List Nat := [1, 1, 5, 2, 2, 2, 3, 1, 1, 3, 2]
def baseStart_1479655 : Nat := 118140960795 + 1479655 * 2 ^ 59
def prefixEnd_1479655 : Nat := 4983230072969 + 3 ^ 40 * 1479655 * 2
def baseEnd_1479655 : Nat := 759774217828513576707697

theorem tailTrace_1479655 : CollatzResearch.WordTrace tailWord_1479655 prefixEnd_1479655 759774217828513576707697 := by
  unfold tailWord_1479655
  simp only [CollatzResearch.WordTrace]
  refine ⟨53967451454470114800240419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35978300969646743200160279 53967451454470114800240419)
  ·
    refine ⟨80951177181705172200360629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53967451454470114800240419 80951177181705172200360629)
    ·
      refine ⟨7589172860784859893783809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80951177181705172200360629 7589172860784859893783809)
      ·
        refine ⟨5691879645588644920337857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7589172860784859893783809 5691879645588644920337857)
        ·
          refine ⟨4268909734191483690253393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5691879645588644920337857 4268909734191483690253393)
          ·
            refine ⟨3201682300643612767690045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4268909734191483690253393 3201682300643612767690045)
            ·
              refine ⟨1200630862741354787883767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3201682300643612767690045 1200630862741354787883767)
              ·
                refine ⟨1800946294112032181825651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1200630862741354787883767 1800946294112032181825651)
                ·
                  refine ⟨2701419441168048272738477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1800946294112032181825651 2701419441168048272738477)
                  ·
                    refine ⟨1013032290438018102276929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2701419441168048272738477 1013032290438018102276929)
                    ·
                      refine ⟨759774217828513576707697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1013032290438018102276929 759774217828513576707697)
                      ·
                        rfl

theorem cell23_1479655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_1479655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479655 prefixEnd_1479655 := by exact prefixLift 1479655
  have htrace : WordTrace (prefixWord ++ tailWord_1479655) baseStart_1479655 baseEnd_1479655 := by
    simpa [prefixWord, tailWord_1479655, baseEnd_1479655] using wordTrace_append hprefix tailTrace_1479655
  have hstable : (prefixWord ++ tailWord_1479655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479655).length < 2 ^ (prefixWord ++ tailWord_1479655).sum := by decide
  have hdescent : baseEnd_1479655 < baseStart_1479655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479677 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 2, 1, 8]
def baseStart_1479677 : Nat := 118140960795 + 1479677 * 2 ^ 59
def prefixEnd_1479677 : Nat := 4983230072969 + 3 ^ 40 * 1479677 * 2
def baseEnd_1479677 : Nat := 759785514402912490632595

theorem tailTrace_1479677 : CollatzResearch.WordTrace tailWord_1479677 prefixEnd_1479677 759785514402912490632595 := by
  unfold tailWord_1479677
  simp only [CollatzResearch.WordTrace]
  refine ⟨53968253860390412557541285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35978835906926941705027523 53968253860390412557541285)
  ·
    refine ⟨10119047598823202354538991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53968253860390412557541285 10119047598823202354538991)
    ·
      refine ⟨15178571398234803531808487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10119047598823202354538991 15178571398234803531808487)
      ·
        refine ⟨22767857097352205297712731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15178571398234803531808487 22767857097352205297712731)
        ·
          refine ⟨34151785646028307946569097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22767857097352205297712731 34151785646028307946569097)
          ·
            refine ⟨25613839234521230959926823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34151785646028307946569097 25613839234521230959926823)
            ·
              refine ⟨38420758851781846439890235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25613839234521230959926823 38420758851781846439890235)
              ·
                refine ⟨57631138277672769659835353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38420758851781846439890235 57631138277672769659835353)
                ·
                  refine ⟨43223353708254577244876515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57631138277672769659835353 43223353708254577244876515)
                  ·
                    refine ⟨64835030562381865867314773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43223353708254577244876515 64835030562381865867314773)
                    ·
                      refine ⟨759785514402912490632595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 64835030562381865867314773 759785514402912490632595)
                      ·
                        rfl

theorem cell23_1479677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_1479677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479677 prefixEnd_1479677 := by exact prefixLift 1479677
  have htrace : WordTrace (prefixWord ++ tailWord_1479677) baseStart_1479677 baseEnd_1479677 := by
    simpa [prefixWord, tailWord_1479677, baseEnd_1479677] using wordTrace_append hprefix tailTrace_1479677
  have hstable : (prefixWord ++ tailWord_1479677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479677).length < 2 ^ (prefixWord ++ tailWord_1479677).sum := by decide
  have hdescent : baseEnd_1479677 < baseStart_1479677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479697 : List Nat := [1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 7]
def baseStart_1479697 : Nat := 118140960795 + 1479697 * 2 ^ 59
def prefixEnd_1479697 : Nat := 4983230072969 + 3 ^ 40 * 1479697 * 2
def baseEnd_1479697 : Nat := 759795784016002412382503

theorem tailTrace_1479697 : CollatzResearch.WordTrace tailWord_1479697 prefixEnd_1479697 759795784016002412382503 := by
  unfold tailWord_1479697
  simp only [CollatzResearch.WordTrace]
  refine ⟨53968983320317955973269345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35979322213545303982179563 53968983320317955973269345)
  ·
    refine ⟨40476737490238466979952009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53968983320317955973269345 40476737490238466979952009)
    ·
      refine ⟨30357553117678850234964007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40476737490238466979952009 30357553117678850234964007)
      ·
        refine ⟨45536329676518275352446011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30357553117678850234964007 45536329676518275352446011)
        ·
          refine ⟨68304494514777413028669017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45536329676518275352446011 68304494514777413028669017)
          ·
            refine ⟨51228370886083059771501763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68304494514777413028669017 51228370886083059771501763)
            ·
              refine ⟨76842556329124589657252645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51228370886083059771501763 76842556329124589657252645)
              ·
                refine ⟨14407979311710860560734871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76842556329124589657252645 14407979311710860560734871)
                ·
                  refine ⟨21611968967566290841102307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14407979311710860560734871 21611968967566290841102307)
                  ·
                    refine ⟨32417953451349436261653461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21611968967566290841102307 32417953451349436261653461)
                    ·
                      refine ⟨759795784016002412382503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 32417953451349436261653461 759795784016002412382503)
                      ·
                        rfl

theorem cell23_1479697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_1479697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479697 prefixEnd_1479697 := by exact prefixLift 1479697
  have htrace : WordTrace (prefixWord ++ tailWord_1479697) baseStart_1479697 baseEnd_1479697 := by
    simpa [prefixWord, tailWord_1479697, baseEnd_1479697] using wordTrace_append hprefix tailTrace_1479697
  have hstable : (prefixWord ++ tailWord_1479697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479697).length < 2 ^ (prefixWord ++ tailWord_1479697).sum := by decide
  have hdescent : baseEnd_1479697 < baseStart_1479697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479704 : List Nat := [2, 1, 2, 3, 2, 3, 1, 1, 1, 7]
def baseStart_1479704 : Nat := 118140960795 + 1479704 * 2 ^ 59
def prefixEnd_1479704 : Nat := 4983230072969 + 3 ^ 40 * 1479704 * 2
def baseEnd_1479704 : Nat := 253266459460194628331657

theorem tailTrace_1479704 : CollatzResearch.WordTrace tailWord_1479704 prefixEnd_1479704 253266459460194628331657 := by
  unfold tailWord_1479704
  simp only [CollatzResearch.WordTrace]
  refine ⟨26984619315646298084387083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35979492420861730779182777 26984619315646298084387083)
  ·
    refine ⟨40476928973469447126580625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26984619315646298084387083 40476928973469447126580625)
    ·
      refine ⟨30357696730102085344935469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40476928973469447126580625 30357696730102085344935469)
      ·
        refine ⟨11384136273788282004350801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30357696730102085344935469 11384136273788282004350801)
        ·
          refine ⟨8538102205341211503263101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11384136273788282004350801 8538102205341211503263101)
          ·
            refine ⟨3201788327002954313723663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8538102205341211503263101 3201788327002954313723663)
            ·
              refine ⟨4802682490504431470585495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3201788327002954313723663 4802682490504431470585495)
              ·
                refine ⟨7204023735756647205878243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4802682490504431470585495 7204023735756647205878243)
                ·
                  refine ⟨10806035603634970808817365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7204023735756647205878243 10806035603634970808817365)
                  ·
                    refine ⟨253266459460194628331657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10806035603634970808817365 253266459460194628331657)
                    ·
                      rfl

theorem cell23_1479704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 1, 7].length) (baseStart_1479704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479704 prefixEnd_1479704 := by exact prefixLift 1479704
  have htrace : WordTrace (prefixWord ++ tailWord_1479704) baseStart_1479704 baseEnd_1479704 := by
    simpa [prefixWord, tailWord_1479704, baseEnd_1479704] using wordTrace_append hprefix tailTrace_1479704
  have hstable : (prefixWord ++ tailWord_1479704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479704).length < 2 ^ (prefixWord ++ tailWord_1479704).sum := by decide
  have hdescent : baseEnd_1479704 < baseStart_1479704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479708 : List Nat := [2, 2, 3, 1, 4, 1, 2, 3, 5]
def baseStart_1479708 : Nat := 118140960795 + 1479708 * 2 ^ 59
def prefixEnd_1479708 : Nat := 4983230072969 + 3 ^ 40 * 1479708 * 2
def baseEnd_1479708 : Nat := 84422381367022429927217

theorem tailTrace_1479708 : CollatzResearch.WordTrace tailWord_1479708 prefixEnd_1479708 84422381367022429927217 := by
  unfold tailWord_1479708
  simp only [CollatzResearch.WordTrace]
  refine ⟨26984692261639052425959889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35979589682185403234613185 26984692261639052425959889)
  ·
    refine ⟨20238519196229289319469917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26984692261639052425959889 20238519196229289319469917)
    ·
      refine ⟨7589444698585983494801219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20238519196229289319469917 7589444698585983494801219)
      ·
        refine ⟨11384167047878975242201829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7589444698585983494801219 11384167047878975242201829)
        ·
          refine ⟨2134531321477307857912843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11384167047878975242201829 2134531321477307857912843)
          ·
            refine ⟨3201796982215961786869265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2134531321477307857912843 3201796982215961786869265)
            ·
              refine ⟨2401347736661971340151949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3201796982215961786869265 2401347736661971340151949)
              ·
                refine ⟨900505401248239252556981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2401347736661971340151949 900505401248239252556981)
                ·
                  refine ⟨84422381367022429927217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 900505401248239252556981 84422381367022429927217)
                  ·
                    rfl

theorem cell23_1479708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 3, 5].length) (baseStart_1479708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479708 prefixEnd_1479708 := by exact prefixLift 1479708
  have htrace : WordTrace (prefixWord ++ tailWord_1479708) baseStart_1479708 baseEnd_1479708 := by
    simpa [prefixWord, tailWord_1479708, baseEnd_1479708] using wordTrace_append hprefix tailTrace_1479708
  have hstable : (prefixWord ++ tailWord_1479708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479708).length < 2 ^ (prefixWord ++ tailWord_1479708).sum := by decide
  have hdescent : baseEnd_1479708 < baseStart_1479708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479724 : List Nat := [2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 4]
def baseStart_1479724 : Nat := 118140960795 + 1479724 * 2 ^ 59
def prefixEnd_1479724 : Nat := 4983230072969 + 3 ^ 40 * 1479724 * 2
def baseEnd_1479724 : Nat := 759809647993673806744879

theorem tailTrace_1479724 : CollatzResearch.WordTrace tailWord_1479724 prefixEnd_1479724 759809647993673806744879 := by
  unfold tailWord_1479724
  simp only [CollatzResearch.WordTrace]
  refine ⟨26984984045610069792251113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35979978727480093056334817 26984984045610069792251113)
  ·
    refine ⟨20238738034207552344188335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26984984045610069792251113 20238738034207552344188335)
    ·
      refine ⟨30358107051311328516282503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20238738034207552344188335 30358107051311328516282503)
      ·
        refine ⟨45537160576966992774423755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30358107051311328516282503 45537160576966992774423755)
        ·
          refine ⟨68305740865450489161635633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45537160576966992774423755 68305740865450489161635633)
          ·
            refine ⟨51229305649087866871226725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68305740865450489161635633 51229305649087866871226725)
            ·
              refine ⟨9605494809203975038355011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51229305649087866871226725 9605494809203975038355011)
              ·
                refine ⟨14408242213805962557532517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9605494809203975038355011 14408242213805962557532517)
                ·
                  refine ⟨2701545415088617979537347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14408242213805962557532517 2701545415088617979537347)
                  ·
                    refine ⟨4052318122632926969306021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2701545415088617979537347 4052318122632926969306021)
                    ·
                      refine ⟨759809647993673806744879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4052318122632926969306021 759809647993673806744879)
                      ·
                        rfl

theorem cell23_1479724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 4].length) (baseStart_1479724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479724 prefixEnd_1479724 := by exact prefixLift 1479724
  have htrace : WordTrace (prefixWord ++ tailWord_1479724) baseStart_1479724 baseEnd_1479724 := by
    simpa [prefixWord, tailWord_1479724, baseEnd_1479724] using wordTrace_append hprefix tailTrace_1479724
  have hstable : (prefixWord ++ tailWord_1479724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479724).length < 2 ^ (prefixWord ++ tailWord_1479724).sum := by decide
  have hdescent : baseEnd_1479724 < baseStart_1479724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479744 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 3]
def baseStart_1479744 : Nat := 118140960795 + 1479744 * 2 ^ 59
def prefixEnd_1479744 : Nat := 4983230072969 + 3 ^ 40 * 1479744 * 2
def baseEnd_1479744 : Nat := 759819917606763728494787

theorem tailTrace_1479744 : CollatzResearch.WordTrace tailWord_1479744 prefixEnd_1479744 759819917606763728494787 := by
  unfold tailWord_1479744
  simp only [CollatzResearch.WordTrace]
  refine ⟨26985348775573841500115143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35980465034098455333486857 26985348775573841500115143)
  ·
    refine ⟨40478023163360762250172715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26985348775573841500115143 40478023163360762250172715)
    ·
      refine ⟨60717034745041143375259073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40478023163360762250172715 60717034745041143375259073)
      ·
        refine ⟨45537776058780857531444305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60717034745041143375259073 45537776058780857531444305)
        ·
          refine ⟨34153332044085643148583229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45537776058780857531444305 34153332044085643148583229)
          ·
            refine ⟨12807499516532116180718711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34153332044085643148583229 12807499516532116180718711)
            ·
              refine ⟨19211249274798174271078067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12807499516532116180718711 19211249274798174271078067)
              ·
                refine ⟨28816873912197261406617101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19211249274798174271078067 28816873912197261406617101)
                ·
                  refine ⟨10806327717073973027481413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28816873912197261406617101 10806327717073973027481413)
                  ·
                    refine ⟨2026186446951369942652765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10806327717073973027481413 2026186446951369942652765)
                    ·
                      refine ⟨759819917606763728494787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2026186446951369942652765 759819917606763728494787)
                      ·
                        rfl

theorem cell23_1479744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 3].length) (baseStart_1479744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479744 prefixEnd_1479744 := by exact prefixLift 1479744
  have htrace : WordTrace (prefixWord ++ tailWord_1479744) baseStart_1479744 baseEnd_1479744 := by
    simpa [prefixWord, tailWord_1479744, baseEnd_1479744] using wordTrace_append hprefix tailTrace_1479744
  have hstable : (prefixWord ++ tailWord_1479744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479744).length < 2 ^ (prefixWord ++ tailWord_1479744).sum := by decide
  have hdescent : baseEnd_1479744 < baseStart_1479744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479751 : List Nat := [1, 1, 4, 1, 3, 2, 2, 2, 3, 4]
def baseStart_1479751 : Nat := 118140960795 + 1479751 * 2 ^ 59
def prefixEnd_1479751 : Nat := 4983230072969 + 3 ^ 40 * 1479751 * 2
def baseEnd_1479751 : Nat := 253274503990448400369085

theorem tailTrace_1479751 : CollatzResearch.WordTrace tailWord_1479751 prefixEnd_1479751 253274503990448400369085 := by
  unfold tailWord_1479751
  simp only [CollatzResearch.WordTrace]
  refine ⟨53970952862122323195735107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35980635241414882130490071 53970952862122323195735107)
  ·
    refine ⟨80956429293183484793602661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53970952862122323195735107 80956429293183484793602661)
    ·
      refine ⟨15179330492471903398800499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80956429293183484793602661 15179330492471903398800499)
      ·
        refine ⟨22768995738707855098200749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15179330492471903398800499 22768995738707855098200749)
        ·
          refine ⟨8538373402015445661825281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22768995738707855098200749 8538373402015445661825281)
          ·
            refine ⟨6403780051511584246368961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8538373402015445661825281 6403780051511584246368961)
            ·
              refine ⟨4802835038633688184776721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6403780051511584246368961 4802835038633688184776721)
              ·
                refine ⟨3602126278975266138582541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4802835038633688184776721 3602126278975266138582541)
                ·
                  refine ⟨1350797354615724801968453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3602126278975266138582541 1350797354615724801968453)
                  ·
                    refine ⟨253274503990448400369085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1350797354615724801968453 253274503990448400369085)
                    ·
                      rfl

theorem cell23_1479751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 3, 4].length) (baseStart_1479751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479751 prefixEnd_1479751 := by exact prefixLift 1479751
  have htrace : WordTrace (prefixWord ++ tailWord_1479751) baseStart_1479751 baseEnd_1479751 := by
    simpa [prefixWord, tailWord_1479751, baseEnd_1479751] using wordTrace_append hprefix tailTrace_1479751
  have hstable : (prefixWord ++ tailWord_1479751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479751).length < 2 ^ (prefixWord ++ tailWord_1479751).sum := by decide
  have hdescent : baseEnd_1479751 < baseStart_1479751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479764 : List Nat := [2, 4, 1, 1, 1, 1, 3, 2, 8]
def baseStart_1479764 : Nat := 118140960795 + 1479764 * 2 ^ 59
def prefixEnd_1479764 : Nat := 4983230072969 + 3 ^ 40 * 1479764 * 2
def baseEnd_1479764 : Nat := 84425576357761516693855

theorem tailTrace_1479764 : CollatzResearch.WordTrace tailWord_1479764 prefixEnd_1479764 84425576357761516693855 := by
  unfold tailWord_1479764
  simp only [CollatzResearch.WordTrace]
  refine ⟨26985713505537613207979173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35980951340716817610638897 26985713505537613207979173)
  ·
    refine ⟨5059821282288302476496095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26985713505537613207979173 5059821282288302476496095)
    ·
      refine ⟨7589731923432453714744143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5059821282288302476496095 7589731923432453714744143)
      ·
        refine ⟨11384597885148680572116215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7589731923432453714744143 11384597885148680572116215)
        ·
          refine ⟨17076896827723020858174323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11384597885148680572116215 17076896827723020858174323)
          ·
            refine ⟨25615345241584531287261485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17076896827723020858174323 25615345241584531287261485)
            ·
              refine ⟨9605754465594199232723057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25615345241584531287261485 9605754465594199232723057)
              ·
                refine ⟨7204315849195649424542293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9605754465594199232723057 7204315849195649424542293)
                ·
                  refine ⟨84425576357761516693855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7204315849195649424542293 84425576357761516693855)
                  ·
                    rfl

theorem cell23_1479764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_1479764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479764 prefixEnd_1479764 := by exact prefixLift 1479764
  have htrace : WordTrace (prefixWord ++ tailWord_1479764) baseStart_1479764 baseEnd_1479764 := by
    simpa [prefixWord, tailWord_1479764, baseEnd_1479764] using wordTrace_append hprefix tailTrace_1479764
  have hstable : (prefixWord ++ tailWord_1479764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479764).length < 2 ^ (prefixWord ++ tailWord_1479764).sum := by decide
  have hdescent : baseEnd_1479764 < baseStart_1479764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479778 : List Nat := [3, 3, 2, 2, 1, 1, 1, 1, 4, 2, 3]
def baseStart_1479778 : Nat := 118140960795 + 1479778 * 2 ^ 59
def prefixEnd_1479778 : Nat := 4983230072969 + 3 ^ 40 * 1479778 * 2
def baseEnd_1479778 : Nat := 759837375949016595469631

theorem tailTrace_1479778 : CollatzResearch.WordTrace tailWord_1479778 prefixEnd_1479778 759837375949016595469631 := by
  unfold tailWord_1479778
  simp only [CollatzResearch.WordTrace]
  refine ⟨13492984408256126701741997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35981291755349671204645325 13492984408256126701741997)
  ·
    refine ⟨5059869153096047513153249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13492984408256126701741997 5059869153096047513153249)
    ·
      refine ⟨3794901864822035634864937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5059869153096047513153249 3794901864822035634864937)
      ·
        refine ⟨2846176398616526726148703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3794901864822035634864937 2846176398616526726148703)
        ·
          refine ⟨4269264597924790089223055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2846176398616526726148703 4269264597924790089223055)
          ·
            refine ⟨6403896896887185133834583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4269264597924790089223055 6403896896887185133834583)
            ·
              refine ⟨9605845345330777700751875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6403896896887185133834583 9605845345330777700751875)
              ·
                refine ⟨14408768017996166551127813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9605845345330777700751875 14408768017996166551127813)
                ·
                  refine ⟨2701644003374281228336465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14408768017996166551127813 2701644003374281228336465)
                  ·
                    refine ⟨2026233002530710921252349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2701644003374281228336465 2026233002530710921252349)
                    ·
                      refine ⟨759837375949016595469631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2026233002530710921252349 759837375949016595469631)
                      ·
                        rfl

theorem cell23_1479778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_1479778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479778 prefixEnd_1479778 := by exact prefixLift 1479778
  have htrace : WordTrace (prefixWord ++ tailWord_1479778) baseStart_1479778 baseEnd_1479778 := by
    simpa [prefixWord, tailWord_1479778, baseEnd_1479778] using wordTrace_append hprefix tailTrace_1479778
  have hstable : (prefixWord ++ tailWord_1479778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479778).length < 2 ^ (prefixWord ++ tailWord_1479778).sum := by decide
  have hdescent : baseEnd_1479778 < baseStart_1479778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479785 : List Nat := [1, 2, 1, 1, 1, 7, 3, 2, 1, 4]
def baseStart_1479785 : Nat := 118140960795 + 1479785 * 2 ^ 59
def prefixEnd_1479785 : Nat := 4983230072969 + 3 ^ 40 * 1479785 * 2
def baseEnd_1479785 : Nat := 253280323437866022694033

theorem tailTrace_1479785 : CollatzResearch.WordTrace tailWord_1479785 prefixEnd_1479785 253280323437866022694033 := by
  unfold tailWord_1479785
  simp only [CollatzResearch.WordTrace]
  refine ⟨53972192943999147002472809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35981461962666098001648539 53972192943999147002472809)
  ·
    refine ⟨40479144707999360251854607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53972192943999147002472809 40479144707999360251854607)
    ·
      refine ⟨60718717061999040377781911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40479144707999360251854607 60718717061999040377781911)
      ·
        refine ⟨91078075592998560566672867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60718717061999040377781911 91078075592998560566672867)
        ·
          refine ⟨136617113389497840850009301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91078075592998560566672867 136617113389497840850009301)
          ·
            refine ⟨3201963595066355644922093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 136617113389497840850009301 3201963595066355644922093)
            ·
              refine ⟨1200736348149883366845785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3201963595066355644922093 1200736348149883366845785)
              ·
                refine ⟨900552261112412525134339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1200736348149883366845785 900552261112412525134339)
                ·
                  refine ⟨1350828391668618787701509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 900552261112412525134339 1350828391668618787701509)
                  ·
                    refine ⟨253280323437866022694033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1350828391668618787701509 253280323437866022694033)
                    ·
                      rfl

theorem cell23_1479785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 2, 1, 4].length) (baseStart_1479785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479785 prefixEnd_1479785 := by exact prefixLift 1479785
  have htrace : WordTrace (prefixWord ++ tailWord_1479785) baseStart_1479785 baseEnd_1479785 := by
    simpa [prefixWord, tailWord_1479785, baseEnd_1479785] using wordTrace_append hprefix tailTrace_1479785
  have hstable : (prefixWord ++ tailWord_1479785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479785).length < 2 ^ (prefixWord ++ tailWord_1479785).sum := by decide
  have hdescent : baseEnd_1479785 < baseStart_1479785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479858 : List Nat := [3, 2, 1, 1, 1, 4, 2, 3, 2, 4]
def baseStart_1479858 : Nat := 118140960795 + 1479858 * 2 ^ 59
def prefixEnd_1479858 : Nat := 4983230072969 + 3 ^ 40 * 1479858 * 2
def baseEnd_1479858 : Nat := 253292818133792094156421

theorem tailTrace_1479858 : CollatzResearch.WordTrace tailWord_1479858 prefixEnd_1479858 253292818133792094156421 := by
  unfold tailWord_1479858
  simp only [CollatzResearch.WordTrace]
  refine ⟨13493713868183670117470057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35983236981823120313253485 13493713868183670117470057)
  ·
    refine ⟨10120285401137752588102543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13493713868183670117470057 10120285401137752588102543)
    ·
      refine ⟨15180428101706628882153815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10120285401137752588102543 15180428101706628882153815)
      ·
        refine ⟨22770642152559943323230723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15180428101706628882153815 22770642152559943323230723)
        ·
          refine ⟨34155963228839914984846085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22770642152559943323230723 34155963228839914984846085)
          ·
            refine ⟨6404243105407484059658641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34155963228839914984846085 6404243105407484059658641)
            ·
              refine ⟨4803182329055613044743981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6404243105407484059658641 4803182329055613044743981)
              ·
                refine ⟨1801193373395854891778993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4803182329055613044743981 1801193373395854891778993)
                ·
                  refine ⟨1350895030046891168834245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1801193373395854891778993 1350895030046891168834245)
                  ·
                    refine ⟨253292818133792094156421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1350895030046891168834245 253292818133792094156421)
                    ·
                      rfl

theorem cell23_1479858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 3, 2, 4].length) (baseStart_1479858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479858 prefixEnd_1479858 := by exact prefixLift 1479858
  have htrace : WordTrace (prefixWord ++ tailWord_1479858) baseStart_1479858 baseEnd_1479858 := by
    simpa [prefixWord, tailWord_1479858, baseEnd_1479858] using wordTrace_append hprefix tailTrace_1479858
  have hstable : (prefixWord ++ tailWord_1479858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479858).length < 2 ^ (prefixWord ++ tailWord_1479858).sum := by decide
  have hdescent : baseEnd_1479858 < baseStart_1479858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479865 : List Nat := [1, 2, 1, 4, 1, 4, 1, 2, 3, 2, 2]
def baseStart_1479865 : Nat := 118140960795 + 1479865 * 2 ^ 59
def prefixEnd_1479865 : Nat := 4983230072969 + 3 ^ 40 * 1479865 * 2
def baseEnd_1479865 : Nat := 759882048765957755081731

theorem tailTrace_1479865 : CollatzResearch.WordTrace tailWord_1479865 prefixEnd_1479865 759882048765957755081731 := by
  unfold tailWord_1479865
  simp only [CollatzResearch.WordTrace]
  refine ⟨53975110783709320665385049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35983407189139547110256699 53975110783709320665385049)
  ·
    refine ⟨40481333087781990499038787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53975110783709320665385049 40481333087781990499038787)
    ·
      refine ⟨60721999631672985748558181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40481333087781990499038787 60721999631672985748558181)
      ·
        refine ⟨11385374930938684827854659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60721999631672985748558181 11385374930938684827854659)
        ·
          refine ⟨17078062396408027241781989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11385374930938684827854659 17078062396408027241781989)
          ·
            refine ⟨3202136699326505107834123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17078062396408027241781989 3202136699326505107834123)
            ·
              refine ⟨4803205048989757661751185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3202136699326505107834123 4803205048989757661751185)
              ·
                refine ⟨3602403786742318246313389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4803205048989757661751185 3602403786742318246313389)
                ·
                  refine ⟨1350901420028369342367521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3602403786742318246313389 1350901420028369342367521)
                  ·
                    refine ⟨1013176065021277006775641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1350901420028369342367521 1013176065021277006775641)
                    ·
                      refine ⟨759882048765957755081731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1013176065021277006775641 759882048765957755081731)
                      ·
                        rfl

theorem cell23_1479865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 3, 2, 2].length) (baseStart_1479865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479865 prefixEnd_1479865 := by exact prefixLift 1479865
  have htrace : WordTrace (prefixWord ++ tailWord_1479865) baseStart_1479865 baseEnd_1479865 := by
    simpa [prefixWord, tailWord_1479865, baseEnd_1479865] using wordTrace_append hprefix tailTrace_1479865
  have hstable : (prefixWord ++ tailWord_1479865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479865).length < 2 ^ (prefixWord ++ tailWord_1479865).sum := by decide
  have hdescent : baseEnd_1479865 < baseStart_1479865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479868 : List Nat := [2, 2, 2, 3, 2, 1, 2, 1, 3, 2, 3]
def baseStart_1479868 : Nat := 118140960795 + 1479868 * 2 ^ 59
def prefixEnd_1479868 : Nat := 4983230072969 + 3 ^ 40 * 1479868 * 2
def baseEnd_1479868 : Nat := 759883589207921243344217

theorem tailTrace_1479868 : CollatzResearch.WordTrace tailWord_1479868 prefixEnd_1479868 759883589207921243344217 := by
  unfold tailWord_1479868
  simp only [CollatzResearch.WordTrace]
  refine ⟨26987610101349226088872129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35983480135132301451829505 26987610101349226088872129)
  ·
    refine ⟨20240707576011919566654097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26987610101349226088872129 20240707576011919566654097)
    ·
      refine ⟨15180530682008939674990573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20240707576011919566654097 15180530682008939674990573)
      ·
        refine ⟨5692699005753352378121465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15180530682008939674990573 5692699005753352378121465)
        ·
          refine ⟨4269524254315014283591099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5692699005753352378121465 4269524254315014283591099)
          ·
            refine ⟨6404286381472521425386649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4269524254315014283591099 6404286381472521425386649)
            ·
              refine ⟨4803214786104391069039987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6404286381472521425386649 4803214786104391069039987)
              ·
                refine ⟨7204822179156586603559981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4803214786104391069039987 7204822179156586603559981)
                ·
                  refine ⟨2701808317183719976334993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7204822179156586603559981 2701808317183719976334993)
                  ·
                    refine ⟨2026356237887789982251245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2701808317183719976334993 2026356237887789982251245)
                    ·
                      refine ⟨759883589207921243344217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2026356237887789982251245 759883589207921243344217)
                      ·
                        rfl

theorem cell23_1479868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_1479868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479868 prefixEnd_1479868 := by exact prefixLift 1479868
  have htrace : WordTrace (prefixWord ++ tailWord_1479868) baseStart_1479868 baseEnd_1479868 := by
    simpa [prefixWord, tailWord_1479868, baseEnd_1479868] using wordTrace_append hprefix tailTrace_1479868
  have hstable : (prefixWord ++ tailWord_1479868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479868).length < 2 ^ (prefixWord ++ tailWord_1479868).sum := by decide
  have hdescent : baseEnd_1479868 < baseStart_1479868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479882 : List Nat := [3, 1, 2, 1, 3, 2, 1, 5, 1, 2, 2]
def baseStart_1479882 : Nat := 118140960795 + 1479882 * 2 ^ 59
def prefixEnd_1479882 : Nat := 4983230072969 + 3 ^ 40 * 1479882 * 2
def baseEnd_1479882 : Nat := 759890777937084188569153

theorem tailTrace_1479882 : CollatzResearch.WordTrace tailWord_1479882 prefixEnd_1479882 759890777937084188569153 := by
  unfold tailWord_1479882
  simp only [CollatzResearch.WordTrace]
  refine ⟨13493932706161933142188475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35983820549765155045835933 13493932706161933142188475)
  ·
    refine ⟨20240899059242899713282713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13493932706161933142188475 20240899059242899713282713)
    ·
      refine ⟨15180674294432174784962035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20240899059242899713282713 15180674294432174784962035)
      ·
        refine ⟨22771011441648262177443053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15180674294432174784962035 22771011441648262177443053)
        ·
          refine ⟨8539129290618098316541145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22771011441648262177443053 8539129290618098316541145)
          ·
            refine ⟨6404346967963573737405859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8539129290618098316541145 6404346967963573737405859)
            ·
              refine ⟨9606520451945360606108789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6404346967963573737405859 9606520451945360606108789)
              ·
                refine ⟨900611292369877556822699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9606520451945360606108789 900611292369877556822699)
                ·
                  refine ⟨1350916938554816335234049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 900611292369877556822699 1350916938554816335234049)
                  ·
                    refine ⟨1013187703916112251425537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1350916938554816335234049 1013187703916112251425537)
                    ·
                      refine ⟨759890777937084188569153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1013187703916112251425537 759890777937084188569153)
                      ·
                        rfl

theorem cell23_1479882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 5, 1, 2, 2].length) (baseStart_1479882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479882 prefixEnd_1479882 := by exact prefixLift 1479882
  have htrace : WordTrace (prefixWord ++ tailWord_1479882) baseStart_1479882 baseEnd_1479882 := by
    simpa [prefixWord, tailWord_1479882, baseEnd_1479882] using wordTrace_append hprefix tailTrace_1479882
  have hstable : (prefixWord ++ tailWord_1479882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479882).length < 2 ^ (prefixWord ++ tailWord_1479882).sum := by decide
  have hdescent : baseEnd_1479882 < baseStart_1479882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479908 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 5, 3, 2]
def baseStart_1479908 : Nat := 118140960795 + 1479908 * 2 ^ 59
def prefixEnd_1479908 : Nat := 4983230072969 + 3 ^ 40 * 1479908 * 2
def baseEnd_1479908 : Nat := 759904128434101086844033

theorem tailTrace_1479908 : CollatzResearch.WordTrace tailWord_1479908 prefixEnd_1479908 759904128434101086844033 := by
  unfold tailWord_1479908
  simp only [CollatzResearch.WordTrace]
  refine ⟨26988339561276769504600189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35984452748369026006133585 26988339561276769504600189)
  ·
    refine ⟨10120627335478788564225071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26988339561276769504600189 10120627335478788564225071)
    ·
      refine ⟨15180941003218182846337607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10120627335478788564225071 15180941003218182846337607)
      ·
        refine ⟨22771411504827274269506411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15180941003218182846337607 22771411504827274269506411)
        ·
          refine ⟨34157117257240911404259617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22771411504827274269506411 34157117257240911404259617)
          ·
            refine ⟨25617837942930683553194713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34157117257240911404259617 25617837942930683553194713)
            ·
              refine ⟨19213378457198012664896035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25617837942930683553194713 19213378457198012664896035)
              ·
                refine ⟨28820067685797018997344053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19213378457198012664896035 28820067685797018997344053)
                ·
                  refine ⟨2701881345543470531001005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28820067685797018997344053 2701881345543470531001005)
                  ·
                    refine ⟨1013205504578801449125377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2701881345543470531001005 1013205504578801449125377)
                    ·
                      refine ⟨759904128434101086844033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1013205504578801449125377 759904128434101086844033)
                      ·
                        rfl

theorem cell23_1479908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 5, 3, 2].length) (baseStart_1479908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479908 prefixEnd_1479908 := by exact prefixLift 1479908
  have htrace : WordTrace (prefixWord ++ tailWord_1479908) baseStart_1479908 baseEnd_1479908 := by
    simpa [prefixWord, tailWord_1479908, baseEnd_1479908] using wordTrace_append hprefix tailTrace_1479908
  have hstable : (prefixWord ++ tailWord_1479908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479908).length < 2 ^ (prefixWord ++ tailWord_1479908).sum := by decide
  have hdescent : baseEnd_1479908 < baseStart_1479908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479941 : List Nat := [1, 3, 1, 1, 2, 1, 5, 1, 2, 1, 5]
def baseStart_1479941 : Nat := 118140960795 + 1479941 * 2 ^ 59
def prefixEnd_1479941 : Nat := 4983230072969 + 3 ^ 40 * 1479941 * 2
def baseEnd_1479941 : Nat := 759921073295699457731381

theorem tailTrace_1479941 : CollatzResearch.WordTrace tailWord_1479941 prefixEnd_1479941 759921073295699457731381 := by
  unfold tailWord_1479941
  simp only [CollatzResearch.WordTrace]
  refine ⟨53977882731433985645151677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35985255154289323763434451 53977882731433985645151677)
  ·
    refine ⟨20241706024287744616931879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53977882731433985645151677 20241706024287744616931879)
    ·
      refine ⟨30362559036431616925397819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20241706024287744616931879 30362559036431616925397819)
      ·
        refine ⟨45543838554647425388096729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30362559036431616925397819 45543838554647425388096729)
        ·
          refine ⟨34157878915985569041072547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45543838554647425388096729 34157878915985569041072547)
          ·
            refine ⟨51236818373978353561608821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34157878915985569041072547 51236818373978353561608821)
            ·
              refine ⟨4803451722560470646400827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51236818373978353561608821 4803451722560470646400827)
              ·
                refine ⟨7205177583840705969601241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4803451722560470646400827 7205177583840705969601241)
                ·
                  refine ⟨5403883187880529477200931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7205177583840705969601241 5403883187880529477200931)
                  ·
                    refine ⟨8105824781820794215801397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5403883187880529477200931 8105824781820794215801397)
                    ·
                      refine ⟨759921073295699457731381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8105824781820794215801397 759921073295699457731381)
                      ·
                        rfl

theorem cell23_1479941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 1, 5].length) (baseStart_1479941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479941 prefixEnd_1479941 := by exact prefixLift 1479941
  have htrace : WordTrace (prefixWord ++ tailWord_1479941) baseStart_1479941 baseEnd_1479941 := by
    simpa [prefixWord, tailWord_1479941, baseEnd_1479941] using wordTrace_append hprefix tailTrace_1479941
  have hstable : (prefixWord ++ tailWord_1479941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479941).length < 2 ^ (prefixWord ++ tailWord_1479941).sum := by decide
  have hdescent : baseEnd_1479941 < baseStart_1479941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479972 : List Nat := [2, 3, 1, 3, 1, 1, 3, 3, 2, 2, 2]
def baseStart_1479972 : Nat := 118140960795 + 1479972 * 2 ^ 59
def prefixEnd_1479972 : Nat := 4983230072969 + 3 ^ 40 * 1479972 * 2
def baseEnd_1479972 : Nat := 759936991195988836443739

theorem tailTrace_1479972 : CollatzResearch.WordTrace tailWord_1479972 prefixEnd_1479972 759936991195988836443739 := by
  unfold tailWord_1479972
  simp only [CollatzResearch.WordTrace]
  refine ⟨26989506697160838969765085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35986008929547785293020113 26989506697160838969765085)
  ·
    refine ⟨10121065011435314613661907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26989506697160838969765085 10121065011435314613661907)
    ·
      refine ⟨15181597517152971920492861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10121065011435314613661907 15181597517152971920492861)
      ·
        refine ⟨5693099068932364470184823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15181597517152971920492861 5693099068932364470184823)
        ·
          refine ⟨8539648603398546705277235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5693099068932364470184823 8539648603398546705277235)
          ·
            refine ⟨12809472905097820057915853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8539648603398546705277235 12809472905097820057915853)
            ·
              refine ⟨4803552339411682521718445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12809472905097820057915853 4803552339411682521718445)
              ·
                refine ⟨1801332127279380945644417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4803552339411682521718445 1801332127279380945644417)
                ·
                  refine ⟨1350999095459535709233313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1801332127279380945644417 1350999095459535709233313)
                  ·
                    refine ⟨1013249321594651781924985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1350999095459535709233313 1013249321594651781924985)
                    ·
                      refine ⟨759936991195988836443739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1013249321594651781924985 759936991195988836443739)
                      ·
                        rfl

theorem cell23_1479972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_1479972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479972 prefixEnd_1479972 := by exact prefixLift 1479972
  have htrace : WordTrace (prefixWord ++ tailWord_1479972) baseStart_1479972 baseEnd_1479972 := by
    simpa [prefixWord, tailWord_1479972, baseEnd_1479972] using wordTrace_append hprefix tailTrace_1479972
  have hstable : (prefixWord ++ tailWord_1479972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479972).length < 2 ^ (prefixWord ++ tailWord_1479972).sum := by decide
  have hdescent : baseEnd_1479972 < baseStart_1479972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480012 : List Nat := [2, 2, 1, 3, 2, 4, 2, 2, 5]
def baseStart_1480012 : Nat := 118140960795 + 1480012 * 2 ^ 59
def prefixEnd_1480012 : Nat := 4983230072969 + 3 ^ 40 * 1480012 * 2
def baseEnd_1480012 : Nat := 84439725602463186660395

theorem tailTrace_1480012 : CollatzResearch.WordTrace tailWord_1480012 prefixEnd_1480012 84439725602463186660395 := by
  unfold tailWord_1480012
  simp only [CollatzResearch.WordTrace]
  refine ⟨26990236157088382385493145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35986981542784509847324193 26990236157088382385493145)
  ·
    refine ⟨20242677117816286789119859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26990236157088382385493145 20242677117816286789119859)
    ·
      refine ⟨30364015676724430183679789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20242677117816286789119859 30364015676724430183679789)
      ·
        refine ⟨11386505878771661318879921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30364015676724430183679789 11386505878771661318879921)
        ·
          refine ⟨8539879409078745989159941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11386505878771661318879921 8539879409078745989159941)
          ·
            refine ⟨1601227389202264872967489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8539879409078745989159941 1601227389202264872967489)
            ·
              refine ⟨1200920541901698654725617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1601227389202264872967489 1200920541901698654725617)
              ·
                refine ⟨900690406426273991044213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1200920541901698654725617 900690406426273991044213)
                ·
                  refine ⟨84439725602463186660395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 900690406426273991044213 84439725602463186660395)
                  ·
                    rfl

theorem cell23_1480012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 2, 5].length) (baseStart_1480012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480012 prefixEnd_1480012 := by exact prefixLift 1480012
  have htrace : WordTrace (prefixWord ++ tailWord_1480012) baseStart_1480012 baseEnd_1480012 := by
    simpa [prefixWord, tailWord_1480012, baseEnd_1480012] using wordTrace_append hprefix tailTrace_1480012
  have hstable : (prefixWord ++ tailWord_1480012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480012).length < 2 ^ (prefixWord ++ tailWord_1480012).sum := by decide
  have hdescent : baseEnd_1480012 < baseStart_1480012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480041 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 1, 6, 4]
def baseStart_1480041 : Nat := 118140960795 + 1480041 * 2 ^ 59
def prefixEnd_1480041 : Nat := 4983230072969 + 3 ^ 40 * 1480041 * 2
def baseEnd_1480041 : Nat := 759972421361149066480921

theorem tailTrace_1480041 : CollatzResearch.WordTrace tailWord_1480041 prefixEnd_1480041 759972421361149066480921 := by
  unfold tailWord_1480041
  simp only [CollatzResearch.WordTrace]
  refine ⟨53981530031071702723791977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35987686687381135149194651 53981530031071702723791977)
  ·
    refine ⟨40486147523303777042843983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53981530031071702723791977 40486147523303777042843983)
    ·
      refine ⟨60729221284955665564265975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40486147523303777042843983 60729221284955665564265975)
      ·
        refine ⟨91093831927433498346398963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60729221284955665564265975 91093831927433498346398963)
        ·
          refine ⟨136640747891150247519598445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91093831927433498346398963 136640747891150247519598445)
          ·
            refine ⟨51240280459181342819849417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136640747891150247519598445 51240280459181342819849417)
            ·
              refine ⟨38430210344386007114887063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51240280459181342819849417 38430210344386007114887063)
              ·
                refine ⟨57645315516579010672330595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38430210344386007114887063 57645315516579010672330595)
                ·
                  refine ⟨86467973274868516008495893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57645315516579010672330595 86467973274868516008495893)
                  ·
                    refine ⟨4053186247259461687898245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 86467973274868516008495893 4053186247259461687898245)
                    ·
                      refine ⟨759972421361149066480921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4053186247259461687898245 759972421361149066480921)
                      ·
                        rfl

theorem cell23_1480041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 6, 4].length) (baseStart_1480041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480041 prefixEnd_1480041 := by exact prefixLift 1480041
  have htrace : WordTrace (prefixWord ++ tailWord_1480041) baseStart_1480041 baseEnd_1480041 := by
    simpa [prefixWord, tailWord_1480041, baseEnd_1480041] using wordTrace_append hprefix tailTrace_1480041
  have hstable : (prefixWord ++ tailWord_1480041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480041).length < 2 ^ (prefixWord ++ tailWord_1480041).sum := by decide
  have hdescent : baseEnd_1480041 < baseStart_1480041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480042 : List Nat := [3, 1, 3, 3, 2, 2, 1, 1, 2, 5]
def baseStart_1480042 : Nat := 118140960795 + 1480042 * 2 ^ 59
def prefixEnd_1480042 : Nat := 4983230072969 + 3 ^ 40 * 1480042 * 2
def baseEnd_1480042 : Nat := 253324311613934520856139

theorem tailTrace_1480042 : CollatzResearch.WordTrace tailWord_1480042 prefixEnd_1480042 253324311613934520856139 := by
  unfold tailWord_1480042
  simp only [CollatzResearch.WordTrace]
  refine ⟨13495391626017019973644595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35987711002712053263052253 13495391626017019973644595)
  ·
    refine ⟨20243087439025529960466893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13495391626017019973644595 20243087439025529960466893)
    ·
      refine ⟨7591157789634573735175085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20243087439025529960466893 7591157789634573735175085)
      ·
        refine ⟨2846684171112965150690657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7591157789634573735175085 2846684171112965150690657)
        ·
          refine ⟨2135013128334723863017993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2846684171112965150690657 2135013128334723863017993)
          ·
            refine ⟨1601259846251042897263495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2135013128334723863017993 1601259846251042897263495)
            ·
              refine ⟨2401889769376564345895243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1601259846251042897263495 2401889769376564345895243)
              ·
                refine ⟨3602834654064846518842865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2401889769376564345895243 3602834654064846518842865)
                ·
                  refine ⟨2702125990548634889132149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3602834654064846518842865 2702125990548634889132149)
                  ·
                    refine ⟨253324311613934520856139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2702125990548634889132149 253324311613934520856139)
                    ·
                      rfl

theorem cell23_1480042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_1480042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480042 prefixEnd_1480042 := by exact prefixLift 1480042
  have htrace : WordTrace (prefixWord ++ tailWord_1480042) baseStart_1480042 baseEnd_1480042 := by
    simpa [prefixWord, tailWord_1480042, baseEnd_1480042] using wordTrace_append hprefix tailTrace_1480042
  have hstable : (prefixWord ++ tailWord_1480042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480042).length < 2 ^ (prefixWord ++ tailWord_1480042).sum := by decide
  have hdescent : baseEnd_1480042 < baseStart_1480042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480045 : List Nat := [1, 5, 1, 1, 1, 3, 3, 1, 2, 1, 4]
def baseStart_1480045 : Nat := 118140960795 + 1480045 * 2 ^ 59
def prefixEnd_1480045 : Nat := 4983230072969 + 3 ^ 40 * 1480045 * 2
def baseEnd_1480045 : Nat := 759974475283767050830903

theorem tailTrace_1480045 : CollatzResearch.WordTrace tailWord_1480045 prefixEnd_1480045 759974475283767050830903 := by
  unfold tailWord_1480045
  simp only [CollatzResearch.WordTrace]
  refine ⟨53981675923057211406937589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35987783948704807604625059 53981675923057211406937589)
  ·
    refine ⟨5060782117786613569400399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53981675923057211406937589 5060782117786613569400399)
    ·
      refine ⟨7591173176679920354100599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5060782117786613569400399 7591173176679920354100599)
      ·
        refine ⟨11386759765019880531150899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7591173176679920354100599 11386759765019880531150899)
        ·
          refine ⟨17080139647529820796726349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11386759765019880531150899 17080139647529820796726349)
          ·
            refine ⟨6405052367823682798772381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17080139647529820796726349 6405052367823682798772381)
            ·
              refine ⟨2401894637933881049539643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6405052367823682798772381 2401894637933881049539643)
              ·
                refine ⟨3602841956900821574309465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2401894637933881049539643 3602841956900821574309465)
                ·
                  refine ⟨2702131467675616180732099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3602841956900821574309465 2702131467675616180732099)
                  ·
                    refine ⟨4053197201513424271098149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2702131467675616180732099 4053197201513424271098149)
                    ·
                      refine ⟨759974475283767050830903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4053197201513424271098149 759974475283767050830903)
                      ·
                        rfl

theorem cell23_1480045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_1480045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480045 prefixEnd_1480045 := by exact prefixLift 1480045
  have htrace : WordTrace (prefixWord ++ tailWord_1480045) baseStart_1480045 baseEnd_1480045 := by
    simpa [prefixWord, tailWord_1480045, baseEnd_1480045] using wordTrace_append hprefix tailTrace_1480045
  have hstable : (prefixWord ++ tailWord_1480045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480045).length < 2 ^ (prefixWord ++ tailWord_1480045).sum := by decide
  have hdescent : baseEnd_1480045 < baseStart_1480045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480048 : List Nat := [2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 3]
def baseStart_1480048 : Nat := 118140960795 + 1480048 * 2 ^ 59
def prefixEnd_1480048 : Nat := 4983230072969 + 3 ^ 40 * 1480048 * 2
def baseEnd_1480048 : Nat := 759976015725730539093389

theorem tailTrace_1480048 : CollatzResearch.WordTrace tailWord_1480048 prefixEnd_1480048 759976015725730539093389 := by
  unfold tailWord_1480048
  simp only [CollatzResearch.WordTrace]
  refine ⟨26990892671023171459648399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35987856894697561946197865 26990892671023171459648399)
  ·
    refine ⟨40486339006534757189472599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26990892671023171459648399 40486339006534757189472599)
    ·
      refine ⟨60729508509802135784208899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40486339006534757189472599 60729508509802135784208899)
      ·
        refine ⟨91094262764703203676313349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60729508509802135784208899 91094262764703203676313349)
        ·
          refine ⟨17080174268381850689308753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91094262764703203676313349 17080174268381850689308753)
          ·
            refine ⟨12810130701286388016981565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17080174268381850689308753 12810130701286388016981565)
            ·
              refine ⟨4803799012982395506368087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12810130701286388016981565 4803799012982395506368087)
              ·
                refine ⟨7205698519473593259552131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4803799012982395506368087 7205698519473593259552131)
                ·
                  refine ⟨10808547779210389889328197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7205698519473593259552131 10808547779210389889328197)
                  ·
                    refine ⟨2026602708601948104249037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10808547779210389889328197 2026602708601948104249037)
                    ·
                      refine ⟨759976015725730539093389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2026602708601948104249037 759976015725730539093389)
                      ·
                        rfl

theorem cell23_1480048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 3].length) (baseStart_1480048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480048 prefixEnd_1480048 := by exact prefixLift 1480048
  have htrace : WordTrace (prefixWord ++ tailWord_1480048) baseStart_1480048 baseEnd_1480048 := by
    simpa [prefixWord, tailWord_1480048, baseEnd_1480048] using wordTrace_append hprefix tailTrace_1480048
  have hstable : (prefixWord ++ tailWord_1480048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480048).length < 2 ^ (prefixWord ++ tailWord_1480048).sum := by decide
  have hdescent : baseEnd_1480048 < baseStart_1480048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480068 : List Nat := [2, 3, 2, 1, 1, 4, 1, 1, 8]
def baseStart_1480068 : Nat := 118140960795 + 1480068 * 2 ^ 59
def prefixEnd_1480068 : Nat := 4983230072969 + 3 ^ 40 * 1480068 * 2
def baseEnd_1480068 : Nat := 84442920593202273427033

theorem tailTrace_1480068 : CollatzResearch.WordTrace tailWord_1480068 prefixEnd_1480068 84442920593202273427033 := by
  unfold tailWord_1480068
  simp only [CollatzResearch.WordTrace]
  refine ⟨26991257400986943167512429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35988343201315924223349905 26991257400986943167512429)
  ·
    refine ⟨10121721525370103687817161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26991257400986943167512429 10121721525370103687817161)
    ·
      refine ⟨7591291144027577765862871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10121721525370103687817161 7591291144027577765862871)
      ·
        refine ⟨11386936716041366648794307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7591291144027577765862871 11386936716041366648794307)
        ·
          refine ⟨17080405074062049973191461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11386936716041366648794307 17080405074062049973191461)
          ·
            refine ⟨3202575951386634369973399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17080405074062049973191461 3202575951386634369973399)
            ·
              refine ⟨4803863927079951554960099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3202575951386634369973399 4803863927079951554960099)
              ·
                refine ⟨7205795890619927332440149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4803863927079951554960099 7205795890619927332440149)
                ·
                  refine ⟨84442920593202273427033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7205795890619927332440149 84442920593202273427033)
                  ·
                    rfl

theorem cell23_1480068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 8].length) (baseStart_1480068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480068 prefixEnd_1480068 := by exact prefixLift 1480068
  have htrace : WordTrace (prefixWord ++ tailWord_1480068) baseStart_1480068 baseEnd_1480068 := by
    simpa [prefixWord, tailWord_1480068, baseEnd_1480068] using wordTrace_append hprefix tailTrace_1480068
  have hstable : (prefixWord ++ tailWord_1480068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480068).length < 2 ^ (prefixWord ++ tailWord_1480068).sum := by decide
  have hdescent : baseEnd_1480068 < baseStart_1480068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480072 : List Nat := [2, 1, 3, 3, 1, 2, 2, 4, 1, 4]
def baseStart_1480072 : Nat := 118140960795 + 1480072 * 2 ^ 59
def prefixEnd_1480072 : Nat := 4983230072969 + 3 ^ 40 * 1480072 * 2
def baseEnd_1480072 : Nat := 253329446420479481731093

theorem tailTrace_1480072 : CollatzResearch.WordTrace tailWord_1480072 prefixEnd_1480072 253329446420479481731093 := by
  unfold tailWord_1480072
  simp only [CollatzResearch.WordTrace]
  refine ⟨26991330346979697509085235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35988440462639596678780313 26991330346979697509085235)
  ·
    refine ⟨40486995520469546263627853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26991330346979697509085235 40486995520469546263627853)
    ·
      refine ⟨15182623320176079848860445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40486995520469546263627853 15182623320176079848860445)
      ·
        refine ⟨5693483745066029943322667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15182623320176079848860445 5693483745066029943322667)
        ·
          refine ⟨8540225617599044914984001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5693483745066029943322667 8540225617599044914984001)
          ·
            refine ⟨6405169213199283686238001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8540225617599044914984001 6405169213199283686238001)
            ·
              refine ⟨4803876909899462764678501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6405169213199283686238001 4803876909899462764678501)
              ·
                refine ⟨900726920606149268377219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4803876909899462764678501 900726920606149268377219)
                ·
                  refine ⟨1351090380909223902565829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 900726920606149268377219 1351090380909223902565829)
                  ·
                    refine ⟨253329446420479481731093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1351090380909223902565829 253329446420479481731093)
                    ·
                      rfl

theorem cell23_1480072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 4, 1, 4].length) (baseStart_1480072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480072 prefixEnd_1480072 := by exact prefixLift 1480072
  have htrace : WordTrace (prefixWord ++ tailWord_1480072) baseStart_1480072 baseEnd_1480072 := by
    simpa [prefixWord, tailWord_1480072, baseEnd_1480072] using wordTrace_append hprefix tailTrace_1480072
  have hstable : (prefixWord ++ tailWord_1480072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480072).length < 2 ^ (prefixWord ++ tailWord_1480072).sum := by decide
  have hdescent : baseEnd_1480072 < baseStart_1480072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480091 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 5]
def baseStart_1480091 : Nat := 118140960795 + 1480091 * 2 ^ 59
def prefixEnd_1480091 : Nat := 4983230072969 + 3 ^ 40 * 1480091 * 2
def baseEnd_1480091 : Nat := 759998095393873870855691

theorem tailTrace_1480091 : CollatzResearch.WordTrace tailWord_1480091 prefixEnd_1480091 759998095393873870855691 := by
  unfold tailWord_1480091
  simp only [CollatzResearch.WordTrace]
  refine ⟨53983353680890561263112127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35988902453927040842074751 53983353680890561263112127)
  ·
    refine ⟨80975030521335841894668191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53983353680890561263112127 80975030521335841894668191)
    ·
      refine ⟨121462545782003762842002287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80975030521335841894668191 121462545782003762842002287)
      ·
        refine ⟨182193818673005644263003431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121462545782003762842002287 182193818673005644263003431)
        ·
          refine ⟨273290728009508466394505147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182193818673005644263003431 273290728009508466394505147)
          ·
            refine ⟨409936092014262699591757721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273290728009508466394505147 409936092014262699591757721)
            ·
              refine ⟨307452069010697024693818291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 409936092014262699591757721 307452069010697024693818291)
              ·
                refine ⟨461178103516045537040727437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 307452069010697024693818291 461178103516045537040727437)
                ·
                  refine ⟨172941788818517076390272789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 461178103516045537040727437 172941788818517076390272789)
                  ·
                    refine ⟨8106646350867987955794037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 172941788818517076390272789 8106646350867987955794037)
                    ·
                      refine ⟨759998095393873870855691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8106646350867987955794037 759998095393873870855691)
                      ·
                        rfl

theorem cell23_1480091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 5].length) (baseStart_1480091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480091 prefixEnd_1480091 := by exact prefixLift 1480091
  have htrace : WordTrace (prefixWord ++ tailWord_1480091) baseStart_1480091 baseEnd_1480091 := by
    simpa [prefixWord, tailWord_1480091, baseEnd_1480091] using wordTrace_append hprefix tailTrace_1480091
  have hstable : (prefixWord ++ tailWord_1480091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480091).length < 2 ^ (prefixWord ++ tailWord_1480091).sum := by decide
  have hdescent : baseEnd_1480091 < baseStart_1480091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480112 : List Nat := [2, 1, 1, 1, 2, 1, 1, 9, 1, 1, 3]
def baseStart_1480112 : Nat := 118140960795 + 1480112 * 2 ^ 59
def prefixEnd_1480112 : Nat := 4983230072969 + 3 ^ 40 * 1480112 * 2
def baseEnd_1480112 : Nat := 760008878487618288693095

theorem tailTrace_1480112 : CollatzResearch.WordTrace tailWord_1480112 prefixEnd_1480112 760008878487618288693095 := by
  unfold tailWord_1480112
  simp only [CollatzResearch.WordTrace]
  refine ⟨26992059806907240924813295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35989413075876321233084393 26992059806907240924813295)
  ·
    refine ⟨40488089710360861387219943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26992059806907240924813295 40488089710360861387219943)
    ·
      refine ⟨60732134565541292080829915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40488089710360861387219943 60732134565541292080829915)
      ·
        refine ⟨91098201848311938121244873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60732134565541292080829915 91098201848311938121244873)
        ·
          refine ⟨68323651386233953590933655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91098201848311938121244873 68323651386233953590933655)
          ·
            refine ⟨102485477079350930386400483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68323651386233953590933655 102485477079350930386400483)
            ·
              refine ⟨153728215619026395579600725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102485477079350930386400483 153728215619026395579600725)
              ·
                refine ⟨900751263392732786599223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 153728215619026395579600725 900751263392732786599223)
                ·
                  refine ⟨1351126895089099179898835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 900751263392732786599223 1351126895089099179898835)
                  ·
                    refine ⟨2026690342633648769848253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1351126895089099179898835 2026690342633648769848253)
                    ·
                      refine ⟨760008878487618288693095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2026690342633648769848253 760008878487618288693095)
                      ·
                        rfl

theorem cell23_1480112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 9, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 9, 1, 1, 3].length) (baseStart_1480112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480112 prefixEnd_1480112 := by exact prefixLift 1480112
  have htrace : WordTrace (prefixWord ++ tailWord_1480112) baseStart_1480112 baseEnd_1480112 := by
    simpa [prefixWord, tailWord_1480112, baseEnd_1480112] using wordTrace_append hprefix tailTrace_1480112
  have hstable : (prefixWord ++ tailWord_1480112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480112).length < 2 ^ (prefixWord ++ tailWord_1480112).sum := by decide
  have hdescent : baseEnd_1480112 < baseStart_1480112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480152 : List Nat := [2, 1, 2, 2, 2, 1, 2, 4, 3, 2, 2]
def baseStart_1480152 : Nat := 118140960795 + 1480152 * 2 ^ 59
def prefixEnd_1480152 : Nat := 4983230072969 + 3 ^ 40 * 1480152 * 2
def baseEnd_1480152 : Nat := 760029417713798132192911

theorem tailTrace_1480152 : CollatzResearch.WordTrace tailWord_1480152 prefixEnd_1480152 760029417713798132192911 := by
  unfold tailWord_1480152
  simp only [CollatzResearch.WordTrace]
  refine ⟨26992789266834784340541355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35990385689113045787388473 26992789266834784340541355)
  ·
    refine ⟨40489183900252176510812033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26992789266834784340541355 40489183900252176510812033)
    ·
      refine ⟨30366887925189132383109025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40489183900252176510812033 30366887925189132383109025)
      ·
        refine ⟨22775165943891849287331769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30366887925189132383109025 22775165943891849287331769)
        ·
          refine ⟨17081374457918886965498827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22775165943891849287331769 17081374457918886965498827)
          ·
            refine ⟨25622061686878330448248241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17081374457918886965498827 25622061686878330448248241)
            ·
              refine ⟨19216546265158747836186181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25622061686878330448248241 19216546265158747836186181)
              ·
                refine ⟨3603102424717265219284909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19216546265158747836186181 3603102424717265219284909)
                ·
                  refine ⟨1351163409268974457231841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3603102424717265219284909 1351163409268974457231841)
                  ·
                    refine ⟨1013372556951730842923881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1351163409268974457231841 1013372556951730842923881)
                    ·
                      refine ⟨760029417713798132192911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1013372556951730842923881 760029417713798132192911)
                      ·
                        rfl

theorem cell23_1480152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 3, 2, 2].length) (baseStart_1480152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480152 prefixEnd_1480152 := by exact prefixLift 1480152
  have htrace : WordTrace (prefixWord ++ tailWord_1480152) baseStart_1480152 baseEnd_1480152 := by
    simpa [prefixWord, tailWord_1480152, baseEnd_1480152] using wordTrace_append hprefix tailTrace_1480152
  have hstable : (prefixWord ++ tailWord_1480152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480152).length < 2 ^ (prefixWord ++ tailWord_1480152).sum := by decide
  have hdescent : baseEnd_1480152 < baseStart_1480152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480165 : List Nat := [1, 3, 1, 5, 1, 1, 1, 1, 3, 2, 4]
def baseStart_1480165 : Nat := 118140960795 + 1480165 * 2 ^ 59
def prefixEnd_1480165 : Nat := 4983230072969 + 3 ^ 40 * 1480165 * 2
def baseEnd_1480165 : Nat := 760036092962306581330351

theorem tailTrace_1480165 : CollatzResearch.WordTrace tailWord_1480165 prefixEnd_1480165 760036092962306581330351 := by
  unfold tailWord_1480165
  simp only [CollatzResearch.WordTrace]
  refine ⟨53986052682622471901305949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35990701788414981267537299 53986052682622471901305949)
  ·
    refine ⟨20244769755983426962989731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53986052682622471901305949 20244769755983426962989731)
    ·
      refine ⟨30367154633975140444484597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20244769755983426962989731 30367154633975140444484597)
      ·
        refine ⟨2846920746935169416670431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30367154633975140444484597 2846920746935169416670431)
        ·
          refine ⟨4270381120402754125005647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2846920746935169416670431 4270381120402754125005647)
          ·
            refine ⟨6405571680604131187508471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4270381120402754125005647 6405571680604131187508471)
            ·
              refine ⟨9608357520906196781262707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6405571680604131187508471 9608357520906196781262707)
              ·
                refine ⟨14412536281359295171894061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9608357520906196781262707 14412536281359295171894061)
                ·
                  refine ⟨5404701105509735689460273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14412536281359295171894061 5404701105509735689460273)
                  ·
                    refine ⟨4053525829132301767095205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5404701105509735689460273 4053525829132301767095205)
                    ·
                      refine ⟨760036092962306581330351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4053525829132301767095205 760036092962306581330351)
                      ·
                        rfl

theorem cell23_1480165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_1480165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480165 prefixEnd_1480165 := by exact prefixLift 1480165
  have htrace : WordTrace (prefixWord ++ tailWord_1480165) baseStart_1480165 baseEnd_1480165 := by
    simpa [prefixWord, tailWord_1480165, baseEnd_1480165] using wordTrace_append hprefix tailTrace_1480165
  have hstable : (prefixWord ++ tailWord_1480165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480165).length < 2 ^ (prefixWord ++ tailWord_1480165).sum := by decide
  have hdescent : baseEnd_1480165 < baseStart_1480165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480188 : List Nat := [2, 2, 2, 1, 2, 1, 3, 1, 2, 7]
def baseStart_1480188 : Nat := 118140960795 + 1480188 * 2 ^ 59
def prefixEnd_1480188 : Nat := 4983230072969 + 3 ^ 40 * 1480188 * 2
def baseEnd_1480188 : Nat := 253349301005786663780915

theorem tailTrace_1480188 : CollatzResearch.WordTrace tailWord_1480188 prefixEnd_1480188 253349301005786663780915 := by
  unfold tailWord_1480188
  simp only [CollatzResearch.WordTrace]
  refine ⟨26993445780769573414696609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35991261041026097886262145 26993445780769573414696609)
  ·
    refine ⟨20245084335577180061022457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26993445780769573414696609 20245084335577180061022457)
    ·
      refine ⟨15183813251682885045766843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20245084335577180061022457 15183813251682885045766843)
      ·
        refine ⟨22775719877524327568650265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15183813251682885045766843 22775719877524327568650265)
        ·
          refine ⟨17081789908143245676487699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22775719877524327568650265 17081789908143245676487699)
          ·
            refine ⟨25622684862214868514731549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17081789908143245676487699 25622684862214868514731549)
            ·
              refine ⟨9608506823330575693024331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25622684862214868514731549 9608506823330575693024331)
              ·
                refine ⟨14412760234995863539536497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9608506823330575693024331 14412760234995863539536497)
                ·
                  refine ⟨10809570176246897654652373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14412760234995863539536497 10809570176246897654652373)
                  ·
                    refine ⟨253349301005786663780915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10809570176246897654652373 253349301005786663780915)
                    ·
                      rfl

theorem cell23_1480188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_1480188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480188 prefixEnd_1480188 := by exact prefixLift 1480188
  have htrace : WordTrace (prefixWord ++ tailWord_1480188) baseStart_1480188 baseEnd_1480188 := by
    simpa [prefixWord, tailWord_1480188, baseEnd_1480188] using wordTrace_append hprefix tailTrace_1480188
  have hstable : (prefixWord ++ tailWord_1480188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480188).length < 2 ^ (prefixWord ++ tailWord_1480188).sum := by decide
  have hdescent : baseEnd_1480188 < baseStart_1480188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480202 : List Nat := [3, 1, 2, 2, 2, 3, 2, 1, 1, 3, 3]
def baseStart_1480202 : Nat := 118140960795 + 1480202 * 2 ^ 59
def prefixEnd_1480202 : Nat := 4983230072969 + 3 ^ 40 * 1480202 * 2
def baseEnd_1480202 : Nat := 760055091746522936567681

theorem tailTrace_1480202 : CollatzResearch.WordTrace tailWord_1480202 prefixEnd_1480202 760055091746522936567681 := by
  unfold tailWord_1480202
  simp only [CollatzResearch.WordTrace]
  refine ⟨13496850545872106805100715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35991601455658951480268573 13496850545872106805100715)
  ·
    refine ⟨20245275818808160207651073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13496850545872106805100715 20245275818808160207651073)
    ·
      refine ⟨15183956864106120155738305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20245275818808160207651073 15183956864106120155738305)
      ·
        refine ⟨11387967648079590116803729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15183956864106120155738305 11387967648079590116803729)
        ·
          refine ⟨8540975736059692587602797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11387967648079590116803729 8540975736059692587602797)
          ·
            refine ⟨3202865901022384720351049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8540975736059692587602797 3202865901022384720351049)
            ·
              refine ⟨2402149425766788540263287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3202865901022384720351049 2402149425766788540263287)
              ·
                refine ⟨3603224138650182810394931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2402149425766788540263287 3603224138650182810394931)
                ·
                  refine ⟨5404836207975274215592397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3603224138650182810394931 5404836207975274215592397)
                  ·
                    refine ⟨2026813577990727830847149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5404836207975274215592397 2026813577990727830847149)
                    ·
                      refine ⟨760055091746522936567681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2026813577990727830847149 760055091746522936567681)
                      ·
                        rfl

theorem cell23_1480202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_1480202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480202 prefixEnd_1480202 := by exact prefixLift 1480202
  have htrace : WordTrace (prefixWord ++ tailWord_1480202) baseStart_1480202 baseEnd_1480202 := by
    simpa [prefixWord, tailWord_1480202, baseEnd_1480202] using wordTrace_append hprefix tailTrace_1480202
  have hstable : (prefixWord ++ tailWord_1480202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480202).length < 2 ^ (prefixWord ++ tailWord_1480202).sum := by decide
  have hdescent : baseEnd_1480202 < baseStart_1480202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480218 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 3, 8]
def baseStart_1480218 : Nat := 118140960795 + 1480218 * 2 ^ 59
def prefixEnd_1480218 : Nat := 4983230072969 + 3 ^ 40 * 1480218 * 2
def baseEnd_1480218 : Nat := 253354435812331624655869

theorem tailTrace_1480218 : CollatzResearch.WordTrace tailWord_1480218 prefixEnd_1480218 253354435812331624655869 := by
  unfold tailWord_1480218
  simp only [CollatzResearch.WordTrace]
  refine ⟨13496996437857615488246327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35991990500953641301990205 13496996437857615488246327)
  ·
    refine ⟨20245494656786423232369491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13496996437857615488246327 20245494656786423232369491)
    ·
      refine ⟨30368241985179634848554237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20245494656786423232369491 30368241985179634848554237)
      ·
        refine ⟨11388090744442363068207839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30368241985179634848554237 11388090744442363068207839)
        ·
          refine ⟨17082136116663544602311759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11388090744442363068207839 17082136116663544602311759)
          ·
            refine ⟨25623204174995316903467639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17082136116663544602311759 25623204174995316903467639)
            ·
              refine ⟨38434806262492975355201459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25623204174995316903467639 38434806262492975355201459)
              ·
                refine ⟨57652209393739463032802189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38434806262492975355201459 57652209393739463032802189)
                ·
                  refine ⟨21619578522652298637300821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57652209393739463032802189 21619578522652298637300821)
                  ·
                    refine ⟨253354435812331624655869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 21619578522652298637300821 253354435812331624655869)
                    ·
                      rfl

theorem cell23_1480218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 3, 8].length) (baseStart_1480218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480218 prefixEnd_1480218 := by exact prefixLift 1480218
  have htrace : WordTrace (prefixWord ++ tailWord_1480218) baseStart_1480218 baseEnd_1480218 := by
    simpa [prefixWord, tailWord_1480218, baseEnd_1480218] using wordTrace_append hprefix tailTrace_1480218
  have hstable : (prefixWord ++ tailWord_1480218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480218).length < 2 ^ (prefixWord ++ tailWord_1480218).sum := by decide
  have hdescent : baseEnd_1480218 < baseStart_1480218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480255 : List Nat := [1, 1, 2, 2, 3, 3, 2, 1, 2, 2, 4]
def baseStart_1480255 : Nat := 118140960795 + 1480255 * 2 ^ 59
def prefixEnd_1480255 : Nat := 4983230072969 + 3 ^ 40 * 1480255 * 2
def baseEnd_1480255 : Nat := 760082306221211229204937

theorem tailTrace_1480255 : CollatzResearch.WordTrace tailWord_1480255 prefixEnd_1480255 760082306221211229204937 := by
  unfold tailWord_1480255
  simp only [CollatzResearch.WordTrace]
  refine ⟨53989335252296417272082219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35992890168197611514721479 53989335252296417272082219)
  ·
    refine ⟨80984002878444625908123329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53989335252296417272082219 80984002878444625908123329)
    ·
      refine ⟨60738002158833469431092497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80984002878444625908123329 60738002158833469431092497)
      ·
        refine ⟨45553501619125102073319373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60738002158833469431092497 45553501619125102073319373)
        ·
          refine ⟨17082563107171913277494765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45553501619125102073319373 17082563107171913277494765)
          ·
            refine ⟨6405961165189467479060537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17082563107171913277494765 6405961165189467479060537)
            ·
              refine ⟨4804470873892100609295403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6405961165189467479060537 4804470873892100609295403)
              ·
                refine ⟨7206706310838150913943105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4804470873892100609295403 7206706310838150913943105)
                ·
                  refine ⟨5405029733128613185457329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7206706310838150913943105 5405029733128613185457329)
                  ·
                    refine ⟨4053772299846459889092997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5405029733128613185457329 4053772299846459889092997)
                    ·
                      refine ⟨760082306221211229204937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4053772299846459889092997 760082306221211229204937)
                      ·
                        rfl

theorem cell23_1480255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 2, 4].length) (baseStart_1480255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480255 prefixEnd_1480255 := by exact prefixLift 1480255
  have htrace : WordTrace (prefixWord ++ tailWord_1480255) baseStart_1480255 baseEnd_1480255 := by
    simpa [prefixWord, tailWord_1480255, baseEnd_1480255] using wordTrace_append hprefix tailTrace_1480255
  have hstable : (prefixWord ++ tailWord_1480255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480255).length < 2 ^ (prefixWord ++ tailWord_1480255).sum := by decide
  have hdescent : baseEnd_1480255 < baseStart_1480255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480295 : List Nat := [1, 1, 5, 1, 1, 1, 3, 1, 4, 5]
def baseStart_1480295 : Nat := 118140960795 + 1480295 * 2 ^ 59
def prefixEnd_1480295 : Nat := 4983230072969 + 3 ^ 40 * 1480295 * 2
def baseEnd_1480295 : Nat := 253367615149130357568251

theorem tailTrace_1480295 : CollatzResearch.WordTrace tailWord_1480295 prefixEnd_1480295 253367615149130357568251 := by
  unfold tailWord_1480295
  simp only [CollatzResearch.WordTrace]
  refine ⟨53990794172151504103538339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35993862781434336069025559 53990794172151504103538339)
  ·
    refine ⟨80986191258227256155307509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53990794172151504103538339 80986191258227256155307509)
    ·
      refine ⟨7592455430458805264560079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80986191258227256155307509 7592455430458805264560079)
      ·
        refine ⟨11388683145688207896840119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7592455430458805264560079 11388683145688207896840119)
        ·
          refine ⟨17083024718532311845260179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11388683145688207896840119 17083024718532311845260179)
          ·
            refine ⟨25624537077798467767890269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17083024718532311845260179 25624537077798467767890269)
            ·
              refine ⟨9609201404174425412958851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25624537077798467767890269 9609201404174425412958851)
              ·
                refine ⟨14413802106261638119438277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9609201404174425412958851 14413802106261638119438277)
                ·
                  refine ⟨2702587894924057147394677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14413802106261638119438277 2702587894924057147394677)
                  ·
                    refine ⟨253367615149130357568251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2702587894924057147394677 253367615149130357568251)
                    ·
                      rfl

theorem cell23_1480295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_1480295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480295 prefixEnd_1480295 := by exact prefixLift 1480295
  have htrace : WordTrace (prefixWord ++ tailWord_1480295) baseStart_1480295 baseEnd_1480295 := by
    simpa [prefixWord, tailWord_1480295, baseEnd_1480295] using wordTrace_append hprefix tailTrace_1480295
  have hstable : (prefixWord ++ tailWord_1480295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480295).length < 2 ^ (prefixWord ++ tailWord_1480295).sum := by decide
  have hdescent : baseEnd_1480295 < baseStart_1480295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480310 : List Nat := [5, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2]
def baseStart_1480310 : Nat := 118140960795 + 1480310 * 2 ^ 59
def prefixEnd_1480310 : Nat := 4983230072969 + 3 ^ 40 * 1480310 * 2
def baseEnd_1480310 : Nat := 760110547657208514017185

theorem tailTrace_1480310 : CollatzResearch.WordTrace tailWord_1480310 prefixEnd_1480310 760110547657208514017185 := by
  unfold tailWord_1480310
  simp only [CollatzResearch.WordTrace]
  refine ⟨3374458829193572604083399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35994227511398107776889589 3374458829193572604083399)
  ·
    refine ⟨5061688243790358906125099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3374458829193572604083399 5061688243790358906125099)
    ·
      refine ⟨7592532365685538359187649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5061688243790358906125099 7592532365685538359187649)
      ·
        refine ⟨5694399274264153769390737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7592532365685538359187649 5694399274264153769390737)
        ·
          refine ⟨4270799455698115327043053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5694399274264153769390737 4270799455698115327043053)
          ·
            refine ⟨1601549795886793247641145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4270799455698115327043053 1601549795886793247641145)
            ·
              refine ⟨1201162346915094935730859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1601549795886793247641145 1201162346915094935730859)
              ·
                refine ⟨1801743520372642403596289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1201162346915094935730859 1801743520372642403596289)
                ·
                  refine ⟨1351307640279481802697217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1801743520372642403596289 1351307640279481802697217)
                  ·
                    refine ⟨1013480730209611352022913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1351307640279481802697217 1013480730209611352022913)
                    ·
                      refine ⟨760110547657208514017185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1013480730209611352022913 760110547657208514017185)
                      ·
                        rfl

theorem cell23_1480310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_1480310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480310 prefixEnd_1480310 := by exact prefixLift 1480310
  have htrace : WordTrace (prefixWord ++ tailWord_1480310) baseStart_1480310 baseEnd_1480310 := by
    simpa [prefixWord, tailWord_1480310, baseEnd_1480310] using wordTrace_append hprefix tailTrace_1480310
  have hstable : (prefixWord ++ tailWord_1480310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480310).length < 2 ^ (prefixWord ++ tailWord_1480310).sum := by decide
  have hdescent : baseEnd_1480310 < baseStart_1480310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480315 : List Nat := [1, 1, 1, 1, 1, 4, 3, 2, 4, 1, 4]
def baseStart_1480315 : Nat := 118140960795 + 1480315 * 2 ^ 59
def prefixEnd_1480315 : Nat := 4983230072969 + 3 ^ 40 * 1480315 * 2
def baseEnd_1480315 : Nat := 760113115060480994454661

theorem tailTrace_1480315 : CollatzResearch.WordTrace tailWord_1480315 prefixEnd_1480315 760113115060480994454661 := by
  unfold tailWord_1480315
  simp only [CollatzResearch.WordTrace]
  refine ⟨53991523632079047519266399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35994349088052698346177599 53991523632079047519266399)
  ·
    refine ⟨80987285448118571278899599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53991523632079047519266399 80987285448118571278899599)
    ·
      refine ⟨121480928172177856918349399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80987285448118571278899599 121480928172177856918349399)
      ·
        refine ⟨182221392258266785377524099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121480928172177856918349399 182221392258266785377524099)
        ·
          refine ⟨273332088387400178066286149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182221392258266785377524099 273332088387400178066286149)
          ·
            refine ⟨51249766572637533387428653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 273332088387400178066286149 51249766572637533387428653)
            ·
              refine ⟨19218662464739075020285745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51249766572637533387428653 19218662464739075020285745)
              ·
                refine ⟨14413996848554306265214309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19218662464739075020285745 14413996848554306265214309)
                ·
                  refine ⟨2702624409103932424727683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14413996848554306265214309 2702624409103932424727683)
                  ·
                    refine ⟨4053936613655898637091525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2702624409103932424727683 4053936613655898637091525)
                    ·
                      refine ⟨760113115060480994454661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4053936613655898637091525 760113115060480994454661)
                      ·
                        rfl

theorem cell23_1480315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 4, 1, 4].length) (baseStart_1480315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480315 prefixEnd_1480315 := by exact prefixLift 1480315
  have htrace : WordTrace (prefixWord ++ tailWord_1480315) baseStart_1480315 baseEnd_1480315 := by
    simpa [prefixWord, tailWord_1480315, baseEnd_1480315] using wordTrace_append hprefix tailTrace_1480315
  have hstable : (prefixWord ++ tailWord_1480315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480315).length < 2 ^ (prefixWord ++ tailWord_1480315).sum := by decide
  have hdescent : baseEnd_1480315 < baseStart_1480315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480332 : List Nat := [2, 2, 1, 2, 1, 1, 6, 1, 2, 1, 4]
def baseStart_1480332 : Nat := 118140960795 + 1480332 * 2 ^ 59
def prefixEnd_1480332 : Nat := 4983230072969 + 3 ^ 40 * 1480332 * 2
def baseEnd_1480332 : Nat := 760121844231607427942083

theorem tailTrace_1480332 : CollatzResearch.WordTrace tailWord_1480332 prefixEnd_1480332 760121844231607427942083 := by
  unfold tailWord_1480332
  simp only [CollatzResearch.WordTrace]
  refine ⟨26996071836508729711317625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35994762448678306281756833 26996071836508729711317625)
  ·
    refine ⟨20247053877381547283488219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26996071836508729711317625 20247053877381547283488219)
    ·
      refine ⟨30370580816072320925232329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20247053877381547283488219 30370580816072320925232329)
      ·
        refine ⟨22777935612054240693924247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30370580816072320925232329 22777935612054240693924247)
        ·
          refine ⟨34166903418081361040886371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22777935612054240693924247 34166903418081361040886371)
          ·
            refine ⟨51250355127122041561329557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34166903418081361040886371 51250355127122041561329557)
            ·
              refine ⟨2402360396583845698187323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51250355127122041561329557 2402360396583845698187323)
              ·
                refine ⟨3603540594875768547280985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2402360396583845698187323 3603540594875768547280985)
                ·
                  refine ⟨2702655446156826410460739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3603540594875768547280985 2702655446156826410460739)
                  ·
                    refine ⟨4053983169235239615691109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2702655446156826410460739 4053983169235239615691109)
                    ·
                      refine ⟨760121844231607427942083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4053983169235239615691109 760121844231607427942083)
                      ·
                        rfl

theorem cell23_1480332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 2, 1, 4].length) (baseStart_1480332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480332 prefixEnd_1480332 := by exact prefixLift 1480332
  have htrace : WordTrace (prefixWord ++ tailWord_1480332) baseStart_1480332 baseEnd_1480332 := by
    simpa [prefixWord, tailWord_1480332, baseEnd_1480332] using wordTrace_append hprefix tailTrace_1480332
  have hstable : (prefixWord ++ tailWord_1480332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480332).length < 2 ^ (prefixWord ++ tailWord_1480332).sum := by decide
  have hdescent : baseEnd_1480332 < baseStart_1480332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480406 : List Nat := [5, 2, 1, 3, 1, 1, 1, 1, 8]
def baseStart_1480406 : Nat := 118140960795 + 1480406 * 2 ^ 59
def prefixEnd_1480406 : Nat := 4983230072969 + 3 ^ 40 * 1480406 * 2
def baseEnd_1480406 : Nat := 84462204644448904268527

theorem tailTrace_1480406 : CollatzResearch.WordTrace tailWord_1480406 prefixEnd_1480406 84462204644448904268527 := by
  unfold tailWord_1480406
  simp only [CollatzResearch.WordTrace]
  refine ⟨3374677667171835628801817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35996561783166246707219381 3374677667171835628801817)
  ·
    refine ⟨2531008250378876721601363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3374677667171835628801817 2531008250378876721601363)
    ·
      refine ⟨3796512375568315082402045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2531008250378876721601363 3796512375568315082402045)
      ·
        refine ⟨1423692140838118155900767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3796512375568315082402045 1423692140838118155900767)
        ·
          refine ⟨2135538211257177233851151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1423692140838118155900767 2135538211257177233851151)
          ·
            refine ⟨3203307316885765850776727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2135538211257177233851151 3203307316885765850776727)
            ·
              refine ⟨4804960975328648776165091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3203307316885765850776727 4804960975328648776165091)
              ·
                refine ⟨7207441462992973164247637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4804960975328648776165091 7207441462992973164247637)
                ·
                  refine ⟨84462204644448904268527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7207441462992973164247637 84462204644448904268527)
                  ·
                    rfl

theorem cell23_1480406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_1480406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480406 prefixEnd_1480406 := by exact prefixLift 1480406
  have htrace : WordTrace (prefixWord ++ tailWord_1480406) baseStart_1480406 baseEnd_1480406 := by
    simpa [prefixWord, tailWord_1480406, baseEnd_1480406] using wordTrace_append hprefix tailTrace_1480406
  have hstable : (prefixWord ++ tailWord_1480406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480406).length < 2 ^ (prefixWord ++ tailWord_1480406).sum := by decide
  have hdescent : baseEnd_1480406 < baseStart_1480406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480416 : List Nat := [2, 1, 1, 3, 1, 2, 4, 4, 1, 1, 3]
def baseStart_1480416 : Nat := 118140960795 + 1480416 * 2 ^ 59
def prefixEnd_1480416 : Nat := 4983230072969 + 3 ^ 40 * 1480416 * 2
def baseEnd_1480416 : Nat := 760164976606585099291697

theorem tailTrace_1480416 : CollatzResearch.WordTrace tailWord_1480416 prefixEnd_1480416 760164976606585099291697 := by
  unfold tailWord_1480416
  simp only [CollatzResearch.WordTrace]
  refine ⟨26997603702356570884346551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35996804936475427845795401 26997603702356570884346551)
  ·
    refine ⟨40496405553534856326519827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26997603702356570884346551 40496405553534856326519827)
    ·
      refine ⟨60744608330302284489779741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40496405553534856326519827 60744608330302284489779741)
      ·
        refine ⟨22779228123863356683667403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60744608330302284489779741 22779228123863356683667403)
        ·
          refine ⟨34168842185795035025501105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22779228123863356683667403 34168842185795035025501105)
          ·
            refine ⟨25626631639346276269125829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34168842185795035025501105 25626631639346276269125829)
            ·
              refine ⟨4804993432377426800461093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25626631639346276269125829 4804993432377426800461093)
              ·
                refine ⟨900936268570767525086455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4804993432377426800461093 900936268570767525086455)
                ·
                  refine ⟨1351404402856151287629683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 900936268570767525086455 1351404402856151287629683)
                  ·
                    refine ⟨2027106604284226931444525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1351404402856151287629683 2027106604284226931444525)
                    ·
                      refine ⟨760164976606585099291697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2027106604284226931444525 760164976606585099291697)
                      ·
                        rfl

theorem cell23_1480416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 4, 1, 1, 3].length) (baseStart_1480416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480416 prefixEnd_1480416 := by exact prefixLift 1480416
  have htrace : WordTrace (prefixWord ++ tailWord_1480416) baseStart_1480416 baseEnd_1480416 := by
    simpa [prefixWord, tailWord_1480416, baseEnd_1480416] using wordTrace_append hprefix tailTrace_1480416
  have hstable : (prefixWord ++ tailWord_1480416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480416).length < 2 ^ (prefixWord ++ tailWord_1480416).sum := by decide
  have hdescent : baseEnd_1480416 < baseStart_1480416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480459 : List Nat := [1, 1, 1, 1, 5, 1, 4, 3, 1, 2, 3]
def baseStart_1480459 : Nat := 118140960795 + 1480459 * 2 ^ 59
def prefixEnd_1480459 : Nat := 4983230072969 + 3 ^ 40 * 1480459 * 2
def baseEnd_1480459 : Nat := 760187056274728431053999

theorem tailTrace_1480459 : CollatzResearch.WordTrace tailWord_1480459 prefixEnd_1480459 760187056274728431053999 := by
  unfold tailWord_1480459
  simp only [CollatzResearch.WordTrace]
  refine ⟨53996775743557360112508431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35997850495704906741672287 53996775743557360112508431)
  ·
    refine ⟨80995163615336040168762647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53996775743557360112508431 80995163615336040168762647)
    ·
      refine ⟨121492745423004060253143971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80995163615336040168762647 121492745423004060253143971)
      ·
        refine ⟨182239118134506090379715957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121492745423004060253143971 182239118134506090379715957)
        ·
          refine ⟨17084917325109945973098371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 182239118134506090379715957 17084917325109945973098371)
          ·
            refine ⟨25627375987664918959647557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17084917325109945973098371 25627375987664918959647557)
            ·
              refine ⟨4805132997687172304933917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25627375987664918959647557 4805132997687172304933917)
              ·
                refine ⟨1801924874132689614350219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4805132997687172304933917 1801924874132689614350219)
                ·
                  refine ⟨2702887311199034421525329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1801924874132689614350219 2702887311199034421525329)
                  ·
                    refine ⟨2027165483399275816143997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2702887311199034421525329 2027165483399275816143997)
                    ·
                      refine ⟨760187056274728431053999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2027165483399275816143997 760187056274728431053999)
                      ·
                        rfl

theorem cell23_1480459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 3, 1, 2, 3].length) (baseStart_1480459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480459 prefixEnd_1480459 := by exact prefixLift 1480459
  have htrace : WordTrace (prefixWord ++ tailWord_1480459) baseStart_1480459 baseEnd_1480459 := by
    simpa [prefixWord, tailWord_1480459, baseEnd_1480459] using wordTrace_append hprefix tailTrace_1480459
  have hstable : (prefixWord ++ tailWord_1480459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480459).length < 2 ^ (prefixWord ++ tailWord_1480459).sum := by decide
  have hdescent : baseEnd_1480459 < baseStart_1480459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480466 : List Nat := [3, 2, 4, 1, 1, 1, 2, 1, 4, 4]
def baseStart_1480466 : Nat := 118140960795 + 1480466 * 2 ^ 59
def prefixEnd_1480466 : Nat := 4983230072969 + 3 ^ 40 * 1480466 * 2
def baseEnd_1480466 : Nat := 253396883546436634555489

theorem tailTrace_1480466 : CollatzResearch.WordTrace tailWord_1480466 prefixEnd_1480466 253396883546436634555489 := by
  unfold tailWord_1480466
  simp only [CollatzResearch.WordTrace]
  refine ⟨13499257763633000077003313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35998020703021333538675501 13499257763633000077003313)
  ·
    refine ⟨10124443322724750057752485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13499257763633000077003313 10124443322724750057752485)
    ·
      refine ⟨1898333123010890635828591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10124443322724750057752485 1898333123010890635828591)
      ·
        refine ⟨2847499684516335953742887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1898333123010890635828591 2847499684516335953742887)
        ·
          refine ⟨4271249526774503930614331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2847499684516335953742887 4271249526774503930614331)
          ·
            refine ⟨6406874290161755895921497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4271249526774503930614331 6406874290161755895921497)
            ·
              refine ⟨4805155717621316921941123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6406874290161755895921497 4805155717621316921941123)
              ·
                refine ⟨7207733576431975382911685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4805155717621316921941123 7207733576431975382911685)
                ·
                  refine ⟨1351450045580995384295941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7207733576431975382911685 1351450045580995384295941)
                  ·
                    refine ⟨253396883546436634555489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1351450045580995384295941 253396883546436634555489)
                    ·
                      rfl

theorem cell23_1480466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_1480466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480466 prefixEnd_1480466 := by exact prefixLift 1480466
  have htrace : WordTrace (prefixWord ++ tailWord_1480466) baseStart_1480466 baseEnd_1480466 := by
    simpa [prefixWord, tailWord_1480466, baseEnd_1480466] using wordTrace_append hprefix tailTrace_1480466
  have hstable : (prefixWord ++ tailWord_1480466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480466).length < 2 ^ (prefixWord ++ tailWord_1480466).sum := by decide
  have hdescent : baseEnd_1480466 < baseStart_1480466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480475 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 1, 9]
def baseStart_1480475 : Nat := 118140960795 + 1480475 * 2 ^ 59
def prefixEnd_1480475 : Nat := 4983230072969 + 3 ^ 40 * 1480475 * 2
def baseEnd_1480475 : Nat := 253398423988400122817975

theorem tailTrace_1480475 : CollatzResearch.WordTrace tailWord_1480475 prefixEnd_1480475 253398423988400122817975 := by
  unfold tailWord_1480475
  simp only [CollatzResearch.WordTrace]
  refine ⟨53997359311499394845090879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35998239540999596563393919 53997359311499394845090879)
  ·
    refine ⟨80996038967249092267636319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53997359311499394845090879 80996038967249092267636319)
    ·
      refine ⟨121494058450873638401454479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80996038967249092267636319 121494058450873638401454479)
      ·
        refine ⟨182241087676310457602181719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121494058450873638401454479 182241087676310457602181719)
        ·
          refine ⟨273361631514465686403272579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182241087676310457602181719 273361631514465686403272579)
          ·
            refine ⟨410042447271698529604908869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273361631514465686403272579 410042447271698529604908869)
            ·
              refine ⟨76882958863443474300920413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 410042447271698529604908869 76882958863443474300920413)
              ·
                refine ⟨28831109573791302862845155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76882958863443474300920413 28831109573791302862845155)
                ·
                  refine ⟨43246664360686954294267733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28831109573791302862845155 43246664360686954294267733)
                  ·
                    refine ⟨253398423988400122817975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 43246664360686954294267733 253398423988400122817975)
                    ·
                      rfl

theorem cell23_1480475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 9].length) (baseStart_1480475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480475 prefixEnd_1480475 := by exact prefixLift 1480475
  have htrace : WordTrace (prefixWord ++ tailWord_1480475) baseStart_1480475 baseEnd_1480475 := by
    simpa [prefixWord, tailWord_1480475, baseEnd_1480475] using wordTrace_append hprefix tailTrace_1480475
  have hstable : (prefixWord ++ tailWord_1480475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480475).length < 2 ^ (prefixWord ++ tailWord_1480475).sum := by decide
  have hdescent : baseEnd_1480475 < baseStart_1480475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480482 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 2, 2, 6]
def baseStart_1480482 : Nat := 118140960795 + 1480482 * 2 ^ 59
def prefixEnd_1480482 : Nat := 4983230072969 + 3 ^ 40 * 1480482 * 2
def baseEnd_1480482 : Nat := 760198866329781841066393

theorem tailTrace_1480482 : CollatzResearch.WordTrace tailWord_1480482 prefixEnd_1480482 760198866329781841066393 := by
  unfold tailWord_1480482
  simp only [CollatzResearch.WordTrace]
  refine ⟨13499403655618508760148925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35998409748316023360397133 13499403655618508760148925)
  ·
    refine ⟨5062276370856940785055847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13499403655618508760148925 5062276370856940785055847)
    ·
      refine ⟨7593414556285411177583771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5062276370856940785055847 7593414556285411177583771)
      ·
        refine ⟨11390121834428116766375657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7593414556285411177583771 11390121834428116766375657)
        ·
          refine ⟨8542591375821087574781743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11390121834428116766375657 8542591375821087574781743)
          ·
            refine ⟨12813887063731631362172615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8542591375821087574781743 12813887063731631362172615)
            ·
              refine ⟨19220830595597447043258923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12813887063731631362172615 19220830595597447043258923)
              ·
                refine ⟨28831245893396170564888385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19220830595597447043258923 28831245893396170564888385)
                ·
                  refine ⟨21623434420047127923666289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28831245893396170564888385 21623434420047127923666289)
                  ·
                    refine ⟨16217575815035345942749717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21623434420047127923666289 16217575815035345942749717)
                    ·
                      refine ⟨760198866329781841066393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16217575815035345942749717 760198866329781841066393)
                      ·
                        rfl

theorem cell23_1480482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_1480482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480482 prefixEnd_1480482 := by exact prefixLift 1480482
  have htrace : WordTrace (prefixWord ++ tailWord_1480482) baseStart_1480482 baseEnd_1480482 := by
    simpa [prefixWord, tailWord_1480482, baseEnd_1480482] using wordTrace_append hprefix tailTrace_1480482
  have hstable : (prefixWord ++ tailWord_1480482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480482).length < 2 ^ (prefixWord ++ tailWord_1480482).sum := by decide
  have hdescent : baseEnd_1480482 < baseStart_1480482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480522 : List Nat := [3, 1, 2, 1, 1, 1, 4, 2, 2, 6]
def baseStart_1480522 : Nat := 118140960795 + 1480522 * 2 ^ 59
def prefixEnd_1480522 : Nat := 4983230072969 + 3 ^ 40 * 1480522 * 2
def baseEnd_1480522 : Nat := 253406468518653894855403

theorem tailTrace_1480522 : CollatzResearch.WordTrace tailWord_1480522 prefixEnd_1480522 253406468518653894855403 := by
  unfold tailWord_1480522
  simp only [CollatzResearch.WordTrace]
  refine ⟨13499768385582280468012955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35999382361552747914701213 13499768385582280468012955)
  ·
    refine ⟨20249652578373420702019433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13499768385582280468012955 20249652578373420702019433)
    ·
      refine ⟨15187239433780065526514575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20249652578373420702019433 15187239433780065526514575)
      ·
        refine ⟨22780859150670098289771863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15187239433780065526514575 22780859150670098289771863)
        ·
          refine ⟨34171288726005147434657795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22780859150670098289771863 34171288726005147434657795)
          ·
            refine ⟨51256933089007721151986693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34171288726005147434657795 51256933089007721151986693)
            ·
              refine ⟨9610674954188947715997505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51256933089007721151986693 9610674954188947715997505)
              ·
                refine ⟨7208006215641710786998129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9610674954188947715997505 7208006215641710786998129)
                ·
                  refine ⟨5406004661731283090248597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7208006215641710786998129 5406004661731283090248597)
                  ·
                    refine ⟨253406468518653894855403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5406004661731283090248597 253406468518653894855403)
                    ·
                      rfl

theorem cell23_1480522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_1480522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480522 prefixEnd_1480522 := by exact prefixLift 1480522
  have htrace : WordTrace (prefixWord ++ tailWord_1480522) baseStart_1480522 baseEnd_1480522 := by
    simpa [prefixWord, tailWord_1480522, baseEnd_1480522] using wordTrace_append hprefix tailTrace_1480522
  have hstable : (prefixWord ++ tailWord_1480522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480522).length < 2 ^ (prefixWord ++ tailWord_1480522).sum := by decide
  have hdescent : baseEnd_1480522 < baseStart_1480522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480524 : List Nat := [2, 2, 1, 3, 5, 1, 2, 2, 1, 2, 2]
def baseStart_1480524 : Nat := 118140960795 + 1480524 * 2 ^ 59
def prefixEnd_1480524 : Nat := 4983230072969 + 3 ^ 40 * 1480524 * 2
def baseEnd_1480524 : Nat := 760220432517270676741201

theorem tailTrace_1480524 : CollatzResearch.WordTrace tailWord_1480524 prefixEnd_1480524 760220432517270676741201 := by
  unfold tailWord_1480524
  simp only [CollatzResearch.WordTrace]
  refine ⟨26999573244160938106812313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35999430992214584142416417 26999573244160938106812313)
  ·
    refine ⟨20249679933120703580109235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26999573244160938106812313 20249679933120703580109235)
    ·
      refine ⟨30374519899681055370163853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20249679933120703580109235 30374519899681055370163853)
      ·
        refine ⟨11390444962380395763811445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30374519899681055370163853 11390444962380395763811445)
        ·
          refine ⟨1067854215223162102857323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11390444962380395763811445 1067854215223162102857323)
          ·
            refine ⟨1601781322834743154285985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1067854215223162102857323 1601781322834743154285985)
            ·
              refine ⟨1201335992126057365714489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1601781322834743154285985 1201335992126057365714489)
              ·
                refine ⟨901001994094543024285867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1201335992126057365714489 901001994094543024285867)
                ·
                  refine ⟨1351502991141814536428801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 901001994094543024285867 1351502991141814536428801)
                  ·
                    refine ⟨1013627243356360902321601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1351502991141814536428801 1013627243356360902321601)
                    ·
                      refine ⟨760220432517270676741201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1013627243356360902321601 760220432517270676741201)
                      ·
                        rfl

theorem cell23_1480524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 2, 1, 2, 2].length) (baseStart_1480524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480524 prefixEnd_1480524 := by exact prefixLift 1480524
  have htrace : WordTrace (prefixWord ++ tailWord_1480524) baseStart_1480524 baseEnd_1480524 := by
    simpa [prefixWord, tailWord_1480524, baseEnd_1480524] using wordTrace_append hprefix tailTrace_1480524
  have hstable : (prefixWord ++ tailWord_1480524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480524).length < 2 ^ (prefixWord ++ tailWord_1480524).sum := by decide
  have hdescent : baseEnd_1480524 < baseStart_1480524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480562 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 1, 2, 7]
def baseStart_1480562 : Nat := 118140960795 + 1480562 * 2 ^ 59
def prefixEnd_1480562 : Nat := 4983230072969 + 3 ^ 40 * 1480562 * 2
def baseEnd_1480562 : Nat := 760239944782141528066025

theorem tailTrace_1480562 : CollatzResearch.WordTrace tailWord_1480562 prefixEnd_1480562 760239944782141528066025 := by
  unfold tailWord_1480562
  simp only [CollatzResearch.WordTrace]
  refine ⟨13500133115546052175876985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36000354974789472469005293 13500133115546052175876985)
  ·
    refine ⟨10125099836659539131907739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13500133115546052175876985 10125099836659539131907739)
    ·
      refine ⟨15187649754989308697861609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10125099836659539131907739 15187649754989308697861609)
      ·
        refine ⟨11390737316241981523396207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15187649754989308697861609 11390737316241981523396207)
        ·
          refine ⟨17086105974362972285094311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11390737316241981523396207 17086105974362972285094311)
          ·
            refine ⟨25629158961544458427641467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17086105974362972285094311 25629158961544458427641467)
            ·
              refine ⟨38443738442316687641462201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25629158961544458427641467 38443738442316687641462201)
              ·
                refine ⟨28832803831737515731096651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38443738442316687641462201 28832803831737515731096651)
                ·
                  refine ⟨43249205747606273596644977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28832803831737515731096651 43249205747606273596644977)
                  ·
                    refine ⟨32436904310704705197483733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43249205747606273596644977 32436904310704705197483733)
                    ·
                      refine ⟨760239944782141528066025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 32436904310704705197483733 760239944782141528066025)
                      ·
                        rfl

theorem cell23_1480562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_1480562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480562 prefixEnd_1480562 := by exact prefixLift 1480562
  have htrace : WordTrace (prefixWord ++ tailWord_1480562) baseStart_1480562 baseEnd_1480562 := by
    simpa [prefixWord, tailWord_1480562, baseEnd_1480562] using wordTrace_append hprefix tailTrace_1480562
  have hstable : (prefixWord ++ tailWord_1480562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480562).length < 2 ^ (prefixWord ++ tailWord_1480562).sum := by decide
  have hdescent : baseEnd_1480562 < baseStart_1480562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480579 : List Nat := [1, 1, 1, 3, 4, 2, 1, 2, 2, 3, 3]
def baseStart_1480579 : Nat := 118140960795 + 1480579 * 2 ^ 59
def prefixEnd_1480579 : Nat := 4983230072969 + 3 ^ 40 * 1480579 * 2
def baseEnd_1480579 : Nat := 760248673953267961553447

theorem tailTrace_1480579 : CollatzResearch.WordTrace tailWord_1480579 prefixEnd_1480579 760248673953267961553447 := by
  unfold tailWord_1480579
  simp only [CollatzResearch.WordTrace]
  refine ⟨54001152503122620606876791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36000768335415080404584527 54001152503122620606876791)
  ·
    refine ⟨81001728754683930910315187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54001152503122620606876791 81001728754683930910315187)
    ·
      refine ⟨121502593132025896365472781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81001728754683930910315187 121502593132025896365472781)
      ·
        refine ⟨45563472424509711137052293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121502593132025896365472781 45563472424509711137052293)
        ·
          refine ⟨8543151079595570838197305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45563472424509711137052293 8543151079595570838197305)
          ·
            refine ⟨6407363309696678128647979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8543151079595570838197305 6407363309696678128647979)
            ·
              refine ⟨9611044964545017192971969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6407363309696678128647979 9611044964545017192971969)
              ·
                refine ⟨7208283723408762894728977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9611044964545017192971969 7208283723408762894728977)
                ·
                  refine ⟨5406212792556572171046733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7208283723408762894728977 5406212792556572171046733)
                  ·
                    refine ⟨2027329797208714564142525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5406212792556572171046733 2027329797208714564142525)
                    ·
                      refine ⟨760248673953267961553447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2027329797208714564142525 760248673953267961553447)
                      ·
                        rfl

theorem cell23_1480579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 3, 3].length) (baseStart_1480579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480579 prefixEnd_1480579 := by exact prefixLift 1480579
  have htrace : WordTrace (prefixWord ++ tailWord_1480579) baseStart_1480579 baseEnd_1480579 := by
    simpa [prefixWord, tailWord_1480579, baseEnd_1480579] using wordTrace_append hprefix tailTrace_1480579
  have hstable : (prefixWord ++ tailWord_1480579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480579).length < 2 ^ (prefixWord ++ tailWord_1480579).sum := by decide
  have hdescent : baseEnd_1480579 < baseStart_1480579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480586 : List Nat := [3, 1, 2, 4, 2, 1, 2, 1, 7]
def baseStart_1480586 : Nat := 118140960795 + 1480586 * 2 ^ 59
def prefixEnd_1480586 : Nat := 4983230072969 + 3 ^ 40 * 1480586 * 2
def baseEnd_1480586 : Nat := 84472474257538826018435

theorem tailTrace_1480586 : CollatzResearch.WordTrace tailWord_1480586 prefixEnd_1480586 84472474257538826018435 := by
  unfold tailWord_1480586
  simp only [CollatzResearch.WordTrace]
  refine ⟨13500351953524315200595403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36000938542731507201587741 13500351953524315200595403)
  ·
    refine ⟨20250527930286472800893105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13500351953524315200595403 20250527930286472800893105)
    ·
      refine ⟨15187895947714854600669829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20250527930286472800893105 15187895947714854600669829)
      ·
        refine ⟨2847730490196535237625593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15187895947714854600669829 2847730490196535237625593)
        ·
          refine ⟨2135797867647401428219195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2847730490196535237625593 2135797867647401428219195)
          ·
            refine ⟨3203696801471102142328793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2135797867647401428219195 3203696801471102142328793)
            ·
              refine ⟨2402772601103326606746595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3203696801471102142328793 2402772601103326606746595)
              ·
                refine ⟨3604158901654989910119893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2402772601103326606746595 3604158901654989910119893)
                ·
                  refine ⟨84472474257538826018435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3604158901654989910119893 84472474257538826018435)
                  ·
                    rfl

theorem cell23_1480586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 7].length) (baseStart_1480586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480586 prefixEnd_1480586 := by exact prefixLift 1480586
  have htrace : WordTrace (prefixWord ++ tailWord_1480586) baseStart_1480586 baseEnd_1480586 := by
    simpa [prefixWord, tailWord_1480586, baseEnd_1480586] using wordTrace_append hprefix tailTrace_1480586
  have hstable : (prefixWord ++ tailWord_1480586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480586).length < 2 ^ (prefixWord ++ tailWord_1480586).sum := by decide
  have hdescent : baseEnd_1480586 < baseStart_1480586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480596 : List Nat := [2, 4, 2, 1, 1, 2, 2, 1, 2, 3, 3]
def baseStart_1480596 : Nat := 118140960795 + 1480596 * 2 ^ 59
def prefixEnd_1480596 : Nat := 4983230072969 + 3 ^ 40 * 1480596 * 2
def baseEnd_1480596 : Nat := 760257403124394395040869

theorem tailTrace_1480596 : CollatzResearch.WordTrace tailWord_1480596 prefixEnd_1480596 760257403124394395040869 := by
  unfold tailWord_1480596
  simp only [CollatzResearch.WordTrace]
  refine ⟨27000886272030516255122821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36001181696040688340163761 27000886272030516255122821)
  ·
    refine ⟨5062666176005721797835529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27000886272030516255122821 5062666176005721797835529)
    ·
      refine ⟨3796999632004291348376647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5062666176005721797835529 3796999632004291348376647)
      ·
        refine ⟨5695499448006437022564971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3796999632004291348376647 5695499448006437022564971)
        ·
          refine ⟨8543249172009655533847457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5695499448006437022564971 8543249172009655533847457)
          ·
            refine ⟨6407436879007241650385593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8543249172009655533847457 6407436879007241650385593)
            ·
              refine ⟨4805577659255431237789195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6407436879007241650385593 4805577659255431237789195)
              ·
                refine ⟨7208366488883146856683793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4805577659255431237789195 7208366488883146856683793)
                ·
                  refine ⟨5406274866662360142512845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7208366488883146856683793 5406274866662360142512845)
                  ·
                    refine ⟨2027353074998385053442317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5406274866662360142512845 2027353074998385053442317)
                    ·
                      refine ⟨760257403124394395040869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2027353074998385053442317 760257403124394395040869)
                      ·
                        rfl

theorem cell23_1480596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_1480596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480596 prefixEnd_1480596 := by exact prefixLift 1480596
  have htrace : WordTrace (prefixWord ++ tailWord_1480596) baseStart_1480596 baseEnd_1480596 := by
    simpa [prefixWord, tailWord_1480596, baseEnd_1480596] using wordTrace_append hprefix tailTrace_1480596
  have hstable : (prefixWord ++ tailWord_1480596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480596).length < 2 ^ (prefixWord ++ tailWord_1480596).sum := by decide
  have hdescent : baseEnd_1480596 < baseStart_1480596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480724 : List Nat := [2, 4, 3, 2, 2, 1, 1, 1, 2, 2, 3]
def baseStart_1480724 : Nat := 118140960795 + 1480724 * 2 ^ 59
def prefixEnd_1480724 : Nat := 4983230072969 + 3 ^ 40 * 1480724 * 2
def baseEnd_1480724 : Nat := 760323128648169894240281

theorem tailTrace_1480724 : CollatzResearch.WordTrace tailWord_1480724 prefixEnd_1480724 760323128648169894240281 := by
  unfold tailWord_1480724
  simp only [CollatzResearch.WordTrace]
  refine ⟨27003220543798655185452613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36004294058398206913936817 27003220543798655185452613)
  ·
    refine ⟨5063103851962247847272365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27003220543798655185452613 5063103851962247847272365)
    ·
      refine ⟨1898663944485842942727137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5063103851962247847272365 1898663944485842942727137)
      ·
        refine ⟨1423997958364382207045353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1898663944485842942727137 1423997958364382207045353)
        ·
          refine ⟨1067998468773286655284015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1423997958364382207045353 1067998468773286655284015)
          ·
            refine ⟨1601997703159929982926023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1067998468773286655284015 1601997703159929982926023)
            ·
              refine ⟨2402996554739894974389035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1601997703159929982926023 2402996554739894974389035)
              ·
                refine ⟨3604494832109842461583553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2402996554739894974389035 3604494832109842461583553)
                ·
                  refine ⟨2703371124082381846187665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3604494832109842461583553 2703371124082381846187665)
                  ·
                    refine ⟨2027528343061786384640749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2703371124082381846187665 2027528343061786384640749)
                    ·
                      refine ⟨760323128648169894240281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2027528343061786384640749 760323128648169894240281)
                      ·
                        rfl

theorem cell23_1480724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_1480724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480724 prefixEnd_1480724 := by exact prefixLift 1480724
  have htrace : WordTrace (prefixWord ++ tailWord_1480724) baseStart_1480724 baseEnd_1480724 := by
    simpa [prefixWord, tailWord_1480724, baseEnd_1480724] using wordTrace_append hprefix tailTrace_1480724
  have hstable : (prefixWord ++ tailWord_1480724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480724).length < 2 ^ (prefixWord ++ tailWord_1480724).sum := by decide
  have hdescent : baseEnd_1480724 < baseStart_1480724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480730 : List Nat := [3, 1, 1, 3, 1, 5, 1, 1, 2, 3, 2]
def baseStart_1480730 : Nat := 118140960795 + 1480730 * 2 ^ 59
def prefixEnd_1480730 : Nat := 4983230072969 + 3 ^ 40 * 1480730 * 2
def baseEnd_1480730 : Nat := 760326209532096870765253

theorem tailTrace_1480730 : CollatzResearch.WordTrace tailWord_1480730 prefixEnd_1480730 760326209532096870765253 := by
  unfold tailWord_1480730
  simp only [CollatzResearch.WordTrace]
  refine ⟨13501664981393893348905911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36004439950383715597082429 13501664981393893348905911)
  ·
    refine ⟨20252497472090840023358867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13501664981393893348905911 20252497472090840023358867)
    ·
      refine ⟨30378746208136260035038301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20252497472090840023358867 30378746208136260035038301)
      ·
        refine ⟨11392029828051097513139363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30378746208136260035038301 11392029828051097513139363)
        ·
          refine ⟨17088044742076646269709045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11392029828051097513139363 17088044742076646269709045)
          ·
            refine ⟨1602004194569685587785223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17088044742076646269709045 1602004194569685587785223)
            ·
              refine ⟨2403006291854528381677835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1602004194569685587785223 2403006291854528381677835)
              ·
                refine ⟨3604509437781792572516753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2403006291854528381677835 3604509437781792572516753)
                ·
                  refine ⟨2703382078336344429387565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3604509437781792572516753 2703382078336344429387565)
                  ·
                    refine ⟨1013768279376129161020337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2703382078336344429387565 1013768279376129161020337)
                    ·
                      refine ⟨760326209532096870765253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1013768279376129161020337 760326209532096870765253)
                      ·
                        rfl

theorem cell23_1480730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 2, 3, 2].length) (baseStart_1480730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480730 prefixEnd_1480730 := by exact prefixLift 1480730
  have htrace : WordTrace (prefixWord ++ tailWord_1480730) baseStart_1480730 baseEnd_1480730 := by
    simpa [prefixWord, tailWord_1480730, baseEnd_1480730] using wordTrace_append hprefix tailTrace_1480730
  have hstable : (prefixWord ++ tailWord_1480730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480730).length < 2 ^ (prefixWord ++ tailWord_1480730).sum := by decide
  have hdescent : baseEnd_1480730 < baseStart_1480730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480737 : List Nat := [1, 2, 3, 2, 4, 1, 2, 3, 1, 1, 3]
def baseStart_1480737 : Nat := 118140960795 + 1480737 * 2 ^ 59
def prefixEnd_1480737 : Nat := 4983230072969 + 3 ^ 40 * 1480737 * 2
def baseEnd_1480737 : Nat := 760329803896678343377721

theorem tailTrace_1480737 : CollatzResearch.WordTrace tailWord_1480737 prefixEnd_1480737 760329803896678343377721 := by
  unfold tailWord_1480737
  simp only [CollatzResearch.WordTrace]
  refine ⟨54006915236550213591128465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36004610157700142394085643 54006915236550213591128465)
  ·
    refine ⟨40505186427412660193346349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54006915236550213591128465 40505186427412660193346349)
    ·
      refine ⟨15189444910279747572504881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40505186427412660193346349 15189444910279747572504881)
      ·
        refine ⟨11392083682709810679378661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15189444910279747572504881 11392083682709810679378661)
        ·
          refine ⟨2136015690508089502383499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11392083682709810679378661 2136015690508089502383499)
          ·
            refine ⟨3204023535762134253575249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2136015690508089502383499 3204023535762134253575249)
            ·
              refine ⟨2403017651821600690181437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3204023535762134253575249 2403017651821600690181437)
              ·
                refine ⟨901131619433100258818039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2403017651821600690181437 901131619433100258818039)
                ·
                  refine ⟨1351697429149650388227059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 901131619433100258818039 1351697429149650388227059)
                  ·
                    refine ⟨2027546143724475582340589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1351697429149650388227059 2027546143724475582340589)
                    ·
                      refine ⟨760329803896678343377721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2027546143724475582340589 760329803896678343377721)
                      ·
                        rfl

theorem cell23_1480737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 3, 1, 1, 3].length) (baseStart_1480737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480737 prefixEnd_1480737 := by exact prefixLift 1480737
  have htrace : WordTrace (prefixWord ++ tailWord_1480737) baseStart_1480737 baseEnd_1480737 := by
    simpa [prefixWord, tailWord_1480737, baseEnd_1480737] using wordTrace_append hprefix tailTrace_1480737
  have hstable : (prefixWord ++ tailWord_1480737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480737).length < 2 ^ (prefixWord ++ tailWord_1480737).sum := by decide
  have hdescent : baseEnd_1480737 < baseStart_1480737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480753 : List Nat := [1, 2, 2, 3, 1, 3, 3, 2, 2, 4]
def baseStart_1480753 : Nat := 118140960795 + 1480753 * 2 ^ 59
def prefixEnd_1480753 : Nat := 4983230072969 + 3 ^ 40 * 1480753 * 2
def baseEnd_1480753 : Nat := 253446006529050093592549

theorem tailTrace_1480753 : CollatzResearch.WordTrace tailWord_1480753 prefixEnd_1480753 253446006529050093592549 := by
  unfold tailWord_1480753
  simp only [CollatzResearch.WordTrace]
  refine ⟨54007498804492248323710913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36004999202994832215807275 54007498804492248323710913)
  ·
    refine ⟨40505624103369186242783185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54007498804492248323710913 40505624103369186242783185)
    ·
      refine ⟨30379218077526889682087389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40505624103369186242783185 30379218077526889682087389)
      ·
        refine ⟨11392206779072583630782771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30379218077526889682087389 11392206779072583630782771)
        ·
          refine ⟨17088310168608875446174157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11392206779072583630782771 17088310168608875446174157)
          ·
            refine ⟨6408116313228328292315309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17088310168608875446174157 6408116313228328292315309)
            ·
              refine ⟨2403043617460623109618241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6408116313228328292315309 2403043617460623109618241)
              ·
                refine ⟨1802282713095467332213681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2403043617460623109618241 1802282713095467332213681)
                ·
                  refine ⟨1351712034821600499160261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1802282713095467332213681 1351712034821600499160261)
                  ·
                    refine ⟨253446006529050093592549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1351712034821600499160261 253446006529050093592549)
                    ·
                      rfl

theorem cell23_1480753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 2, 2, 4].length) (baseStart_1480753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480753 prefixEnd_1480753 := by exact prefixLift 1480753
  have htrace : WordTrace (prefixWord ++ tailWord_1480753) baseStart_1480753 baseEnd_1480753 := by
    simpa [prefixWord, tailWord_1480753, baseEnd_1480753] using wordTrace_append hprefix tailTrace_1480753
  have hstable : (prefixWord ++ tailWord_1480753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480753).length < 2 ^ (prefixWord ++ tailWord_1480753).sum := by decide
  have hdescent : baseEnd_1480753 < baseStart_1480753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480776 : List Nat := [2, 1, 3, 1, 1, 1, 2, 5, 1, 3, 3]
def baseStart_1480776 : Nat := 118140960795 + 1480776 * 2 ^ 59
def prefixEnd_1480776 : Nat := 4983230072969 + 3 ^ 40 * 1480776 * 2
def baseEnd_1480776 : Nat := 760349829642203690790041

theorem tailTrace_1480776 : CollatzResearch.WordTrace tailWord_1480776 prefixEnd_1480776 760349829642203690790041 := by
  unfold tailWord_1480776
  simp only [CollatzResearch.WordTrace]
  refine ⟨27004168841704461625899091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36005558455605948834532121 27004168841704461625899091)
  ·
    refine ⟨40506253262556692438848637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27004168841704461625899091 40506253262556692438848637)
    ·
      refine ⟨15189844973458759664568239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40506253262556692438848637 15189844973458759664568239)
      ·
        refine ⟨22784767460188139496852359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15189844973458759664568239 22784767460188139496852359)
        ·
          refine ⟨34177151190282209245278539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22784767460188139496852359 34177151190282209245278539)
          ·
            refine ⟨51265726785423313867917809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34177151190282209245278539 51265726785423313867917809)
            ·
              refine ⟨38449295089067485400938357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51265726785423313867917809 38449295089067485400938357)
              ·
                refine ⟨3604621414600076756337971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38449295089067485400938357 3604621414600076756337971)
                ·
                  refine ⟨5406932121900115134506957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3604621414600076756337971 5406932121900115134506957)
                  ·
                    refine ⟨2027599545712543175440109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5406932121900115134506957 2027599545712543175440109)
                    ·
                      refine ⟨760349829642203690790041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2027599545712543175440109 760349829642203690790041)
                      ·
                        rfl

theorem cell23_1480776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 1, 3, 3].length) (baseStart_1480776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480776 prefixEnd_1480776 := by exact prefixLift 1480776
  have htrace : WordTrace (prefixWord ++ tailWord_1480776) baseStart_1480776 baseEnd_1480776 := by
    simpa [prefixWord, tailWord_1480776, baseEnd_1480776] using wordTrace_append hprefix tailTrace_1480776
  have hstable : (prefixWord ++ tailWord_1480776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480776).length < 2 ^ (prefixWord ++ tailWord_1480776).sum := by decide
  have hdescent : baseEnd_1480776 < baseStart_1480776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480836 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 4, 1, 5]
def baseStart_1480836 : Nat := 118140960795 + 1480836 * 2 ^ 59
def prefixEnd_1480836 : Nat := 4983230072969 + 3 ^ 40 * 1480836 * 2
def baseEnd_1480836 : Nat := 760380638481473456039765

theorem tailTrace_1480836 : CollatzResearch.WordTrace tailWord_1480836 prefixEnd_1480836 760380638481473456039765 := by
  unfold tailWord_1480836
  simp only [CollatzResearch.WordTrace]
  refine ⟨27005263031595776749491181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36007017375461035665988241 27005263031595776749491181)
  ·
    refine ⟨10126973636848416281059193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27005263031595776749491181 10126973636848416281059193)
    ·
      refine ⟨7595230227636312210794395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10126973636848416281059193 7595230227636312210794395)
      ·
        refine ⟨11392845341454468316191593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7595230227636312210794395 11392845341454468316191593)
        ·
          refine ⟨8544634006090851237143695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11392845341454468316191593 8544634006090851237143695)
          ·
            refine ⟨12816951009136276855715543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8544634006090851237143695 12816951009136276855715543)
            ·
              refine ⟨19225426513704415283573315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12816951009136276855715543 19225426513704415283573315)
              ·
                refine ⟨28838139770556622925359973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19225426513704415283573315 28838139770556622925359973)
                ·
                  refine ⟨5407151206979366798504995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28838139770556622925359973 5407151206979366798504995)
                  ·
                    refine ⟨8110726810469050197757493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5407151206979366798504995 8110726810469050197757493)
                    ·
                      refine ⟨760380638481473456039765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8110726810469050197757493 760380638481473456039765)
                      ·
                        rfl

theorem cell23_1480836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_1480836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480836 prefixEnd_1480836 := by exact prefixLift 1480836
  have htrace : WordTrace (prefixWord ++ tailWord_1480836) baseStart_1480836 baseEnd_1480836 := by
    simpa [prefixWord, tailWord_1480836, baseEnd_1480836] using wordTrace_append hprefix tailTrace_1480836
  have hstable : (prefixWord ++ tailWord_1480836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480836).length < 2 ^ (prefixWord ++ tailWord_1480836).sum := by decide
  have hdescent : baseEnd_1480836 < baseStart_1480836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480837 : List Nat := [1, 3, 1, 1, 5, 3, 1, 2, 1, 3, 2]
def baseStart_1480837 : Nat := 118140960795 + 1480837 * 2 ^ 59
def prefixEnd_1480837 : Nat := 4983230072969 + 3 ^ 40 * 1480837 * 2
def baseEnd_1480837 : Nat := 760381151962127952127261

theorem tailTrace_1480837 : CollatzResearch.WordTrace tailWord_1480837 prefixEnd_1480837 760381151962127952127261 := by
  unfold tailWord_1480837
  simp only [CollatzResearch.WordTrace]
  refine ⟨54010562536187930669768765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36007041690791953779845843 54010562536187930669768765)
  ·
    refine ⟨20253960951070474001163287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54010562536187930669768765 20253960951070474001163287)
    ·
      refine ⟨30380941426605711001744931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20253960951070474001163287 30380941426605711001744931)
      ·
        refine ⟨45571412139908566502617397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30380941426605711001744931 45571412139908566502617397)
        ·
          refine ⟨4272319888116428109620381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45571412139908566502617397 4272319888116428109620381)
          ·
            refine ⟨1602119958043660541107643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4272319888116428109620381 1602119958043660541107643)
            ·
              refine ⟨2403179937065490811661465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1602119958043660541107643 2403179937065490811661465)
              ·
                refine ⟨1802384952799118108746099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2403179937065490811661465 1802384952799118108746099)
                ·
                  refine ⟨2703577429198677163119149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1802384952799118108746099 2703577429198677163119149)
                  ·
                    refine ⟨1013841535949503936169681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2703577429198677163119149 1013841535949503936169681)
                    ·
                      refine ⟨760381151962127952127261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1013841535949503936169681 760381151962127952127261)
                      ·
                        rfl

theorem cell23_1480837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 2, 1, 3, 2].length) (baseStart_1480837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480837 prefixEnd_1480837 := by exact prefixLift 1480837
  have htrace : WordTrace (prefixWord ++ tailWord_1480837) baseStart_1480837 baseEnd_1480837 := by
    simpa [prefixWord, tailWord_1480837, baseEnd_1480837] using wordTrace_append hprefix tailTrace_1480837
  have hstable : (prefixWord ++ tailWord_1480837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480837).length < 2 ^ (prefixWord ++ tailWord_1480837).sum := by decide
  have hdescent : baseEnd_1480837 < baseStart_1480837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480850 : List Nat := [3, 2, 3, 1, 1, 1, 3, 2, 1, 4, 2]
def baseStart_1480850 : Nat := 118140960795 + 1480850 * 2 ^ 59
def prefixEnd_1480850 : Nat := 4983230072969 + 3 ^ 40 * 1480850 * 2
def baseEnd_1480850 : Nat := 760387827210636401264701

theorem tailTrace_1480850 : CollatzResearch.WordTrace tailWord_1480850 prefixEnd_1480850 760387827210636401264701 := by
  unfold tailWord_1480850
  simp only [CollatzResearch.WordTrace]
  refine ⟨13502759171285208472498001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36007357790093889259994669 13502759171285208472498001)
  ·
    refine ⟨10127069378463906354373501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13502759171285208472498001 10127069378463906354373501)
    ·
      refine ⟨3797651016923964882890063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10127069378463906354373501 3797651016923964882890063)
      ·
        refine ⟨5696476525385947324335095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3797651016923964882890063 5696476525385947324335095)
        ·
          refine ⟨8544714788078920986502643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5696476525385947324335095 8544714788078920986502643)
          ·
            refine ⟨12817072182118381479753965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8544714788078920986502643 12817072182118381479753965)
            ·
              refine ⟨4806402068294393054907737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12817072182118381479753965 4806402068294393054907737)
              ·
                refine ⟨3604801551220794791180803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4806402068294393054907737 3604801551220794791180803)
                ·
                  refine ⟨5407202326831192186771205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3604801551220794791180803 5407202326831192186771205)
                  ·
                    refine ⟨1013850436280848535019601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5407202326831192186771205 1013850436280848535019601)
                    ·
                      refine ⟨760387827210636401264701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1013850436280848535019601 760387827210636401264701)
                      ·
                        rfl

theorem cell23_1480850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_1480850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480850 prefixEnd_1480850 := by exact prefixLift 1480850
  have htrace : WordTrace (prefixWord ++ tailWord_1480850) baseStart_1480850 baseEnd_1480850 := by
    simpa [prefixWord, tailWord_1480850, baseEnd_1480850] using wordTrace_append hprefix tailTrace_1480850
  have hstable : (prefixWord ++ tailWord_1480850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480850).length < 2 ^ (prefixWord ++ tailWord_1480850).sum := by decide
  have hdescent : baseEnd_1480850 < baseStart_1480850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480893 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 4, 5, 2]
def baseStart_1480893 : Nat := 118140960795 + 1480893 * 2 ^ 59
def prefixEnd_1480893 : Nat := 4983230072969 + 3 ^ 40 * 1480893 * 2
def baseEnd_1480893 : Nat := 760409906878779733027003

theorem tailTrace_1480893 : CollatzResearch.WordTrace tailWord_1480893 prefixEnd_1480893 760409906878779733027003 := by
  unfold tailWord_1480893
  simp only [CollatzResearch.WordTrace]
  refine ⟨54012605023985052233807333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36008403349323368155871555 54012605023985052233807333)
  ·
    refine ⟨10127363441997197293838875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54012605023985052233807333 10127363441997197293838875)
    ·
      refine ⟨15191045162995795940758313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10127363441997197293838875 15191045162995795940758313)
      ·
        refine ⟨11393283872246846955568735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15191045162995795940758313 11393283872246846955568735)
        ·
          refine ⟨17089925808370270433353103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11393283872246846955568735 17089925808370270433353103)
          ·
            refine ⟨25634888712555405650029655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17089925808370270433353103 25634888712555405650029655)
            ·
              refine ⟨38452333068833108475044483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25634888712555405650029655 38452333068833108475044483)
              ·
                refine ⟨57678499603249662712566725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38452333068833108475044483 57678499603249662712566725)
                ·
                  refine ⟨10814718675609311758606261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57678499603249662712566725 10814718675609311758606261)
                  ·
                    refine ⟨1013879875838372977369337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10814718675609311758606261 1013879875838372977369337)
                    ·
                      refine ⟨760409906878779733027003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1013879875838372977369337 760409906878779733027003)
                      ·
                        rfl

theorem cell23_1480893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 5, 2].length) (baseStart_1480893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480893 prefixEnd_1480893 := by exact prefixLift 1480893
  have htrace : WordTrace (prefixWord ++ tailWord_1480893) baseStart_1480893 baseEnd_1480893 := by
    simpa [prefixWord, tailWord_1480893, baseEnd_1480893] using wordTrace_append hprefix tailTrace_1480893
  have hstable : (prefixWord ++ tailWord_1480893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480893).length < 2 ^ (prefixWord ++ tailWord_1480893).sum := by decide
  have hdescent : baseEnd_1480893 < baseStart_1480893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480923 : List Nat := [1, 1, 1, 1, 1, 1, 1, 8, 2, 4, 2]
def baseStart_1480923 : Nat := 118140960795 + 1480923 * 2 ^ 59
def prefixEnd_1480923 : Nat := 4983230072969 + 3 ^ 40 * 1480923 * 2
def baseEnd_1480923 : Nat := 760425311298414615651865

theorem tailTrace_1480923 : CollatzResearch.WordTrace tailWord_1480923 prefixEnd_1480923 760425311298414615651865 := by
  unfold tailWord_1480923
  simp only [CollatzResearch.WordTrace]
  refine ⟨54013699213876367357399423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36009132809250911571599615 54013699213876367357399423)
  ·
    refine ⟨81020548820814551036099135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54013699213876367357399423 81020548820814551036099135)
    ·
      refine ⟨121530823231221826554148703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81020548820814551036099135 121530823231221826554148703)
      ·
        refine ⟨182296234846832739831223055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121530823231221826554148703 182296234846832739831223055)
        ·
          refine ⟨273444352270249109746834583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182296234846832739831223055 273444352270249109746834583)
          ·
            refine ⟨410166528405373664620251875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273444352270249109746834583 410166528405373664620251875)
            ·
              refine ⟨615249792608060496930377813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 410166528405373664620251875 615249792608060496930377813)
              ·
                refine ⟨7209958507125708948402865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 615249792608060496930377813 7209958507125708948402865)
                ·
                  refine ⟨5407468880344281711302149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7209958507125708948402865 5407468880344281711302149)
                  ·
                    refine ⟨1013900415064552820869153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5407468880344281711302149 1013900415064552820869153)
                    ·
                      refine ⟨760425311298414615651865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1013900415064552820869153 760425311298414615651865)
                      ·
                        rfl

theorem cell23_1480923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 4, 2].length) (baseStart_1480923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480923 prefixEnd_1480923 := by exact prefixLift 1480923
  have htrace : WordTrace (prefixWord ++ tailWord_1480923) baseStart_1480923 baseEnd_1480923 := by
    simpa [prefixWord, tailWord_1480923, baseEnd_1480923] using wordTrace_append hprefix tailTrace_1480923
  have hstable : (prefixWord ++ tailWord_1480923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480923).length < 2 ^ (prefixWord ++ tailWord_1480923).sum := by decide
  have hdescent : baseEnd_1480923 < baseStart_1480923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480943 : List Nat := [1, 1, 2, 1, 6, 1, 1, 2, 1, 4, 3]
def baseStart_1480943 : Nat := 118140960795 + 1480943 * 2 ^ 59
def prefixEnd_1480943 : Nat := 4983230072969 + 3 ^ 40 * 1480943 * 2
def baseEnd_1480943 : Nat := 760435580911504537401773

theorem tailTrace_1480943 : CollatzResearch.WordTrace tailWord_1480943 prefixEnd_1480943 760435580911504537401773 := by
  unfold tailWord_1480943
  simp only [CollatzResearch.WordTrace]
  refine ⟨54014428673803910773127483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36009619115869273848751655 54014428673803910773127483)
  ·
    refine ⟨81021643010705866159691225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54014428673803910773127483 81021643010705866159691225)
    ·
      refine ⟨60766232258029399619768419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81021643010705866159691225 60766232258029399619768419)
      ·
        refine ⟨91149348387044099429652629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60766232258029399619768419 91149348387044099429652629)
        ·
          refine ⟨4272625705642692160764967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 91149348387044099429652629 4272625705642692160764967)
          ·
            refine ⟨6408938558464038241147451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4272625705642692160764967 6408938558464038241147451)
            ·
              refine ⟨9613407837696057361721177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6408938558464038241147451 9613407837696057361721177)
              ·
                refine ⟨7210055878272043021290883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9613407837696057361721177 7210055878272043021290883)
                ·
                  refine ⟨10815083817408064531936325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7210055878272043021290883 10815083817408064531936325)
                  ·
                    refine ⟨2027828215764012099738061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10815083817408064531936325 2027828215764012099738061)
                    ·
                      refine ⟨760435580911504537401773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2027828215764012099738061 760435580911504537401773)
                      ·
                        rfl

theorem cell23_1480943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 4, 3].length) (baseStart_1480943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480943 prefixEnd_1480943 := by exact prefixLift 1480943
  have htrace : WordTrace (prefixWord ++ tailWord_1480943) baseStart_1480943 baseEnd_1480943 := by
    simpa [prefixWord, tailWord_1480943, baseEnd_1480943] using wordTrace_append hprefix tailTrace_1480943
  have hstable : (prefixWord ++ tailWord_1480943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480943).length < 2 ^ (prefixWord ++ tailWord_1480943).sum := by decide
  have hdescent : baseEnd_1480943 < baseStart_1480943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480950 : List Nat := [5, 1, 1, 1, 1, 1, 4, 2, 3, 4]
def baseStart_1480950 : Nat := 118140960795 + 1480950 * 2 ^ 59
def prefixEnd_1480950 : Nat := 4983230072969 + 3 ^ 40 * 1480950 * 2
def baseEnd_1480950 : Nat := 253479725092028670004747

theorem tailTrace_1480950 : CollatzResearch.WordTrace tailWord_1480950 prefixEnd_1480950 253479725092028670004747 := by
  unfold tailWord_1480950
  simp only [CollatzResearch.WordTrace]
  refine ⟨3375917749048659435539519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36009789323185700645754869 3375917749048659435539519)
  ·
    refine ⟨5063876623572989153309279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3375917749048659435539519 5063876623572989153309279)
    ·
      refine ⟨7595814935359483729963919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5063876623572989153309279 7595814935359483729963919)
      ·
        refine ⟨11393722403039225594945879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7595814935359483729963919 11393722403039225594945879)
        ·
          refine ⟨17090583604558838392418819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11393722403039225594945879 17090583604558838392418819)
          ·
            refine ⟨25635875406838257588628229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17090583604558838392418819 25635875406838257588628229)
            ·
              refine ⟨4806726638782173297867793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25635875406838257588628229 4806726638782173297867793)
              ·
                refine ⟨3605044979086629973400845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4806726638782173297867793 3605044979086629973400845)
                ·
                  refine ⟨1351891867157486240025317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3605044979086629973400845 1351891867157486240025317)
                  ·
                    refine ⟨253479725092028670004747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1351891867157486240025317 253479725092028670004747)
                    ·
                      rfl

theorem cell23_1480950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_1480950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480950 prefixEnd_1480950 := by exact prefixLift 1480950
  have htrace : WordTrace (prefixWord ++ tailWord_1480950) baseStart_1480950 baseEnd_1480950 := by
    simpa [prefixWord, tailWord_1480950, baseEnd_1480950] using wordTrace_append hprefix tailTrace_1480950
  have hstable : (prefixWord ++ tailWord_1480950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480950).length < 2 ^ (prefixWord ++ tailWord_1480950).sum := by decide
  have hdescent : baseEnd_1480950 < baseStart_1480950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480997 : List Nat := [1, 3, 1, 2, 5, 2, 2, 1, 6]
def baseStart_1480997 : Nat := 118140960795 + 1480997 * 2 ^ 59
def prefixEnd_1480997 : Nat := 4983230072969 + 3 ^ 40 * 1480997 * 2
def baseEnd_1480997 : Nat := 84495923207427480680725

theorem tailTrace_1480997 : CollatzResearch.WordTrace tailWord_1480997 prefixEnd_1480997 84495923207427480680725 := by
  unfold tailWord_1480997
  simp only [CollatzResearch.WordTrace]
  refine ⟨54016398215608277995593245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36010932143738851997062163 54016398215608277995593245)
  ·
    refine ⟨20256149330853104248347467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54016398215608277995593245 20256149330853104248347467)
    ·
      refine ⟨30384223996279656372521201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20256149330853104248347467 30384223996279656372521201)
      ·
        refine ⟨22788167997209742279390901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30384223996279656372521201 22788167997209742279390901)
        ·
          refine ⟨2136390749738413338692897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22788167997209742279390901 2136390749738413338692897)
          ·
            refine ⟨1602293062303810004019673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2136390749738413338692897 1602293062303810004019673)
            ·
              refine ⟨1201719796727857503014755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1602293062303810004019673 1201719796727857503014755)
              ·
                refine ⟨1802579695091786254522133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1201719796727857503014755 1802579695091786254522133)
                ·
                  refine ⟨84495923207427480680725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1802579695091786254522133 84495923207427480680725)
                  ·
                    rfl

theorem cell23_1480997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 1, 6].length) (baseStart_1480997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1480997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1480997 prefixEnd_1480997 := by exact prefixLift 1480997
  have htrace : WordTrace (prefixWord ++ tailWord_1480997) baseStart_1480997 baseEnd_1480997 := by
    simpa [prefixWord, tailWord_1480997, baseEnd_1480997] using wordTrace_append hprefix tailTrace_1480997
  have hstable : (prefixWord ++ tailWord_1480997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480997).length < 2 ^ (prefixWord ++ tailWord_1480997).sum := by decide
  have hdescent : baseEnd_1480997 < baseStart_1480997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481010 : List Nat := [3, 2, 1, 1, 5, 1, 1, 1, 3, 5]
def baseStart_1481010 : Nat := 118140960795 + 1481010 * 2 ^ 59
def prefixEnd_1481010 : Nat := 4983230072969 + 3 ^ 40 * 1481010 * 2
def baseEnd_1481010 : Nat := 253489994705118591754655

theorem tailTrace_1481010 : CollatzResearch.WordTrace tailWord_1481010 prefixEnd_1481010 253489994705118591754655 := by
  unfold tailWord_1481010
  simp only [CollatzResearch.WordTrace]
  refine ⟨13504218091140295303954121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36011248243040787477210989 13504218091140295303954121)
  ·
    refine ⟨10128163568355221477965591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13504218091140295303954121 10128163568355221477965591)
    ·
      refine ⟨15192245352532832216948387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10128163568355221477965591 15192245352532832216948387)
      ·
        refine ⟨22788368028799248325422581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15192245352532832216948387 22788368028799248325422581)
        ·
          refine ⟨2136409502699929530508367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22788368028799248325422581 2136409502699929530508367)
          ·
            refine ⟨3204614254049894295762551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2136409502699929530508367 3204614254049894295762551)
            ·
              refine ⟨4806921381074841443643827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3204614254049894295762551 4806921381074841443643827)
              ·
                refine ⟨7210382071612262165465741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4806921381074841443643827 7210382071612262165465741)
                ·
                  refine ⟨2703893276854598312049653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7210382071612262165465741 2703893276854598312049653)
                  ·
                    refine ⟨253489994705118591754655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2703893276854598312049653 253489994705118591754655)
                    ·
                      rfl

theorem cell23_1481010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 3, 5].length) (baseStart_1481010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481010 prefixEnd_1481010 := by exact prefixLift 1481010
  have htrace : WordTrace (prefixWord ++ tailWord_1481010) baseStart_1481010 baseEnd_1481010 := by
    simpa [prefixWord, tailWord_1481010, baseEnd_1481010] using wordTrace_append hprefix tailTrace_1481010
  have hstable : (prefixWord ++ tailWord_1481010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481010).length < 2 ^ (prefixWord ++ tailWord_1481010).sum := by decide
  have hdescent : baseEnd_1481010 < baseStart_1481010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481017 : List Nat := [1, 2, 1, 6, 1, 1, 1, 3, 2, 3, 2]
def baseStart_1481017 : Nat := 118140960795 + 1481017 * 2 ^ 59
def prefixEnd_1481017 : Nat := 4983230072969 + 3 ^ 40 * 1481017 * 2
def baseEnd_1481017 : Nat := 760473578479937247876433

theorem tailTrace_1481017 : CollatzResearch.WordTrace tailWord_1481017 prefixEnd_1481017 760473578479937247876433 := by
  unfold tailWord_1481017
  simp only [CollatzResearch.WordTrace]
  refine ⟨54017127675535821411321305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36011418450357214274214203 54017127675535821411321305)
  ·
    refine ⟨40512845756651866058490979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54017127675535821411321305 40512845756651866058490979)
    ·
      refine ⟨60769268634977799087736469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40512845756651866058490979 60769268634977799087736469)
      ·
        refine ⟨2848559467264584332237647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 60769268634977799087736469 2848559467264584332237647)
        ·
          refine ⟨4272839200896876498356471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2848559467264584332237647 4272839200896876498356471)
          ·
            refine ⟨6409258801345314747534707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4272839200896876498356471 6409258801345314747534707)
            ·
              refine ⟨9613888202017972121302061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6409258801345314747534707 9613888202017972121302061)
              ·
                refine ⟨3605208075756739545488273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9613888202017972121302061 3605208075756739545488273)
                ·
                  refine ⟨2703906056817554659116205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3605208075756739545488273 2703906056817554659116205)
                  ·
                    refine ⟨1013964771306582997168577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2703906056817554659116205 1013964771306582997168577)
                    ·
                      refine ⟨760473578479937247876433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1013964771306582997168577 760473578479937247876433)
                      ·
                        rfl

theorem cell23_1481017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_1481017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481017 prefixEnd_1481017 := by exact prefixLift 1481017
  have htrace : WordTrace (prefixWord ++ tailWord_1481017) baseStart_1481017 baseEnd_1481017 := by
    simpa [prefixWord, tailWord_1481017, baseEnd_1481017] using wordTrace_append hprefix tailTrace_1481017
  have hstable : (prefixWord ++ tailWord_1481017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481017).length < 2 ^ (prefixWord ++ tailWord_1481017).sum := by decide
  have hdescent : baseEnd_1481017 < baseStart_1481017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481023 : List Nat := [1, 1, 2, 2, 4, 1, 3, 2, 1, 6]
def baseStart_1481023 : Nat := 118140960795 + 1481023 * 2 ^ 59
def prefixEnd_1481023 : Nat := 4983230072969 + 3 ^ 40 * 1481023 * 2
def baseEnd_1481023 : Nat := 253492219787954741467135

theorem tailTrace_1481023 : CollatzResearch.WordTrace tailWord_1481023 prefixEnd_1481023 253492219787954741467135 := by
  unfold tailWord_1481023
  simp only [CollatzResearch.WordTrace]
  refine ⟨54017346513514084436039723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36011564342342722957359815 54017346513514084436039723)
  ·
    refine ⟨81026019770271126654059585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54017346513514084436039723 81026019770271126654059585)
    ·
      refine ⟨60769514827703344990544689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81026019770271126654059585 60769514827703344990544689)
      ·
        refine ⟨45577136120777508742908517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60769514827703344990544689 45577136120777508742908517)
        ·
          refine ⟨8545713022645782889295347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45577136120777508742908517 8545713022645782889295347)
          ·
            refine ⟨12818569533968674333943021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8545713022645782889295347 12818569533968674333943021)
            ·
              refine ⟨4806963575238252875228633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12818569533968674333943021 4806963575238252875228633)
              ·
                refine ⟨3605222681428689656421475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4806963575238252875228633 3605222681428689656421475)
                ·
                  refine ⟨5407834022143034484632213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3605222681428689656421475 5407834022143034484632213)
                  ·
                    refine ⟨253492219787954741467135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5407834022143034484632213 253492219787954741467135)
                    ·
                      rfl

theorem cell23_1481023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 6].length) (baseStart_1481023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481023 prefixEnd_1481023 := by exact prefixLift 1481023
  have htrace : WordTrace (prefixWord ++ tailWord_1481023) baseStart_1481023 baseEnd_1481023 := by
    simpa [prefixWord, tailWord_1481023, baseEnd_1481023] using wordTrace_append hprefix tailTrace_1481023
  have hstable : (prefixWord ++ tailWord_1481023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481023).length < 2 ^ (prefixWord ++ tailWord_1481023).sum := by decide
  have hdescent : baseEnd_1481023 < baseStart_1481023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481040 : List Nat := [2, 1, 1, 1, 1, 6, 1, 4, 2, 4]
def baseStart_1481040 : Nat := 118140960795 + 1481040 * 2 ^ 59
def prefixEnd_1481040 : Nat := 4983230072969 + 3 ^ 40 * 1481040 * 2
def baseEnd_1481040 : Nat := 253495129511663552629609

theorem tailTrace_1481040 : CollatzResearch.WordTrace tailWord_1481040 prefixEnd_1481040 253495129511663552629609 := by
  unfold tailWord_1481040
  simp only [CollatzResearch.WordTrace]
  refine ⟨27008983277226248169704287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36011977702968330892939049 27008983277226248169704287)
  ·
    refine ⟨40513474915839372254556431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27008983277226248169704287 40513474915839372254556431)
    ·
      refine ⟨60770212373759058381834647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40513474915839372254556431 60770212373759058381834647)
      ·
        refine ⟨91155318560638587572751971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60770212373759058381834647 91155318560638587572751971)
        ·
          refine ⟨136732977840957881359127957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91155318560638587572751971 136732977840957881359127957)
          ·
            refine ⟨6409358336294900688709123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 136732977840957881359127957 6409358336294900688709123)
            ·
              refine ⟨9614037504442351033063685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6409358336294900688709123 9614037504442351033063685)
              ·
                refine ⟨1802632032082940818699441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9614037504442351033063685 1802632032082940818699441)
                ·
                  refine ⟨1351974024062205614024581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1802632032082940818699441 1351974024062205614024581)
                  ·
                    refine ⟨253495129511663552629609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1351974024062205614024581 253495129511663552629609)
                    ·
                      rfl

theorem cell23_1481040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 4, 2, 4].length) (baseStart_1481040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481040 prefixEnd_1481040 := by exact prefixLift 1481040
  have htrace : WordTrace (prefixWord ++ tailWord_1481040) baseStart_1481040 baseEnd_1481040 := by
    simpa [prefixWord, tailWord_1481040, baseEnd_1481040] using wordTrace_append hprefix tailTrace_1481040
  have hstable : (prefixWord ++ tailWord_1481040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481040).length < 2 ^ (prefixWord ++ tailWord_1481040).sum := by decide
  have hdescent : baseEnd_1481040 < baseStart_1481040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481041 : List Nat := [1, 2, 2, 1, 4, 4, 2, 2, 1, 1, 3]
def baseStart_1481041 : Nat := 118140960795 + 1481041 * 2 ^ 59
def prefixEnd_1481041 : Nat := 4983230072969 + 3 ^ 40 * 1481041 * 2
def baseEnd_1481041 : Nat := 760485902015645153976323

theorem tailTrace_1481041 : CollatzResearch.WordTrace tailWord_1481041 prefixEnd_1481041 760485902015645153976323 := by
  unfold tailWord_1481041
  simp only [CollatzResearch.WordTrace]
  refine ⟨54018003027448873510194977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36012002018299249006796651 54018003027448873510194977)
  ·
    refine ⟨40513502270586655132646233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54018003027448873510194977 40513502270586655132646233)
    ·
      refine ⟨30385126702939991349484675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40513502270586655132646233 30385126702939991349484675)
      ·
        refine ⟨45577690054409987024227013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30385126702939991349484675 45577690054409987024227013)
        ·
          refine ⟨8545816885201872567042565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45577690054409987024227013 8545816885201872567042565)
          ·
            refine ⟨1602340665975351106320481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8545816885201872567042565 1602340665975351106320481)
            ·
              refine ⟨1201755499481513329740361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1602340665975351106320481 1201755499481513329740361)
              ·
                refine ⟨901316624611134997305271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1201755499481513329740361 901316624611134997305271)
                ·
                  refine ⟨1351974936916702495957907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 901316624611134997305271 1351974936916702495957907)
                  ·
                    refine ⟨2027962405375053743936861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1351974936916702495957907 2027962405375053743936861)
                    ·
                      refine ⟨760485902015645153976323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2027962405375053743936861 760485902015645153976323)
                      ·
                        rfl

theorem cell23_1481041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 2, 1, 1, 3].length) (baseStart_1481041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481041 prefixEnd_1481041 := by exact prefixLift 1481041
  have htrace : WordTrace (prefixWord ++ tailWord_1481041) baseStart_1481041 baseEnd_1481041 := by
    simpa [prefixWord, tailWord_1481041, baseEnd_1481041] using wordTrace_append hprefix tailTrace_1481041
  have hstable : (prefixWord ++ tailWord_1481041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481041).length < 2 ^ (prefixWord ++ tailWord_1481041).sum := by decide
  have hdescent : baseEnd_1481041 < baseStart_1481041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481047 : List Nat := [1, 1, 3, 2, 3, 1, 2, 3, 3, 2, 2]
def baseStart_1481047 : Nat := 118140960795 + 1481047 * 2 ^ 59
def prefixEnd_1481047 : Nat := 4983230072969 + 3 ^ 40 * 1481047 * 2
def baseEnd_1481047 : Nat := 760488982899572130501295

theorem tailTrace_1481047 : CollatzResearch.WordTrace tailWord_1481047 prefixEnd_1481047 760488982899572130501295 := by
  unfold tailWord_1481047
  simp only [CollatzResearch.WordTrace]
  refine ⟨54018221865427136534913395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36012147910284757689942263 54018221865427136534913395)
  ·
    refine ⟨81027332798140704802370093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54018221865427136534913395 81027332798140704802370093)
    ·
      refine ⟨30385249799302764300888785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81027332798140704802370093 30385249799302764300888785)
      ·
        refine ⟨22788937349477073225666589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30385249799302764300888785 22788937349477073225666589)
        ·
          refine ⟨8545851506053902459624971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22788937349477073225666589 8545851506053902459624971)
          ·
            refine ⟨12818777259080853689437457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8545851506053902459624971 12818777259080853689437457)
            ·
              refine ⟨9614082944310640267078093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12818777259080853689437457 9614082944310640267078093)
              ·
                refine ⟨3605281104116490100154285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9614082944310640267078093 3605281104116490100154285)
                ·
                  refine ⟨1351980414043683787557857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3605281104116490100154285 1351980414043683787557857)
                  ·
                    refine ⟨1013985310532762840668393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1351980414043683787557857 1013985310532762840668393)
                    ·
                      refine ⟨760488982899572130501295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1013985310532762840668393 760488982899572130501295)
                      ·
                        rfl

theorem cell23_1481047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 3, 2, 2].length) (baseStart_1481047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481047 prefixEnd_1481047 := by exact prefixLift 1481047
  have htrace : WordTrace (prefixWord ++ tailWord_1481047) baseStart_1481047 baseEnd_1481047 := by
    simpa [prefixWord, tailWord_1481047, baseEnd_1481047] using wordTrace_append hprefix tailTrace_1481047
  have hstable : (prefixWord ++ tailWord_1481047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481047).length < 2 ^ (prefixWord ++ tailWord_1481047).sum := by decide
  have hdescent : baseEnd_1481047 < baseStart_1481047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481060 : List Nat := [2, 3, 1, 1, 3, 1, 4, 1, 1, 2, 4]
def baseStart_1481060 : Nat := 118140960795 + 1481060 * 2 ^ 59
def prefixEnd_1481060 : Nat := 4983230072969 + 3 ^ 40 * 1481060 * 2
def baseEnd_1481060 : Nat := 760495658148080579638735

theorem tailTrace_1481060 : CollatzResearch.WordTrace tailWord_1481060 prefixEnd_1481060 760495658148080579638735 := by
  unfold tailWord_1481060
  simp only [CollatzResearch.WordTrace]
  refine ⟨27009348007190019877568317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36012464009586693170091089 27009348007190019877568317)
  ·
    refine ⟨10128505502696257454088119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27009348007190019877568317 10128505502696257454088119)
    ·
      refine ⟨15192758254044386181132179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10128505502696257454088119 15192758254044386181132179)
      ·
        refine ⟨22789137381066579271698269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15192758254044386181132179 22789137381066579271698269)
        ·
          refine ⟨8545926517899967226886851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22789137381066579271698269 8545926517899967226886851)
          ·
            refine ⟨12818889776849950840330277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8545926517899967226886851 12818889776849950840330277)
            ·
              refine ⟨2403541833159365782561927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12818889776849950840330277 2403541833159365782561927)
              ·
                refine ⟨3605312749739048673842891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2403541833159365782561927 3605312749739048673842891)
                ·
                  refine ⟨5407969124608573010764337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3605312749739048673842891 5407969124608573010764337)
                  ·
                    refine ⟨4055976843456429758073253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5407969124608573010764337 4055976843456429758073253)
                    ·
                      refine ⟨760495658148080579638735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4055976843456429758073253 760495658148080579638735)
                      ·
                        rfl

theorem cell23_1481060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 1, 2, 4].length) (baseStart_1481060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481060 prefixEnd_1481060 := by exact prefixLift 1481060
  have htrace : WordTrace (prefixWord ++ tailWord_1481060) baseStart_1481060 baseEnd_1481060 := by
    simpa [prefixWord, tailWord_1481060, baseEnd_1481060] using wordTrace_append hprefix tailTrace_1481060
  have hstable : (prefixWord ++ tailWord_1481060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481060).length < 2 ^ (prefixWord ++ tailWord_1481060).sum := by decide
  have hdescent : baseEnd_1481060 < baseStart_1481060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481064 : List Nat := [2, 1, 4, 2, 2, 2, 1, 2, 3, 2, 2]
def baseStart_1481064 : Nat := 118140960795 + 1481064 * 2 ^ 59
def prefixEnd_1481064 : Nat := 4983230072969 + 3 ^ 40 * 1481064 * 2
def baseEnd_1481064 : Nat := 760497712070698563988717

theorem tailTrace_1481064 : CollatzResearch.WordTrace tailWord_1481064 prefixEnd_1481064 760497712070698563988717 := by
  unfold tailWord_1481064
  simp only [CollatzResearch.WordTrace]
  refine ⟨27009420953182774219141123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36012561270910365625521497 27009420953182774219141123)
  ·
    refine ⟨40514131429774161328711685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27009420953182774219141123 40514131429774161328711685)
    ·
      refine ⟨7596399643082655249133441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40514131429774161328711685 7596399643082655249133441)
      ·
        refine ⟨5697299732311991436850081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7596399643082655249133441 5697299732311991436850081)
        ·
          refine ⟨4272974799233993577637561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5697299732311991436850081 4272974799233993577637561)
          ·
            refine ⟨3204731099425495183228171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4272974799233993577637561 3204731099425495183228171)
            ·
              refine ⟨4807096649138242774842257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3204731099425495183228171 4807096649138242774842257)
              ·
                refine ⟨3605322486853682081131693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4807096649138242774842257 3605322486853682081131693)
                ·
                  refine ⟨1351995932570130780424385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3605322486853682081131693 1351995932570130780424385)
                  ·
                    refine ⟨1013996949427598085318289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1351995932570130780424385 1013996949427598085318289)
                    ·
                      refine ⟨760497712070698563988717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1013996949427598085318289 760497712070698563988717)
                      ·
                        rfl

theorem cell23_1481064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_1481064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481064 prefixEnd_1481064 := by exact prefixLift 1481064
  have htrace : WordTrace (prefixWord ++ tailWord_1481064) baseStart_1481064 baseEnd_1481064 := by
    simpa [prefixWord, tailWord_1481064, baseEnd_1481064] using wordTrace_append hprefix tailTrace_1481064
  have hstable : (prefixWord ++ tailWord_1481064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481064).length < 2 ^ (prefixWord ++ tailWord_1481064).sum := by decide
  have hdescent : baseEnd_1481064 < baseStart_1481064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481078 : List Nat := [5, 1, 1, 4, 2, 1, 2, 1, 1, 5]
def baseStart_1481078 : Nat := 118140960795 + 1481078 * 2 ^ 59
def prefixEnd_1481078 : Nat := 4983230072969 + 3 ^ 40 * 1481078 * 2
def baseEnd_1481078 : Nat := 253501633599953836404551

theorem tailTrace_1481078 : CollatzResearch.WordTrace tailWord_1481078 prefixEnd_1481078 253501633599953836404551 := by
  unfold tailWord_1481078
  simp only [CollatzResearch.WordTrace]
  refine ⟨3376209533019676801830743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36012901685543219219527925 3376209533019676801830743)
  ·
    refine ⟨5064314299529515202746115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3376209533019676801830743 5064314299529515202746115)
    ·
      refine ⟨7596471449294272804119173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5064314299529515202746115 7596471449294272804119173)
      ·
        refine ⟨1424338396742676150772345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7596471449294272804119173 1424338396742676150772345)
        ·
          refine ⟨1068253797557007113079259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1424338396742676150772345 1068253797557007113079259)
          ·
            refine ⟨1602380696335510669618889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1068253797557007113079259 1602380696335510669618889)
            ·
              refine ⟨1201785522251633002214167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1602380696335510669618889 1201785522251633002214167)
              ·
                refine ⟨1802678283377449503321251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1201785522251633002214167 1802678283377449503321251)
                ·
                  refine ⟨2704017425066174254981877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1802678283377449503321251 2704017425066174254981877)
                  ·
                    refine ⟨253501633599953836404551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2704017425066174254981877 253501633599953836404551)
                    ·
                      rfl

theorem cell23_1481078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_1481078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481078 prefixEnd_1481078 := by exact prefixLift 1481078
  have htrace : WordTrace (prefixWord ++ tailWord_1481078) baseStart_1481078 baseEnd_1481078 := by
    simpa [prefixWord, tailWord_1481078, baseEnd_1481078] using wordTrace_append hprefix tailTrace_1481078
  have hstable : (prefixWord ++ tailWord_1481078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481078).length < 2 ^ (prefixWord ++ tailWord_1481078).sum := by decide
  have hdescent : baseEnd_1481078 < baseStart_1481078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481097 : List Nat := [1, 2, 1, 1, 6, 2, 1, 1, 4, 1, 3]
def baseStart_1481097 : Nat := 118140960795 + 1481097 * 2 ^ 59
def prefixEnd_1481097 : Nat := 4983230072969 + 3 ^ 40 * 1481097 * 2
def baseEnd_1481097 : Nat := 760514656932296934876065

theorem tailTrace_1481097 : CollatzResearch.WordTrace tailWord_1481097 prefixEnd_1481097 760514656932296934876065 := by
  unfold tailWord_1481097
  simp only [CollatzResearch.WordTrace]
  refine ⟨54020045515245995074233545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36013363676830663382822363 54020045515245995074233545)
  ·
    refine ⟨40515034136434496305675159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54020045515245995074233545 40515034136434496305675159)
    ·
      refine ⟨60772551204651744458512739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40515034136434496305675159 60772551204651744458512739)
      ·
        refine ⟨91158826806977616687769109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60772551204651744458512739 91158826806977616687769109)
        ·
          refine ⟨4273070006577075782239177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 91158826806977616687769109 4273070006577075782239177)
          ·
            refine ⟨3204802504932806836679383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4273070006577075782239177 3204802504932806836679383)
            ·
              refine ⟨4807203757399210255019075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3204802504932806836679383 4807203757399210255019075)
              ·
                refine ⟨7210805636098815382528613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4807203757399210255019075 7210805636098815382528613)
                ·
                  refine ⟨1352026056768527884224115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7210805636098815382528613 1352026056768527884224115)
                  ·
                    refine ⟨2028039085152791826336173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1352026056768527884224115 2028039085152791826336173)
                    ·
                      refine ⟨760514656932296934876065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2028039085152791826336173 760514656932296934876065)
                      ·
                        rfl

theorem cell23_1481097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 4, 1, 3].length) (baseStart_1481097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481097 prefixEnd_1481097 := by exact prefixLift 1481097
  have htrace : WordTrace (prefixWord ++ tailWord_1481097) baseStart_1481097 baseEnd_1481097 := by
    simpa [prefixWord, tailWord_1481097, baseEnd_1481097] using wordTrace_append hprefix tailTrace_1481097
  have hstable : (prefixWord ++ tailWord_1481097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481097).length < 2 ^ (prefixWord ++ tailWord_1481097).sum := by decide
  have hdescent : baseEnd_1481097 < baseStart_1481097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481113 : List Nat := [1, 2, 1, 2, 1, 4, 1, 3, 2, 6]
def baseStart_1481113 : Nat := 118140960795 + 1481113 * 2 ^ 59
def prefixEnd_1481113 : Nat := 4983230072969 + 3 ^ 40 * 1481113 * 2
def baseEnd_1481113 : Nat := 253507624207589624091997

theorem tailTrace_1481113 : CollatzResearch.WordTrace tailWord_1481113 prefixEnd_1481113 253507624207589624091997 := by
  unfold tailWord_1481113
  simp only [CollatzResearch.WordTrace]
  refine ⟨54020629083188029806815993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36013752722125353204543995 54020629083188029806815993)
  ·
    refine ⟨40515471812391022355111995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54020629083188029806815993 40515471812391022355111995)
    ·
      refine ⟨60773207718586533532667993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40515471812391022355111995 60773207718586533532667993)
      ·
        refine ⟨45579905788939900149500995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60773207718586533532667993 45579905788939900149500995)
        ·
          refine ⟨68369858683409850224251493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45579905788939900149500995 68369858683409850224251493)
          ·
            refine ⟨12819348503139346917047155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68369858683409850224251493 12819348503139346917047155)
            ·
              refine ⟨19229022754709020375570733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12819348503139346917047155 19229022754709020375570733)
              ·
                refine ⟨7210883533015882640839025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19229022754709020375570733 7210883533015882640839025)
                ·
                  refine ⟨5408162649761911980629269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7210883533015882640839025 5408162649761911980629269)
                  ·
                    refine ⟨253507624207589624091997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5408162649761911980629269 253507624207589624091997)
                    ·
                      rfl

theorem cell23_1481113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 6].length) (baseStart_1481113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481113 prefixEnd_1481113 := by exact prefixLift 1481113
  have htrace : WordTrace (prefixWord ++ tailWord_1481113) baseStart_1481113 baseEnd_1481113 := by
    simpa [prefixWord, tailWord_1481113, baseEnd_1481113] using wordTrace_append hprefix tailTrace_1481113
  have hstable : (prefixWord ++ tailWord_1481113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481113).length < 2 ^ (prefixWord ++ tailWord_1481113).sum := by decide
  have hdescent : baseEnd_1481113 < baseStart_1481113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481150 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4]
def baseStart_1481150 : Nat := 118140960795 + 1481150 * 2 ^ 59
def prefixEnd_1481150 : Nat := 4983230072969 + 3 ^ 40 * 1481150 * 2
def baseEnd_1481150 : Nat := 760541871406985227513321

theorem tailTrace_1481150 : CollatzResearch.WordTrace tailWord_1481150 prefixEnd_1481150 760541871406985227513321 := by
  unfold tailWord_1481150
  simp only [CollatzResearch.WordTrace]
  refine ⟨6752747323006748140739113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36014652389369323417275269 6752747323006748140739113)
  ·
    refine ⟨5064560492255061105554335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6752747323006748140739113 5064560492255061105554335)
    ·
      refine ⟨7596840738382591658331503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5064560492255061105554335 7596840738382591658331503)
      ·
        refine ⟨11395261107573887487497255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7596840738382591658331503 11395261107573887487497255)
        ·
          refine ⟨17092891661360831231245883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11395261107573887487497255 17092891661360831231245883)
          ·
            refine ⟨25639337492041246846868825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17092891661360831231245883 25639337492041246846868825)
            ·
              refine ⟨19229503119030935135151619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25639337492041246846868825 19229503119030935135151619)
              ·
                refine ⟨28844254678546402702727429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19229503119030935135151619 28844254678546402702727429)
                ·
                  refine ⟨5408297752227450506761393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28844254678546402702727429 5408297752227450506761393)
                  ·
                    refine ⟨4056223314170587880071045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5408297752227450506761393 4056223314170587880071045)
                    ·
                      refine ⟨760541871406985227513321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4056223314170587880071045 760541871406985227513321)
                      ·
                        rfl

theorem cell23_1481150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_1481150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481150 prefixEnd_1481150 := by exact prefixLift 1481150
  have htrace : WordTrace (prefixWord ++ tailWord_1481150) baseStart_1481150 baseEnd_1481150 := by
    simpa [prefixWord, tailWord_1481150, baseEnd_1481150] using wordTrace_append hprefix tailTrace_1481150
  have hstable : (prefixWord ++ tailWord_1481150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481150).length < 2 ^ (prefixWord ++ tailWord_1481150).sum := by decide
  have hdescent : baseEnd_1481150 < baseStart_1481150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481160 : List Nat := [2, 1, 3, 1, 3, 2, 3, 1, 7]
def baseStart_1481160 : Nat := 118140960795 + 1481160 * 2 ^ 59
def prefixEnd_1481160 : Nat := 4983230072969 + 3 ^ 40 * 1481160 * 2
def baseEnd_1481160 : Nat := 84505222912614465376475

theorem tailTrace_1481160 : CollatzResearch.WordTrace tailWord_1481160 prefixEnd_1481160 84505222912614465376475 := by
  unfold tailWord_1481160
  simp only [CollatzResearch.WordTrace]
  refine ⟨27011171657008878416888467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36014895542678504555851289 27011171657008878416888467)
  ·
    refine ⟨40516757485513317625332701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27011171657008878416888467 40516757485513317625332701)
    ·
      refine ⟨15193784057067494109499763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40516757485513317625332701 15193784057067494109499763)
      ·
        refine ⟨22790676085601241164249645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15193784057067494109499763 22790676085601241164249645)
        ·
          refine ⟨8546503532100465436593617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22790676085601241164249645 8546503532100465436593617)
          ·
            refine ⟨6409877649075349077445213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8546503532100465436593617 6409877649075349077445213)
            ·
              refine ⟨2403704118403255904041955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6409877649075349077445213 2403704118403255904041955)
              ·
                refine ⟨3605556177604883856062933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2403704118403255904041955 3605556177604883856062933)
                ·
                  refine ⟨84505222912614465376475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3605556177604883856062933 84505222912614465376475)
                  ·
                    rfl

theorem cell23_1481160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 7].length) (baseStart_1481160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481160 prefixEnd_1481160 := by exact prefixLift 1481160
  have htrace : WordTrace (prefixWord ++ tailWord_1481160) baseStart_1481160 baseEnd_1481160 := by
    simpa [prefixWord, tailWord_1481160, baseEnd_1481160] using wordTrace_append hprefix tailTrace_1481160
  have hstable : (prefixWord ++ tailWord_1481160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481160).length < 2 ^ (prefixWord ++ tailWord_1481160).sum := by decide
  have hdescent : baseEnd_1481160 < baseStart_1481160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481210 : List Nat := [3, 1, 1, 1, 1, 2, 2, 3, 4, 1, 4]
def baseStart_1481210 : Nat := 118140960795 + 1481210 * 2 ^ 59
def prefixEnd_1481210 : Nat := 4983230072969 + 3 ^ 40 * 1481210 * 2
def baseEnd_1481210 : Nat := 760572680246254992763045

theorem tailTrace_1481210 : CollatzResearch.WordTrace tailWord_1481210 prefixEnd_1481210 760572680246254992763045 := by
  unfold tailWord_1481210
  simp only [CollatzResearch.WordTrace]
  refine ⟨13506041740959153843274271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36016111309224410248731389 13506041740959153843274271)
  ·
    refine ⟨20259062611438730764911407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13506041740959153843274271 20259062611438730764911407)
    ·
      refine ⟨30388593917158096147367111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20259062611438730764911407 30388593917158096147367111)
      ·
        refine ⟨45582890875737144221050667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30388593917158096147367111 45582890875737144221050667)
        ·
          refine ⟨68374336313605716331576001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45582890875737144221050667 68374336313605716331576001)
          ·
            refine ⟨51280752235204287248682001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68374336313605716331576001 51280752235204287248682001)
            ·
              refine ⟨38460564176403215436511501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51280752235204287248682001 38460564176403215436511501)
              ·
                refine ⟨14422711566151205788691813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38460564176403215436511501 14422711566151205788691813)
                ·
                  refine ⟨2704258418653351085379715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14422711566151205788691813 2704258418653351085379715)
                  ·
                    refine ⟨4056387627980026628069573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2704258418653351085379715 4056387627980026628069573)
                    ·
                      refine ⟨760572680246254992763045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4056387627980026628069573 760572680246254992763045)
                      ·
                        rfl

theorem cell23_1481210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 4, 1, 4].length) (baseStart_1481210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481210 prefixEnd_1481210 := by exact prefixLift 1481210
  have htrace : WordTrace (prefixWord ++ tailWord_1481210) baseStart_1481210 baseEnd_1481210 := by
    simpa [prefixWord, tailWord_1481210, baseEnd_1481210] using wordTrace_append hprefix tailTrace_1481210
  have hstable : (prefixWord ++ tailWord_1481210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481210).length < 2 ^ (prefixWord ++ tailWord_1481210).sum := by decide
  have hdescent : baseEnd_1481210 < baseStart_1481210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481227 : List Nat := [1, 1, 1, 1, 7, 1, 1, 1, 1, 6, 2]
def baseStart_1481227 : Nat := 118140960795 + 1481227 * 2 ^ 59
def prefixEnd_1481227 : Nat := 4983230072969 + 3 ^ 40 * 1481227 * 2
def baseEnd_1481227 : Nat := 760581409417381426250467

theorem tailTrace_1481227 : CollatzResearch.WordTrace tailWord_1481227 prefixEnd_1481227 760581409417381426250467 := by
  unfold tailWord_1481227
  simp only [CollatzResearch.WordTrace]
  refine ⟨54024787004775027276465935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36016524669850018184310623 54024787004775027276465935)
  ·
    refine ⟨81037180507162540914698903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54024787004775027276465935 81037180507162540914698903)
    ·
      refine ⟨121555770760743811372048355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81037180507162540914698903 121555770760743811372048355)
      ·
        refine ⟨182333656141115717058072533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121555770760743811372048355 182333656141115717058072533)
        ·
          refine ⟨4273445065807399618548575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 182333656141115717058072533 4273445065807399618548575)
          ·
            refine ⟨6410167598711099427822863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4273445065807399618548575 6410167598711099427822863)
            ·
              refine ⟨9615251398066649141734295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6410167598711099427822863 9615251398066649141734295)
              ·
                refine ⟨14422877097099973712601443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9615251398066649141734295 14422877097099973712601443)
                ·
                  refine ⟨21634315645649960568902165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14422877097099973712601443 21634315645649960568902165)
                  ·
                    refine ⟨1014108545889841901667289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21634315645649960568902165 1014108545889841901667289)
                    ·
                      refine ⟨760581409417381426250467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1014108545889841901667289 760581409417381426250467)
                      ·
                        rfl

theorem cell23_1481227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 6, 2].length) (baseStart_1481227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481227 prefixEnd_1481227 := by exact prefixLift 1481227
  have htrace : WordTrace (prefixWord ++ tailWord_1481227) baseStart_1481227 baseEnd_1481227 := by
    simpa [prefixWord, tailWord_1481227, baseEnd_1481227] using wordTrace_append hprefix tailTrace_1481227
  have hstable : (prefixWord ++ tailWord_1481227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481227).length < 2 ^ (prefixWord ++ tailWord_1481227).sum := by decide
  have hdescent : baseEnd_1481227 < baseStart_1481227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481237 : List Nat := [1, 3, 2, 1, 3, 1, 3, 2, 3, 4]
def baseStart_1481237 : Nat := 118140960795 + 1481237 * 2 ^ 59
def prefixEnd_1481237 : Nat := 4983230072969 + 3 ^ 40 * 1481237 * 2
def baseEnd_1481237 : Nat := 253528848074642129041807

theorem tailTrace_1481237 : CollatzResearch.WordTrace tailWord_1481237 prefixEnd_1481237 253528848074642129041807 := by
  unfold tailWord_1481237
  simp only [CollatzResearch.WordTrace]
  refine ⟨54025151734738798984329965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36016767823159199322886643 54025151734738798984329965)
  ·
    refine ⟨20259431900527049619123737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54025151734738798984329965 20259431900527049619123737)
    ·
      refine ⟨15194573925395287214342803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20259431900527049619123737 15194573925395287214342803)
      ·
        refine ⟨22791860888092930821514205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15194573925395287214342803 22791860888092930821514205)
        ·
          refine ⟨8546947833034849058067827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22791860888092930821514205 8546947833034849058067827)
          ·
            refine ⟨12820421749552273587101741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8546947833034849058067827 12820421749552273587101741)
            ·
              refine ⟨4807658156082102595163153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12820421749552273587101741 4807658156082102595163153)
              ·
                refine ⟨3605743617061576946372365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4807658156082102595163153 3605743617061576946372365)
                ·
                  refine ⟨1352153856398091354889637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3605743617061576946372365 1352153856398091354889637)
                  ·
                    refine ⟨253528848074642129041807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1352153856398091354889637 253528848074642129041807)
                    ·
                      rfl

theorem cell23_1481237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 3, 4].length) (baseStart_1481237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481237 prefixEnd_1481237 := by exact prefixLift 1481237
  have htrace : WordTrace (prefixWord ++ tailWord_1481237) baseStart_1481237 baseEnd_1481237 := by
    simpa [prefixWord, tailWord_1481237, baseEnd_1481237] using wordTrace_append hprefix tailTrace_1481237
  have hstable : (prefixWord ++ tailWord_1481237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481237).length < 2 ^ (prefixWord ++ tailWord_1481237).sum := by decide
  have hdescent : baseEnd_1481237 < baseStart_1481237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481244 : List Nat := [2, 2, 3, 1, 2, 4, 1, 1, 2, 1, 4]
def baseStart_1481244 : Nat := 118140960795 + 1481244 * 2 ^ 59
def prefixEnd_1481244 : Nat := 4983230072969 + 3 ^ 40 * 1481244 * 2
def baseEnd_1481244 : Nat := 760590138588507859737889

theorem tailTrace_1481244 : CollatzResearch.WordTrace tailWord_1481244 prefixEnd_1481244 760590138588507859737889 := by
  unfold tailWord_1481244
  simp only [CollatzResearch.WordTrace]
  refine ⟨27012703522856719589917393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36016938030475626119889857 27012703522856719589917393)
  ·
    refine ⟨20259527642142539692438045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27012703522856719589917393 20259527642142539692438045)
    ·
      refine ⟨7597322865803452384664267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20259527642142539692438045 7597322865803452384664267)
      ·
        refine ⟨11395984298705178576996401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7597322865803452384664267 11395984298705178576996401)
        ·
          refine ⟨8546988224028883932747301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11395984298705178576996401 8546988224028883932747301)
          ·
            refine ⟨1602560292005415737390119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8546988224028883932747301 1602560292005415737390119)
            ·
              refine ⟨2403840438008123606085179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1602560292005415737390119 2403840438008123606085179)
              ·
                refine ⟨3605760657012185409127769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2403840438008123606085179 3605760657012185409127769)
                ·
                  refine ⟨2704320492759139056845827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3605760657012185409127769 2704320492759139056845827)
                  ·
                    refine ⟨4056480739138708585268741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2704320492759139056845827 4056480739138708585268741)
                    ·
                      refine ⟨760590138588507859737889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4056480739138708585268741 760590138588507859737889)
                      ·
                        rfl

theorem cell23_1481244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_1481244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481244 prefixEnd_1481244 := by exact prefixLift 1481244
  have htrace : WordTrace (prefixWord ++ tailWord_1481244) baseStart_1481244 baseEnd_1481244 := by
    simpa [prefixWord, tailWord_1481244, baseEnd_1481244] using wordTrace_append hprefix tailTrace_1481244
  have hstable : (prefixWord ++ tailWord_1481244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481244).length < 2 ^ (prefixWord ++ tailWord_1481244).sum := by decide
  have hdescent : baseEnd_1481244 < baseStart_1481244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481250 : List Nat := [3, 3, 1, 1, 1, 1, 1, 4, 8]
def baseStart_1481250 : Nat := 118140960795 + 1481250 * 2 ^ 59
def prefixEnd_1481250 : Nat := 4983230072969 + 3 ^ 40 * 1481250 * 2
def baseEnd_1481250 : Nat := 84510357719159426251429

theorem tailTrace_1481250 : CollatzResearch.WordTrace tailWord_1481250 prefixEnd_1481250 84510357719159426251429 := by
  unfold tailWord_1481250
  simp only [CollatzResearch.WordTrace]
  refine ⟨13506406470922925551138301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36017083922461134803035469 13506406470922925551138301)
  ·
    refine ⟨5064902426596097081676863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13506406470922925551138301 5064902426596097081676863)
    ·
      refine ⟨7597353639894145622515295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5064902426596097081676863 7597353639894145622515295)
      ·
        refine ⟨11396030459841218433772943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7597353639894145622515295 11396030459841218433772943)
        ·
          refine ⟨17094045689761827650659415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11396030459841218433772943 17094045689761827650659415)
          ·
            refine ⟨25641068534642741475989123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17094045689761827650659415 25641068534642741475989123)
            ·
              refine ⟨38461602801964112213983685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25641068534642741475989123 38461602801964112213983685)
              ·
                refine ⟨7211550525368271040121941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38461602801964112213983685 7211550525368271040121941)
                ·
                  refine ⟨84510357719159426251429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7211550525368271040121941 84510357719159426251429)
                  ·
                    rfl

theorem cell23_1481250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_1481250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481250 prefixEnd_1481250 := by exact prefixLift 1481250
  have htrace : WordTrace (prefixWord ++ tailWord_1481250) baseStart_1481250 baseEnd_1481250 := by
    simpa [prefixWord, tailWord_1481250, baseEnd_1481250] using wordTrace_append hprefix tailTrace_1481250
  have hstable : (prefixWord ++ tailWord_1481250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481250).length < 2 ^ (prefixWord ++ tailWord_1481250).sum := by decide
  have hdescent : baseEnd_1481250 < baseStart_1481250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481260 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 3]
def baseStart_1481260 : Nat := 118140960795 + 1481260 * 2 ^ 59
def prefixEnd_1481260 : Nat := 4983230072969 + 3 ^ 40 * 1481260 * 2
def baseEnd_1481260 : Nat := 760598354278979797137815

theorem tailTrace_1481260 : CollatzResearch.WordTrace tailWord_1481260 prefixEnd_1481260 760598354278979797137815 := by
  unfold tailWord_1481260
  simp only [CollatzResearch.WordTrace]
  refine ⟨27012995306827736956208617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36017327075770315941611489 27012995306827736956208617)
  ·
    refine ⟨20259746480120802717156463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27012995306827736956208617 20259746480120802717156463)
    ·
      refine ⟨30389619720181204075734695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20259746480120802717156463 30389619720181204075734695)
      ·
        refine ⟨45584429580271806113602043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30389619720181204075734695 45584429580271806113602043)
        ·
          refine ⟨68376644370407709170403065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45584429580271806113602043 68376644370407709170403065)
          ·
            refine ⟨51282483277805781877802299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68376644370407709170403065 51282483277805781877802299)
            ·
              refine ⟨76923724916708672816703449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51282483277805781877802299 76923724916708672816703449)
              ·
                refine ⟨57692793687531504612527587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76923724916708672816703449 57692793687531504612527587)
                ·
                  refine ⟨86539190531297256918791381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57692793687531504612527587 86539190531297256918791381)
                  ·
                    refine ⟨2028262278077279459034173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 86539190531297256918791381 2028262278077279459034173)
                    ·
                      refine ⟨760598354278979797137815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2028262278077279459034173 760598354278979797137815)
                      ·
                        rfl

theorem cell23_1481260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 3].length) (baseStart_1481260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481260 prefixEnd_1481260 := by exact prefixLift 1481260
  have htrace : WordTrace (prefixWord ++ tailWord_1481260) baseStart_1481260 baseEnd_1481260 := by
    simpa [prefixWord, tailWord_1481260, baseEnd_1481260] using wordTrace_append hprefix tailTrace_1481260
  have hstable : (prefixWord ++ tailWord_1481260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481260).length < 2 ^ (prefixWord ++ tailWord_1481260).sum := by decide
  have hdescent : baseEnd_1481260 < baseStart_1481260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481280 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 5, 5]
def baseStart_1481280 : Nat := 118140960795 + 1481280 * 2 ^ 59
def prefixEnd_1481280 : Nat := 4983230072969 + 3 ^ 40 * 1481280 * 2
def baseEnd_1481280 : Nat := 253536207964023239629241

theorem tailTrace_1481280 : CollatzResearch.WordTrace tailWord_1481280 prefixEnd_1481280 253536207964023239629241 := by
  unfold tailWord_1481280
  simp only [CollatzResearch.WordTrace]
  refine ⟨27013360036791508664072647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36017813382388678218763529 27013360036791508664072647)
  ·
    refine ⟨40520040055187262996108971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27013360036791508664072647 40520040055187262996108971)
    ·
      refine ⟨60780060082780894494163457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40520040055187262996108971 60780060082780894494163457)
      ·
        refine ⟨45585045062085670870622593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60780060082780894494163457 45585045062085670870622593)
        ·
          refine ⟨34188783796564253152966945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45585045062085670870622593 34188783796564253152966945)
          ·
            refine ⟨25641587847423189864725209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34188783796564253152966945 25641587847423189864725209)
            ·
              refine ⟨19231190885567392398543907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25641587847423189864725209 19231190885567392398543907)
              ·
                refine ⟨28846786328351088597815861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19231190885567392398543907 28846786328351088597815861)
                ·
                  refine ⟨2704386218282914556045237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28846786328351088597815861 2704386218282914556045237)
                  ·
                    refine ⟨253536207964023239629241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2704386218282914556045237 253536207964023239629241)
                    ·
                      rfl

theorem cell23_1481280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 5, 5].length) (baseStart_1481280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481280 prefixEnd_1481280 := by exact prefixLift 1481280
  have htrace : WordTrace (prefixWord ++ tailWord_1481280) baseStart_1481280 baseEnd_1481280 := by
    simpa [prefixWord, tailWord_1481280, baseEnd_1481280] using wordTrace_append hprefix tailTrace_1481280
  have hstable : (prefixWord ++ tailWord_1481280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481280).length < 2 ^ (prefixWord ++ tailWord_1481280).sum := by decide
  have hdescent : baseEnd_1481280 < baseStart_1481280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481294 : List Nat := [4, 1, 1, 1, 1, 2, 4, 2, 3, 1, 3]
def baseStart_1481294 : Nat := 118140960795 + 1481294 * 2 ^ 59
def prefixEnd_1481294 : Nat := 4983230072969 + 3 ^ 40 * 1481294 * 2
def baseEnd_1481294 : Nat := 760615812621232664112659

theorem tailTrace_1481294 : CollatzResearch.WordTrace tailWord_1481294 prefixEnd_1481294 760615812621232664112659 := by
  unfold tailWord_1481294
  simp only [CollatzResearch.WordTrace]
  refine ⟨6753403836941537214894367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36018153797021531812769957 6753403836941537214894367)
  ·
    refine ⟨10130105755412305822341551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6753403836941537214894367 10130105755412305822341551)
    ·
      refine ⟨15195158633118458733512327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10130105755412305822341551 15195158633118458733512327)
      ·
        refine ⟨22792737949677688100268491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15195158633118458733512327 22792737949677688100268491)
        ·
          refine ⟨34189106924516532150402737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22792737949677688100268491 34189106924516532150402737)
          ·
            refine ⟨25641830193387399112802053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34189106924516532150402737 25641830193387399112802053)
            ·
              refine ⟨4807843161260137333650385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25641830193387399112802053 4807843161260137333650385)
              ·
                refine ⟨3605882370945103000237789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4807843161260137333650385 3605882370945103000237789)
                ·
                  refine ⟨1352205889104413625089171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3605882370945103000237789 1352205889104413625089171)
                  ·
                    refine ⟨2028308833656620437633757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1352205889104413625089171 2028308833656620437633757)
                    ·
                      refine ⟨760615812621232664112659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2028308833656620437633757 760615812621232664112659)
                      ·
                        rfl

theorem cell23_1481294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 3, 1, 3].length) (baseStart_1481294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481294 prefixEnd_1481294 := by exact prefixLift 1481294
  have htrace : WordTrace (prefixWord ++ tailWord_1481294) baseStart_1481294 baseEnd_1481294 := by
    simpa [prefixWord, tailWord_1481294, baseEnd_1481294] using wordTrace_append hprefix tailTrace_1481294
  have hstable : (prefixWord ++ tailWord_1481294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481294).length < 2 ^ (prefixWord ++ tailWord_1481294).sum := by decide
  have hdescent : baseEnd_1481294 < baseStart_1481294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481297 : List Nat := [1, 2, 2, 1, 3, 3, 1, 4, 1, 5]
def baseStart_1481297 : Nat := 118140960795 + 1481297 * 2 ^ 59
def prefixEnd_1481297 : Nat := 4983230072969 + 3 ^ 40 * 1481297 * 2
def baseEnd_1481297 : Nat := 253539117687732050791715

theorem tailTrace_1481297 : CollatzResearch.WordTrace tailWord_1481297 prefixEnd_1481297 253539117687732050791715 := by
  unfold tailWord_1481297
  simp only [CollatzResearch.WordTrace]
  refine ⟨54027340114521429231514145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36018226743014286154342763 54027340114521429231514145)
  ·
    refine ⟨40520505085891071923635609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54027340114521429231514145 40520505085891071923635609)
    ·
      refine ⟨30390378814418303942726707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40520505085891071923635609 30390378814418303942726707)
      ·
        refine ⟨45585568221627455914090061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30390378814418303942726707 45585568221627455914090061)
        ·
          refine ⟨17094588083110295967783773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45585568221627455914090061 17094588083110295967783773)
          ·
            refine ⟨6410470531166360987918915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17094588083110295967783773 6410470531166360987918915)
            ·
              refine ⟨9615705796749541481878373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6410470531166360987918915 9615705796749541481878373)
              ·
                refine ⟨1802944836890539027852195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9615705796749541481878373 1802944836890539027852195)
                ·
                  refine ⟨2704417255335808541778293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1802944836890539027852195 2704417255335808541778293)
                  ·
                    refine ⟨253539117687732050791715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2704417255335808541778293 253539117687732050791715)
                    ·
                      rfl

theorem cell23_1481297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 4, 1, 5].length) (baseStart_1481297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481297 prefixEnd_1481297 := by exact prefixLift 1481297
  have htrace : WordTrace (prefixWord ++ tailWord_1481297) baseStart_1481297 baseEnd_1481297 := by
    simpa [prefixWord, tailWord_1481297, baseEnd_1481297] using wordTrace_append hprefix tailTrace_1481297
  have hstable : (prefixWord ++ tailWord_1481297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481297).length < 2 ^ (prefixWord ++ tailWord_1481297).sum := by decide
  have hdescent : baseEnd_1481297 < baseStart_1481297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481327 : List Nat := [1, 1, 2, 1, 3, 2, 4, 1, 4, 4]
def baseStart_1481327 : Nat := 118140960795 + 1481327 * 2 ^ 59
def prefixEnd_1481327 : Nat := 4983230072969 + 3 ^ 40 * 1481327 * 2
def baseEnd_1481327 : Nat := 253544252494277011666669

theorem tailTrace_1481327 : CollatzResearch.WordTrace tailWord_1481327 prefixEnd_1481327 253544252494277011666669 := by
  unfold tailWord_1481327
  simp only [CollatzResearch.WordTrace]
  refine ⟨54028434304412744355106235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36018956202941829570070823 54028434304412744355106235)
  ·
    refine ⟨81042651456619116532659353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54028434304412744355106235 81042651456619116532659353)
    ·
      refine ⟨60781988592464337399494515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81042651456619116532659353 60781988592464337399494515)
      ·
        refine ⟨91172982888696506099241773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60781988592464337399494515 91172982888696506099241773)
        ·
          refine ⟨34189868583261189787215665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91172982888696506099241773 34189868583261189787215665)
          ·
            refine ⟨25642401437445892340411749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34189868583261189787215665 25642401437445892340411749)
            ·
              refine ⟨4807950269521104813827203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25642401437445892340411749 4807950269521104813827203)
              ·
                refine ⟨7211925404281657220740805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4807950269521104813827203 7211925404281657220740805)
                ·
                  refine ⟨1352236013302810728888901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7211925404281657220740805 1352236013302810728888901)
                  ·
                    refine ⟨253544252494277011666669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1352236013302810728888901 253544252494277011666669)
                    ·
                      rfl

theorem cell23_1481327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 4, 4].length) (baseStart_1481327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481327 prefixEnd_1481327 := by exact prefixLift 1481327
  have htrace : WordTrace (prefixWord ++ tailWord_1481327) baseStart_1481327 baseEnd_1481327 := by
    simpa [prefixWord, tailWord_1481327, baseEnd_1481327] using wordTrace_append hprefix tailTrace_1481327
  have hstable : (prefixWord ++ tailWord_1481327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481327).length < 2 ^ (prefixWord ++ tailWord_1481327).sum := by decide
  have hdescent : baseEnd_1481327 < baseStart_1481327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481328 : List Nat := [2, 1, 1, 1, 8, 1, 1, 1, 3, 1, 3]
def baseStart_1481328 : Nat := 118140960795 + 1481328 * 2 ^ 59
def prefixEnd_1481328 : Nat := 4983230072969 + 3 ^ 40 * 1481328 * 2
def baseEnd_1481328 : Nat := 760633270963485531087503

theorem tailTrace_1481328 : CollatzResearch.WordTrace tailWord_1481328 prefixEnd_1481328 760633270963485531087503 := by
  unfold tailWord_1481328
  simp only [CollatzResearch.WordTrace]
  refine ⟨27014235388704560762946319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36018980518272747683928425 27014235388704560762946319)
  ·
    refine ⟨40521353083056841144419479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27014235388704560762946319 40521353083056841144419479)
    ·
      refine ⟨60782029624585261716629219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40521353083056841144419479 60782029624585261716629219)
      ·
        refine ⟨91173044436877892574943829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60782029624585261716629219 91173044436877892574943829)
        ·
          refine ⟨1068434114494662803612623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 91173044436877892574943829 1068434114494662803612623)
          ·
            refine ⟨1602651171741994205418935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1068434114494662803612623 1602651171741994205418935)
            ·
              refine ⟨2403976757612991308128403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1602651171741994205418935 2403976757612991308128403)
              ·
                refine ⟨3605965136419486962192605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2403976757612991308128403 3605965136419486962192605)
                ·
                  refine ⟨1352236926157307610822227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3605965136419486962192605 1352236926157307610822227)
                  ·
                    refine ⟨2028355389235961416233341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1352236926157307610822227 2028355389235961416233341)
                    ·
                      refine ⟨760633270963485531087503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2028355389235961416233341 760633270963485531087503)
                      ·
                        rfl

theorem cell23_1481328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 3, 1, 3].length) (baseStart_1481328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481328 prefixEnd_1481328 := by exact prefixLift 1481328
  have htrace : WordTrace (prefixWord ++ tailWord_1481328) baseStart_1481328 baseEnd_1481328 := by
    simpa [prefixWord, tailWord_1481328, baseEnd_1481328] using wordTrace_append hprefix tailTrace_1481328
  have hstable : (prefixWord ++ tailWord_1481328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481328).length < 2 ^ (prefixWord ++ tailWord_1481328).sum := by decide
  have hdescent : baseEnd_1481328 < baseStart_1481328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481337 : List Nat := [1, 2, 1, 3, 3, 2, 2, 2, 1, 1, 5]
def baseStart_1481337 : Nat := 118140960795 + 1481337 * 2 ^ 59
def prefixEnd_1481337 : Nat := 4983230072969 + 3 ^ 40 * 1481337 * 2
def baseEnd_1481337 : Nat := 760637892289375995874961

theorem tailTrace_1481337 : CollatzResearch.WordTrace tailWord_1481337 prefixEnd_1481337 760637892289375995874961 := by
  unfold tailWord_1481337
  simp only [CollatzResearch.WordTrace]
  refine ⟨54028799034376516062970265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36019199356251010708646843 54028799034376516062970265)
  ·
    refine ⟨40521599275782387047227699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54028799034376516062970265 40521599275782387047227699)
    ·
      refine ⟨60782398913673580570841549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40521599275782387047227699 60782398913673580570841549)
      ·
        refine ⟨22793399592627592714065581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60782398913673580570841549 22793399592627592714065581)
        ·
          refine ⟨8547524847235347267774593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22793399592627592714065581 8547524847235347267774593)
          ·
            refine ⟨6410643635426510450830945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8547524847235347267774593 6410643635426510450830945)
            ·
              refine ⟨4807982726569882838123209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6410643635426510450830945 4807982726569882838123209)
              ·
                refine ⟨3605987044927412128592407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4807982726569882838123209 3605987044927412128592407)
                ·
                  refine ⟨5408980567391118192888611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3605987044927412128592407 5408980567391118192888611)
                  ·
                    refine ⟨8113470851086677289332917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5408980567391118192888611 8113470851086677289332917)
                    ·
                      refine ⟨760637892289375995874961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8113470851086677289332917 760637892289375995874961)
                      ·
                        rfl

theorem cell23_1481337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_1481337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481337 prefixEnd_1481337 := by exact prefixLift 1481337
  have htrace : WordTrace (prefixWord ++ tailWord_1481337) baseStart_1481337 baseEnd_1481337 := by
    simpa [prefixWord, tailWord_1481337, baseEnd_1481337] using wordTrace_append hprefix tailTrace_1481337
  have hstable : (prefixWord ++ tailWord_1481337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481337).length < 2 ^ (prefixWord ++ tailWord_1481337).sum := by decide
  have hdescent : baseEnd_1481337 < baseStart_1481337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481340 : List Nat := [2, 2, 2, 1, 1, 2, 3, 10]
def baseStart_1481340 : Nat := 118140960795 + 1481340 * 2 ^ 59
def prefixEnd_1481340 : Nat := 4983230072969 + 3 ^ 40 * 1481340 * 2
def baseEnd_1481340 : Nat := 28171830841901462375461

theorem tailTrace_1481340 : CollatzResearch.WordTrace tailWord_1481340 prefixEnd_1481340 28171830841901462375461 := by
  unfold tailWord_1481340
  simp only [CollatzResearch.WordTrace]
  refine ⟨27014454226682823787664737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36019272302243765050219649 27014454226682823787664737)
  ·
    refine ⟨20260840670012117840748553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27014454226682823787664737 20260840670012117840748553)
    ·
      refine ⟨15195630502509088380561415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20260840670012117840748553 15195630502509088380561415)
      ·
        refine ⟨22793445753763632570842123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15195630502509088380561415 22793445753763632570842123)
        ·
          refine ⟨34190168630645448856263185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22793445753763632570842123 34190168630645448856263185)
          ·
            refine ⟨25642626472984086642197389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34190168630645448856263185 25642626472984086642197389)
            ·
              refine ⟨9615984927369032490824021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25642626472984086642197389 9615984927369032490824021)
              ·
                refine ⟨28171830841901462375461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 9615984927369032490824021 28171830841901462375461)
                ·
                  rfl

theorem cell23_1481340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 10].length) (baseStart_1481340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481340 prefixEnd_1481340 := by exact prefixLift 1481340
  have htrace : WordTrace (prefixWord ++ tailWord_1481340) baseStart_1481340 baseEnd_1481340 := by
    simpa [prefixWord, tailWord_1481340, baseEnd_1481340] using wordTrace_append hprefix tailTrace_1481340
  have hstable : (prefixWord ++ tailWord_1481340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481340).length < 2 ^ (prefixWord ++ tailWord_1481340).sum := by decide
  have hdescent : baseEnd_1481340 < baseStart_1481340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481344 : List Nat := [2, 1, 1, 2, 1, 6, 1, 3, 2, 4]
def baseStart_1481344 : Nat := 118140960795 + 1481344 * 2 ^ 59
def prefixEnd_1481344 : Nat := 4983230072969 + 3 ^ 40 * 1481344 * 2
def baseEnd_1481344 : Nat := 253547162217985822829143

theorem tailTrace_1481344 : CollatzResearch.WordTrace tailWord_1481344 prefixEnd_1481344 253547162217985822829143 := by
  unfold tailWord_1481344
  simp only [CollatzResearch.WordTrace]
  refine ⟨27014527172675578129237543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36019369563567437505650057 27014527172675578129237543)
  ·
    refine ⟨40521790759013367193856315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27014527172675578129237543 40521790759013367193856315)
    ·
      refine ⟨60782686138520050790784473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40521790759013367193856315 60782686138520050790784473)
      ·
        refine ⟨45587014603890038093088355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60782686138520050790784473 45587014603890038093088355)
        ·
          refine ⟨68380521905835057139632533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45587014603890038093088355 68380521905835057139632533)
          ·
            refine ⟨3205336964336018303420275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 68380521905835057139632533 3205336964336018303420275)
            ·
              refine ⟨4808005446504027455130413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3205336964336018303420275 4808005446504027455130413)
              ·
                refine ⟨1803002042439010295673905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4808005446504027455130413 1803002042439010295673905)
                ·
                  refine ⟨1352251531829257721755429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1803002042439010295673905 1352251531829257721755429)
                  ·
                    refine ⟨253547162217985822829143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1352251531829257721755429 253547162217985822829143)
                    ·
                      rfl

theorem cell23_1481344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 3, 2, 4].length) (baseStart_1481344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481344 prefixEnd_1481344 := by exact prefixLift 1481344
  have htrace : WordTrace (prefixWord ++ tailWord_1481344) baseStart_1481344 baseEnd_1481344 := by
    simpa [prefixWord, tailWord_1481344, baseEnd_1481344] using wordTrace_append hprefix tailTrace_1481344
  have hstable : (prefixWord ++ tailWord_1481344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481344).length < 2 ^ (prefixWord ++ tailWord_1481344).sum := by decide
  have hdescent : baseEnd_1481344 < baseStart_1481344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481364 : List Nat := [2, 4, 2, 2, 1, 1, 1, 1, 3, 2, 4]
def baseStart_1481364 : Nat := 118140960795 + 1481364 * 2 ^ 59
def prefixEnd_1481364 : Nat := 4983230072969 + 3 ^ 40 * 1481364 * 2
def baseEnd_1481364 : Nat := 760651756267047390237337

theorem tailTrace_1481364 : CollatzResearch.WordTrace tailWord_1481364 prefixEnd_1481364 760651756267047390237337 := by
  unfold tailWord_1481364
  simp only [CollatzResearch.WordTrace]
  refine ⟨27014891902639349837101573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36019855870185799782802097 27014891902639349837101573)
  ·
    refine ⟨5065292231744878094456545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27014891902639349837101573 5065292231744878094456545)
    ·
      refine ⟨3798969173808658570842409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5065292231744878094456545 3798969173808658570842409)
      ·
        refine ⟨2849226880356493928131807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3798969173808658570842409 2849226880356493928131807)
        ·
          refine ⟨4273840320534740892197711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2849226880356493928131807 4273840320534740892197711)
          ·
            refine ⟨6410760480802111338296567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4273840320534740892197711 6410760480802111338296567)
            ·
              refine ⟨9616140721203167007444851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6410760480802111338296567 9616140721203167007444851)
              ·
                refine ⟨14424211081804750511167277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9616140721203167007444851 14424211081804750511167277)
                ·
                  refine ⟨5409079155676781441687729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14424211081804750511167277 5409079155676781441687729)
                  ·
                    refine ⟨4056809366757586081265797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5409079155676781441687729 4056809366757586081265797)
                    ·
                      refine ⟨760651756267047390237337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4056809366757586081265797 760651756267047390237337)
                      ·
                        rfl

theorem cell23_1481364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_1481364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481364 prefixEnd_1481364 := by exact prefixLift 1481364
  have htrace : WordTrace (prefixWord ++ tailWord_1481364) baseStart_1481364 baseEnd_1481364 := by
    simpa [prefixWord, tailWord_1481364, baseEnd_1481364] using wordTrace_append hprefix tailTrace_1481364
  have hstable : (prefixWord ++ tailWord_1481364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481364).length < 2 ^ (prefixWord ++ tailWord_1481364).sum := by decide
  have hdescent : baseEnd_1481364 < baseStart_1481364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481368 : List Nat := [2, 1, 2, 4, 1, 1, 2, 5, 1, 2, 2]
def baseStart_1481368 : Nat := 118140960795 + 1481368 * 2 ^ 59
def prefixEnd_1481368 : Nat := 4983230072969 + 3 ^ 40 * 1481368 * 2
def baseEnd_1481368 : Nat := 760653810189665374587319

theorem tailTrace_1481368 : CollatzResearch.WordTrace tailWord_1481368 prefixEnd_1481368 760653810189665374587319 := by
  unfold tailWord_1481368
  simp only [CollatzResearch.WordTrace]
  refine ⟨27014964848632104178674379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36019953131509472238232505 27014964848632104178674379)
  ·
    refine ⟨40522447272948156268011569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27014964848632104178674379 40522447272948156268011569)
    ·
      refine ⟨30391835454711117201008677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40522447272948156268011569 30391835454711117201008677)
      ·
        refine ⟨5698469147758334475189127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30391835454711117201008677 5698469147758334475189127)
        ·
          refine ⟨8547703721637501712783691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5698469147758334475189127 8547703721637501712783691)
          ·
            refine ⟨12821555582456252569175537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8547703721637501712783691 12821555582456252569175537)
            ·
              refine ⟨9616166686842189426881653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12821555582456252569175537 9616166686842189426881653)
              ·
                refine ⟨901515626891455258770155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9616166686842189426881653 901515626891455258770155)
                ·
                  refine ⟨1352273440337182888155233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 901515626891455258770155 1352273440337182888155233)
                  ·
                    refine ⟨1014205080252887166116425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1352273440337182888155233 1014205080252887166116425)
                    ·
                      refine ⟨760653810189665374587319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1014205080252887166116425 760653810189665374587319)
                      ·
                        rfl

theorem cell23_1481368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_1481368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481368 prefixEnd_1481368 := by exact prefixLift 1481368
  have htrace : WordTrace (prefixWord ++ tailWord_1481368) baseStart_1481368 baseEnd_1481368 := by
    simpa [prefixWord, tailWord_1481368, baseEnd_1481368] using wordTrace_append hprefix tailTrace_1481368
  have hstable : (prefixWord ++ tailWord_1481368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481368).length < 2 ^ (prefixWord ++ tailWord_1481368).sum := by decide
  have hdescent : baseEnd_1481368 < baseStart_1481368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481398 : List Nat := [5, 1, 3, 1, 2, 1, 2, 1, 1, 2, 4]
def baseStart_1481398 : Nat := 118140960795 + 1481398 * 2 ^ 59
def prefixEnd_1481398 : Nat := 4983230072969 + 3 ^ 40 * 1481398 * 2
def baseEnd_1481398 : Nat := 760669214609300257212181

theorem tailTrace_1481398 : CollatzResearch.WordTrace tailWord_1481398 prefixEnd_1481398 760669214609300257212181 := by
  unfold tailWord_1481398
  simp only [CollatzResearch.WordTrace]
  refine ⟨3376938992947220217558803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36020682591437015653960565 3376938992947220217558803)
  ·
    refine ⟨5065408489420830326338205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3376938992947220217558803 5065408489420830326338205)
    ·
      refine ⟨1899528183532811372376827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5065408489420830326338205 1899528183532811372376827)
      ·
        refine ⟨2849292275299217058565241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1899528183532811372376827 2849292275299217058565241)
        ·
          refine ⟨2136969206474412793923931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2849292275299217058565241 2136969206474412793923931)
          ·
            refine ⟨3205453809711619190885897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2136969206474412793923931 3205453809711619190885897)
            ·
              refine ⟨2404090357283714393164423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3205453809711619190885897 2404090357283714393164423)
              ·
                refine ⟨3606135535925571589746635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2404090357283714393164423 3606135535925571589746635)
                ·
                  refine ⟨5409203303888357384619953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3606135535925571589746635 5409203303888357384619953)
                  ·
                    refine ⟨4056902477916268038464965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5409203303888357384619953 4056902477916268038464965)
                    ·
                      refine ⟨760669214609300257212181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4056902477916268038464965 760669214609300257212181)
                      ·
                        rfl

theorem cell23_1481398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_1481398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481398 prefixEnd_1481398 := by exact prefixLift 1481398
  have htrace : WordTrace (prefixWord ++ tailWord_1481398) baseStart_1481398 baseEnd_1481398 := by
    simpa [prefixWord, tailWord_1481398, baseEnd_1481398] using wordTrace_append hprefix tailTrace_1481398
  have hstable : (prefixWord ++ tailWord_1481398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481398).length < 2 ^ (prefixWord ++ tailWord_1481398).sum := by decide
  have hdescent : baseEnd_1481398 < baseStart_1481398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481454 : List Nat := [4, 1, 2, 1, 1, 3, 2, 1, 2, 2, 4]
def baseStart_1481454 : Nat := 118140960795 + 1481454 * 2 ^ 59
def prefixEnd_1481454 : Nat := 4983230072969 + 3 ^ 40 * 1481454 * 2
def baseEnd_1481454 : Nat := 760697969525952038111923

theorem tailTrace_1481454 : CollatzResearch.WordTrace tailWord_1481454 prefixEnd_1481454 760697969525952038111923 := by
  unfold tailWord_1481454
  simp only [CollatzResearch.WordTrace]
  refine ⟨6754133296869080630622427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36022044249968430029986277 6754133296869080630622427)
  ·
    refine ⟨10131199945303620945933641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6754133296869080630622427 10131199945303620945933641)
    ·
      refine ⟨7598399958977715709450231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10131199945303620945933641 7598399958977715709450231)
      ·
        refine ⟨11397599938466573564175347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7598399958977715709450231 11397599938466573564175347)
        ·
          refine ⟨17096399907699860346263021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11397599938466573564175347 17096399907699860346263021)
          ·
            refine ⟨6411149965387447629848633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17096399907699860346263021 6411149965387447629848633)
            ·
              refine ⟨4808362474040585722386475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6411149965387447629848633 4808362474040585722386475)
              ·
                refine ⟨7212543711060878583579713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4808362474040585722386475 7212543711060878583579713)
                ·
                  refine ⟨5409407783295658937684785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7212543711060878583579713 5409407783295658937684785)
                  ·
                    refine ⟨4057055837471744203263589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5409407783295658937684785 4057055837471744203263589)
                    ·
                      refine ⟨760697969525952038111923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4057055837471744203263589 760697969525952038111923)
                      ·
                        rfl

theorem cell23_1481454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_1481454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481454 prefixEnd_1481454 := by exact prefixLift 1481454
  have htrace : WordTrace (prefixWord ++ tailWord_1481454) baseStart_1481454 baseEnd_1481454 := by
    simpa [prefixWord, tailWord_1481454, baseEnd_1481454] using wordTrace_append hprefix tailTrace_1481454
  have hstable : (prefixWord ++ tailWord_1481454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481454).length < 2 ^ (prefixWord ++ tailWord_1481454).sum := by decide
  have hdescent : baseEnd_1481454 < baseStart_1481454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481458 : List Nat := [3, 2, 1, 3, 1, 4, 1, 1, 1, 4, 2]
def baseStart_1481458 : Nat := 118140960795 + 1481458 * 2 ^ 59
def prefixEnd_1481458 : Nat := 4983230072969 + 3 ^ 40 * 1481458 * 2
def baseEnd_1481458 : Nat := 760700023448570022461905

theorem tailTrace_1481458 : CollatzResearch.WordTrace tailWord_1481458 prefixEnd_1481458 760700023448570022461905 := by
  unfold tailWord_1481458
  simp only [CollatzResearch.WordTrace]
  refine ⟨13508303066734538432031257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36022141511292102485416685 13508303066734538432031257)
  ·
    refine ⟨10131227300050903824023443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13508303066734538432031257 10131227300050903824023443)
    ·
      refine ⟨15196840950076355736035165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10131227300050903824023443 15196840950076355736035165)
      ·
        refine ⟨5698815356278633401013187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15196840950076355736035165 5698815356278633401013187)
        ·
          refine ⟨8548223034417950101519781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5698815356278633401013187 8548223034417950101519781)
          ·
            refine ⟨1602791818953365644034959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8548223034417950101519781 1602791818953365644034959)
            ·
              refine ⟨2404187728430048466052439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1602791818953365644034959 2404187728430048466052439)
              ·
                refine ⟨3606281592645072699078659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2404187728430048466052439 3606281592645072699078659)
                ·
                  refine ⟨5409422388967609048617989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3606281592645072699078659 5409422388967609048617989)
                  ·
                    refine ⟨1014266697931426696615873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5409422388967609048617989 1014266697931426696615873)
                    ·
                      refine ⟨760700023448570022461905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1014266697931426696615873 760700023448570022461905)
                      ·
                        rfl

theorem cell23_1481458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_1481458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481458 prefixEnd_1481458 := by exact prefixLift 1481458
  have htrace : WordTrace (prefixWord ++ tailWord_1481458) baseStart_1481458 baseEnd_1481458 := by
    simpa [prefixWord, tailWord_1481458, baseEnd_1481458] using wordTrace_append hprefix tailTrace_1481458
  have hstable : (prefixWord ++ tailWord_1481458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481458).length < 2 ^ (prefixWord ++ tailWord_1481458).sum := by decide
  have hdescent : baseEnd_1481458 < baseStart_1481458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481477 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 6, 5]
def baseStart_1481477 : Nat := 118140960795 + 1481477 * 2 ^ 59
def prefixEnd_1481477 : Nat := 4983230072969 + 3 ^ 40 * 1481477 * 2
def baseEnd_1481477 : Nat := 253569926527001816041439

theorem tailTrace_1481477 : CollatzResearch.WordTrace tailWord_1481477 prefixEnd_1481477 253569926527001816041439 := by
  unfold tailWord_1481477
  simp only [CollatzResearch.WordTrace]
  refine ⟨54033905253869319973066685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36022603502579546648711123 54033905253869319973066685)
  ·
    refine ⟨20262714470200994989900007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54033905253869319973066685 20262714470200994989900007)
    ·
      refine ⟨30394071705301492484850011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20262714470200994989900007 30394071705301492484850011)
      ·
        refine ⟨45591107557952238727275017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30394071705301492484850011 45591107557952238727275017)
        ·
          refine ⟨34193330668464179045456263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45591107557952238727275017 34193330668464179045456263)
          ·
            refine ⟨51289996002696268568184395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34193330668464179045456263 51289996002696268568184395)
            ·
              refine ⟨76934994004044402852276593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51289996002696268568184395 76934994004044402852276593)
              ·
                refine ⟨57701245503033302139207445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76934994004044402852276593 57701245503033302139207445)
                ·
                  refine ⟨2704745882954686037775349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 57701245503033302139207445 2704745882954686037775349)
                  ·
                    refine ⟨253569926527001816041439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2704745882954686037775349 253569926527001816041439)
                    ·
                      rfl

theorem cell23_1481477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 6, 5].length) (baseStart_1481477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481477 prefixEnd_1481477 := by exact prefixLift 1481477
  have htrace : WordTrace (prefixWord ++ tailWord_1481477) baseStart_1481477 baseEnd_1481477 := by
    simpa [prefixWord, tailWord_1481477, baseEnd_1481477] using wordTrace_append hprefix tailTrace_1481477
  have hstable : (prefixWord ++ tailWord_1481477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481477).length < 2 ^ (prefixWord ++ tailWord_1481477).sum := by decide
  have hdescent : baseEnd_1481477 < baseStart_1481477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481484 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 1, 7, 2]
def baseStart_1481484 : Nat := 118140960795 + 1481484 * 2 ^ 59
def prefixEnd_1481484 : Nat := 4983230072969 + 3 ^ 40 * 1481484 * 2
def baseEnd_1481484 : Nat := 760713373945586920736785

theorem tailTrace_1481484 : CollatzResearch.WordTrace tailWord_1481484 prefixEnd_1481484 760713373945586920736785 := by
  unfold tailWord_1481484
  simp only [CollatzResearch.WordTrace]
  refine ⟨27017080282421980084285753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36022773709895973445714337 27017080282421980084285753)
  ·
    refine ⟨20262810211816485063214315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27017080282421980084285753 20262810211816485063214315)
    ·
      refine ⟨30394215317724727594821473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20262810211816485063214315 30394215317724727594821473)
      ·
        refine ⟨22795661488293545696116105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30394215317724727594821473 22795661488293545696116105)
        ·
          refine ⟨17096746116220159272087079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22795661488293545696116105 17096746116220159272087079)
          ·
            refine ⟨25645119174330238908130619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17096746116220159272087079 25645119174330238908130619)
            ·
              refine ⟨38467678761495358362195929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25645119174330238908130619 38467678761495358362195929)
              ·
                refine ⟨28850759071121518771646947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38467678761495358362195929 28850759071121518771646947)
                ·
                  refine ⟨43276138606682278157470421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28850759071121518771646947 43276138606682278157470421)
                  ·
                    refine ⟨1014284498594115894315713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43276138606682278157470421 1014284498594115894315713)
                    ·
                      refine ⟨760713373945586920736785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1014284498594115894315713 760713373945586920736785)
                      ·
                        rfl

theorem cell23_1481484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1, 7, 2].length) (baseStart_1481484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481484 prefixEnd_1481484 := by exact prefixLift 1481484
  have htrace : WordTrace (prefixWord ++ tailWord_1481484) baseStart_1481484 baseEnd_1481484 := by
    simpa [prefixWord, tailWord_1481484, baseEnd_1481484] using wordTrace_append hprefix tailTrace_1481484
  have hstable : (prefixWord ++ tailWord_1481484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481484).length < 2 ^ (prefixWord ++ tailWord_1481484).sum := by decide
  have hdescent : baseEnd_1481484 < baseStart_1481484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481487 : List Nat := [1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 5]
def baseStart_1481487 : Nat := 118140960795 + 1481487 * 2 ^ 59
def prefixEnd_1481487 : Nat := 4983230072969 + 3 ^ 40 * 1481487 * 2
def baseEnd_1481487 : Nat := 760714914387550408999271

theorem tailTrace_1481487 : CollatzResearch.WordTrace tailWord_1481487 prefixEnd_1481487 760714914387550408999271 := by
  unfold tailWord_1481487
  simp only [CollatzResearch.WordTrace]
  refine ⟨54034269983833091680930715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36022846655888727787287143 54034269983833091680930715)
  ·
    refine ⟨81051404975749637521396073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54034269983833091680930715 81051404975749637521396073)
    ·
      refine ⟨60788553731812228141047055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81051404975749637521396073 60788553731812228141047055)
      ·
        refine ⟨91182830597718342211570583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60788553731812228141047055 91182830597718342211570583)
        ·
          refine ⟨136774245896577513317355875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91182830597718342211570583 136774245896577513317355875)
          ·
            refine ⟨205161368844866269976033813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136774245896577513317355875 205161368844866269976033813)
            ·
              refine ⟨9616939164603106405126585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 205161368844866269976033813 9616939164603106405126585)
              ·
                refine ⟨7212704373452329803844939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9616939164603106405126585 7212704373452329803844939)
                ·
                  refine ⟨10819056560178494705767409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7212704373452329803844939 10819056560178494705767409)
                  ·
                    refine ⟨8114292420133871029325557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10819056560178494705767409 8114292420133871029325557)
                    ·
                      refine ⟨760714914387550408999271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8114292420133871029325557 760714914387550408999271)
                      ·
                        rfl

theorem cell23_1481487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 5].length) (baseStart_1481487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481487 prefixEnd_1481487 := by exact prefixLift 1481487
  have htrace : WordTrace (prefixWord ++ tailWord_1481487) baseStart_1481487 baseEnd_1481487 := by
    simpa [prefixWord, tailWord_1481487, baseEnd_1481487] using wordTrace_append hprefix tailTrace_1481487
  have hstable : (prefixWord ++ tailWord_1481487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481487).length < 2 ^ (prefixWord ++ tailWord_1481487).sum := by decide
  have hdescent : baseEnd_1481487 < baseStart_1481487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481497 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 3, 3, 4]
def baseStart_1481497 : Nat := 118140960795 + 1481497 * 2 ^ 59
def prefixEnd_1481497 : Nat := 4983230072969 + 3 ^ 40 * 1481497 * 2
def baseEnd_1481497 : Nat := 760720049194095369874225

theorem tailTrace_1481497 : CollatzResearch.WordTrace tailWord_1481497 prefixEnd_1481497 760720049194095369874225 := by
  unfold tailWord_1481497
  simp only [CollatzResearch.WordTrace]
  refine ⟨54034634713796863388794745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36023089809197908925863163 54034634713796863388794745)
  ·
    refine ⟨40525976035347647541596059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54034634713796863388794745 40525976035347647541596059)
    ·
      refine ⟨60788964053021471312394089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40525976035347647541596059 60788964053021471312394089)
      ·
        refine ⟨45591723039766103484295567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60788964053021471312394089 45591723039766103484295567)
        ·
          refine ⟨68387584559649155226443351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45591723039766103484295567 68387584559649155226443351)
          ·
            refine ⟨102581376839473732839665027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68387584559649155226443351 102581376839473732839665027)
            ·
              refine ⟨153872065259210599259497541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102581376839473732839665027 153872065259210599259497541)
              ·
                refine ⟨28851012236101987361155789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 153872065259210599259497541 28851012236101987361155789)
                ·
                  refine ⟨10819129588538245260433421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28851012236101987361155789 10819129588538245260433421)
                  ·
                    refine ⟨4057173595701841972662533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10819129588538245260433421 4057173595701841972662533)
                    ·
                      refine ⟨760720049194095369874225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4057173595701841972662533 760720049194095369874225)
                      ·
                        rfl

theorem cell23_1481497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 3, 4].length) (baseStart_1481497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481497 prefixEnd_1481497 := by exact prefixLift 1481497
  have htrace : WordTrace (prefixWord ++ tailWord_1481497) baseStart_1481497 baseEnd_1481497 := by
    simpa [prefixWord, tailWord_1481497, baseEnd_1481497] using wordTrace_append hprefix tailTrace_1481497
  have hstable : (prefixWord ++ tailWord_1481497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481497).length < 2 ^ (prefixWord ++ tailWord_1481497).sum := by decide
  have hdescent : baseEnd_1481497 < baseStart_1481497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481504 : List Nat := [2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 5]
def baseStart_1481504 : Nat := 118140960795 + 1481504 * 2 ^ 59
def prefixEnd_1481504 : Nat := 4983230072969 + 3 ^ 40 * 1481504 * 2
def baseEnd_1481504 : Nat := 760723643558676842486693

theorem tailTrace_1481504 : CollatzResearch.WordTrace tailWord_1481504 prefixEnd_1481504 760723643558676842486693 := by
  unfold tailWord_1481504
  simp only [CollatzResearch.WordTrace]
  refine ⟨27017445012385751792149783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36023260016514335722866377 27017445012385751792149783)
  ·
    refine ⟨40526167518578627688224675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27017445012385751792149783 40526167518578627688224675)
    ·
      refine ⟨60789251277867941532337013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40526167518578627688224675 60789251277867941532337013)
      ·
        refine ⟨5698992307300119518656595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60789251277867941532337013 5698992307300119518656595)
        ·
          refine ⟨8548488460950179277984893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5698992307300119518656595 8548488460950179277984893)
          ·
            refine ⟨3205683172856317229244335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8548488460950179277984893 3205683172856317229244335)
            ·
              refine ⟨4808524759284475843866503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3205683172856317229244335 4808524759284475843866503)
              ·
                refine ⟨7212787138926713765799755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4808524759284475843866503 7212787138926713765799755)
                ·
                  refine ⟨10819180708390070648699633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7212787138926713765799755 10819180708390070648699633)
                  ·
                    refine ⟨8114385531292552986524725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10819180708390070648699633 8114385531292552986524725)
                    ·
                      refine ⟨760723643558676842486693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8114385531292552986524725 760723643558676842486693)
                      ·
                        rfl

theorem cell23_1481504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_1481504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481504 prefixEnd_1481504 := by exact prefixLift 1481504
  have htrace : WordTrace (prefixWord ++ tailWord_1481504) baseStart_1481504 baseEnd_1481504 := by
    simpa [prefixWord, tailWord_1481504, baseEnd_1481504] using wordTrace_append hprefix tailTrace_1481504
  have hstable : (prefixWord ++ tailWord_1481504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481504).length < 2 ^ (prefixWord ++ tailWord_1481504).sum := by decide
  have hdescent : baseEnd_1481504 < baseStart_1481504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481584 : List Nat := [2, 1, 1, 1, 4, 1, 4, 1, 3, 5]
def baseStart_1481584 : Nat := 118140960795 + 1481584 * 2 ^ 59
def prefixEnd_1481584 : Nat := 4983230072969 + 3 ^ 40 * 1481584 * 2
def baseEnd_1481584 : Nat := 253588240670345509828775

theorem tailTrace_1481584 : CollatzResearch.WordTrace tailWord_1481584 prefixEnd_1481584 253588240670345509828775 := by
  unfold tailWord_1481584
  simp only [CollatzResearch.WordTrace]
  refine ⟨27018903932240838623605903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36025205242987784831474537 27018903932240838623605903)
  ·
    refine ⟨40528355898361257935408855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27018903932240838623605903 40528355898361257935408855)
    ·
      refine ⟨60792533847541886903113283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40528355898361257935408855 60792533847541886903113283)
      ·
        refine ⟨91188800771312830354669925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60792533847541886903113283 91188800771312830354669925)
        ·
          refine ⟨17097900144621155691500611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91188800771312830354669925 17097900144621155691500611)
          ·
            refine ⟨25646850216931733537250917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17097900144621155691500611 25646850216931733537250917)
            ·
              refine ⟨4808784415674700038234547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25646850216931733537250917 4808784415674700038234547)
              ·
                refine ⟨7213176623512050057351821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4808784415674700038234547 7213176623512050057351821)
                ·
                  refine ⟨2704941233817018771506933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7213176623512050057351821 2704941233817018771506933)
                  ·
                    refine ⟨253588240670345509828775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2704941233817018771506933 253588240670345509828775)
                    ·
                      rfl

theorem cell23_1481584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 3, 5].length) (baseStart_1481584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481584 prefixEnd_1481584 := by exact prefixLift 1481584
  have htrace : WordTrace (prefixWord ++ tailWord_1481584) baseStart_1481584 baseEnd_1481584 := by
    simpa [prefixWord, tailWord_1481584, baseEnd_1481584] using wordTrace_append hprefix tailTrace_1481584
  have hstable : (prefixWord ++ tailWord_1481584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481584).length < 2 ^ (prefixWord ++ tailWord_1481584).sum := by decide
  have hdescent : baseEnd_1481584 < baseStart_1481584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481622 : List Nat := [5, 3, 1, 1, 1, 2, 3, 1, 6]
def baseStart_1481622 : Nat := 118140960795 + 1481622 * 2 ^ 59
def prefixEnd_1481622 : Nat := 4983230072969 + 3 ^ 40 * 1481622 * 2
def baseEnd_1481622 : Nat := 84531581586211931201239

theorem tailTrace_1481622 : CollatzResearch.WordTrace tailWord_1481622 prefixEnd_1481622 84531581586211931201239 := by
  unfold tailWord_1481622
  simp only [CollatzResearch.WordTrace]
  refine ⟨3377449614896500608568445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36026129225562673158063413 3377449614896500608568445)
  ·
    refine ⟨1266543605586187728213167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3377449614896500608568445 1266543605586187728213167)
    ·
      refine ⟨1899815408379281592319751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1266543605586187728213167 1899815408379281592319751)
      ·
        refine ⟨2849723112568922388479627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1899815408379281592319751 2849723112568922388479627)
        ·
          refine ⟨4274584668853383582719441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2849723112568922388479627 4274584668853383582719441)
          ·
            refine ⟨3205938501640037687039581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4274584668853383582719441 3205938501640037687039581)
            ·
              refine ⟨1202226938115014132639843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3205938501640037687039581 1202226938115014132639843)
              ·
                refine ⟨1803340407172521198959765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1202226938115014132639843 1803340407172521198959765)
                ·
                  refine ⟨84531581586211931201239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1803340407172521198959765 84531581586211931201239)
                  ·
                    rfl

theorem cell23_1481622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_1481622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481622 prefixEnd_1481622 := by exact prefixLift 1481622
  have htrace : WordTrace (prefixWord ++ tailWord_1481622) baseStart_1481622 baseEnd_1481622 := by
    simpa [prefixWord, tailWord_1481622, baseEnd_1481622] using wordTrace_append hprefix tailTrace_1481622
  have hstable : (prefixWord ++ tailWord_1481622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481622).length < 2 ^ (prefixWord ++ tailWord_1481622).sum := by decide
  have hdescent : baseEnd_1481622 < baseStart_1481622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481631 : List Nat := [1, 1, 2, 5, 2, 1, 3, 1, 1, 6]
def baseStart_1481631 : Nat := 118140960795 + 1481631 * 2 ^ 59
def prefixEnd_1481631 : Nat := 4983230072969 + 3 ^ 40 * 1481631 * 2
def baseEnd_1481631 : Nat := 253596285200599281866203

theorem tailTrace_1481631 : CollatzResearch.WordTrace tailWord_1481631 prefixEnd_1481631 253596285200599281866203 := by
  unfold tailWord_1481631
  simp only [CollatzResearch.WordTrace]
  refine ⟨54039522095311404274172747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36026348063540936182781831 54039522095311404274172747)
  ·
    refine ⟨81059283142967106411259121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54039522095311404274172747 81059283142967106411259121)
    ·
      refine ⟨60794462357225329808444341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81059283142967106411259121 60794462357225329808444341)
      ·
        refine ⟨5699480845989874669541657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60794462357225329808444341 5699480845989874669541657)
        ·
          refine ⟨4274610634492406002156243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5699480845989874669541657 4274610634492406002156243)
          ·
            refine ⟨6411915951738609003234365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4274610634492406002156243 6411915951738609003234365)
            ·
              refine ⟨2404468481901978376212887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6411915951738609003234365 2404468481901978376212887)
              ·
                refine ⟨3606702722852967564319331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2404468481901978376212887 3606702722852967564319331)
                ·
                  refine ⟨5410054084279451346478997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3606702722852967564319331 5410054084279451346478997)
                  ·
                    refine ⟨253596285200599281866203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5410054084279451346478997 253596285200599281866203)
                    ·
                      rfl

theorem cell23_1481631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 6].length) (baseStart_1481631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481631 prefixEnd_1481631 := by exact prefixLift 1481631
  have htrace : WordTrace (prefixWord ++ tailWord_1481631) baseStart_1481631 baseEnd_1481631 := by
    simpa [prefixWord, tailWord_1481631, baseEnd_1481631] using wordTrace_append hprefix tailTrace_1481631
  have hstable : (prefixWord ++ tailWord_1481631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481631).length < 2 ^ (prefixWord ++ tailWord_1481631).sum := by decide
  have hdescent : baseEnd_1481631 < baseStart_1481631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481649 : List Nat := [1, 2, 2, 4, 4, 1, 1, 3, 1, 1, 3]
def baseStart_1481649 : Nat := 118140960795 + 1481649 * 2 ^ 59
def prefixEnd_1481649 : Nat := 4983230072969 + 3 ^ 40 * 1481649 * 2
def baseEnd_1481649 : Nat := 760798098253578775173527

theorem tailTrace_1481649 : CollatzResearch.WordTrace tailWord_1481649 prefixEnd_1481649 760798098253578775173527 := by
  unfold tailWord_1481649
  simp only [CollatzResearch.WordTrace]
  refine ⟨54040178609246193348328001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36026785739497462232218667 54040178609246193348328001)
  ·
    refine ⟨40530133956934645011246001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54040178609246193348328001 40530133956934645011246001)
    ·
      refine ⟨30397600467700983758434501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40530133956934645011246001 30397600467700983758434501)
      ·
        refine ⟨5699550087693934454706469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30397600467700983758434501 5699550087693934454706469)
        ·
          refine ⟨1068665641442612710257463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5699550087693934454706469 1068665641442612710257463)
          ·
            refine ⟨1602998462163919065386195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1068665641442612710257463 1602998462163919065386195)
            ·
              refine ⟨2404497693245878598079293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1602998462163919065386195 2404497693245878598079293)
              ·
                refine ⟨901686634967204474279735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2404497693245878598079293 901686634967204474279735)
                ·
                  refine ⟨1352529952450806711419603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 901686634967204474279735 1352529952450806711419603)
                  ·
                    refine ⟨2028794928676210067129405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1352529952450806711419603 2028794928676210067129405)
                    ·
                      refine ⟨760798098253578775173527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2028794928676210067129405 760798098253578775173527)
                      ·
                        rfl

theorem cell23_1481649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_1481649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481649 prefixEnd_1481649 := by exact prefixLift 1481649
  have htrace : WordTrace (prefixWord ++ tailWord_1481649) baseStart_1481649 baseEnd_1481649 := by
    simpa [prefixWord, tailWord_1481649, baseEnd_1481649] using wordTrace_append hprefix tailTrace_1481649
  have hstable : (prefixWord ++ tailWord_1481649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481649).length < 2 ^ (prefixWord ++ tailWord_1481649).sum := by decide
  have hdescent : baseEnd_1481649 < baseStart_1481649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481661 : List Nat := [1, 4, 1, 2, 4, 2, 9]
def baseStart_1481661 : Nat := 118140960795 + 1481661 * 2 ^ 59
def prefixEnd_1481661 : Nat := 4983230072969 + 3 ^ 40 * 1481661 * 2
def baseEnd_1481661 : Nat := 9392645185449786768191

theorem tailTrace_1481661 : CollatzResearch.WordTrace tailWord_1481661 prefixEnd_1481661 9392645185449786768191 := by
  unfold tailWord_1481661
  simp only [CollatzResearch.WordTrace]
  refine ⟨54040616285202719397764837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36027077523468479598509891 54040616285202719397764837)
  ·
    refine ⟨10132615553475509887080907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54040616285202719397764837 10132615553475509887080907)
    ·
      refine ⟨15198923330213264830621361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10132615553475509887080907 15198923330213264830621361)
      ·
        refine ⟨11399192497659948622966021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15198923330213264830621361 11399192497659948622966021)
        ·
          refine ⟨2137348593311240366806129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11399192497659948622966021 2137348593311240366806129)
          ·
            refine ⟨1603011444983430275104597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2137348593311240366806129 1603011444983430275104597)
            ·
              refine ⟨9392645185449786768191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1603011444983430275104597 9392645185449786768191)
              ·
                rfl

theorem cell23_1481661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 9].length) (baseStart_1481661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481661 prefixEnd_1481661 := by exact prefixLift 1481661
  have htrace : WordTrace (prefixWord ++ tailWord_1481661) baseStart_1481661 baseEnd_1481661 := by
    simpa [prefixWord, tailWord_1481661, baseEnd_1481661] using wordTrace_append hprefix tailTrace_1481661
  have hstable : (prefixWord ++ tailWord_1481661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481661).length < 2 ^ (prefixWord ++ tailWord_1481661).sum := by decide
  have hdescent : baseEnd_1481661 < baseStart_1481661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481672 : List Nat := [2, 1, 3, 1, 5, 2, 1, 1, 3, 2, 2]
def baseStart_1481672 : Nat := 118140960795 + 1481672 * 2 ^ 59
def prefixEnd_1481672 : Nat := 4983230072969 + 3 ^ 40 * 1481672 * 2
def baseEnd_1481672 : Nat := 760809908308632185185921

theorem tailTrace_1481672 : CollatzResearch.WordTrace tailWord_1481672 prefixEnd_1481672 760809908308632185185921 := by
  unfold tailWord_1481672
  simp only [CollatzResearch.WordTrace]
  refine ⟨27020508744081434138207635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36027344992108578850943513 27020508744081434138207635)
  ·
    refine ⟨40530763116122151207311453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27020508744081434138207635 40530763116122151207311453)
    ·
      refine ⟨15199036168545806702741795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40530763116122151207311453 15199036168545806702741795)
      ·
        refine ⟨22798554252818710054112693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15199036168545806702741795 22798554252818710054112693)
        ·
          refine ⟨2137364461201754067573065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22798554252818710054112693 2137364461201754067573065)
          ·
            refine ⟨1603023345901315550679799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2137364461201754067573065 1603023345901315550679799)
            ·
              refine ⟨2404535018851973326019699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1603023345901315550679799 2404535018851973326019699)
              ·
                refine ⟨3606802528277959989029549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2404535018851973326019699 3606802528277959989029549)
                ·
                  refine ⟨1352550948104234995886081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3606802528277959989029549 1352550948104234995886081)
                  ·
                    refine ⟨1014413211078176246914561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1352550948104234995886081 1014413211078176246914561)
                    ·
                      refine ⟨760809908308632185185921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1014413211078176246914561 760809908308632185185921)
                      ·
                        rfl

theorem cell23_1481672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 3, 2, 2].length) (baseStart_1481672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481672 prefixEnd_1481672 := by exact prefixLift 1481672
  have htrace : WordTrace (prefixWord ++ tailWord_1481672) baseStart_1481672 baseEnd_1481672 := by
    simpa [prefixWord, tailWord_1481672, baseEnd_1481672] using wordTrace_append hprefix tailTrace_1481672
  have hstable : (prefixWord ++ tailWord_1481672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481672).length < 2 ^ (prefixWord ++ tailWord_1481672).sum := by decide
  have hdescent : baseEnd_1481672 < baseStart_1481672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481674 : List Nat := [3, 1, 2, 1, 2, 1, 1, 3, 2, 7]
def baseStart_1481674 : Nat := 118140960795 + 1481674 * 2 ^ 59
def prefixEnd_1481674 : Nat := 4983230072969 + 3 ^ 40 * 1481674 * 2
def baseEnd_1481674 : Nat := 253603645089980392453637

theorem tailTrace_1481674 : CollatzResearch.WordTrace tailWord_1481674 prefixEnd_1481674 253603645089980392453637 := by
  unfold tailWord_1481674
  simp only [CollatzResearch.WordTrace]
  refine ⟨13510272608538905654497019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36027393622770415078658717 13510272608538905654497019)
  ·
    refine ⟨20265408912808358481745529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13510272608538905654497019 20265408912808358481745529)
    ·
      refine ⟨15199056684606268861309147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20265408912808358481745529 15199056684606268861309147)
      ·
        refine ⟨22798585026909403291963721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15199056684606268861309147 22798585026909403291963721)
        ·
          refine ⟨17098938770182052468972791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22798585026909403291963721 17098938770182052468972791)
          ·
            refine ⟨25648408155273078703459187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17098938770182052468972791 25648408155273078703459187)
            ·
              refine ⟨38472612232909618055188781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25648408155273078703459187 38472612232909618055188781)
              ·
                refine ⟨14427229587341106770695793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38472612232909618055188781 14427229587341106770695793)
                ·
                  refine ⟨10820422190505830078021845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14427229587341106770695793 10820422190505830078021845)
                  ·
                    refine ⟨253603645089980392453637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10820422190505830078021845 253603645089980392453637)
                    ·
                      rfl

theorem cell23_1481674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_1481674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481674 prefixEnd_1481674 := by exact prefixLift 1481674
  have htrace : WordTrace (prefixWord ++ tailWord_1481674) baseStart_1481674 baseEnd_1481674 := by
    simpa [prefixWord, tailWord_1481674, baseEnd_1481674] using wordTrace_append hprefix tailTrace_1481674
  have hstable : (prefixWord ++ tailWord_1481674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481674).length < 2 ^ (prefixWord ++ tailWord_1481674).sum := by decide
  have hdescent : baseEnd_1481674 < baseStart_1481674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481682 : List Nat := [3, 2, 2, 3, 1, 3, 2, 1, 2, 4]
def baseStart_1481682 : Nat := 118140960795 + 1481682 * 2 ^ 59
def prefixEnd_1481682 : Nat := 4983230072969 + 3 ^ 40 * 1481682 * 2
def baseEnd_1481682 : Nat := 253605014371725715353625

theorem tailTrace_1481682 : CollatzResearch.WordTrace tailWord_1481682 prefixEnd_1481682 253605014371725715353625 := by
  unfold tailWord_1481682
  simp only [CollatzResearch.WordTrace]
  refine ⟨13510345554531659996069825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36027588145417759989519533 13510345554531659996069825)
  ·
    refine ⟨10132759165898744997052369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13510345554531659996069825 10132759165898744997052369)
    ·
      refine ⟨7599569374424058747789277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10132759165898744997052369 7599569374424058747789277)
      ·
        refine ⟨2849838515409022030420979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7599569374424058747789277 2849838515409022030420979)
        ·
          refine ⟨4274757773113533045631469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2849838515409022030420979 4274757773113533045631469)
          ·
            refine ⟨1603034164917574892111801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4274757773113533045631469 1603034164917574892111801)
            ·
              refine ⟨1202275623688181169083851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1603034164917574892111801 1202275623688181169083851)
              ·
                refine ⟨1803413435532271753625777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1202275623688181169083851 1803413435532271753625777)
                ·
                  refine ⟨1352560076649203815219333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1803413435532271753625777 1352560076649203815219333)
                  ·
                    refine ⟨253605014371725715353625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1352560076649203815219333 253605014371725715353625)
                    ·
                      rfl

theorem cell23_1481682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_1481682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481682 prefixEnd_1481682 := by exact prefixLift 1481682
  have htrace : WordTrace (prefixWord ++ tailWord_1481682) baseStart_1481682 baseEnd_1481682 := by
    simpa [prefixWord, tailWord_1481682, baseEnd_1481682] using wordTrace_append hprefix tailTrace_1481682
  have hstable : (prefixWord ++ tailWord_1481682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481682).length < 2 ^ (prefixWord ++ tailWord_1481682).sum := by decide
  have hdescent : baseEnd_1481682 < baseStart_1481682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481716 : List Nat := [2, 6, 2, 1, 1, 1, 2, 2, 2, 4]
def baseStart_1481716 : Nat := 118140960795 + 1481716 * 2 ^ 59
def prefixEnd_1481716 : Nat := 4983230072969 + 3 ^ 40 * 1481716 * 2
def baseEnd_1481716 : Nat := 253610833819143337678573

theorem tailTrace_1481716 : CollatzResearch.WordTrace tailWord_1481716 prefixEnd_1481716 253610833819143337678573 := by
  unfold tailWord_1481716
  simp only [CollatzResearch.WordTrace]
  refine ⟨27021311150001731895508501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36028414866668975860678001 27021311150001731895508501)
  ·
    refine ⟨1266623960156331182601961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27021311150001731895508501 1266623960156331182601961)
    ·
      refine ⟨949967970117248386951471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1266623960156331182601961 949967970117248386951471)
      ·
        refine ⟨1424951955175872580427207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 949967970117248386951471 1424951955175872580427207)
        ·
          refine ⟨2137427932763808870640811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1424951955175872580427207 2137427932763808870640811)
          ·
            refine ⟨3206141899145713305961217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2137427932763808870640811 3206141899145713305961217)
            ·
              refine ⟨2404606424359284979470913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3206141899145713305961217 2404606424359284979470913)
              ·
                refine ⟨1803454818269463734603185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2404606424359284979470913 1803454818269463734603185)
                ·
                  refine ⟨1352591113702097800952389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1803454818269463734603185 1352591113702097800952389)
                  ·
                    refine ⟨253610833819143337678573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1352591113702097800952389 253610833819143337678573)
                    ·
                      rfl

theorem cell23_1481716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_1481716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481716 prefixEnd_1481716 := by exact prefixLift 1481716
  have htrace : WordTrace (prefixWord ++ tailWord_1481716) baseStart_1481716 baseEnd_1481716 := by
    simpa [prefixWord, tailWord_1481716, baseEnd_1481716] using wordTrace_append hprefix tailTrace_1481716
  have hstable : (prefixWord ++ tailWord_1481716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481716).length < 2 ^ (prefixWord ++ tailWord_1481716).sum := by decide
  have hdescent : baseEnd_1481716 < baseStart_1481716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481728 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 8, 2, 2]
def baseStart_1481728 : Nat := 118140960795 + 1481728 * 2 ^ 59
def prefixEnd_1481728 : Nat := 4983230072969 + 3 ^ 40 * 1481728 * 2
def baseEnd_1481728 : Nat := 760838663225283966085663

theorem tailTrace_1481728 : CollatzResearch.WordTrace tailWord_1481728 prefixEnd_1481728 760838663225283966085663 := by
  unfold tailWord_1481728
  simp only [CollatzResearch.WordTrace]
  refine ⟨27021529987979994920226919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36028706650639993226969225 27021529987979994920226919)
  ·
    refine ⟨40532294981969992380340379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27021529987979994920226919 40532294981969992380340379)
    ·
      refine ⟨60798442472954988570510569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40532294981969992380340379 60798442472954988570510569)
      ·
        refine ⟨45598831854716241427882927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60798442472954988570510569 45598831854716241427882927)
        ·
          refine ⟨68398247782074362141824391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45598831854716241427882927 68398247782074362141824391)
          ·
            refine ⟨102597371673111543212736587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68398247782074362141824391 102597371673111543212736587)
            ·
              refine ⟨153896057509667314819104881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102597371673111543212736587 153896057509667314819104881)
              ·
                refine ⟨115422043132250486114328661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153896057509667314819104881 115422043132250486114328661)
                ·
                  refine ⟨1352602067956060384152289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 115422043132250486114328661 1352602067956060384152289)
                  ·
                    refine ⟨1014451550967045288114217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1352602067956060384152289 1014451550967045288114217)
                    ·
                      refine ⟨760838663225283966085663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1014451550967045288114217 760838663225283966085663)
                      ·
                        rfl

theorem cell23_1481728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 8, 2, 2].length) (baseStart_1481728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481728 prefixEnd_1481728 := by exact prefixLift 1481728
  have htrace : WordTrace (prefixWord ++ tailWord_1481728) baseStart_1481728 baseEnd_1481728 := by
    simpa [prefixWord, tailWord_1481728, baseEnd_1481728] using wordTrace_append hprefix tailTrace_1481728
  have hstable : (prefixWord ++ tailWord_1481728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481728).length < 2 ^ (prefixWord ++ tailWord_1481728).sum := by decide
  have hdescent : baseEnd_1481728 < baseStart_1481728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481751 : List Nat := [1, 1, 3, 5, 1, 1, 1, 1, 9]
def baseStart_1481751 : Nat := 118140960795 + 1481751 * 2 ^ 59
def prefixEnd_1481751 : Nat := 4983230072969 + 3 ^ 40 * 1481751 * 2
def baseEnd_1481751 : Nat := 84538941475593041788673

theorem tailTrace_1481751 : CollatzResearch.WordTrace tailWord_1481751 prefixEnd_1481751 84538941475593041788673 := by
  unfold tailWord_1481751
  simp only [CollatzResearch.WordTrace]
  refine ⟨54043898854876664768541107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36029265903251109845694071 54043898854876664768541107)
  ·
    refine ⟨81065848282314997152811661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54043898854876664768541107 81065848282314997152811661)
    ·
      refine ⟨30399693105868123932304373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81065848282314997152811661 30399693105868123932304373)
      ·
        refine ⟨2849971228675136618653535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30399693105868123932304373 2849971228675136618653535)
        ·
          refine ⟨4274956843012704927980303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2849971228675136618653535 4274956843012704927980303)
          ·
            refine ⟨6412435264519057391970455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4274956843012704927980303 6412435264519057391970455)
            ·
              refine ⟨9618652896778586087955683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6412435264519057391970455 9618652896778586087955683)
              ·
                refine ⟨14427979345167879131933525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9618652896778586087955683 14427979345167879131933525)
                ·
                  refine ⟨84538941475593041788673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 14427979345167879131933525 84538941475593041788673)
                  ·
                    rfl

theorem cell23_1481751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 9].length) (baseStart_1481751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481751 prefixEnd_1481751 := by exact prefixLift 1481751
  have htrace : WordTrace (prefixWord ++ tailWord_1481751) baseStart_1481751 baseEnd_1481751 := by
    simpa [prefixWord, tailWord_1481751, baseEnd_1481751] using wordTrace_append hprefix tailTrace_1481751
  have hstable : (prefixWord ++ tailWord_1481751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481751).length < 2 ^ (prefixWord ++ tailWord_1481751).sum := by decide
  have hdescent : baseEnd_1481751 < baseStart_1481751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481781 : List Nat := [1, 3, 3, 1, 1, 1, 1, 3, 4, 5]
def baseStart_1481781 : Nat := 118140960795 + 1481781 * 2 ^ 59
def prefixEnd_1481781 : Nat := 4983230072969 + 3 ^ 40 * 1481781 * 2
def baseEnd_1481781 : Nat := 253621959233324086240973

theorem tailTrace_1481781 : CollatzResearch.WordTrace tailWord_1481781 prefixEnd_1481781 253621959233324086240973 := by
  unfold tailWord_1481781
  simp only [CollatzResearch.WordTrace]
  refine ⟨54044993044767979892133197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36029995363178653261422131 54044993044767979892133197)
  ·
    refine ⟨20266872391787992459549949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54044993044767979892133197 20266872391787992459549949)
    ·
      refine ⟨7600077146920497172331231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20266872391787992459549949 7600077146920497172331231)
      ·
        refine ⟨11400115720380745758496847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7600077146920497172331231 11400115720380745758496847)
        ·
          refine ⟨17100173580571118637745271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11400115720380745758496847 17100173580571118637745271)
          ·
            refine ⟨25650260370856677956617907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17100173580571118637745271 25650260370856677956617907)
            ·
              refine ⟨38475390556285016934926861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25650260370856677956617907 38475390556285016934926861)
              ·
                refine ⟨14428271458606881350597573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38475390556285016934926861 14428271458606881350597573)
                ·
                  refine ⟨2705300898488790253237045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14428271458606881350597573 2705300898488790253237045)
                  ·
                    refine ⟨253621959233324086240973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2705300898488790253237045 253621959233324086240973)
                    ·
                      rfl

theorem cell23_1481781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_1481781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481781 prefixEnd_1481781 := by exact prefixLift 1481781
  have htrace : WordTrace (prefixWord ++ tailWord_1481781) baseStart_1481781 baseEnd_1481781 := by
    simpa [prefixWord, tailWord_1481781, baseEnd_1481781] using wordTrace_append hprefix tailTrace_1481781
  have hstable : (prefixWord ++ tailWord_1481781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481781).length < 2 ^ (prefixWord ++ tailWord_1481781).sum := by decide
  have hdescent : baseEnd_1481781 < baseStart_1481781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481801 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 6, 1, 4]
def baseStart_1481801 : Nat := 118140960795 + 1481801 * 2 ^ 59
def prefixEnd_1481801 : Nat := 4983230072969 + 3 ^ 40 * 1481801 * 2
def baseEnd_1481801 : Nat := 760876147313062180472827

theorem tailTrace_1481801 : CollatzResearch.WordTrace tailWord_1481801 prefixEnd_1481801 760876147313062180472827 := by
  unfold tailWord_1481801
  simp only [CollatzResearch.WordTrace]
  refine ⟨54045722504695523307861257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36030481669797015538574171 54045722504695523307861257)
  ·
    refine ⟨40534291878521642480895943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54045722504695523307861257 40534291878521642480895943)
    ·
      refine ⟨60801437817782463721343915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40534291878521642480895943 60801437817782463721343915)
      ·
        refine ⟨91202156726673695582015873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60801437817782463721343915 91202156726673695582015873)
        ·
          refine ⟨68401617545005271686511905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91202156726673695582015873 68401617545005271686511905)
          ·
            refine ⟨51301213158753953764883929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68401617545005271686511905 51301213158753953764883929)
            ·
              refine ⟨38475909869065465323662947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51301213158753953764883929 38475909869065465323662947)
              ·
                refine ⟨57713864803598197985494421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38475909869065465323662947 57713864803598197985494421)
                ·
                  refine ⟨2705337412668665530570051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 57713864803598197985494421 2705337412668665530570051)
                  ·
                    refine ⟨4058006119002998295855077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2705337412668665530570051 4058006119002998295855077)
                    ·
                      refine ⟨760876147313062180472827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4058006119002998295855077 760876147313062180472827)
                      ·
                        rfl

theorem cell23_1481801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 6, 1, 4].length) (baseStart_1481801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481801 prefixEnd_1481801 := by exact prefixLift 1481801
  have htrace : WordTrace (prefixWord ++ tailWord_1481801) baseStart_1481801 baseEnd_1481801 := by
    simpa [prefixWord, tailWord_1481801, baseEnd_1481801] using wordTrace_append hprefix tailTrace_1481801
  have hstable : (prefixWord ++ tailWord_1481801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481801).length < 2 ^ (prefixWord ++ tailWord_1481801).sum := by decide
  have hdescent : baseEnd_1481801 < baseStart_1481801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481818 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 4, 4, 2]
def baseStart_1481818 : Nat := 118140960795 + 1481818 * 2 ^ 59
def prefixEnd_1481818 : Nat := 4983230072969 + 3 ^ 40 * 1481818 * 2
def baseEnd_1481818 : Nat := 760884876484188613960249

theorem tailTrace_1481818 : CollatzResearch.WordTrace tailWord_1481818 prefixEnd_1481818 760884876484188613960249 := by
  unfold tailWord_1481818
  simp only [CollatzResearch.WordTrace]
  refine ⟨13511585636408483802807527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36030895030422623474153405 13511585636408483802807527)
  ·
    refine ⟨20267378454612725704211291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13511585636408483802807527 20267378454612725704211291)
    ·
      refine ⟨30401067681919088556316937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20267378454612725704211291 30401067681919088556316937)
      ·
        refine ⟨22800800761439316417237703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30401067681919088556316937 22800800761439316417237703)
        ·
          refine ⟨34201201142158974625856555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22800800761439316417237703 34201201142158974625856555)
          ·
            refine ⟨51301801713238461938784833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34201201142158974625856555 51301801713238461938784833)
            ·
              refine ⟨38476351284928846454088625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51301801713238461938784833 38476351284928846454088625)
              ·
                refine ⟨28857263463696634840566469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38476351284928846454088625 28857263463696634840566469)
                ·
                  refine ⟨5410736899443119032606213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28857263463696634840566469 5410736899443119032606213)
                  ·
                    refine ⟨1014513168645584818613665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5410736899443119032606213 1014513168645584818613665)
                    ·
                      refine ⟨760884876484188613960249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1014513168645584818613665 760884876484188613960249)
                      ·
                        rfl

theorem cell23_1481818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 4, 4, 2].length) (baseStart_1481818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481818 prefixEnd_1481818 := by exact prefixLift 1481818
  have htrace : WordTrace (prefixWord ++ tailWord_1481818) baseStart_1481818 baseEnd_1481818 := by
    simpa [prefixWord, tailWord_1481818, baseEnd_1481818] using wordTrace_append hprefix tailTrace_1481818
  have hstable : (prefixWord ++ tailWord_1481818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481818).length < 2 ^ (prefixWord ++ tailWord_1481818).sum := by decide
  have hdescent : baseEnd_1481818 < baseStart_1481818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481952 : List Nat := [2, 1, 1, 3, 1, 6, 1, 2, 2, 4]
def baseStart_1481952 : Nat := 118140960795 + 1481952 * 2 ^ 59
def prefixEnd_1481952 : Nat := 4983230072969 + 3 ^ 40 * 1481952 * 2
def baseEnd_1481952 : Nat := 253651227630630363228211

theorem tailTrace_1481952 : CollatzResearch.WordTrace tailWord_1481952 prefixEnd_1481952 253651227630630363228211 := by
  unfold tailWord_1481952
  simp only [CollatzResearch.WordTrace]
  refine ⟨27025614963574238048304055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36034153284765650731072073 27025614963574238048304055)
  ·
    refine ⟨40538422445361357072456083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27025614963574238048304055 40538422445361357072456083)
    ·
      refine ⟨60807633668042035608684125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40538422445361357072456083 60807633668042035608684125)
      ·
        refine ⟨22802862625515763353256547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60807633668042035608684125 22802862625515763353256547)
        ·
          refine ⟨34204293938273645029884821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22802862625515763353256547 34204293938273645029884821)
          ·
            refine ⟨1603326278356577110775851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 34204293938273645029884821 1603326278356577110775851)
            ·
              refine ⟨2404989417534865666163777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1603326278356577110775851 2404989417534865666163777)
              ·
                refine ⟨1803742063151149249622833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2404989417534865666163777 1803742063151149249622833)
                ·
                  refine ⟨1352806547363361937217125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1803742063151149249622833 1352806547363361937217125)
                  ·
                    refine ⟨253651227630630363228211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1352806547363361937217125 253651227630630363228211)
                    ·
                      rfl

theorem cell23_1481952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 2, 2, 4].length) (baseStart_1481952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481952 prefixEnd_1481952 := by exact prefixLift 1481952
  have htrace : WordTrace (prefixWord ++ tailWord_1481952) baseStart_1481952 baseEnd_1481952 := by
    simpa [prefixWord, tailWord_1481952, baseEnd_1481952] using wordTrace_append hprefix tailTrace_1481952
  have hstable : (prefixWord ++ tailWord_1481952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481952).length < 2 ^ (prefixWord ++ tailWord_1481952).sum := by decide
  have hdescent : baseEnd_1481952 < baseStart_1481952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481982 : List Nat := [4, 2, 2, 1, 1, 4, 2, 7]
def baseStart_1481982 : Nat := 118140960795 + 1481982 * 2 ^ 59
def prefixEnd_1481982 : Nat := 4983230072969 + 3 ^ 40 * 1481982 * 2
def baseEnd_1481982 : Nat := 28184040270797258233685

theorem tailTrace_1481982 : CollatzResearch.WordTrace tailWord_1481982 prefixEnd_1481982 28184040270797258233685 := by
  unfold tailWord_1481982
  simp only [CollatzResearch.WordTrace]
  refine ⟨6756540514629973902525025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36034882744693194146800133 6756540514629973902525025)
  ·
    refine ⟨5067405385972480426893769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6756540514629973902525025 5067405385972480426893769)
    ·
      refine ⟨3800554039479360320170327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5067405385972480426893769 3800554039479360320170327)
      ·
        refine ⟨5700831059219040480255491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3800554039479360320170327 5700831059219040480255491)
        ·
          refine ⟨8551246588828560720383237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5700831059219040480255491 8551246588828560720383237)
          ·
            refine ⟨1603358735405355135071857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8551246588828560720383237 1603358735405355135071857)
            ·
              refine ⟨1202519051554016351303893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1603358735405355135071857 1202519051554016351303893)
              ·
                refine ⟨28184040270797258233685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1202519051554016351303893 28184040270797258233685)
                ·
                  rfl

theorem cell23_1481982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 7].length) (baseStart_1481982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1481982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1481982 prefixEnd_1481982 := by exact prefixLift 1481982
  have htrace : WordTrace (prefixWord ++ tailWord_1481982) baseStart_1481982 baseEnd_1481982 := by
    simpa [prefixWord, tailWord_1481982, baseEnd_1481982] using wordTrace_append hprefix tailTrace_1481982
  have hstable : (prefixWord ++ tailWord_1481982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481982).length < 2 ^ (prefixWord ++ tailWord_1481982).sum := by decide
  have hdescent : baseEnd_1481982 < baseStart_1481982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482026 : List Nat := [3, 1, 4, 2, 1, 1, 4, 1, 2, 1, 3]
def baseStart_1482026 : Nat := 118140960795 + 1482026 * 2 ^ 59
def prefixEnd_1482026 : Nat := 4983230072969 + 3 ^ 40 * 1482026 * 2
def baseEnd_1482026 : Nat := 760991680460323800159293

theorem tailTrace_1482026 : CollatzResearch.WordTrace tailWord_1482026 prefixEnd_1482026 760991680460323800159293 := by
  unfold tailWord_1482026
  simp only [CollatzResearch.WordTrace]
  refine ⟨13513482232220096683700483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36035952619253591156534621 13513482232220096683700483)
  ·
    refine ⟨20270223348330145025550725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13513482232220096683700483 20270223348330145025550725)
    ·
      refine ⟨3800666877811902192290761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20270223348330145025550725 3800666877811902192290761)
      ·
        refine ⟨2850500158358926644218071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3800666877811902192290761 2850500158358926644218071)
        ·
          refine ⟨4275750237538389966327107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2850500158358926644218071 4275750237538389966327107)
          ·
            refine ⟨6413625356307584949490661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4275750237538389966327107 6413625356307584949490661)
            ·
              refine ⟨1202554754307672178029499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6413625356307584949490661 1202554754307672178029499)
              ·
                refine ⟨1803832131461508267044249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1202554754307672178029499 1803832131461508267044249)
                ·
                  refine ⟨1352874098596131200283187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1803832131461508267044249 1352874098596131200283187)
                  ·
                    refine ⟨2029311147894196800424781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1352874098596131200283187 2029311147894196800424781)
                    ·
                      refine ⟨760991680460323800159293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2029311147894196800424781 760991680460323800159293)
                      ·
                        rfl

theorem cell23_1482026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_1482026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482026 prefixEnd_1482026 := by exact prefixLift 1482026
  have htrace : WordTrace (prefixWord ++ tailWord_1482026) baseStart_1482026 baseEnd_1482026 := by
    simpa [prefixWord, tailWord_1482026, baseEnd_1482026] using wordTrace_append hprefix tailTrace_1482026
  have hstable : (prefixWord ++ tailWord_1482026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482026).length < 2 ^ (prefixWord ++ tailWord_1482026).sum := by decide
  have hdescent : baseEnd_1482026 < baseStart_1482026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482028 : List Nat := [2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 4]
def baseStart_1482028 : Nat := 118140960795 + 1482028 * 2 ^ 59
def prefixEnd_1482028 : Nat := 4983230072969 + 3 ^ 40 * 1482028 * 2
def baseEnd_1482028 : Nat := 760992707421632792334283

theorem tailTrace_1482028 : CollatzResearch.WordTrace tailWord_1482028 prefixEnd_1482028 760992707421632792334283 := by
  unfold tailWord_1482028
  simp only [CollatzResearch.WordTrace]
  refine ⟨27027000937436570538187369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36036001249915427384249825 27027000937436570538187369)
  ·
    refine ⟨20270250703077427903640527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27027000937436570538187369 20270250703077427903640527)
    ·
      refine ⟨30405376054616141855460791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20270250703077427903640527 30405376054616141855460791)
      ·
        refine ⟨45608064081924212783191187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30405376054616141855460791 45608064081924212783191187)
        ·
          refine ⟨68412096122886319174786781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45608064081924212783191187 68412096122886319174786781)
          ·
            refine ⟨25654536046082369690545043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68412096122886319174786781 25654536046082369690545043)
            ·
              refine ⟨38481804069123554535817565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25654536046082369690545043 38481804069123554535817565)
              ·
                refine ⟨14430676525921332950931587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38481804069123554535817565 14430676525921332950931587)
                ·
                  refine ⟨21646014788881999426397381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14430676525921332950931587 21646014788881999426397381)
                  ·
                    refine ⟨4058627772915374892449509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21646014788881999426397381 4058627772915374892449509)
                    ·
                      refine ⟨760992707421632792334283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4058627772915374892449509 760992707421632792334283)
                      ·
                        rfl

theorem cell23_1482028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 4].length) (baseStart_1482028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482028 prefixEnd_1482028 := by exact prefixLift 1482028
  have htrace : WordTrace (prefixWord ++ tailWord_1482028) baseStart_1482028 baseEnd_1482028 := by
    simpa [prefixWord, tailWord_1482028, baseEnd_1482028] using wordTrace_append hprefix tailTrace_1482028
  have hstable : (prefixWord ++ tailWord_1482028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482028).length < 2 ^ (prefixWord ++ tailWord_1482028).sum := by decide
  have hdescent : baseEnd_1482028 < baseStart_1482028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482049 : List Nat := [1, 2, 5, 2, 1, 2, 1, 2, 1, 4, 2]
def baseStart_1482049 : Nat := 118140960795 + 1482049 * 2 ^ 59
def prefixEnd_1482049 : Nat := 4983230072969 + 3 ^ 40 * 1482049 * 2
def baseEnd_1482049 : Nat := 761003490515377210171687

theorem tailTrace_1482049 : CollatzResearch.WordTrace tailWord_1482049 prefixEnd_1482049 761003490515377210171687 := by
  unfold tailWord_1482049
  simp only [CollatzResearch.WordTrace]
  refine ⟨54054767807797061662889201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36036511871864707775259467 54054767807797061662889201)
  ·
    refine ⟨40541075855847796247166901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54054767807797061662889201 40541075855847796247166901)
    ·
      refine ⟨3800725861485730898171897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40541075855847796247166901 3800725861485730898171897)
      ·
        refine ⟨2850544396114298173628923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3800725861485730898171897 2850544396114298173628923)
        ·
          refine ⟨4275816594171447260443385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2850544396114298173628923 4275816594171447260443385)
          ·
            refine ⟨3206862445628585445332539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4275816594171447260443385 3206862445628585445332539)
            ·
              refine ⟨4810293668442878167998809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3206862445628585445332539 4810293668442878167998809)
              ·
                refine ⟨3607720251332158625999107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4810293668442878167998809 3607720251332158625999107)
                ·
                  refine ⟨5411580376998237938998661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3607720251332158625999107 5411580376998237938998661)
                  ·
                    refine ⟨1014671320687169613562249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5411580376998237938998661 1014671320687169613562249)
                    ·
                      refine ⟨761003490515377210171687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1014671320687169613562249 761003490515377210171687)
                      ·
                        rfl

theorem cell23_1482049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_1482049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482049 prefixEnd_1482049 := by exact prefixLift 1482049
  have htrace : WordTrace (prefixWord ++ tailWord_1482049) baseStart_1482049 baseEnd_1482049 := by
    simpa [prefixWord, tailWord_1482049, baseEnd_1482049] using wordTrace_append hprefix tailTrace_1482049
  have hstable : (prefixWord ++ tailWord_1482049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482049).length < 2 ^ (prefixWord ++ tailWord_1482049).sum := by decide
  have hdescent : baseEnd_1482049 < baseStart_1482049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482052 : List Nat := [2, 3, 4, 1, 1, 1, 2, 1, 2, 1, 5]
def baseStart_1482052 : Nat := 118140960795 + 1482052 * 2 ^ 59
def prefixEnd_1482052 : Nat := 4983230072969 + 3 ^ 40 * 1482052 * 2
def baseEnd_1482052 : Nat := 761005030957340698434173

theorem tailTrace_1482052 : CollatzResearch.WordTrace tailWord_1482052 prefixEnd_1482052 761005030957340698434173 := by
  unfold tailWord_1482052
  simp only [CollatzResearch.WordTrace]
  refine ⟨27027438613393096587624205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36036584817857462116832273 27027438613393096587624205)
  ·
    refine ⟨10135289480022411220359077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27027438613393096587624205 10135289480022411220359077)
    ·
      refine ⟨1900366777504202103817327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10135289480022411220359077 1900366777504202103817327)
      ·
        refine ⟨2850550166256303155725991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1900366777504202103817327 2850550166256303155725991)
        ·
          refine ⟨4275825249384454733588987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2850550166256303155725991 4275825249384454733588987)
          ·
            refine ⟨6413737874076682100383481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4275825249384454733588987 6413737874076682100383481)
            ·
              refine ⟨4810303405557511575287611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6413737874076682100383481 4810303405557511575287611)
              ·
                refine ⟨7215455108336267362931417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4810303405557511575287611 7215455108336267362931417)
                ·
                  refine ⟨5411591331252200522198563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7215455108336267362931417 5411591331252200522198563)
                  ·
                    refine ⟨8117386996878300783297845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5411591331252200522198563 8117386996878300783297845)
                    ·
                      refine ⟨761005030957340698434173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8117386996878300783297845 761005030957340698434173)
                      ·
                        rfl

theorem cell23_1482052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_1482052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482052 prefixEnd_1482052 := by exact prefixLift 1482052
  have htrace : WordTrace (prefixWord ++ tailWord_1482052) baseStart_1482052 baseEnd_1482052 := by
    simpa [prefixWord, tailWord_1482052, baseEnd_1482052] using wordTrace_append hprefix tailTrace_1482052
  have hstable : (prefixWord ++ tailWord_1482052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482052).length < 2 ^ (prefixWord ++ tailWord_1482052).sum := by decide
  have hdescent : baseEnd_1482052 < baseStart_1482052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482065 : List Nat := [1, 2, 2, 1, 4, 1, 2, 2, 2, 3, 3]
def baseStart_1482065 : Nat := 118140960795 + 1482065 * 2 ^ 59
def prefixEnd_1482065 : Nat := 4983230072969 + 3 ^ 40 * 1482065 * 2
def baseEnd_1482065 : Nat := 761011706205849147571613

theorem tailTrace_1482065 : CollatzResearch.WordTrace tailWord_1482065 prefixEnd_1482065 761011706205849147571613 := by
  unfold tailWord_1482065
  simp only [CollatzResearch.WordTrace]
  refine ⟨54055351375739096395471649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36036900917159397596981099 54055351375739096395471649)
  ·
    refine ⟨40541513531804322296603737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54055351375739096395471649 40541513531804322296603737)
    ·
      refine ⟨30406135148853241722452803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40541513531804322296603737 30406135148853241722452803)
      ·
        refine ⟨45609202723279862583679205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30406135148853241722452803 45609202723279862583679205)
        ·
          refine ⟨8551725510614974234439851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45609202723279862583679205 8551725510614974234439851)
          ·
            refine ⟨12827588265922461351659777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8551725510614974234439851 12827588265922461351659777)
            ·
              refine ⟨9620691199441846013744833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12827588265922461351659777 9620691199441846013744833)
              ·
                refine ⟨7215518399581384510308625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9620691199441846013744833 7215518399581384510308625)
                ·
                  refine ⟨5411638799686038382731469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7215518399581384510308625 5411638799686038382731469)
                  ·
                    refine ⟨2029364549882264393524301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5411638799686038382731469 2029364549882264393524301)
                    ·
                      refine ⟨761011706205849147571613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2029364549882264393524301 761011706205849147571613)
                      ·
                        rfl

theorem cell23_1482065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 3, 3].length) (baseStart_1482065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482065 prefixEnd_1482065 := by exact prefixLift 1482065
  have htrace : WordTrace (prefixWord ++ tailWord_1482065) baseStart_1482065 baseEnd_1482065 := by
    simpa [prefixWord, tailWord_1482065, baseEnd_1482065] using wordTrace_append hprefix tailTrace_1482065
  have hstable : (prefixWord ++ tailWord_1482065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482065).length < 2 ^ (prefixWord ++ tailWord_1482065).sum := by decide
  have hdescent : baseEnd_1482065 < baseStart_1482065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482082 : List Nat := [3, 3, 2, 1, 1, 1, 3, 1, 2, 3, 3]
def baseStart_1482082 : Nat := 118140960795 + 1482082 * 2 ^ 59
def prefixEnd_1482082 : Nat := 4983230072969 + 3 ^ 40 * 1482082 * 2
def baseEnd_1482082 : Nat := 761020435376975581059035

theorem tailTrace_1482082 : CollatzResearch.WordTrace tailWord_1482082 prefixEnd_1482082 761020435376975581059035 := by
  unfold tailWord_1482082
  simp only [CollatzResearch.WordTrace]
  refine ⟨13513992854169377074710125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36037314277785005532560333 13513992854169377074710125)
  ·
    refine ⟨5067747320313516403016297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13513992854169377074710125 5067747320313516403016297)
    ·
      refine ⟨3800810490235137302262223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5067747320313516403016297 3800810490235137302262223)
      ·
        refine ⟨5701215735352705953393335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3800810490235137302262223 5701215735352705953393335)
        ·
          refine ⟨8551823603029058930090003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5701215735352705953393335 8551823603029058930090003)
          ·
            refine ⟨12827735404543588395135005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8551823603029058930090003 12827735404543588395135005)
            ·
              refine ⟨4810400776703845648175627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12827735404543588395135005 4810400776703845648175627)
              ·
                refine ⟨7215601165055768472263441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4810400776703845648175627 7215601165055768472263441)
                ·
                  refine ⟨5411700873791826354197581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7215601165055768472263441 5411700873791826354197581)
                  ·
                    refine ⟨2029387827671934882824093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5411700873791826354197581 2029387827671934882824093)
                    ·
                      refine ⟨761020435376975581059035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2029387827671934882824093 761020435376975581059035)
                      ·
                        rfl

theorem cell23_1482082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_1482082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482082 prefixEnd_1482082 := by exact prefixLift 1482082
  have htrace : WordTrace (prefixWord ++ tailWord_1482082) baseStart_1482082 baseEnd_1482082 := by
    simpa [prefixWord, tailWord_1482082, baseEnd_1482082] using wordTrace_append hprefix tailTrace_1482082
  have hstable : (prefixWord ++ tailWord_1482082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482082).length < 2 ^ (prefixWord ++ tailWord_1482082).sum := by decide
  have hdescent : baseEnd_1482082 < baseStart_1482082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482196 : List Nat := [2, 4, 1, 2, 3, 2, 2, 1, 6]
def baseStart_1482196 : Nat := 118140960795 + 1482196 * 2 ^ 59
def prefixEnd_1482196 : Nat := 4983230072969 + 3 ^ 40 * 1482196 * 2
def baseEnd_1482196 : Nat := 84564330241287570559279

theorem tailTrace_1482196 : CollatzResearch.WordTrace tailWord_1482196 prefixEnd_1482196 84564330241287570559279 := by
  unfold tailWord_1482196
  simp only [CollatzResearch.WordTrace]
  refine ⟨27030064669132252884245221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36040086225509670512326961 27030064669132252884245221)
  ·
    refine ⟨5068137125462297415795979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27030064669132252884245221 5068137125462297415795979)
    ·
      refine ⟨7602205688193446123693969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5068137125462297415795979 7602205688193446123693969)
      ·
        refine ⟨5701654266145084592770477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7602205688193446123693969 5701654266145084592770477)
        ·
          refine ⟨2138120349804406722288929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5701654266145084592770477 2138120349804406722288929)
          ·
            refine ⟨1603590262353305041716697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2138120349804406722288929 1603590262353305041716697)
            ·
              refine ⟨1202692696764978781287523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1603590262353305041716697 1202692696764978781287523)
              ·
                refine ⟨1804039045147468171931285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1202692696764978781287523 1804039045147468171931285)
                ·
                  refine ⟨84564330241287570559279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1804039045147468171931285 84564330241287570559279)
                  ·
                    rfl

theorem cell23_1482196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_1482196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482196 prefixEnd_1482196 := by exact prefixLift 1482196
  have htrace : WordTrace (prefixWord ++ tailWord_1482196) baseStart_1482196 baseEnd_1482196 := by
    simpa [prefixWord, tailWord_1482196, baseEnd_1482196] using wordTrace_append hprefix tailTrace_1482196
  have hstable : (prefixWord ++ tailWord_1482196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482196).length < 2 ^ (prefixWord ++ tailWord_1482196).sum := by decide
  have hdescent : baseEnd_1482196 < baseStart_1482196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482209 : List Nat := [1, 2, 3, 1, 2, 5, 1, 2, 1, 5]
def baseStart_1482209 : Nat := 118140960795 + 1482209 * 2 ^ 59
def prefixEnd_1482209 : Nat := 4983230072969 + 3 ^ 40 * 1482209 * 2
def baseEnd_1482209 : Nat := 253695215806698861390317

theorem tailTrace_1482209 : CollatzResearch.WordTrace tailWord_1482209 prefixEnd_1482209 253695215806698861390317 := by
  unfold tailWord_1482209
  simp only [CollatzResearch.WordTrace]
  refine ⟨54060603487217408988713681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36040402324811605992475787 54060603487217408988713681)
  ·
    refine ⟨40545452615413056741535261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54060603487217408988713681 40545452615413056741535261)
    ·
      refine ⟨15204544730779896278075723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40545452615413056741535261 15204544730779896278075723)
      ·
        refine ⟨22806817096169844417113585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15204544730779896278075723 22806817096169844417113585)
        ·
          refine ⟨17105112822127383312835189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22806817096169844417113585 17105112822127383312835189)
          ·
            refine ⟨1603604327074442185578299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17105112822127383312835189 1603604327074442185578299)
            ·
              refine ⟨2405406490611663278367449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1603604327074442185578299 2405406490611663278367449)
              ·
                refine ⟨1804054867958747458775587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2405406490611663278367449 1804054867958747458775587)
                ·
                  refine ⟨2706082301938121188163381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1804054867958747458775587 2706082301938121188163381)
                  ·
                    refine ⟨253695215806698861390317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2706082301938121188163381 253695215806698861390317)
                    ·
                      rfl

theorem cell23_1482209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 2, 1, 5].length) (baseStart_1482209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482209 prefixEnd_1482209 := by exact prefixLift 1482209
  have htrace : WordTrace (prefixWord ++ tailWord_1482209) baseStart_1482209 baseEnd_1482209 := by
    simpa [prefixWord, tailWord_1482209, baseEnd_1482209] using wordTrace_append hprefix tailTrace_1482209
  have hstable : (prefixWord ++ tailWord_1482209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482209).length < 2 ^ (prefixWord ++ tailWord_1482209).sum := by decide
  have hdescent : baseEnd_1482209 < baseStart_1482209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482212 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 2, 6, 2]
def baseStart_1482212 : Nat := 118140960795 + 1482212 * 2 ^ 59
def prefixEnd_1482212 : Nat := 4983230072969 + 3 ^ 40 * 1482212 * 2
def baseEnd_1482212 : Nat := 761087187862060072433437

theorem tailTrace_1482212 : CollatzResearch.WordTrace tailWord_1482212 prefixEnd_1482212 761087187862060072433437 := by
  unfold tailWord_1482212
  simp only [CollatzResearch.WordTrace]
  refine ⟨27030356453103270250536445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36040475270804360334048593 27030356453103270250536445)
  ·
    refine ⟨10136383669913726343951167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27030356453103270250536445 10136383669913726343951167)
    ·
      refine ⟨15204575504870589515926751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10136383669913726343951167 15204575504870589515926751)
      ·
        refine ⟨22806863257305884273890127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15204575504870589515926751 22806863257305884273890127)
        ·
          refine ⟨34210294885958826410835191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22806863257305884273890127 34210294885958826410835191)
          ·
            refine ⟨51315442328938239616252787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34210294885958826410835191 51315442328938239616252787)
            ·
              refine ⟨76973163493407359424379181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51315442328938239616252787 76973163493407359424379181)
              ·
                refine ⟨28864936310027759784142193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76973163493407359424379181 28864936310027759784142193)
                ·
                  refine ⟨21648702232520819838106645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28864936310027759784142193 21648702232520819838106645)
                  ·
                    refine ⟨1014782917149413429911249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21648702232520819838106645 1014782917149413429911249)
                    ·
                      refine ⟨761087187862060072433437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1014782917149413429911249 761087187862060072433437)
                      ·
                        rfl

theorem cell23_1482212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 2, 6, 2].length) (baseStart_1482212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482212 prefixEnd_1482212 := by exact prefixLift 1482212
  have htrace : WordTrace (prefixWord ++ tailWord_1482212) baseStart_1482212 baseEnd_1482212 := by
    simpa [prefixWord, tailWord_1482212, baseEnd_1482212] using wordTrace_append hprefix tailTrace_1482212
  have hstable : (prefixWord ++ tailWord_1482212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482212).length < 2 ^ (prefixWord ++ tailWord_1482212).sum := by decide
  have hdescent : baseEnd_1482212 < baseStart_1482212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482222 : List Nat := [4, 1, 2, 1, 2, 1, 3, 2, 1, 6]
def baseStart_1482222 : Nat := 118140960795 + 1482222 * 2 ^ 59
def prefixEnd_1482222 : Nat := 4983230072969 + 3 ^ 40 * 1482222 * 2
def baseEnd_1482222 : Nat := 253697440889535011102797

theorem tailTrace_1482222 : CollatzResearch.WordTrace tailWord_1482222 prefixEnd_1482222 253697440889535011102797 := by
  unfold tailWord_1482222
  simp only [CollatzResearch.WordTrace]
  refine ⟨6757634704521289026117115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36040718424113541472624613 6757634704521289026117115)
  ·
    refine ⟨10136452056781933539175673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6757634704521289026117115 10136452056781933539175673)
    ·
      refine ⟨7602339042586450154381755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10136452056781933539175673 7602339042586450154381755)
      ·
        refine ⟨11403508563879675231572633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7602339042586450154381755 11403508563879675231572633)
        ·
          refine ⟨8552631422909756423679475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11403508563879675231572633 8552631422909756423679475)
          ·
            refine ⟨12828947134364634635519213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8552631422909756423679475 12828947134364634635519213)
            ·
              refine ⟨4810855175386737988319705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12828947134364634635519213 4810855175386737988319705)
              ·
                refine ⟨3608141381540053491239779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4810855175386737988319705 3608141381540053491239779)
                ·
                  refine ⟨5412212072310080236859669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3608141381540053491239779 5412212072310080236859669)
                  ·
                    refine ⟨253697440889535011102797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5412212072310080236859669 253697440889535011102797)
                    ·
                      rfl

theorem cell23_1482222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_1482222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482222 prefixEnd_1482222 := by exact prefixLift 1482222
  have htrace : WordTrace (prefixWord ++ tailWord_1482222) baseStart_1482222 baseEnd_1482222 := by
    simpa [prefixWord, tailWord_1482222, baseEnd_1482222] using wordTrace_append hprefix tailTrace_1482222
  have hstable : (prefixWord ++ tailWord_1482222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482222).length < 2 ^ (prefixWord ++ tailWord_1482222).sum := by decide
  have hdescent : baseEnd_1482222 < baseStart_1482222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482226 : List Nat := [3, 2, 1, 4, 1, 2, 3, 1, 1, 5]
def baseStart_1482226 : Nat := 118140960795 + 1482226 * 2 ^ 59
def prefixEnd_1482226 : Nat := 4983230072969 + 3 ^ 40 * 1482226 * 2
def baseEnd_1482226 : Nat := 253698125530407672552791

theorem tailTrace_1482226 : CollatzResearch.WordTrace tailWord_1482226 prefixEnd_1482226 253698125530407672552791 := by
  unfold tailWord_1482226
  simp only [CollatzResearch.WordTrace]
  refine ⟨13515305882038955223020633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36040815685437213928055021 13515305882038955223020633)
  ·
    refine ⟨10136479411529216417265475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13515305882038955223020633 10136479411529216417265475)
    ·
      refine ⟨15204719117293824625898213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10136479411529216417265475 15204719117293824625898213)
      ·
        refine ⟨2850884834492592117355915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15204719117293824625898213 2850884834492592117355915)
        ·
          refine ⟨4276327251738888176033873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2850884834492592117355915 4276327251738888176033873)
          ·
            refine ⟨3207245438804166132025405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4276327251738888176033873 3207245438804166132025405)
            ·
              refine ⟨1202717039551562299509527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3207245438804166132025405 1202717039551562299509527)
              ·
                refine ⟨1804075559327343449264291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1202717039551562299509527 1804075559327343449264291)
                ·
                  refine ⟨2706113338991015173896437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1804075559327343449264291 2706113338991015173896437)
                  ·
                    refine ⟨253698125530407672552791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2706113338991015173896437 253698125530407672552791)
                    ·
                      rfl

theorem cell23_1482226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 1, 1, 5].length) (baseStart_1482226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482226 prefixEnd_1482226 := by exact prefixLift 1482226
  have htrace : WordTrace (prefixWord ++ tailWord_1482226) baseStart_1482226 baseEnd_1482226 := by
    simpa [prefixWord, tailWord_1482226, baseEnd_1482226] using wordTrace_append hprefix tailTrace_1482226
  have hstable : (prefixWord ++ tailWord_1482226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482226).length < 2 ^ (prefixWord ++ tailWord_1482226).sum := by decide
  have hdescent : baseEnd_1482226 < baseStart_1482226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482232 : List Nat := [2, 1, 2, 1, 1, 5, 3, 1, 1, 1, 5]
def baseStart_1482232 : Nat := 118140960795 + 1482232 * 2 ^ 59
def prefixEnd_1482232 : Nat := 4983230072969 + 3 ^ 40 * 1482232 * 2
def baseEnd_1482232 : Nat := 761097457475149994183345

theorem tailTrace_1482232 : CollatzResearch.WordTrace tailWord_1482232 prefixEnd_1482232 761097457475149994183345 := by
  unfold tailWord_1482232
  simp only [CollatzResearch.WordTrace]
  refine ⟨27030721183067041958400475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36040961577422722611200633 27030721183067041958400475)
  ·
    refine ⟨40546081774600562937600713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27030721183067041958400475 40546081774600562937600713)
    ·
      refine ⟨30409561330950422203200535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40546081774600562937600713 30409561330950422203200535)
      ·
        refine ⟨45614341996425633304800803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30409561330950422203200535 45614341996425633304800803)
        ·
          refine ⟨68421512994638449957201205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45614341996425633304800803 68421512994638449957201205)
          ·
            refine ⟨6414516843247354683487613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68421512994638449957201205 6414516843247354683487613)
            ·
              refine ⟨2405443816217758006307855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6414516843247354683487613 2405443816217758006307855)
              ·
                refine ⟨3608165724326637009461783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2405443816217758006307855 3608165724326637009461783)
                ·
                  refine ⟨5412248586489955514192675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3608165724326637009461783 5412248586489955514192675)
                  ·
                    refine ⟨8118372879734933271289013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5412248586489955514192675 8118372879734933271289013)
                    ·
                      refine ⟨761097457475149994183345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8118372879734933271289013 761097457475149994183345)
                      ·
                        rfl

theorem cell23_1482232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 1, 1, 5].length) (baseStart_1482232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482232 prefixEnd_1482232 := by exact prefixLift 1482232
  have htrace : WordTrace (prefixWord ++ tailWord_1482232) baseStart_1482232 baseEnd_1482232 := by
    simpa [prefixWord, tailWord_1482232, baseEnd_1482232] using wordTrace_append hprefix tailTrace_1482232
  have hstable : (prefixWord ++ tailWord_1482232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482232).length < 2 ^ (prefixWord ++ tailWord_1482232).sum := by decide
  have hdescent : baseEnd_1482232 < baseStart_1482232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482280 : List Nat := [2, 1, 5, 2, 3, 1, 2, 1, 1, 1, 4]
def baseStart_1482280 : Nat := 118140960795 + 1482280 * 2 ^ 59
def prefixEnd_1482280 : Nat := 4983230072969 + 3 ^ 40 * 1482280 * 2
def baseEnd_1482280 : Nat := 761122104546565806383125

theorem tailTrace_1482280 : CollatzResearch.WordTrace tailWord_1482280 prefixEnd_1482280 761122104546565806383125 := by
  unfold tailWord_1482280
  simp only [CollatzResearch.WordTrace]
  refine ⟨27031596534980094057274147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36042128713306792076365529 27031596534980094057274147)
  ·
    refine ⟨40547394802470141085911221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27031596534980094057274147 40547394802470141085911221)
    ·
      refine ⟨3801318262731575726804177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40547394802470141085911221 3801318262731575726804177)
      ·
        refine ⟨2850988697048681795103133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3801318262731575726804177 2850988697048681795103133)
        ·
          refine ⟨1069120761393255673163675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2850988697048681795103133 1069120761393255673163675)
          ·
            refine ⟨1603681142089883509745513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1069120761393255673163675 1603681142089883509745513)
            ·
              refine ⟨1202760856567412632309135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1603681142089883509745513 1202760856567412632309135)
              ·
                refine ⟨1804141284851118948463703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1202760856567412632309135 1804141284851118948463703)
                ·
                  refine ⟨2706211927276678422695555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1804141284851118948463703 2706211927276678422695555)
                  ·
                    refine ⟨4059317890915017634043333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2706211927276678422695555 4059317890915017634043333)
                    ·
                      refine ⟨761122104546565806383125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4059317890915017634043333 761122104546565806383125)
                      ·
                        rfl

theorem cell23_1482280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_1482280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482280 prefixEnd_1482280 := by exact prefixLift 1482280
  have htrace : WordTrace (prefixWord ++ tailWord_1482280) baseStart_1482280 baseEnd_1482280 := by
    simpa [prefixWord, tailWord_1482280, baseEnd_1482280] using wordTrace_append hprefix tailTrace_1482280
  have hstable : (prefixWord ++ tailWord_1482280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482280).length < 2 ^ (prefixWord ++ tailWord_1482280).sum := by decide
  have hdescent : baseEnd_1482280 < baseStart_1482280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482296 : List Nat := [2, 1, 2, 1, 4, 2, 3, 2, 2, 1, 3]
def baseStart_1482296 : Nat := 118140960795 + 1482296 * 2 ^ 59
def prefixEnd_1482296 : Nat := 4983230072969 + 3 ^ 40 * 1482296 * 2
def baseEnd_1482296 : Nat := 761130320237037743783051

theorem tailTrace_1482296 : CollatzResearch.WordTrace tailWord_1482296 prefixEnd_1482296 761130320237037743783051 := by
  unfold tailWord_1482296
  simp only [CollatzResearch.WordTrace]
  refine ⟨27031888318951111423565371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36042517758601481898087161 27031888318951111423565371)
  ·
    refine ⟨40547832478426667135348057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27031888318951111423565371 40547832478426667135348057)
    ·
      refine ⟨30410874358820000351511043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40547832478426667135348057 30410874358820000351511043)
      ·
        refine ⟨45616311538230000527266565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30410874358820000351511043 45616311538230000527266565)
        ·
          refine ⟨8553058413418125098862481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45616311538230000527266565 8553058413418125098862481)
          ·
            refine ⟨6414793810063593824146861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8553058413418125098862481 6414793810063593824146861)
            ·
              refine ⟨2405547678773847684055073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6414793810063593824146861 2405547678773847684055073)
              ·
                refine ⟨1804160759080385763041305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2405547678773847684055073 1804160759080385763041305)
                ·
                  refine ⟨1353120569310289322280979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1804160759080385763041305 1353120569310289322280979)
                  ·
                    refine ⟨2029680853965433983421469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1353120569310289322280979 2029680853965433983421469)
                    ·
                      refine ⟨761130320237037743783051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2029680853965433983421469 761130320237037743783051)
                      ·
                        rfl

theorem cell23_1482296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 2, 2, 1, 3].length) (baseStart_1482296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482296 prefixEnd_1482296 := by exact prefixLift 1482296
  have htrace : WordTrace (prefixWord ++ tailWord_1482296) baseStart_1482296 baseEnd_1482296 := by
    simpa [prefixWord, tailWord_1482296, baseEnd_1482296] using wordTrace_append hprefix tailTrace_1482296
  have hstable : (prefixWord ++ tailWord_1482296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482296).length < 2 ^ (prefixWord ++ tailWord_1482296).sum := by decide
  have hdescent : baseEnd_1482296 < baseStart_1482296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482310 : List Nat := [6, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4]
def baseStart_1482310 : Nat := 118140960795 + 1482310 * 2 ^ 59
def prefixEnd_1482310 : Nat := 4983230072969 + 3 ^ 40 * 1482310 * 2
def baseEnd_1482310 : Nat := 761137508966200689007987

theorem tailTrace_1482310 : CollatzResearch.WordTrace tailWord_1482310 prefixEnd_1482310 761137508966200689007987 := by
  unfold tailWord_1482310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1689508976870359476191887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 36042858173234335492093589 1689508976870359476191887)
  ·
    refine ⟨2534263465305539214287831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1689508976870359476191887 2534263465305539214287831)
    ·
      refine ⟨3801395197958308821431747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2534263465305539214287831 3801395197958308821431747)
      ·
        refine ⟨5702092796937463232147621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3801395197958308821431747 5702092796937463232147621)
        ·
          refine ⟨1069142399425774356027679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5702092796937463232147621 1069142399425774356027679)
          ·
            refine ⟨1603713599138661534041519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1069142399425774356027679 1603713599138661534041519)
            ·
              refine ⟨2405570398707992301062279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1603713599138661534041519 2405570398707992301062279)
              ·
                refine ⟨3608355598061988451593419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2405570398707992301062279 3608355598061988451593419)
                ·
                  refine ⟨5412533397092982677390129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3608355598061988451593419 5412533397092982677390129)
                  ·
                    refine ⟨4059400047819737008042597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5412533397092982677390129 4059400047819737008042597)
                    ·
                      refine ⟨761137508966200689007987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4059400047819737008042597 761137508966200689007987)
                      ·
                        rfl

theorem cell23_1482310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_1482310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482310 prefixEnd_1482310 := by exact prefixLift 1482310
  have htrace : WordTrace (prefixWord ++ tailWord_1482310) baseStart_1482310 baseEnd_1482310 := by
    simpa [prefixWord, tailWord_1482310, baseEnd_1482310] using wordTrace_append hprefix tailTrace_1482310
  have hstable : (prefixWord ++ tailWord_1482310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482310).length < 2 ^ (prefixWord ++ tailWord_1482310).sum := by decide
  have hdescent : baseEnd_1482310 < baseStart_1482310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482419 : List Nat := [1, 1, 1, 2, 3, 3, 2, 3, 3, 4]
def baseStart_1482419 : Nat := 118140960795 + 1482419 * 2 ^ 59
def prefixEnd_1482419 : Nat := 4983230072969 + 3 ^ 40 * 1482419 * 2
def baseEnd_1482419 : Nat := 253731159452513587514995

theorem tailTrace_1482419 : CollatzResearch.WordTrace tailWord_1482419 prefixEnd_1482419 253731159452513587514995 := by
  unfold tailWord_1482419
  simp only [CollatzResearch.WordTrace]
  refine ⟨54068262816456614853858311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36045508544304409902572207 54068262816456614853858311)
  ·
    refine ⟨81102394224684922280787467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54068262816456614853858311 81102394224684922280787467)
    ·
      refine ⟨121653591337027383421181201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81102394224684922280787467 121653591337027383421181201)
      ·
        refine ⟨91240193502770537565885901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121653591337027383421181201 91240193502770537565885901)
        ·
          refine ⟨34215072563538951587207213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91240193502770537565885901 34215072563538951587207213)
          ·
            refine ⟨12830652211327106845202705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34215072563538951587207213 12830652211327106845202705)
            ·
              refine ⟨9622989158495330133902029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12830652211327106845202705 9622989158495330133902029)
              ·
                refine ⟨3608620934435748800213261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9622989158495330133902029 3608620934435748800213261)
                ·
                  refine ⟨1353232850413405800079973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3608620934435748800213261 1353232850413405800079973)
                  ·
                    refine ⟨253731159452513587514995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1353232850413405800079973 253731159452513587514995)
                    ·
                      rfl

theorem cell23_1482419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 3, 4].length) (baseStart_1482419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482419 prefixEnd_1482419 := by exact prefixLift 1482419
  have htrace : WordTrace (prefixWord ++ tailWord_1482419) baseStart_1482419 baseEnd_1482419 := by
    simpa [prefixWord, tailWord_1482419, baseEnd_1482419] using wordTrace_append hprefix tailTrace_1482419
  have hstable : (prefixWord ++ tailWord_1482419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482419).length < 2 ^ (prefixWord ++ tailWord_1482419).sum := by decide
  have hdescent : baseEnd_1482419 < baseStart_1482419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482426 : List Nat := [3, 1, 1, 1, 2, 5, 1, 1, 2, 4, 2]
def baseStart_1482426 : Nat := 118140960795 + 1482426 * 2 ^ 59
def prefixEnd_1482426 : Nat := 4983230072969 + 3 ^ 40 * 1482426 * 2
def baseEnd_1482426 : Nat := 761197072722122235157453

theorem tailTrace_1482426 : CollatzResearch.WordTrace tailWord_1482426 prefixEnd_1482426 761197072722122235157453 := by
  unfold tailWord_1482426
  simp only [CollatzResearch.WordTrace]
  refine ⟨13517129531857813762340783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36045678751620836699575421 13517129531857813762340783)
  ·
    refine ⟨20275694297786720643511175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13517129531857813762340783 20275694297786720643511175)
    ·
      refine ⟨30413541446680080965266763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20275694297786720643511175 30413541446680080965266763)
      ·
        refine ⟨45620312170020121447900145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30413541446680080965266763 45620312170020121447900145)
        ·
          refine ⟨34215234127515091085925109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45620312170020121447900145 34215234127515091085925109)
          ·
            refine ⟨3207678199454539789305479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34215234127515091085925109 3207678199454539789305479)
            ·
              refine ⟨4811517299181809683958219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3207678199454539789305479 4811517299181809683958219)
              ·
                refine ⟨7217275948772714525937329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4811517299181809683958219 7217275948772714525937329)
                ·
                  refine ⟨5412956961579535894452997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7217275948772714525937329 5412956961579535894452997)
                  ·
                    refine ⟨1014929430296162980209937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5412956961579535894452997 1014929430296162980209937)
                    ·
                      refine ⟨761197072722122235157453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1014929430296162980209937 761197072722122235157453)
                      ·
                        rfl

theorem cell23_1482426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 2, 4, 2].length) (baseStart_1482426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482426 prefixEnd_1482426 := by exact prefixLift 1482426
  have htrace : WordTrace (prefixWord ++ tailWord_1482426) baseStart_1482426 baseEnd_1482426 := by
    simpa [prefixWord, tailWord_1482426, baseEnd_1482426] using wordTrace_append hprefix tailTrace_1482426
  have hstable : (prefixWord ++ tailWord_1482426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482426).length < 2 ^ (prefixWord ++ tailWord_1482426).sum := by decide
  have hdescent : baseEnd_1482426 < baseStart_1482426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482429 : List Nat := [1, 4, 1, 2, 1, 2, 2, 2, 1, 4, 3]
def baseStart_1482429 : Nat := 118140960795 + 1482429 * 2 ^ 59
def prefixEnd_1482429 : Nat := 4983230072969 + 3 ^ 40 * 1482429 * 2
def baseEnd_1482429 : Nat := 761198613164085723419939

theorem tailTrace_1482429 : CollatzResearch.WordTrace tailWord_1482429 prefixEnd_1482429 761198613164085723419939 := by
  unfold tailWord_1482429
  simp only [CollatzResearch.WordTrace]
  refine ⟨54068627546420386561722341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36045751697613591041148227 54068627546420386561722341)
  ·
    refine ⟨10137867664953822480322939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54068627546420386561722341 10137867664953822480322939)
    ·
      refine ⟨15206801497430733720484409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10137867664953822480322939 15206801497430733720484409)
      ·
        refine ⟨11405101123073050290363307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15206801497430733720484409 11405101123073050290363307)
        ·
          refine ⟨17107651684609575435544961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11405101123073050290363307 17107651684609575435544961)
          ·
            refine ⟨12830738763457181576658721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17107651684609575435544961 12830738763457181576658721)
            ·
              refine ⟨9623054072592886182494041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12830738763457181576658721 9623054072592886182494041)
              ·
                refine ⟨7217290554444664636870531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9623054072592886182494041 7217290554444664636870531)
                ·
                  refine ⟨10825935831666996955305797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7217290554444664636870531 10825935831666996955305797)
                  ·
                    refine ⟨2029862968437561929119837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10825935831666996955305797 2029862968437561929119837)
                    ·
                      refine ⟨761198613164085723419939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2029862968437561929119837 761198613164085723419939)
                      ·
                        rfl

theorem cell23_1482429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_1482429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482429 prefixEnd_1482429 := by exact prefixLift 1482429
  have htrace : WordTrace (prefixWord ++ tailWord_1482429) baseStart_1482429 baseEnd_1482429 := by
    simpa [prefixWord, tailWord_1482429, baseEnd_1482429] using wordTrace_append hprefix tailTrace_1482429
  have hstable : (prefixWord ++ tailWord_1482429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482429).length < 2 ^ (prefixWord ++ tailWord_1482429).sum := by decide
  have hdescent : baseEnd_1482429 < baseStart_1482429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482436 : List Nat := [2, 3, 3, 1, 1, 1, 3, 2, 3, 4]
def baseStart_1482436 : Nat := 118140960795 + 1482436 * 2 ^ 59
def prefixEnd_1482436 : Nat := 4983230072969 + 3 ^ 40 * 1482436 * 2
def baseEnd_1482436 : Nat := 253734069176222398677469

theorem tailTrace_1482436 : CollatzResearch.WordTrace tailWord_1482436 prefixEnd_1482436 253734069176222398677469 := by
  unfold tailWord_1482436
  simp only [CollatzResearch.WordTrace]
  refine ⟨27034441428697513378613581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36045921904930017838151441 27034441428697513378613581)
  ·
    refine ⟨10137915535761567516980093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27034441428697513378613581 10137915535761567516980093)
    ·
      refine ⟨3801718325910587818867535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10137915535761567516980093 3801718325910587818867535)
      ·
        refine ⟨5702577488865881728301303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3801718325910587818867535 5702577488865881728301303)
        ·
          refine ⟨8553866233298822592451955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5702577488865881728301303 8553866233298822592451955)
          ·
            refine ⟨12830799349948233888677933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8553866233298822592451955 12830799349948233888677933)
            ·
              refine ⟨4811549756230587708254225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12830799349948233888677933 4811549756230587708254225)
              ·
                refine ⟨3608662317172940781190669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4811549756230587708254225 3608662317172940781190669)
                ·
                  refine ⟨1353248368939852792946501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3608662317172940781190669 1353248368939852792946501)
                  ·
                    refine ⟨253734069176222398677469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1353248368939852792946501 253734069176222398677469)
                    ·
                      rfl

theorem cell23_1482436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_1482436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482436 prefixEnd_1482436 := by exact prefixLift 1482436
  have htrace : WordTrace (prefixWord ++ tailWord_1482436) baseStart_1482436 baseEnd_1482436 := by
    simpa [prefixWord, tailWord_1482436, baseEnd_1482436] using wordTrace_append hprefix tailTrace_1482436
  have hstable : (prefixWord ++ tailWord_1482436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482436).length < 2 ^ (prefixWord ++ tailWord_1482436).sum := by decide
  have hdescent : baseEnd_1482436 < baseStart_1482436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482476 : List Nat := [2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 3]
def baseStart_1482476 : Nat := 118140960795 + 1482476 * 2 ^ 59
def prefixEnd_1482476 : Nat := 4983230072969 + 3 ^ 40 * 1482476 * 2
def baseEnd_1482476 : Nat := 761222746754847039532223

theorem tailTrace_1482476 : CollatzResearch.WordTrace tailWord_1482476 prefixEnd_1482476 761222746754847039532223 := by
  unfold tailWord_1482476
  simp only [CollatzResearch.WordTrace]
  refine ⟨27035170888625056794341641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36046894518166742392455521 27035170888625056794341641)
  ·
    refine ⟨20276378166468792595756231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27035170888625056794341641 20276378166468792595756231)
    ·
      refine ⟨30414567249703188893634347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20276378166468792595756231 30414567249703188893634347)
      ·
        refine ⟨45621850874554783340451521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30414567249703188893634347 45621850874554783340451521)
        ·
          refine ⟨34216388155916087505338641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45621850874554783340451521 34216388155916087505338641)
          ·
            refine ⟨25662291116937065629003981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34216388155916087505338641 25662291116937065629003981)
            ·
              refine ⟨9623359168851399610876493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25662291116937065629003981 9623359168851399610876493)
              ·
                refine ⟨3608759688319274854078685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9623359168851399610876493 3608759688319274854078685)
                ·
                  refine ⟨1353284883119728070279507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3608759688319274854078685 1353284883119728070279507)
                  ·
                    refine ⟨2029927324679592105419261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1353284883119728070279507 2029927324679592105419261)
                    ·
                      refine ⟨761222746754847039532223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2029927324679592105419261 761222746754847039532223)
                      ·
                        rfl

theorem cell23_1482476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 3].length) (baseStart_1482476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482476 prefixEnd_1482476 := by exact prefixLift 1482476
  have htrace : WordTrace (prefixWord ++ tailWord_1482476) baseStart_1482476 baseEnd_1482476 := by
    simpa [prefixWord, tailWord_1482476, baseEnd_1482476] using wordTrace_append hprefix tailTrace_1482476
  have hstable : (prefixWord ++ tailWord_1482476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482476).length < 2 ^ (prefixWord ++ tailWord_1482476).sum := by decide
  have hdescent : baseEnd_1482476 < baseStart_1482476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482499 : List Nat := [1, 1, 1, 3, 2, 2, 2, 3, 3, 1, 4]
def baseStart_1482499 : Nat := 118140960795 + 1482499 * 2 ^ 59
def prefixEnd_1482499 : Nat := 4983230072969 + 3 ^ 40 * 1482499 * 2
def baseEnd_1482499 : Nat := 761234556809900449544617

theorem tailTrace_1482499 : CollatzResearch.WordTrace tailWord_1482499 prefixEnd_1482499 761234556809900449544617 := by
  unfold tailWord_1482499
  simp only [CollatzResearch.WordTrace]
  refine ⟨54071180656166788516770551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36047453770777859011180367 54071180656166788516770551)
  ·
    refine ⟨81106770984250182775155827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54071180656166788516770551 81106770984250182775155827)
    ·
      refine ⟨121660156476375274162733741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81106770984250182775155827 121660156476375274162733741)
      ·
        refine ⟨45622558678640727811025153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121660156476375274162733741 45622558678640727811025153)
        ·
          refine ⟨34216919008980545858268865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45622558678640727811025153 34216919008980545858268865)
          ·
            refine ⟨25662689256735409393701649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34216919008980545858268865 25662689256735409393701649)
            ·
              refine ⟨19247016942551557045276237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25662689256735409393701649 19247016942551557045276237)
              ·
                refine ⟨7217631353456833891978589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19247016942551557045276237 7217631353456833891978589)
                ·
                  refine ⟨2706611757546312709491971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7217631353456833891978589 2706611757546312709491971)
                  ·
                    refine ⟨4059917636319469064237957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2706611757546312709491971 4059917636319469064237957)
                    ·
                      refine ⟨761234556809900449544617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4059917636319469064237957 761234556809900449544617)
                      ·
                        rfl

theorem cell23_1482499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 3, 1, 4].length) (baseStart_1482499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482499 prefixEnd_1482499 := by exact prefixLift 1482499
  have htrace : WordTrace (prefixWord ++ tailWord_1482499) baseStart_1482499 baseEnd_1482499 := by
    simpa [prefixWord, tailWord_1482499, baseEnd_1482499] using wordTrace_append hprefix tailTrace_1482499
  have hstable : (prefixWord ++ tailWord_1482499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482499).length < 2 ^ (prefixWord ++ tailWord_1482499).sum := by decide
  have hdescent : baseEnd_1482499 < baseStart_1482499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482510 : List Nat := [4, 1, 1, 2, 1, 1, 5, 3, 1, 1, 3]
def baseStart_1482510 : Nat := 118140960795 + 1482510 * 2 ^ 59
def prefixEnd_1482510 : Nat := 4983230072969 + 3 ^ 40 * 1482510 * 2
def baseEnd_1482510 : Nat := 761240205097099906507067

theorem tailTrace_1482510 : CollatzResearch.WordTrace tailWord_1482510 prefixEnd_1482510 761240205097099906507067 := by
  unfold tailWord_1482510
  simp only [CollatzResearch.WordTrace]
  refine ⟨6758947732390867174427623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36047721239417958263613989 6758947732390867174427623)
  ·
    refine ⟨10138421598586300761641435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6758947732390867174427623 10138421598586300761641435)
    ·
      refine ⟨15207632397879451142462153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10138421598586300761641435 15207632397879451142462153)
      ·
        refine ⟨11405724298409588356846615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15207632397879451142462153 11405724298409588356846615)
        ·
          refine ⟨17108586447614382535269923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11405724298409588356846615 17108586447614382535269923)
          ·
            refine ⟨25662879671421573802904885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17108586447614382535269923 25662879671421573802904885)
            ·
              refine ⟨2405894969195772544022333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25662879671421573802904885 2405894969195772544022333)
              ·
                refine ⟨902210613448414704008375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2405894969195772544022333 902210613448414704008375)
                ·
                  refine ⟨1353315920172622056012563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 902210613448414704008375 1353315920172622056012563)
                  ·
                    refine ⟨2029973880258933084018845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1353315920172622056012563 2029973880258933084018845)
                    ·
                      refine ⟨761240205097099906507067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2029973880258933084018845 761240205097099906507067)
                      ·
                        rfl

theorem cell23_1482510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 3, 1, 1, 3].length) (baseStart_1482510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482510 prefixEnd_1482510 := by exact prefixLift 1482510
  have htrace : WordTrace (prefixWord ++ tailWord_1482510) baseStart_1482510 baseEnd_1482510 := by
    simpa [prefixWord, tailWord_1482510, baseEnd_1482510] using wordTrace_append hprefix tailTrace_1482510
  have hstable : (prefixWord ++ tailWord_1482510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482510).length < 2 ^ (prefixWord ++ tailWord_1482510).sum := by decide
  have hdescent : baseEnd_1482510 < baseStart_1482510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482529 : List Nat := [1, 2, 3, 2, 1, 3, 1, 2, 1, 1, 6]
def baseStart_1482529 : Nat := 118140960795 + 1482529 * 2 ^ 59
def prefixEnd_1482529 : Nat := 4983230072969 + 3 ^ 40 * 1482529 * 2
def baseEnd_1482529 : Nat := 761249961229535332169479

theorem tailTrace_1482529 : CollatzResearch.WordTrace tailWord_1482529 prefixEnd_1482529 761249961229535332169479 := by
  unfold tailWord_1482529
  simp only [CollatzResearch.WordTrace]
  refine ⟨54072274846058103640362641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36048183230705402426908427 54072274846058103640362641)
  ·
    refine ⟨40554206134543577730271981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54072274846058103640362641 40554206134543577730271981)
    ·
      refine ⟨15207827300453841648851993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40554206134543577730271981 15207827300453841648851993)
      ·
        refine ⟨11405870475340381236638995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15207827300453841648851993 11405870475340381236638995)
        ·
          refine ⟨17108805713010571854958493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11405870475340381236638995 17108805713010571854958493)
          ·
            refine ⟨6415802142378964445609435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17108805713010571854958493 6415802142378964445609435)
            ·
              refine ⟨9623703213568446668414153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6415802142378964445609435 9623703213568446668414153)
              ·
                refine ⟨7217777410176335001310615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9623703213568446668414153 7217777410176335001310615)
                ·
                  refine ⟨10826666115264502501965923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7217777410176335001310615 10826666115264502501965923)
                  ·
                    refine ⟨16239999172896753752948885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10826666115264502501965923 16239999172896753752948885)
                    ·
                      refine ⟨761249961229535332169479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16239999172896753752948885 761249961229535332169479)
                      ·
                        rfl

theorem cell23_1482529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_1482529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482529 prefixEnd_1482529 := by exact prefixLift 1482529
  have htrace : WordTrace (prefixWord ++ tailWord_1482529) baseStart_1482529 baseEnd_1482529 := by
    simpa [prefixWord, tailWord_1482529, baseEnd_1482529] using wordTrace_append hprefix tailTrace_1482529
  have hstable : (prefixWord ++ tailWord_1482529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482529).length < 2 ^ (prefixWord ++ tailWord_1482529).sum := by decide
  have hdescent : baseEnd_1482529 < baseStart_1482529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482536 : List Nat := [2, 1, 5, 1, 1, 2, 2, 2, 1, 1, 5]
def baseStart_1482536 : Nat := 118140960795 + 1482536 * 2 ^ 59
def prefixEnd_1482536 : Nat := 4983230072969 + 3 ^ 40 * 1482536 * 2
def baseEnd_1482536 : Nat := 761253555594116804781947

theorem tailTrace_1482536 : CollatzResearch.WordTrace tailWord_1482536 prefixEnd_1482536 761253555594116804781947 := by
  unfold tailWord_1482536
  simp only [CollatzResearch.WordTrace]
  refine ⟨27036265078516371917933731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36048353438021829223911641 27036265078516371917933731)
  ·
    refine ⟨40554397617774557876900597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27036265078516371917933731 40554397617774557876900597)
    ·
      refine ⟨3801974776666364800959431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40554397617774557876900597 3801974776666364800959431)
      ·
        refine ⟨5702962164999547201439147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3801974776666364800959431 5702962164999547201439147)
        ·
          refine ⟨8554443247499320802158721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5702962164999547201439147 8554443247499320802158721)
          ·
            refine ⟨6415832435624490601619041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8554443247499320802158721 6415832435624490601619041)
            ·
              refine ⟨4811874326718367951214281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6415832435624490601619041 4811874326718367951214281)
              ·
                refine ⟨3608905745038775963410711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4811874326718367951214281 3608905745038775963410711)
                ·
                  refine ⟨5413358617558163945116067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3608905745038775963410711 5413358617558163945116067)
                  ·
                    refine ⟨8120037926337245917674101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5413358617558163945116067 8120037926337245917674101)
                    ·
                      refine ⟨761253555594116804781947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8120037926337245917674101 761253555594116804781947)
                      ·
                        rfl

theorem cell23_1482536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_1482536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482536 prefixEnd_1482536 := by exact prefixLift 1482536
  have htrace : WordTrace (prefixWord ++ tailWord_1482536) baseStart_1482536 baseEnd_1482536 := by
    simpa [prefixWord, tailWord_1482536, baseEnd_1482536] using wordTrace_append hprefix tailTrace_1482536
  have hstable : (prefixWord ++ tailWord_1482536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482536).length < 2 ^ (prefixWord ++ tailWord_1482536).sum := by decide
  have hdescent : baseEnd_1482536 < baseStart_1482536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482550 : List Nat := [5, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4]
def baseStart_1482550 : Nat := 118140960795 + 1482550 * 2 ^ 59
def prefixEnd_1482550 : Nat := 4983230072969 + 3 ^ 40 * 1482550 * 2
def baseEnd_1482550 : Nat := 761260744323279750006883

theorem tailTrace_1482550 : CollatzResearch.WordTrace tailWord_1482550 prefixEnd_1482550 761260744323279750006883 := by
  unfold tailWord_1482550
  simp only [CollatzResearch.WordTrace]
  refine ⟨3379565048686376514179819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36048693852654682817918069 3379565048686376514179819)
  ·
    refine ⟨5069347573029564771269729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3379565048686376514179819 5069347573029564771269729)
    ·
      refine ⟨3802010679772173578452297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5069347573029564771269729 3802010679772173578452297)
      ·
        refine ⟨2851508009829130183839223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3802010679772173578452297 2851508009829130183839223)
        ·
          refine ⟨4277262014743695275758835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2851508009829130183839223 4277262014743695275758835)
          ·
            refine ⟨6415893022115542913638253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4277262014743695275758835 6415893022115542913638253)
            ·
              refine ⟨2405959883293328592614345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6415893022115542913638253 2405959883293328592614345)
              ·
                refine ⟨1804469912469996444460759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2405959883293328592614345 1804469912469996444460759)
                ·
                  refine ⟨2706704868704994666691139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1804469912469996444460759 2706704868704994666691139)
                  ·
                    refine ⟨4060057303057492000036709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2706704868704994666691139 4060057303057492000036709)
                    ·
                      refine ⟨761260744323279750006883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4060057303057492000036709 761260744323279750006883)
                      ·
                        rfl

theorem cell23_1482550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_1482550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482550 prefixEnd_1482550 := by exact prefixLift 1482550
  have htrace : WordTrace (prefixWord ++ tailWord_1482550) baseStart_1482550 baseEnd_1482550 := by
    simpa [prefixWord, tailWord_1482550, baseEnd_1482550] using wordTrace_append hprefix tailTrace_1482550
  have hstable : (prefixWord ++ tailWord_1482550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482550).length < 2 ^ (prefixWord ++ tailWord_1482550).sum := by decide
  have hdescent : baseEnd_1482550 < baseStart_1482550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482619 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 3, 4, 4]
def baseStart_1482619 : Nat := 118140960795 + 1482619 * 2 ^ 59
def prefixEnd_1482619 : Nat := 4983230072969 + 3 ^ 40 * 1482619 * 2
def baseEnd_1482619 : Nat := 761296174488439980044065

theorem tailTrace_1482619 : CollatzResearch.WordTrace tailWord_1482619 prefixEnd_1482619 761296174488439980044065 := by
  unfold tailWord_1482619
  simp only [CollatzResearch.WordTrace]
  refine ⟨54075557415732049011138911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36050371610488032674092607 54075557415732049011138911)
  ·
    refine ⟨81113336123598073516708367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54075557415732049011138911 81113336123598073516708367)
    ·
      refine ⟨121670004185397110275062551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81113336123598073516708367 121670004185397110275062551)
      ·
        refine ⟨182505006278095665412593827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121670004185397110275062551 182505006278095665412593827)
        ·
          refine ⟨273757509417143498118890741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182505006278095665412593827 273757509417143498118890741)
          ·
            refine ⟨25664766507857202948646007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 273757509417143498118890741 25664766507857202948646007)
            ·
              refine ⟨38497149761785804422969011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25664766507857202948646007 38497149761785804422969011)
              ·
                refine ⟨57745724642678706634453517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38497149761785804422969011 57745724642678706634453517)
                ·
                  refine ⟨21654646741004514987920069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57745724642678706634453517 21654646741004514987920069)
                  ·
                    refine ⟨4060246263938346560235013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21654646741004514987920069 4060246263938346560235013)
                    ·
                      refine ⟨761296174488439980044065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4060246263938346560235013 761296174488439980044065)
                      ·
                        rfl

theorem cell23_1482619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 4, 4].length) (baseStart_1482619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482619 prefixEnd_1482619 := by exact prefixLift 1482619
  have htrace : WordTrace (prefixWord ++ tailWord_1482619) baseStart_1482619 baseEnd_1482619 := by
    simpa [prefixWord, tailWord_1482619, baseEnd_1482619] using wordTrace_append hprefix tailTrace_1482619
  have hstable : (prefixWord ++ tailWord_1482619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482619).length < 2 ^ (prefixWord ++ tailWord_1482619).sum := by decide
  have hdescent : baseEnd_1482619 < baseStart_1482619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482623 : List Nat := [1, 1, 2, 2, 1, 1, 3, 4, 4, 2, 2]
def baseStart_1482623 : Nat := 118140960795 + 1482623 * 2 ^ 59
def prefixEnd_1482623 : Nat := 4983230072969 + 3 ^ 40 * 1482623 * 2
def baseEnd_1482623 : Nat := 761298228411057964394047

theorem tailTrace_1482623 : CollatzResearch.WordTrace tailWord_1482623 prefixEnd_1482623 761298228411057964394047 := by
  unfold tailWord_1482623
  simp only [CollatzResearch.WordTrace]
  refine ⟨54075703307717557694284523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36050468871811705129523015 54075703307717557694284523)
  ·
    refine ⟨81113554961576336541426785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54075703307717557694284523 81113554961576336541426785)
    ·
      refine ⟨60835166221182252406070089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81113554961576336541426785 60835166221182252406070089)
      ·
        refine ⟨45626374665886689304552567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60835166221182252406070089 45626374665886689304552567)
        ·
          refine ⟨68439561998830033956828851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45626374665886689304552567 68439561998830033956828851)
          ·
            refine ⟨102659342998245050935243277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68439561998830033956828851 102659342998245050935243277)
            ·
              refine ⟨38497253624341894100716229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102659342998245050935243277 38497253624341894100716229)
              ·
                refine ⟨7218235054564105143884293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38497253624341894100716229 7218235054564105143884293)
                ·
                  refine ⟨1353419072730769714478305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7218235054564105143884293 1353419072730769714478305)
                  ·
                    refine ⟨1015064304548077285858729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1353419072730769714478305 1015064304548077285858729)
                    ·
                      refine ⟨761298228411057964394047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1015064304548077285858729 761298228411057964394047)
                      ·
                        rfl

theorem cell23_1482623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 4, 2, 2].length) (baseStart_1482623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482623 prefixEnd_1482623 := by exact prefixLift 1482623
  have htrace : WordTrace (prefixWord ++ tailWord_1482623) baseStart_1482623 baseEnd_1482623 := by
    simpa [prefixWord, tailWord_1482623, baseEnd_1482623] using wordTrace_append hprefix tailTrace_1482623
  have hstable : (prefixWord ++ tailWord_1482623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482623).length < 2 ^ (prefixWord ++ tailWord_1482623).sum := by decide
  have hdescent : baseEnd_1482623 < baseStart_1482623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482627 : List Nat := [1, 1, 1, 3, 4, 4, 2, 1, 1, 3, 2]
def baseStart_1482627 : Nat := 118140960795 + 1482627 * 2 ^ 59
def prefixEnd_1482627 : Nat := 4983230072969 + 3 ^ 40 * 1482627 * 2
def baseEnd_1482627 : Nat := 761300282333675948744029

theorem tailTrace_1482627 : CollatzResearch.WordTrace tailWord_1482627 prefixEnd_1482627 761300282333675948744029 := by
  unfold tailWord_1482627
  simp only [CollatzResearch.WordTrace]
  refine ⟨54075849199703066377430135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36050566133135377584953423 54075849199703066377430135)
  ·
    refine ⟨81113773799554599566145203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54075849199703066377430135 81113773799554599566145203)
    ·
      refine ⟨121670660699331899349217805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81113773799554599566145203 121670660699331899349217805)
      ·
        refine ⟨45626497762249462255956677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121670660699331899349217805 45626497762249462255956677)
        ·
          refine ⟨8554968330421774172991877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45626497762249462255956677 8554968330421774172991877)
          ·
            refine ⟨1604056561954082657435977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8554968330421774172991877 1604056561954082657435977)
            ·
              refine ⟨1203042421465561993076983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1604056561954082657435977 1203042421465561993076983)
              ·
                refine ⟨1804563632198342989615475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1203042421465561993076983 1804563632198342989615475)
                ·
                  refine ⟨2706845448297514484423213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1804563632198342989615475 2706845448297514484423213)
                  ·
                    refine ⟨1015067043111567931658705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2706845448297514484423213 1015067043111567931658705)
                    ·
                      refine ⟨761300282333675948744029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1015067043111567931658705 761300282333675948744029)
                      ·
                        rfl

theorem cell23_1482627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 1, 1, 3, 2].length) (baseStart_1482627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482627 prefixEnd_1482627 := by exact prefixLift 1482627
  have htrace : WordTrace (prefixWord ++ tailWord_1482627) baseStart_1482627 baseEnd_1482627 := by
    simpa [prefixWord, tailWord_1482627, baseEnd_1482627] using wordTrace_append hprefix tailTrace_1482627
  have hstable : (prefixWord ++ tailWord_1482627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482627).length < 2 ^ (prefixWord ++ tailWord_1482627).sum := by decide
  have hdescent : baseEnd_1482627 < baseStart_1482627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482629 : List Nat := [1, 3, 1, 1, 3, 2, 1, 2, 9]
def baseStart_1482629 : Nat := 118140960795 + 1482629 * 2 ^ 59
def prefixEnd_1482629 : Nat := 4983230072969 + 3 ^ 40 * 1482629 * 2
def baseEnd_1482629 : Nat := 84589034366109437879891

theorem tailTrace_1482629 : CollatzResearch.WordTrace tailWord_1482629 prefixEnd_1482629 84589034366109437879891 := by
  unfold tailWord_1482629
  simp only [CollatzResearch.WordTrace]
  refine ⟨54075922145695820719002941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36050614763797213812668627 54075922145695820719002941)
  ·
    refine ⟨20278470804635932769626103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54075922145695820719002941 20278470804635932769626103)
    ·
      refine ⟨30417706206953899154439155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20278470804635932769626103 30417706206953899154439155)
      ·
        refine ⟨45626559310430848731658733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30417706206953899154439155 45626559310430848731658733)
        ·
          refine ⟨17109959741411568274372025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45626559310430848731658733 17109959741411568274372025)
          ·
            refine ⟨12832469806058676205779019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17109959741411568274372025 12832469806058676205779019)
            ·
              refine ⟨19248704709088014308668529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12832469806058676205779019 19248704709088014308668529)
              ·
                refine ⟨14436528531816010731501397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19248704709088014308668529 14436528531816010731501397)
                ·
                  refine ⟨84589034366109437879891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 14436528531816010731501397 84589034366109437879891)
                  ·
                    rfl

theorem cell23_1482629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 9].length) (baseStart_1482629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482629 prefixEnd_1482629 := by exact prefixLift 1482629
  have htrace : WordTrace (prefixWord ++ tailWord_1482629) baseStart_1482629 baseEnd_1482629 := by
    simpa [prefixWord, tailWord_1482629, baseEnd_1482629] using wordTrace_append hprefix tailTrace_1482629
  have hstable : (prefixWord ++ tailWord_1482629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482629).length < 2 ^ (prefixWord ++ tailWord_1482629).sum := by decide
  have hdescent : baseEnd_1482629 < baseStart_1482629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482634 : List Nat := [3, 1, 2, 4, 3, 1, 1, 2, 2, 1, 3]
def baseStart_1482634 : Nat := 118140960795 + 1482634 * 2 ^ 59
def prefixEnd_1482634 : Nat := 4983230072969 + 3 ^ 40 * 1482634 * 2
def baseEnd_1482634 : Nat := 761303876698257421356497

theorem tailTrace_1482634 : CollatzResearch.WordTrace tailWord_1482634 prefixEnd_1482634 761303876698257421356497 := by
  unfold tailWord_1482634
  simp only [CollatzResearch.WordTrace]
  refine ⟨13519026127669426643233739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36050736340451804381956637 13519026127669426643233739)
  ·
    refine ⟨20278539191504139964850609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13519026127669426643233739 20278539191504139964850609)
    ·
      refine ⟨15208904393628104973637957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20278539191504139964850609 15208904393628104973637957)
      ·
        refine ⟨2851669573805269682557117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15208904393628104973637957 2851669573805269682557117)
        ·
          refine ⟨1069376090176976130958919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2851669573805269682557117 1069376090176976130958919)
          ·
            refine ⟨1604064135265464196438379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1069376090176976130958919 1604064135265464196438379)
            ·
              refine ⟨2406096202898196294657569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1604064135265464196438379 2406096202898196294657569)
              ·
                refine ⟨1804572152173647220993177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2406096202898196294657569 1804572152173647220993177)
                ·
                  refine ⟨1353429114130235415744883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1804572152173647220993177 1353429114130235415744883)
                  ·
                    refine ⟨2030143671195353123617325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1353429114130235415744883 2030143671195353123617325)
                    ·
                      refine ⟨761303876698257421356497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2030143671195353123617325 761303876698257421356497)
                      ·
                        rfl

theorem cell23_1482634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_1482634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482634 prefixEnd_1482634 := by exact prefixLift 1482634
  have htrace : WordTrace (prefixWord ++ tailWord_1482634) baseStart_1482634 baseEnd_1482634 := by
    simpa [prefixWord, tailWord_1482634, baseEnd_1482634] using wordTrace_append hprefix tailTrace_1482634
  have hstable : (prefixWord ++ tailWord_1482634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482634).length < 2 ^ (prefixWord ++ tailWord_1482634).sum := by decide
  have hdescent : baseEnd_1482634 < baseStart_1482634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482657 : List Nat := [1, 2, 3, 4, 2, 2, 1, 1, 1, 4, 2]
def baseStart_1482657 : Nat := 118140960795 + 1482657 * 2 ^ 59
def prefixEnd_1482657 : Nat := 4983230072969 + 3 ^ 40 * 1482657 * 2
def baseEnd_1482657 : Nat := 761315686753310831368891

theorem tailTrace_1482657 : CollatzResearch.WordTrace tailWord_1482657 prefixEnd_1482657 761315686753310831368891 := by
  unfold tailWord_1482657
  simp only [CollatzResearch.WordTrace]
  refine ⟨54076943389594381501022225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36051295593062921000681483 54076943389594381501022225)
  ·
    refine ⟨40557707542195786125766669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54076943389594381501022225 40557707542195786125766669)
    ·
      refine ⟨15209140328323419797162501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40557707542195786125766669 15209140328323419797162501)
      ·
        refine ⟨2851713811560641211967969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15209140328323419797162501 2851713811560641211967969)
        ·
          refine ⟨2138785358670480908975977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2851713811560641211967969 2138785358670480908975977)
          ·
            refine ⟨1604089019002860681731983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2138785358670480908975977 1604089019002860681731983)
            ·
              refine ⟨2406133528504291022597975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1604089019002860681731983 2406133528504291022597975)
              ·
                refine ⟨3609200292756436533896963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2406133528504291022597975 3609200292756436533896963)
                ·
                  refine ⟨5413800439134654800845445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3609200292756436533896963 5413800439134654800845445)
                  ·
                    refine ⟨1015087582337747775158521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5413800439134654800845445 1015087582337747775158521)
                    ·
                      refine ⟨761315686753310831368891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1015087582337747775158521 761315686753310831368891)
                      ·
                        rfl

theorem cell23_1482657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_1482657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482657 prefixEnd_1482657 := by exact prefixLift 1482657
  have htrace : WordTrace (prefixWord ++ tailWord_1482657) baseStart_1482657 baseEnd_1482657 := by
    simpa [prefixWord, tailWord_1482657, baseEnd_1482657] using wordTrace_append hprefix tailTrace_1482657
  have hstable : (prefixWord ++ tailWord_1482657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482657).length < 2 ^ (prefixWord ++ tailWord_1482657).sum := by decide
  have hdescent : baseEnd_1482657 < baseStart_1482657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482753 : List Nat := [1, 2, 4, 1, 2, 1, 4, 2, 6]
def baseStart_1482753 : Nat := 118140960795 + 1482753 * 2 ^ 59
def prefixEnd_1482753 : Nat := 4983230072969 + 3 ^ 40 * 1482753 * 2
def baseEnd_1482753 : Nat := 84596108988460272863161

theorem tailTrace_1482753 : CollatzResearch.WordTrace tailWord_1482753 prefixEnd_1482753 84596108988460272863161 := by
  unfold tailWord_1482753
  simp only [CollatzResearch.WordTrace]
  refine ⟨54080444797246589896516913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36053629864831059931011275 54080444797246589896516913)
  ·
    refine ⟨40560333597934942422387685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54080444797246589896516913 40560333597934942422387685)
    ·
      refine ⟨7605062549612801704197691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40560333597934942422387685 7605062549612801704197691)
      ·
        refine ⟨11407593824419202556296537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7605062549612801704197691 11407593824419202556296537)
        ·
          refine ⟨8555695368314401917222403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11407593824419202556296537 8555695368314401917222403)
          ·
            refine ⟨12833543052471602875833605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8555695368314401917222403 12833543052471602875833605)
            ·
              refine ⟨2406289322338425539218801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12833543052471602875833605 2406289322338425539218801)
              ·
                refine ⟨1804716991753819154414101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2406289322338425539218801 1804716991753819154414101)
                ·
                  refine ⟨84596108988460272863161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1804716991753819154414101 84596108988460272863161)
                  ·
                    rfl

theorem cell23_1482753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 2, 6].length) (baseStart_1482753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482753 prefixEnd_1482753 := by exact prefixLift 1482753
  have htrace : WordTrace (prefixWord ++ tailWord_1482753) baseStart_1482753 baseEnd_1482753 := by
    simpa [prefixWord, tailWord_1482753, baseEnd_1482753] using wordTrace_append hprefix tailTrace_1482753
  have hstable : (prefixWord ++ tailWord_1482753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482753).length < 2 ^ (prefixWord ++ tailWord_1482753).sum := by decide
  have hdescent : baseEnd_1482753 < baseStart_1482753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482757 : List Nat := [1, 3, 1, 1, 2, 4, 4, 2, 1, 4]
def baseStart_1482757 : Nat := 118140960795 + 1482757 * 2 ^ 59
def prefixEnd_1482757 : Nat := 4983230072969 + 3 ^ 40 * 1482757 * 2
def baseEnd_1482757 : Nat := 253789011606253480039477

theorem tailTrace_1482757 : CollatzResearch.WordTrace tailWord_1482757 prefixEnd_1482757 253789011606253480039477 := by
  unfold tailWord_1482757
  simp only [CollatzResearch.WordTrace]
  refine ⟨54080590689232098579662525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36053727126154732386441683 54080590689232098579662525)
  ·
    refine ⟨20280221508462036967373447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54080590689232098579662525 20280221508462036967373447)
    ·
      refine ⟨30420332262693055451060171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20280221508462036967373447 30420332262693055451060171)
      ·
        refine ⟨45630498394039583176590257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30420332262693055451060171 45630498394039583176590257)
        ·
          refine ⟨34222873795529687382442693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45630498394039583176590257 34222873795529687382442693)
          ·
            refine ⟨6416788836661816384208005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34222873795529687382442693 6416788836661816384208005)
            ·
              refine ⟨1203147906874090572039001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6416788836661816384208005 1203147906874090572039001)
              ·
                refine ⟨902360930155567929029251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1203147906874090572039001 902360930155567929029251)
                ·
                  refine ⟨1353541395233351893543877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 902360930155567929029251 1353541395233351893543877)
                  ·
                    refine ⟨253789011606253480039477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1353541395233351893543877 253789011606253480039477)
                    ·
                      rfl

theorem cell23_1482757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 2, 1, 4].length) (baseStart_1482757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482757 prefixEnd_1482757 := by exact prefixLift 1482757
  have htrace : WordTrace (prefixWord ++ tailWord_1482757) baseStart_1482757 baseEnd_1482757 := by
    simpa [prefixWord, tailWord_1482757, baseEnd_1482757] using wordTrace_append hprefix tailTrace_1482757
  have hstable : (prefixWord ++ tailWord_1482757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482757).length < 2 ^ (prefixWord ++ tailWord_1482757).sum := by decide
  have hdescent : baseEnd_1482757 < baseStart_1482757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482776 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 2, 1, 7]
def baseStart_1482776 : Nat := 118140960795 + 1482776 * 2 ^ 59
def prefixEnd_1482776 : Nat := 4983230072969 + 3 ^ 40 * 1482776 * 2
def baseEnd_1482776 : Nat := 761376790951195865780843

theorem tailTrace_1482776 : CollatzResearch.WordTrace tailWord_1482776 prefixEnd_1482776 761376790951195865780843 := by
  unfold tailWord_1482776
  simp only [CollatzResearch.WordTrace]
  refine ⟨27040641838081632412302091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36054189117442176549736121 27040641838081632412302091)
  ·
    refine ⟨40560962757122448618453137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27040641838081632412302091 40560962757122448618453137)
    ·
      refine ⟨30420722067841836463839853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40560962757122448618453137 30420722067841836463839853)
      ·
        refine ⟨11407770775440688673939945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30420722067841836463839853 11407770775440688673939945)
        ·
          refine ⟨8555828081580516505454959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11407770775440688673939945 8555828081580516505454959)
          ·
            refine ⟨12833742122370774758182439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8555828081580516505454959 12833742122370774758182439)
            ·
              refine ⟨19250613183556162137273659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12833742122370774758182439 19250613183556162137273659)
              ·
                refine ⟨28875919775334243205910489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19250613183556162137273659 28875919775334243205910489)
                ·
                  refine ⟨21656939831500682404432867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28875919775334243205910489 21656939831500682404432867)
                  ·
                    refine ⟨32485409747251023606649301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21656939831500682404432867 32485409747251023606649301)
                    ·
                      refine ⟨761376790951195865780843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 32485409747251023606649301 761376790951195865780843)
                      ·
                        rfl

theorem cell23_1482776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_1482776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482776 prefixEnd_1482776 := by exact prefixLift 1482776
  have htrace : WordTrace (prefixWord ++ tailWord_1482776) baseStart_1482776 baseEnd_1482776 := by
    simpa [prefixWord, tailWord_1482776, baseEnd_1482776] using wordTrace_append hprefix tailTrace_1482776
  have hstable : (prefixWord ++ tailWord_1482776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482776).length < 2 ^ (prefixWord ++ tailWord_1482776).sum := by decide
  have hdescent : baseEnd_1482776 < baseStart_1482776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482780 : List Nat := [2, 2, 3, 1, 3, 1, 1, 1, 5, 1, 3]
def baseStart_1482780 : Nat := 118140960795 + 1482780 * 2 ^ 59
def prefixEnd_1482780 : Nat := 4983230072969 + 3 ^ 40 * 1482780 * 2
def baseEnd_1482780 : Nat := 761378844873813850130825

theorem tailTrace_1482780 : CollatzResearch.WordTrace tailWord_1482780 prefixEnd_1482780 761378844873813850130825 := by
  unfold tailWord_1482780
  simp only [CollatzResearch.WordTrace]
  refine ⟨27040714784074386753874897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36054286378765849005166529 27040714784074386753874897)
  ·
    refine ⟨20280536088055790065406173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27040714784074386753874897 20280536088055790065406173)
    ·
      refine ⟨7605201033020921274527315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20280536088055790065406173 7605201033020921274527315)
      ·
        refine ⟨11407801549531381911790973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7605201033020921274527315 11407801549531381911790973)
        ·
          refine ⟨4277925581074268216921615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11407801549531381911790973 4277925581074268216921615)
          ·
            refine ⟨6416888371611402325382423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4277925581074268216921615 6416888371611402325382423)
            ·
              refine ⟨9625332557417103488073635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6416888371611402325382423 9625332557417103488073635)
              ·
                refine ⟨14437998836125655232110453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9625332557417103488073635 14437998836125655232110453)
                ·
                  refine ⟨1353562390886780178010355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14437998836125655232110453 1353562390886780178010355)
                  ·
                    refine ⟨2030343586330170267015533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1353562390886780178010355 2030343586330170267015533)
                    ·
                      refine ⟨761378844873813850130825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2030343586330170267015533 761378844873813850130825)
                      ·
                        rfl

theorem cell23_1482780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_1482780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482780 prefixEnd_1482780 := by exact prefixLift 1482780
  have htrace : WordTrace (prefixWord ++ tailWord_1482780) baseStart_1482780 baseEnd_1482780 := by
    simpa [prefixWord, tailWord_1482780, baseEnd_1482780] using wordTrace_append hprefix tailTrace_1482780
  have hstable : (prefixWord ++ tailWord_1482780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482780).length < 2 ^ (prefixWord ++ tailWord_1482780).sum := by decide
  have hdescent : baseEnd_1482780 < baseStart_1482780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482783 : List Nat := [1, 1, 2, 4, 1, 2, 2, 4, 1, 5]
def baseStart_1482783 : Nat := 118140960795 + 1482783 * 2 ^ 59
def prefixEnd_1482783 : Nat := 4983230072969 + 3 ^ 40 * 1482783 * 2
def baseEnd_1482783 : Nat := 253793461771925779464437

theorem tailTrace_1482783 : CollatzResearch.WordTrace tailWord_1482783 prefixEnd_1482783 253793461771925779464437 := by
  unfold tailWord_1482783
  simp only [CollatzResearch.WordTrace]
  refine ⟨54081538987137905020109003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36054359324758603346739335 54081538987137905020109003)
  ·
    refine ⟨81122308480706857530163505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54081538987137905020109003 81122308480706857530163505)
    ·
      refine ⟨60841731360530143147622629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81122308480706857530163505 60841731360530143147622629)
      ·
        refine ⟨11407824630099401840179243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60841731360530143147622629 11407824630099401840179243)
        ·
          refine ⟨17111736945149102760268865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11407824630099401840179243 17111736945149102760268865)
          ·
            refine ⟨12833802708861827070201649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17111736945149102760268865 12833802708861827070201649)
            ·
              refine ⟨9625352031646370302651237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12833802708861827070201649 9625352031646370302651237)
              ·
                refine ⟨1804753505933694431747107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9625352031646370302651237 1804753505933694431747107)
                ·
                  refine ⟨2707130258900541647620661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1804753505933694431747107 2707130258900541647620661)
                  ·
                    refine ⟨253793461771925779464437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2707130258900541647620661 253793461771925779464437)
                    ·
                      rfl

theorem cell23_1482783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 4, 1, 5].length) (baseStart_1482783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482783 prefixEnd_1482783 := by exact prefixLift 1482783
  have htrace : WordTrace (prefixWord ++ tailWord_1482783) baseStart_1482783 baseEnd_1482783 := by
    simpa [prefixWord, tailWord_1482783, baseEnd_1482783] using wordTrace_append hprefix tailTrace_1482783
  have hstable : (prefixWord ++ tailWord_1482783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482783).length < 2 ^ (prefixWord ++ tailWord_1482783).sum := by decide
  have hdescent : baseEnd_1482783 < baseStart_1482783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482796 : List Nat := [2, 2, 1, 1, 1, 2, 2, 3, 3, 6]
def baseStart_1482796 : Nat := 118140960795 + 1482796 * 2 ^ 59
def prefixEnd_1482796 : Nat := 4983230072969 + 3 ^ 40 * 1482796 * 2
def baseEnd_1482796 : Nat := 253795686854761929176917

theorem tailTrace_1482796 : CollatzResearch.WordTrace tailWord_1482796 prefixEnd_1482796 253795686854761929176917 := by
  unfold tailWord_1482796
  simp only [CollatzResearch.WordTrace]
  refine ⟨27041006568045404120166121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36054675424060538826888161 27041006568045404120166121)
  ·
    refine ⟨20280754926034053090124591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27041006568045404120166121 20280754926034053090124591)
    ·
      refine ⟨30421132389051079635186887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20280754926034053090124591 30421132389051079635186887)
      ·
        refine ⟨45631698583576619452780331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30421132389051079635186887 45631698583576619452780331)
        ·
          refine ⟨68447547875364929179170497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45631698583576619452780331 68447547875364929179170497)
          ·
            refine ⟨51335660906523696884377873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68447547875364929179170497 51335660906523696884377873)
            ·
              refine ⟨38501745679892772663283405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51335660906523696884377873 38501745679892772663283405)
              ·
                refine ⟨14438154629959789748731277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38501745679892772663283405 14438154629959789748731277)
                ·
                  refine ⟨5414307986234921155774229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14438154629959789748731277 5414307986234921155774229)
                  ·
                    refine ⟨253795686854761929176917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5414307986234921155774229 253795686854761929176917)
                    ·
                      rfl

theorem cell23_1482796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 6].length) (baseStart_1482796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482796 prefixEnd_1482796 := by exact prefixLift 1482796
  have htrace : WordTrace (prefixWord ++ tailWord_1482796) baseStart_1482796 baseEnd_1482796 := by
    simpa [prefixWord, tailWord_1482796, baseEnd_1482796] using wordTrace_append hprefix tailTrace_1482796
  have hstable : (prefixWord ++ tailWord_1482796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482796).length < 2 ^ (prefixWord ++ tailWord_1482796).sum := by decide
  have hdescent : baseEnd_1482796 < baseStart_1482796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482800 : List Nat := [2, 1, 1, 1, 2, 5, 4, 1, 1, 5]
def baseStart_1482800 : Nat := 118140960795 + 1482800 * 2 ^ 59
def prefixEnd_1482800 : Nat := 4983230072969 + 3 ^ 40 * 1482800 * 2
def baseEnd_1482800 : Nat := 253796371495634590626911

theorem tailTrace_1482800 : CollatzResearch.WordTrace tailWord_1482800 prefixEnd_1482800 253796371495634590626911 := by
  unfold tailWord_1482800
  simp only [CollatzResearch.WordTrace]
  refine ⟨27041079514038158461738927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36054772685384211282318569 27041079514038158461738927)
  ·
    refine ⟨40561619271057237692608391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27041079514038158461738927 40561619271057237692608391)
    ·
      refine ⟨60842428906585856538912587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40561619271057237692608391 60842428906585856538912587)
      ·
        refine ⟨91263643359878784808368881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60842428906585856538912587 91263643359878784808368881)
        ·
          refine ⟨68447732519909088606276661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91263643359878784808368881 68447732519909088606276661)
          ·
            refine ⟨6416974923741477056838437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68447732519909088606276661 6416974923741477056838437)
            ·
              refine ⟨1203182798201526948157207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6416974923741477056838437 1203182798201526948157207)
              ·
                refine ⟨1804774197302290422235811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1203182798201526948157207 1804774197302290422235811)
                ·
                  refine ⟨2707161295953435633353717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1804774197302290422235811 2707161295953435633353717)
                  ·
                    refine ⟨253796371495634590626911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2707161295953435633353717 253796371495634590626911)
                    ·
                      rfl

theorem cell23_1482800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 1, 1, 5].length) (baseStart_1482800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482800 prefixEnd_1482800 := by exact prefixLift 1482800
  have htrace : WordTrace (prefixWord ++ tailWord_1482800) baseStart_1482800 baseEnd_1482800 := by
    simpa [prefixWord, tailWord_1482800, baseEnd_1482800] using wordTrace_append hprefix tailTrace_1482800
  have hstable : (prefixWord ++ tailWord_1482800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482800).length < 2 ^ (prefixWord ++ tailWord_1482800).sum := by decide
  have hdescent : baseEnd_1482800 < baseStart_1482800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482804 : List Nat := [2, 5, 1, 2, 3, 1, 1, 2, 6]
def baseStart_1482804 : Nat := 118140960795 + 1482804 * 2 ^ 59
def prefixEnd_1482804 : Nat := 4983230072969 + 3 ^ 40 * 1482804 * 2
def baseEnd_1482804 : Nat := 84599018712169084025635

theorem tailTrace_1482804 : CollatzResearch.WordTrace tailWord_1482804 prefixEnd_1482804 84599018712169084025635 := by
  unfold tailWord_1482804
  simp only [CollatzResearch.WordTrace]
  refine ⟨27041152460030912803311733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36054869946707883737748977 27041152460030912803311733)
  ·
    refine ⟨2535108043127898075310475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27041152460030912803311733 2535108043127898075310475)
    ·
      refine ⟨3802662064691847112965713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2535108043127898075310475 3802662064691847112965713)
      ·
        refine ⟨2851996548518885334724285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3802662064691847112965713 2851996548518885334724285)
        ·
          refine ⟨1069498705694582000521607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2851996548518885334724285 1069498705694582000521607)
          ·
            refine ⟨1604248058541873000782411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1069498705694582000521607 1604248058541873000782411)
            ·
              refine ⟨2406372087812809501173617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1604248058541873000782411 2406372087812809501173617)
              ·
                refine ⟨1804779065859607125880213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2406372087812809501173617 1804779065859607125880213)
                ·
                  refine ⟨84599018712169084025635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1804779065859607125880213 84599018712169084025635)
                  ·
                    rfl

theorem cell23_1482804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_1482804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482804 prefixEnd_1482804 := by exact prefixLift 1482804
  have htrace : WordTrace (prefixWord ++ tailWord_1482804) baseStart_1482804 baseEnd_1482804 := by
    simpa [prefixWord, tailWord_1482804, baseEnd_1482804] using wordTrace_append hprefix tailTrace_1482804
  have hstable : (prefixWord ++ tailWord_1482804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482804).length < 2 ^ (prefixWord ++ tailWord_1482804).sum := by decide
  have hdescent : baseEnd_1482804 < baseStart_1482804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482814 : List Nat := [4, 2, 1, 3, 2, 1, 2, 1, 3, 1, 3]
def baseStart_1482814 : Nat := 118140960795 + 1482814 * 2 ^ 59
def prefixEnd_1482814 : Nat := 4983230072969 + 3 ^ 40 * 1482814 * 2
def baseEnd_1482814 : Nat := 761396303216066717105669

theorem tailTrace_1482814 : CollatzResearch.WordTrace tailWord_1482814 prefixEnd_1482814 761396303216066717105669 := by
  unfold tailWord_1482814
  simp only [CollatzResearch.WordTrace]
  refine ⟨6760333706253199664310937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36055113100017064876324997 6760333706253199664310937)
  ·
    refine ⟨5070250279689899748233203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6760333706253199664310937 5070250279689899748233203)
    ·
      refine ⟨7605375419534849622349805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5070250279689899748233203 7605375419534849622349805)
      ·
        refine ⟨2852015782325568608381177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7605375419534849622349805 2852015782325568608381177)
        ·
          refine ⟨2139011836744176456285883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2852015782325568608381177 2139011836744176456285883)
          ·
            refine ⟨3208517755116264684428825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2139011836744176456285883 3208517755116264684428825)
            ·
              refine ⟨2406388316337198513321619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3208517755116264684428825 2406388316337198513321619)
              ·
                refine ⟨3609582474505797769982429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2406388316337198513321619 3609582474505797769982429)
                ·
                  refine ⟨1353593427939674163743411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3609582474505797769982429 1353593427939674163743411)
                  ·
                    refine ⟨2030390141909511245615117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1353593427939674163743411 2030390141909511245615117)
                    ·
                      refine ⟨761396303216066717105669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2030390141909511245615117 761396303216066717105669)
                      ·
                        rfl

theorem cell23_1482814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_1482814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482814 prefixEnd_1482814 := by exact prefixLift 1482814
  have htrace : WordTrace (prefixWord ++ tailWord_1482814) baseStart_1482814 baseEnd_1482814 := by
    simpa [prefixWord, tailWord_1482814, baseEnd_1482814] using wordTrace_append hprefix tailTrace_1482814
  have hstable : (prefixWord ++ tailWord_1482814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482814).length < 2 ^ (prefixWord ++ tailWord_1482814).sum := by decide
  have hdescent : baseEnd_1482814 < baseStart_1482814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482823 : List Nat := [1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 5]
def baseStart_1482823 : Nat := 118140960795 + 1482823 * 2 ^ 59
def prefixEnd_1482823 : Nat := 4983230072969 + 3 ^ 40 * 1482823 * 2
def baseEnd_1482823 : Nat := 761400924541957181893127

theorem tailTrace_1482823 : CollatzResearch.WordTrace tailWord_1482823 prefixEnd_1482823 761400924541957181893127 := by
  unfold tailWord_1482823
  simp only [CollatzResearch.WordTrace]
  refine ⟨54082997906992991851565123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36055331937995327901043415 54082997906992991851565123)
  ·
    refine ⟨81124496860489487777347685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54082997906992991851565123 81124496860489487777347685)
    ·
      refine ⟨15210843161341778958252691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81124496860489487777347685 15210843161341778958252691)
      ·
        refine ⟨22816264742012668437379037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15210843161341778958252691 22816264742012668437379037)
        ·
          refine ⟨8556099278254750664017139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22816264742012668437379037 8556099278254750664017139)
          ·
            refine ⟨12834148917382125996025709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8556099278254750664017139 12834148917382125996025709)
            ·
              refine ⟨4812805844018297248509641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12834148917382125996025709 4812805844018297248509641)
              ·
                refine ⟨3609604383013722936382231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4812805844018297248509641 3609604383013722936382231)
                ·
                  refine ⟨5414406574520584404573347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3609604383013722936382231 5414406574520584404573347)
                  ·
                    refine ⟨8121609861780876606860021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5414406574520584404573347 8121609861780876606860021)
                    ·
                      refine ⟨761400924541957181893127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8121609861780876606860021 761400924541957181893127)
                      ·
                        rfl

theorem cell23_1482823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_1482823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482823 prefixEnd_1482823 := by exact prefixLift 1482823
  have htrace : WordTrace (prefixWord ++ tailWord_1482823) baseStart_1482823 baseEnd_1482823 := by
    simpa [prefixWord, tailWord_1482823, baseEnd_1482823] using wordTrace_append hprefix tailTrace_1482823
  have hstable : (prefixWord ++ tailWord_1482823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482823).length < 2 ^ (prefixWord ++ tailWord_1482823).sum := by decide
  have hdescent : baseEnd_1482823 < baseStart_1482823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482826 : List Nat := [3, 1, 2, 1, 1, 2, 1, 12]
def baseStart_1482826 : Nat := 118140960795 + 1482826 * 2 ^ 59
def prefixEnd_1482826 : Nat := 4983230072969 + 3 ^ 40 * 1482826 * 2
def baseEnd_1482826 : Nat := 28200091295700765561319

theorem tailTrace_1482826 : CollatzResearch.WordTrace tailWord_1482826 prefixEnd_1482826 28200091295700765561319 := by
  unfold tailWord_1482826
  simp only [CollatzResearch.WordTrace]
  refine ⟨13520776831495530840981083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36055404883988082242616221 13520776831495530840981083)
  ·
    refine ⟨20281165247243296261471625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13520776831495530840981083 20281165247243296261471625)
    ·
      refine ⟨15210873935432472196103719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20281165247243296261471625 15210873935432472196103719)
      ·
        refine ⟨22816310903148708294155579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15210873935432472196103719 22816310903148708294155579)
        ·
          refine ⟨34224466354723062441233369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22816310903148708294155579 34224466354723062441233369)
          ·
            refine ⟨25668349766042296830925027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34224466354723062441233369 25668349766042296830925027)
            ·
              refine ⟨38502524649063445246387541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25668349766042296830925027 38502524649063445246387541)
              ·
                refine ⟨28200091295700765561319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 38502524649063445246387541 28200091295700765561319)
                ·
                  rfl

theorem cell23_1482826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 12].length) (baseStart_1482826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482826 prefixEnd_1482826 := by exact prefixLift 1482826
  have htrace : WordTrace (prefixWord ++ tailWord_1482826) baseStart_1482826 baseEnd_1482826 := by
    simpa [prefixWord, tailWord_1482826, baseEnd_1482826] using wordTrace_append hprefix tailTrace_1482826
  have hstable : (prefixWord ++ tailWord_1482826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482826).length < 2 ^ (prefixWord ++ tailWord_1482826).sum := by decide
  have hdescent : baseEnd_1482826 < baseStart_1482826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482830 : List Nat := [4, 1, 1, 1, 1, 6, 1, 1, 1, 6]
def baseStart_1482830 : Nat := 118140960795 + 1482830 * 2 ^ 59
def prefixEnd_1482830 : Nat := 4983230072969 + 3 ^ 40 * 1482830 * 2
def baseEnd_1482830 : Nat := 253801506302179551501865

theorem tailTrace_1482830 : CollatzResearch.WordTrace tailWord_1482830 prefixEnd_1482830 253801506302179551501865 := by
  unfold tailWord_1482830
  simp only [CollatzResearch.WordTrace]
  refine ⟨6760406652245954005883743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36055502145311754698046629 6760406652245954005883743)
  ·
    refine ⟨10140609978368931008825615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6760406652245954005883743 10140609978368931008825615)
    ·
      refine ⟨15210914967553396513238423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10140609978368931008825615 15210914967553396513238423)
      ·
        refine ⟨22816372451330094769857635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15210914967553396513238423 22816372451330094769857635)
        ·
          refine ⟨34224558676995142154786453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22816372451330094769857635 34224558676995142154786453)
          ·
            refine ⟨1604276187984147288505615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 34224558676995142154786453 1604276187984147288505615)
            ·
              refine ⟨2406414281976220932758423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1604276187984147288505615 2406414281976220932758423)
              ·
                refine ⟨3609621422964331399137635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2406414281976220932758423 3609621422964331399137635)
                ·
                  refine ⟨5414432134446497098706453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3609621422964331399137635 5414432134446497098706453)
                  ·
                    refine ⟨253801506302179551501865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5414432134446497098706453 253801506302179551501865)
                    ·
                      rfl

theorem cell23_1482830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 1, 6].length) (baseStart_1482830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482830 prefixEnd_1482830 := by exact prefixLift 1482830
  have htrace : WordTrace (prefixWord ++ tailWord_1482830) baseStart_1482830 baseEnd_1482830 := by
    simpa [prefixWord, tailWord_1482830, baseEnd_1482830] using wordTrace_append hprefix tailTrace_1482830
  have hstable : (prefixWord ++ tailWord_1482830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482830).length < 2 ^ (prefixWord ++ tailWord_1482830).sum := by decide
  have hdescent : baseEnd_1482830 < baseStart_1482830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482837 : List Nat := [1, 3, 2, 2, 1, 3, 2, 2, 3, 2, 2]
def baseStart_1482837 : Nat := 118140960795 + 1482837 * 2 ^ 59
def prefixEnd_1482837 : Nat := 4983230072969 + 3 ^ 40 * 1482837 * 2
def baseEnd_1482837 : Nat := 761408113271120127118063

theorem tailTrace_1482837 : CollatzResearch.WordTrace tailWord_1482837 prefixEnd_1482837 761408113271120127118063 := by
  unfold tailWord_1482837
  simp only [CollatzResearch.WordTrace]
  refine ⟨54083508528942272242574765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36055672352628181495049843 54083508528942272242574765)
  ·
    refine ⟨20281315698353352090965537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54083508528942272242574765 20281315698353352090965537)
    ·
      refine ⟨15210986773765014068224153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20281315698353352090965537 15210986773765014068224153)
      ·
        refine ⟨11408240080323760551168115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15210986773765014068224153 11408240080323760551168115)
        ·
          refine ⟨17112360120485640826752173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11408240080323760551168115 17112360120485640826752173)
          ·
            refine ⟨6417135045182115310032065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17112360120485640826752173 6417135045182115310032065)
            ·
              refine ⟨4812851283886586482524049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6417135045182115310032065 4812851283886586482524049)
              ·
                refine ⟨3609638462914939861893037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4812851283886586482524049 3609638462914939861893037)
                ·
                  refine ⟨1353614423593102448209889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3609638462914939861893037 1353614423593102448209889)
                  ·
                    refine ⟨1015210817694826836157417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1353614423593102448209889 1015210817694826836157417)
                    ·
                      refine ⟨761408113271120127118063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1015210817694826836157417 761408113271120127118063)
                      ·
                        rfl

theorem cell23_1482837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 3, 2, 2].length) (baseStart_1482837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482837 prefixEnd_1482837 := by exact prefixLift 1482837
  have htrace : WordTrace (prefixWord ++ tailWord_1482837) baseStart_1482837 baseEnd_1482837 := by
    simpa [prefixWord, tailWord_1482837, baseEnd_1482837] using wordTrace_append hprefix tailTrace_1482837
  have hstable : (prefixWord ++ tailWord_1482837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482837).length < 2 ^ (prefixWord ++ tailWord_1482837).sum := by decide
  have hdescent : baseEnd_1482837 < baseStart_1482837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482840 : List Nat := [2, 1, 2, 2, 1, 4, 1, 4, 1, 2, 3]
def baseStart_1482840 : Nat := 118140960795 + 1482840 * 2 ^ 59
def prefixEnd_1482840 : Nat := 4983230072969 + 3 ^ 40 * 1482840 * 2
def baseEnd_1482840 : Nat := 761409653713083615380549

theorem tailTrace_1482840 : CollatzResearch.WordTrace tailWord_1482840 prefixEnd_1482840 761409653713083615380549 := by
  unfold tailWord_1482840
  simp only [CollatzResearch.WordTrace]
  refine ⟨27041808973965701877466987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36055745298620935836622649 27041808973965701877466987)
  ·
    refine ⟨40562713460948552816200481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27041808973965701877466987 40562713460948552816200481)
    ·
      refine ⟨30422035095711414612150361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40562713460948552816200481 30422035095711414612150361)
      ·
        refine ⟨22816526321783560959112771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30422035095711414612150361 22816526321783560959112771)
        ·
          refine ⟨34224789482675341438669157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22816526321783560959112771 34224789482675341438669157)
          ·
            refine ⟨6417148028001626519750467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34224789482675341438669157 6417148028001626519750467)
            ·
              refine ⟨9625722042002439779625701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6417148028001626519750467 9625722042002439779625701)
              ·
                refine ⟨1804822882875457458679819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9625722042002439779625701 1804822882875457458679819)
                ·
                  refine ⟨2707234324313186188019729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1804822882875457458679819 2707234324313186188019729)
                  ·
                    refine ⟨2030425743234889641014797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2707234324313186188019729 2030425743234889641014797)
                    ·
                      refine ⟨761409653713083615380549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2030425743234889641014797 761409653713083615380549)
                      ·
                        rfl

theorem cell23_1482840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 4, 1, 2, 3].length) (baseStart_1482840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482840 prefixEnd_1482840 := by exact prefixLift 1482840
  have htrace : WordTrace (prefixWord ++ tailWord_1482840) baseStart_1482840 baseEnd_1482840 := by
    simpa [prefixWord, tailWord_1482840, baseEnd_1482840] using wordTrace_append hprefix tailTrace_1482840
  have hstable : (prefixWord ++ tailWord_1482840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482840).length < 2 ^ (prefixWord ++ tailWord_1482840).sum := by decide
  have hdescent : baseEnd_1482840 < baseStart_1482840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482871 : List Nat := [1, 1, 3, 1, 1, 6, 3, 2, 1, 2, 2]
def baseStart_1482871 : Nat := 118140960795 + 1482871 * 2 ^ 59
def prefixEnd_1482871 : Nat := 4983230072969 + 3 ^ 40 * 1482871 * 2
def baseEnd_1482871 : Nat := 761425571613372994092907

theorem tailTrace_1482871 : CollatzResearch.WordTrace tailWord_1482871 prefixEnd_1482871 761425571613372994092907 := by
  unfold tailWord_1482871
  simp only [CollatzResearch.WordTrace]
  refine ⟨54084748610819096049312467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36056499073879397366208311 54084748610819096049312467)
  ·
    refine ⟨81127122916228644073968701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54084748610819096049312467 81127122916228644073968701)
    ·
      refine ⟨30422671093585741527738263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81127122916228644073968701 30422671093585741527738263)
      ·
        refine ⟨45634006640378612291607395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30422671093585741527738263 45634006640378612291607395)
        ·
          refine ⟨68451009960567918437411093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45634006640378612291607395 68451009960567918437411093)
          ·
            refine ⟨3208641091901621176753645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 68451009960567918437411093 3208641091901621176753645)
            ·
              refine ⟨1203240409463107941282617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3208641091901621176753645 1203240409463107941282617)
              ·
                refine ⟨902430307097330955961963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1203240409463107941282617 902430307097330955961963)
                ·
                  refine ⟨1353645460645996433942945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 902430307097330955961963 1353645460645996433942945)
                  ·
                    refine ⟨1015234095484497325457209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1353645460645996433942945 1015234095484497325457209)
                    ·
                      refine ⟨761425571613372994092907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1015234095484497325457209 761425571613372994092907)
                      ·
                        rfl

theorem cell23_1482871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 2, 1, 2, 2].length) (baseStart_1482871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482871 prefixEnd_1482871 := by exact prefixLift 1482871
  have htrace : WordTrace (prefixWord ++ tailWord_1482871) baseStart_1482871 baseEnd_1482871 := by
    simpa [prefixWord, tailWord_1482871, baseEnd_1482871] using wordTrace_append hprefix tailTrace_1482871
  have hstable : (prefixWord ++ tailWord_1482871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482871).length < 2 ^ (prefixWord ++ tailWord_1482871).sum := by decide
  have hdescent : baseEnd_1482871 < baseStart_1482871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482880 : List Nat := [2, 1, 1, 2, 1, 3, 1, 4, 3, 3, 2]
def baseStart_1482880 : Nat := 118140960795 + 1482880 * 2 ^ 59
def prefixEnd_1482880 : Nat := 4983230072969 + 3 ^ 40 * 1482880 * 2
def baseEnd_1482880 : Nat := 761430192939263458880365

theorem tailTrace_1482880 : CollatzResearch.WordTrace tailWord_1482880 prefixEnd_1482880 761430192939263458880365 := by
  unfold tailWord_1482880
  simp only [CollatzResearch.WordTrace]
  refine ⟨27042538433893245293195047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36056717911857660390926729 27042538433893245293195047)
  ·
    refine ⟨40563807650839867939792571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27042538433893245293195047 40563807650839867939792571)
    ·
      refine ⟨60845711476259801909688857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40563807650839867939792571 60845711476259801909688857)
      ·
        refine ⟨45634283607194851432266643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60845711476259801909688857 45634283607194851432266643)
        ·
          refine ⟨68451425410792277148399965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45634283607194851432266643 68451425410792277148399965)
          ·
            refine ⟨25669284529047103930649987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68451425410792277148399965 25669284529047103930649987)
            ·
              refine ⟨38503926793570655895974981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25669284529047103930649987 38503926793570655895974981)
              ·
                refine ⟨7219486273794497980495309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38503926793570655895974981 7219486273794497980495309)
                ·
                  refine ⟨2707307352672936742685741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7219486273794497980495309 2707307352672936742685741)
                  ·
                    refine ⟨1015240257252351278507153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2707307352672936742685741 1015240257252351278507153)
                    ·
                      refine ⟨761430192939263458880365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1015240257252351278507153 761430192939263458880365)
                      ·
                        rfl

theorem cell23_1482880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 3, 3, 2].length) (baseStart_1482880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482880 prefixEnd_1482880 := by exact prefixLift 1482880
  have htrace : WordTrace (prefixWord ++ tailWord_1482880) baseStart_1482880 baseEnd_1482880 := by
    simpa [prefixWord, tailWord_1482880, baseEnd_1482880] using wordTrace_append hprefix tailTrace_1482880
  have hstable : (prefixWord ++ tailWord_1482880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482880).length < 2 ^ (prefixWord ++ tailWord_1482880).sum := by decide
  have hdescent : baseEnd_1482880 < baseStart_1482880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482881 : List Nat := [1, 2, 4, 2, 4, 1, 2, 1, 2, 4]
def baseStart_1482881 : Nat := 118140960795 + 1482881 * 2 ^ 59
def prefixEnd_1482881 : Nat := 4983230072969 + 3 ^ 40 * 1482881 * 2
def baseEnd_1482881 : Nat := 253810235473305984989287

theorem tailTrace_1482881 : CollatzResearch.WordTrace tailWord_1482881 prefixEnd_1482881 253810235473305984989287 := by
  unfold tailWord_1482881
  simp only [CollatzResearch.WordTrace]
  refine ⟨54085113340782867757176497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36056742227188578504784331 54085113340782867757176497)
  ·
    refine ⟨40563835005587150817882373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54085113340782867757176497 40563835005587150817882373)
    ·
      refine ⟨7605719063547590778352945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40563835005587150817882373 7605719063547590778352945)
      ·
        refine ⟨5704289297660693083764709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7605719063547590778352945 5704289297660693083764709)
        ·
          refine ⟨1069554243311379953205883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5704289297660693083764709 1069554243311379953205883)
          ·
            refine ⟨1604331364967069929808825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1069554243311379953205883 1604331364967069929808825)
            ·
              refine ⟨1203248523725302447356619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1604331364967069929808825 1203248523725302447356619)
              ·
                refine ⟨1804872785587953671034929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1203248523725302447356619 1804872785587953671034929)
                ·
                  refine ⟨1353654589190965253276197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1804872785587953671034929 1353654589190965253276197)
                  ·
                    refine ⟨253810235473305984989287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1353654589190965253276197 253810235473305984989287)
                    ·
                      rfl

theorem cell23_1482881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_1482881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482881 prefixEnd_1482881 := by exact prefixLift 1482881
  have htrace : WordTrace (prefixWord ++ tailWord_1482881) baseStart_1482881 baseEnd_1482881 := by
    simpa [prefixWord, tailWord_1482881, baseEnd_1482881] using wordTrace_append hprefix tailTrace_1482881
  have hstable : (prefixWord ++ tailWord_1482881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482881).length < 2 ^ (prefixWord ++ tailWord_1482881).sum := by decide
  have hdescent : baseEnd_1482881 < baseStart_1482881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482922 : List Nat := [3, 1, 5, 1, 3, 1, 2, 2, 1, 2, 2]
def baseStart_1482922 : Nat := 118140960795 + 1482922 * 2 ^ 59
def prefixEnd_1482922 : Nat := 4983230072969 + 3 ^ 40 * 1482922 * 2
def baseEnd_1482922 : Nat := 761451759126752294555173

theorem tailTrace_1482922 : CollatzResearch.WordTrace tailWord_1482922 prefixEnd_1482922 761451759126752294555173 := by
  unfold tailWord_1482922
  simp only [CollatzResearch.WordTrace]
  refine ⟨13521652183408582939854755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36057739155756221172946013 13521652183408582939854755)
  ·
    refine ⟨20282478275112874409782133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13521652183408582939854755 20282478275112874409782133)
    ·
      refine ⟨1901482338291831975917075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20282478275112874409782133 1901482338291831975917075)
      ·
        refine ⟨2852223507437747963875613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1901482338291831975917075 2852223507437747963875613)
        ·
          refine ⟨1069583815289155486453355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2852223507437747963875613 1069583815289155486453355)
          ·
            refine ⟨1604375722933733229680033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1069583815289155486453355 1604375722933733229680033)
            ·
              refine ⟨1203281792200299922260025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1604375722933733229680033 1203281792200299922260025)
              ·
                refine ⟨902461344150224941695019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1203281792200299922260025 902461344150224941695019)
                ·
                  refine ⟨1353692016225337412542529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 902461344150224941695019 1353692016225337412542529)
                  ·
                    refine ⟨1015269012169003059406897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1353692016225337412542529 1015269012169003059406897)
                    ·
                      refine ⟨761451759126752294555173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1015269012169003059406897 761451759126752294555173)
                      ·
                        rfl

theorem cell23_1482922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_1482922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482922 prefixEnd_1482922 := by exact prefixLift 1482922
  have htrace : WordTrace (prefixWord ++ tailWord_1482922) baseStart_1482922 baseEnd_1482922 := by
    simpa [prefixWord, tailWord_1482922, baseEnd_1482922] using wordTrace_append hprefix tailTrace_1482922
  have hstable : (prefixWord ++ tailWord_1482922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482922).length < 2 ^ (prefixWord ++ tailWord_1482922).sum := by decide
  have hdescent : baseEnd_1482922 < baseStart_1482922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482944 : List Nat := [2, 1, 1, 2, 5, 1, 2, 3, 2, 2, 2]
def baseStart_1482944 : Nat := 118140960795 + 1482944 * 2 ^ 59
def prefixEnd_1482944 : Nat := 4983230072969 + 3 ^ 40 * 1482944 * 2
def baseEnd_1482944 : Nat := 761463055701151208480071

theorem tailTrace_1482944 : CollatzResearch.WordTrace tailWord_1482944 prefixEnd_1482944 761463055701151208480071 := by
  unfold tailWord_1482944
  simp only [CollatzResearch.WordTrace]
  refine ⟨27043705569777314758359943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36058274093036419677813257 27043705569777314758359943)
  ·
    refine ⟨40565558354665972137539915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27043705569777314758359943 40565558354665972137539915)
    ·
      refine ⟨60848337531998958206309873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40565558354665972137539915 60848337531998958206309873)
      ·
        refine ⟨45636253148999218654732405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60848337531998958206309873 45636253148999218654732405)
        ·
          refine ⟨4278398732718676748881163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45636253148999218654732405 4278398732718676748881163)
          ·
            refine ⟨6417598099078015123321745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4278398732718676748881163 6417598099078015123321745)
            ·
              refine ⟨4813198574308511342491309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6417598099078015123321745 4813198574308511342491309)
              ·
                refine ⟨1804949465365691753434241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4813198574308511342491309 1804949465365691753434241)
                ·
                  refine ⟨1353712099024268815075681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1804949465365691753434241 1353712099024268815075681)
                  ·
                    refine ⟨1015284074268201611306761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1353712099024268815075681 1015284074268201611306761)
                    ·
                      refine ⟨761463055701151208480071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1015284074268201611306761 761463055701151208480071)
                      ·
                        rfl

theorem cell23_1482944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 3, 2, 2, 2].length) (baseStart_1482944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1482944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1482944 prefixEnd_1482944 := by exact prefixLift 1482944
  have htrace : WordTrace (prefixWord ++ tailWord_1482944) baseStart_1482944 baseEnd_1482944 := by
    simpa [prefixWord, tailWord_1482944, baseEnd_1482944] using wordTrace_append hprefix tailTrace_1482944
  have hstable : (prefixWord ++ tailWord_1482944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482944).length < 2 ^ (prefixWord ++ tailWord_1482944).sum := by decide
  have hdescent : baseEnd_1482944 < baseStart_1482944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483013 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 1, 3, 6]
def baseStart_1483013 : Nat := 118140960795 + 1483013 * 2 ^ 59
def prefixEnd_1483013 : Nat := 4983230072969 + 3 ^ 40 * 1483013 * 2
def baseEnd_1483013 : Nat := 761498485866311438517253

theorem tailTrace_1483013 : CollatzResearch.WordTrace tailWord_1483013 prefixEnd_1483013 761498485866311438517253 := by
  unfold tailWord_1483013
  simp only [CollatzResearch.WordTrace]
  refine ⟨54089927776304654300981693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36059951850869769533987795 54089927776304654300981693)
  ·
    refine ⟨20283722916114245362868135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54089927776304654300981693 20283722916114245362868135)
    ·
      refine ⟨30425584374171368044302203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20283722916114245362868135 30425584374171368044302203)
      ·
        refine ⟨45638376561257052066453305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30425584374171368044302203 45638376561257052066453305)
        ·
          refine ⟨34228782420942789049839979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45638376561257052066453305 34228782420942789049839979)
          ·
            refine ⟨51343173631414183574759969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34228782420942789049839979 51343173631414183574759969)
            ·
              refine ⟨38507380223560637681069977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51343173631414183574759969 38507380223560637681069977)
              ·
                refine ⟨28880535167670478260802483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38507380223560637681069977 28880535167670478260802483)
                ·
                  refine ⟨43320802751505717391203725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28880535167670478260802483 43320802751505717391203725)
                  ·
                    refine ⟨16245301031814644021701397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43320802751505717391203725 16245301031814644021701397)
                    ·
                      refine ⟨761498485866311438517253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16245301031814644021701397 761498485866311438517253)
                      ·
                        rfl

theorem cell23_1483013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_1483013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1483013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1483013 prefixEnd_1483013 := by exact prefixLift 1483013
  have htrace : WordTrace (prefixWord ++ tailWord_1483013) baseStart_1483013 baseEnd_1483013 := by
    simpa [prefixWord, tailWord_1483013, baseEnd_1483013] using wordTrace_append hprefix tailTrace_1483013
  have hstable : (prefixWord ++ tailWord_1483013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483013).length < 2 ^ (prefixWord ++ tailWord_1483013).sum := by decide
  have hdescent : baseEnd_1483013 < baseStart_1483013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483020 : List Nat := [2, 2, 1, 2, 2, 2, 1, 3, 1, 4, 3]
def baseStart_1483020 : Nat := 118140960795 + 1483020 * 2 ^ 59
def prefixEnd_1483020 : Nat := 4983230072969 + 3 ^ 40 * 1483020 * 2
def baseEnd_1483020 : Nat := 761502080230892911129721

theorem tailTrace_1483020 : CollatzResearch.WordTrace tailWord_1483020 prefixEnd_1483020 761502080230892911129721 := by
  unfold tailWord_1483020
  simp only [CollatzResearch.WordTrace]
  refine ⟨27045091543639647248243257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36060122058186196330991009 27045091543639647248243257)
  ·
    refine ⟨20283818657729735436182443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27045091543639647248243257 20283818657729735436182443)
    ·
      refine ⟨30425727986594603154273665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20283818657729735436182443 30425727986594603154273665)
      ·
        refine ⟨22819295989945952365705249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30425727986594603154273665 22819295989945952365705249)
        ·
          refine ⟨17114471992459464274278937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22819295989945952365705249 17114471992459464274278937)
          ·
            refine ⟨12835853994344598205709203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17114471992459464274278937 12835853994344598205709203)
            ·
              refine ⟨19253780991516897308563805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12835853994344598205709203 19253780991516897308563805)
              ·
                refine ⟨7220167871818836490711427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19253780991516897308563805 7220167871818836490711427)
                ·
                  refine ⟨10830251807728254736067141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7220167871818836490711427 10830251807728254736067141)
                  ·
                    refine ⟨2030672213949047763012589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10830251807728254736067141 2030672213949047763012589)
                    ·
                      refine ⟨761502080230892911129721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2030672213949047763012589 761502080230892911129721)
                      ·
                        rfl

theorem cell23_1483020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 1, 4, 3].length) (baseStart_1483020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1483020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1483020 prefixEnd_1483020 := by exact prefixLift 1483020
  have htrace : WordTrace (prefixWord ++ tailWord_1483020) baseStart_1483020 baseEnd_1483020 := by
    simpa [prefixWord, tailWord_1483020, baseEnd_1483020] using wordTrace_append hprefix tailTrace_1483020
  have hstable : (prefixWord ++ tailWord_1483020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483020).length < 2 ^ (prefixWord ++ tailWord_1483020).sum := by decide
  have hdescent : baseEnd_1483020 < baseStart_1483020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483040 : List Nat := [2, 1, 1, 5, 2, 1, 2, 1, 8]
def baseStart_1483040 : Nat := 118140960795 + 1483040 * 2 ^ 59
def prefixEnd_1483040 : Nat := 4983230072969 + 3 ^ 40 * 1483040 * 2
def baseEnd_1483040 : Nat := 84612483315998092542181

theorem tailTrace_1483040 : CollatzResearch.WordTrace tailWord_1483040 prefixEnd_1483040 84612483315998092542181 := by
  unfold tailWord_1483040
  simp only [CollatzResearch.WordTrace]
  refine ⟨27045456273603418956107287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36060608364804558608143049 27045456273603418956107287)
  ·
    refine ⟨40568184410405128434160931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27045456273603418956107287 40568184410405128434160931)
    ·
      refine ⟨60852276615607692651241397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40568184410405128434160931 60852276615607692651241397)
      ·
        refine ⟨5704900932713221186053881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60852276615607692651241397 5704900932713221186053881)
        ·
          refine ⟨4278675699534915889540411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5704900932713221186053881 4278675699534915889540411)
          ·
            refine ⟨6418013549302373834310617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4278675699534915889540411 6418013549302373834310617)
            ·
              refine ⟨4813510161976780375732963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6418013549302373834310617 4813510161976780375732963)
              ·
                refine ⟨7220265242965170563599445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4813510161976780375732963 7220265242965170563599445)
                ·
                  refine ⟨84612483315998092542181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7220265242965170563599445 84612483315998092542181)
                  ·
                    rfl

theorem cell23_1483040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 8].length) (baseStart_1483040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1483040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1483040 prefixEnd_1483040 := by exact prefixLift 1483040
  have htrace : WordTrace (prefixWord ++ tailWord_1483040) baseStart_1483040 baseEnd_1483040 := by
    simpa [prefixWord, tailWord_1483040, baseEnd_1483040] using wordTrace_append hprefix tailTrace_1483040
  have hstable : (prefixWord ++ tailWord_1483040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483040).length < 2 ^ (prefixWord ++ tailWord_1483040).sum := by decide
  have hdescent : baseEnd_1483040 < baseStart_1483040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483044 : List Nat := [2, 3, 1, 3, 1, 4, 1, 1, 3, 4]
def baseStart_1483044 : Nat := 118140960795 + 1483044 * 2 ^ 59
def prefixEnd_1483044 : Nat := 4983230072969 + 3 ^ 40 * 1483044 * 2
def baseEnd_1483044 : Nat := 253838134588866939076537

theorem tailTrace_1483044 : CollatzResearch.WordTrace tailWord_1483044 prefixEnd_1483044 253838134588866939076537 := by
  unfold tailWord_1483044
  simp only [CollatzResearch.WordTrace]
  refine ⟨27045529219596173297680093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36060705626128231063573457 27045529219596173297680093)
  ·
    refine ⟨10142073457348564986630035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27045529219596173297680093 10142073457348564986630035)
    ·
      refine ⟨15213110186022847479945053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10142073457348564986630035 15213110186022847479945053)
      ·
        refine ⟨5704916319758567804979395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15213110186022847479945053 5704916319758567804979395)
        ·
          refine ⟨8557374479637851707469093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5704916319758567804979395 8557374479637851707469093)
          ·
            refine ⟨1604507714932097195150455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8557374479637851707469093 1604507714932097195150455)
            ·
              refine ⟨2406761572398145792725683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1604507714932097195150455 2406761572398145792725683)
              ·
                refine ⟨3610142358597218689088525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2406761572398145792725683 3610142358597218689088525)
                ·
                  refine ⟨1353803384473957008408197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3610142358597218689088525 1353803384473957008408197)
                  ·
                    refine ⟨253838134588866939076537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1353803384473957008408197 253838134588866939076537)
                    ·
                      rfl

theorem cell23_1483044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 3, 4].length) (baseStart_1483044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1483044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1483044 prefixEnd_1483044 := by exact prefixLift 1483044
  have htrace : WordTrace (prefixWord ++ tailWord_1483044) baseStart_1483044 baseEnd_1483044 := by
    simpa [prefixWord, tailWord_1483044, baseEnd_1483044] using wordTrace_append hprefix tailTrace_1483044
  have hstable : (prefixWord ++ tailWord_1483044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483044).length < 2 ^ (prefixWord ++ tailWord_1483044).sum := by decide
  have hdescent : baseEnd_1483044 < baseStart_1483044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483057 : List Nat := [1, 2, 2, 3, 4, 1, 1, 3, 6]
def baseStart_1483057 : Nat := 118140960795 + 1483057 * 2 ^ 59
def prefixEnd_1483057 : Nat := 4983230072969 + 3 ^ 40 * 1483057 * 2
def baseEnd_1483057 : Nat := 84613453223901029596339

theorem tailTrace_1483057 : CollatzResearch.WordTrace tailWord_1483057 prefixEnd_1483057 84613453223901029596339 := by
  unfold tailWord_1483057
  simp only [CollatzResearch.WordTrace]
  refine ⟨54091532588145249815583425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36061021725430166543722283 54091532588145249815583425)
  ·
    refine ⟨40568649441108937361687569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54091532588145249815583425 40568649441108937361687569)
    ·
      refine ⟨30426487080831703021265677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40568649441108937361687569 30426487080831703021265677)
      ·
        refine ⟨11409932655311888632974629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30426487080831703021265677 11409932655311888632974629)
        ·
          refine ⟨2139362372870979118682743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11409932655311888632974629 2139362372870979118682743)
          ·
            refine ⟨3209043559306468678024115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2139362372870979118682743 3209043559306468678024115)
            ·
              refine ⟨4813565338959703017036173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3209043559306468678024115 4813565338959703017036173)
              ·
                refine ⟨1805087002109888631388565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4813565338959703017036173 1805087002109888631388565)
                ·
                  refine ⟨84613453223901029596339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1805087002109888631388565 84613453223901029596339)
                  ·
                    rfl

theorem cell23_1483057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 3, 6].length) (baseStart_1483057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1483057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1483057 prefixEnd_1483057 := by exact prefixLift 1483057
  have htrace : WordTrace (prefixWord ++ tailWord_1483057) baseStart_1483057 baseEnd_1483057 := by
    simpa [prefixWord, tailWord_1483057, baseEnd_1483057] using wordTrace_append hprefix tailTrace_1483057
  have hstable : (prefixWord ++ tailWord_1483057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483057).length < 2 ^ (prefixWord ++ tailWord_1483057).sum := by decide
  have hdescent : baseEnd_1483057 < baseStart_1483057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483117 : List Nat := [1, 5, 1, 1, 1, 2, 4, 1, 1, 6]
def baseStart_1483117 : Nat := 118140960795 + 1483117 * 2 ^ 59
def prefixEnd_1483117 : Nat := 4983230072969 + 3 ^ 40 * 1483117 * 2
def baseEnd_1483117 : Nat := 253850629284793010538925

theorem tailTrace_1483117 : CollatzResearch.WordTrace tailWord_1483117 prefixEnd_1483117 253850629284793010538925 := by
  unfold tailWord_1483117
  simp only [CollatzResearch.WordTrace]
  refine ⟨54093720967927880062767605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36062480645285253375178403 54093720967927880062767605)
  ·
    refine ⟨5071286340743238755884463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54093720967927880062767605 5071286340743238755884463)
    ·
      refine ⟨7606929511114858133826695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5071286340743238755884463 7606929511114858133826695)
      ·
        refine ⟨11410394266672287200740043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7606929511114858133826695 11410394266672287200740043)
        ·
          refine ⟨17115591400008430801110065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11410394266672287200740043 17115591400008430801110065)
          ·
            refine ⟨12836693550006323100832549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17115591400008430801110065 12836693550006323100832549)
            ·
              refine ⟨2406880040626185581406103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12836693550006323100832549 2406880040626185581406103)
              ·
                refine ⟨3610320060939278372109155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2406880040626185581406103 3610320060939278372109155)
                ·
                  refine ⟨5415480091408917558163733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3610320060939278372109155 5415480091408917558163733)
                  ·
                    refine ⟨253850629284793010538925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5415480091408917558163733 253850629284793010538925)
                    ·
                      rfl

theorem cell23_1483117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_1483117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1483117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1483117 prefixEnd_1483117 := by exact prefixLift 1483117
  have htrace : WordTrace (prefixWord ++ tailWord_1483117) baseStart_1483117 baseEnd_1483117 := by
    simpa [prefixWord, tailWord_1483117, baseEnd_1483117] using wordTrace_append hprefix tailTrace_1483117
  have hstable : (prefixWord ++ tailWord_1483117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483117).length < 2 ^ (prefixWord ++ tailWord_1483117).sum := by decide
  have hdescent : baseEnd_1483117 < baseStart_1483117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483144 : List Nat := [2, 1, 3, 3, 1, 1, 3, 3, 1, 2, 3]
def baseStart_1483144 : Nat := 118140960795 + 1483144 * 2 ^ 59
def prefixEnd_1483144 : Nat := 4983230072969 + 3 ^ 40 * 1483144 * 2
def baseEnd_1483144 : Nat := 761565751832050425979151

theorem tailTrace_1483144 : CollatzResearch.WordTrace tailWord_1483144 prefixEnd_1483144 761565751832050425979151 := by
  unfold tailWord_1483144
  simp only [CollatzResearch.WordTrace]
  refine ⟨27047352869415031837000243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36063137159220042449333657 27047352869415031837000243)
  ·
    refine ⟨40571029304122547755500365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27047352869415031837000243 40571029304122547755500365)
    ·
      refine ⟨15214135989045955408312637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40571029304122547755500365 15214135989045955408312637)
      ·
        refine ⟨5705300995892233278117239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15214135989045955408312637 5705300995892233278117239)
        ·
          refine ⟨8557951493838349917175859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5705300995892233278117239 8557951493838349917175859)
          ·
            refine ⟨12836927240757524875763789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8557951493838349917175859 12836927240757524875763789)
            ·
              refine ⟨4813847715284071828411421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12836927240757524875763789 4813847715284071828411421)
              ·
                refine ⟨1805192893231526935654283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4813847715284071828411421 1805192893231526935654283)
                ·
                  refine ⟨2707789339847290403481425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1805192893231526935654283 2707789339847290403481425)
                  ·
                    refine ⟨2030842004885467802611069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2707789339847290403481425 2030842004885467802611069)
                    ·
                      refine ⟨761565751832050425979151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2030842004885467802611069 761565751832050425979151)
                      ·
                        rfl

theorem cell23_1483144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_1483144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1483144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1483144 prefixEnd_1483144 := by exact prefixLift 1483144
  have htrace : WordTrace (prefixWord ++ tailWord_1483144) baseStart_1483144 baseEnd_1483144 := by
    simpa [prefixWord, tailWord_1483144, baseEnd_1483144] using wordTrace_append hprefix tailTrace_1483144
  have hstable : (prefixWord ++ tailWord_1483144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483144).length < 2 ^ (prefixWord ++ tailWord_1483144).sum := by decide
  have hdescent : baseEnd_1483144 < baseStart_1483144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483181 : List Nat := [1, 5, 2, 2, 2, 2, 2, 7]
def baseStart_1483181 : Nat := 118140960795 + 1483181 * 2 ^ 59
def prefixEnd_1483181 : Nat := 4983230072969 + 3 ^ 40 * 1483181 * 2
def baseEnd_1483181 : Nat := 28206842615417288193203

theorem tailTrace_1483181 : CollatzResearch.WordTrace tailWord_1483181 prefixEnd_1483181 28206842615417288193203 := by
  unfold tailWord_1483181
  simp only [CollatzResearch.WordTrace]
  refine ⟨54096055239696018993097397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36064036826464012662064931 54096055239696018993097397)
  ·
    refine ⟨5071505178721501780602881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54096055239696018993097397 5071505178721501780602881)
    ·
      refine ⟨3803628884041126335452161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5071505178721501780602881 3803628884041126335452161)
      ·
        refine ⟨2852721663030844751589121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3803628884041126335452161 2852721663030844751589121)
        ·
          refine ⟨2139541247273133563691841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2852721663030844751589121 2139541247273133563691841)
          ·
            refine ⟨1604655935454850172768881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2139541247273133563691841 1604655935454850172768881)
            ·
              refine ⟨1203491951591137629576661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1604655935454850172768881 1203491951591137629576661)
              ·
                refine ⟨28206842615417288193203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1203491951591137629576661 28206842615417288193203)
                ·
                  rfl

theorem cell23_1483181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 7].length) (baseStart_1483181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1483181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1483181 prefixEnd_1483181 := by exact prefixLift 1483181
  have htrace : WordTrace (prefixWord ++ tailWord_1483181) baseStart_1483181 baseEnd_1483181 := by
    simpa [prefixWord, tailWord_1483181, baseEnd_1483181] using wordTrace_append hprefix tailTrace_1483181
  have hstable : (prefixWord ++ tailWord_1483181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483181).length < 2 ^ (prefixWord ++ tailWord_1483181).sum := by decide
  have hdescent : baseEnd_1483181 < baseStart_1483181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483235 : List Nat := [1, 1, 1, 6, 4, 1, 1, 2, 1, 3, 2]
def baseStart_1483235 : Nat := 118140960795 + 1483235 * 2 ^ 59
def prefixEnd_1483235 : Nat := 4983230072969 + 3 ^ 40 * 1483235 * 2
def baseEnd_1483235 : Nat := 761612478571609569941233

theorem tailTrace_1483235 : CollatzResearch.WordTrace tailWord_1483235 prefixEnd_1483235 761612478571609569941233 := by
  unfold tailWord_1483235
  simp only [CollatzResearch.WordTrace]
  refine ⟨54098024781500386215563159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36065349854333590810375439 54098024781500386215563159)
  ·
    refine ⟨81147037172250579323344739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54098024781500386215563159 81147037172250579323344739)
    ·
      refine ⟨121720555758375868985017109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81147037172250579323344739 121720555758375868985017109)
      ·
        refine ⟨5705651051173868858672677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 121720555758375868985017109 5705651051173868858672677)
        ·
          refine ⟨1069809572095100411001127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5705651051173868858672677 1069809572095100411001127)
          ·
            refine ⟨1604714358142650616501691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1069809572095100411001127 1604714358142650616501691)
            ·
              refine ⟨2407071537213975924752537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1604714358142650616501691 2407071537213975924752537)
              ·
                refine ⟨1805303652910481943564403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2407071537213975924752537 1805303652910481943564403)
                ·
                  refine ⟨2707955479365722915346605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1805303652910481943564403 2707955479365722915346605)
                  ·
                    refine ⟨1015483304762146093254977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2707955479365722915346605 1015483304762146093254977)
                    ·
                      refine ⟨761612478571609569941233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1015483304762146093254977 761612478571609569941233)
                      ·
                        rfl

theorem cell23_1483235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_1483235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1483235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1483235 prefixEnd_1483235 := by exact prefixLift 1483235
  have htrace : WordTrace (prefixWord ++ tailWord_1483235) baseStart_1483235 baseEnd_1483235 := by
    simpa [prefixWord, tailWord_1483235, baseEnd_1483235] using wordTrace_append hprefix tailTrace_1483235
  have hstable : (prefixWord ++ tailWord_1483235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483235).length < 2 ^ (prefixWord ++ tailWord_1483235).sum := by decide
  have hdescent : baseEnd_1483235 < baseStart_1483235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483247 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 4, 3, 3]
def baseStart_1483247 : Nat := 118140960795 + 1483247 * 2 ^ 59
def prefixEnd_1483247 : Nat := 4983230072969 + 3 ^ 40 * 1483247 * 2
def baseEnd_1483247 : Nat := 761618640339463522991177

theorem tailTrace_1483247 : CollatzResearch.WordTrace tailWord_1483247 prefixEnd_1483247 761618640339463522991177 := by
  unfold tailWord_1483247
  simp only [CollatzResearch.WordTrace]
  refine ⟨54098462457456912264999995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36065641638304608176666663 54098462457456912264999995)
  ·
    refine ⟨81147693686185368397499993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54098462457456912264999995 81147693686185368397499993)
    ·
      refine ⟨60860770264639026298124995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81147693686185368397499993 60860770264639026298124995)
      ·
        refine ⟨91291155396958539447187493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60860770264639026298124995 91291155396958539447187493)
        ·
          refine ⟨17117091636929726146347655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91291155396958539447187493 17117091636929726146347655)
          ·
            refine ⟨25675637455394589219521483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17117091636929726146347655 25675637455394589219521483)
            ·
              refine ⟨38513456183091883829282225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25675637455394589219521483 38513456183091883829282225)
              ·
                refine ⟨28885092137318912871961669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38513456183091883829282225 28885092137318912871961669)
                ·
                  refine ⟨5415954775747296163492813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28885092137318912871961669 5415954775747296163492813)
                  ·
                    refine ⟨2030983040905236061309805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5415954775747296163492813 2030983040905236061309805)
                    ·
                      refine ⟨761618640339463522991177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2030983040905236061309805 761618640339463522991177)
                      ·
                        rfl

theorem cell23_1483247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 3, 3].length) (baseStart_1483247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1483247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1483247 prefixEnd_1483247 := by exact prefixLift 1483247
  have htrace : WordTrace (prefixWord ++ tailWord_1483247) baseStart_1483247 baseEnd_1483247 := by
    simpa [prefixWord, tailWord_1483247, baseEnd_1483247] using wordTrace_append hprefix tailTrace_1483247
  have hstable : (prefixWord ++ tailWord_1483247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483247).length < 2 ^ (prefixWord ++ tailWord_1483247).sum := by decide
  have hdescent : baseEnd_1483247 < baseStart_1483247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483267 : List Nat := [1, 1, 1, 3, 2, 1, 3, 4, 2, 5]
def baseStart_1483267 : Nat := 118140960795 + 1483267 * 2 ^ 59
def prefixEnd_1483267 : Nat := 4983230072969 + 3 ^ 40 * 1483267 * 2
def baseEnd_1483267 : Nat := 253876303317517814913695

theorem tailTrace_1483267 : CollatzResearch.WordTrace tailWord_1483267 prefixEnd_1483267 253876303317517814913695 := by
  unfold tailWord_1483267
  simp only [CollatzResearch.WordTrace]
  refine ⟨54099191917384455680728055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36066127944922970453818703 54099191917384455680728055)
  ·
    refine ⟨81148787876076683521092083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54099191917384455680728055 81148787876076683521092083)
    ·
      refine ⟨121723181814115025281638125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81148787876076683521092083 121723181814115025281638125)
      ·
        refine ⟨45646193180293134480614297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121723181814115025281638125 45646193180293134480614297)
        ·
          refine ⟨34234644885219850860460723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45646193180293134480614297 34234644885219850860460723)
          ·
            refine ⟨51351967327829776290691085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34234644885219850860460723 51351967327829776290691085)
            ·
              refine ⟨19256987747936166109009157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51351967327829776290691085 19256987747936166109009157)
              ·
                refine ⟨3610685202738031145439217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19256987747936166109009157 3610685202738031145439217)
                ·
                  refine ⟨2708013902053523359079413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3610685202738031145439217 2708013902053523359079413)
                  ·
                    refine ⟨253876303317517814913695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2708013902053523359079413 253876303317517814913695)
                    ·
                      rfl

theorem cell23_1483267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 2, 5].length) (baseStart_1483267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1483267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1483267 prefixEnd_1483267 := by exact prefixLift 1483267
  have htrace : WordTrace (prefixWord ++ tailWord_1483267) baseStart_1483267 baseEnd_1483267 := by
    simpa [prefixWord, tailWord_1483267, baseEnd_1483267] using wordTrace_append hprefix tailTrace_1483267
  have hstable : (prefixWord ++ tailWord_1483267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483267).length < 2 ^ (prefixWord ++ tailWord_1483267).sum := by decide
  have hdescent : baseEnd_1483267 < baseStart_1483267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483271 : List Nat := [1, 1, 4, 3, 3, 1, 1, 4, 5]
def baseStart_1483271 : Nat := 118140960795 + 1483271 * 2 ^ 59
def prefixEnd_1483271 : Nat := 4983230072969 + 3 ^ 40 * 1483271 * 2
def baseEnd_1483271 : Nat := 84625662652796825454563

theorem tailTrace_1483271 : CollatzResearch.WordTrace tailWord_1483271 prefixEnd_1483271 84625662652796825454563 := by
  unfold tailWord_1483271
  simp only [CollatzResearch.WordTrace]
  refine ⟨54099337809369964363873667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36066225206246642909249111 54099337809369964363873667)
  ·
    refine ⟨81149006714054946545810501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54099337809369964363873667 81149006714054946545810501)
    ·
      refine ⟨15215438758885302477339469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81149006714054946545810501 15215438758885302477339469)
      ·
        refine ⟨5705789534581988429002301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15215438758885302477339469 5705789534581988429002301)
        ·
          refine ⟨2139671075468245660875863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5705789534581988429002301 2139671075468245660875863)
          ·
            refine ⟨3209506613202368491313795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2139671075468245660875863 3209506613202368491313795)
            ·
              refine ⟨4814259919803552736970693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3209506613202368491313795 4814259919803552736970693)
              ·
                refine ⟨902673734963166138182005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4814259919803552736970693 902673734963166138182005)
                ·
                  refine ⟨84625662652796825454563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 902673734963166138182005 84625662652796825454563)
                  ·
                    rfl

theorem cell23_1483271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 4, 5].length) (baseStart_1483271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1483271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1483271 prefixEnd_1483271 := by exact prefixLift 1483271
  have htrace : WordTrace (prefixWord ++ tailWord_1483271) baseStart_1483271 baseEnd_1483271 := by
    simpa [prefixWord, tailWord_1483271, baseEnd_1483271] using wordTrace_append hprefix tailTrace_1483271
  have hstable : (prefixWord ++ tailWord_1483271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483271).length < 2 ^ (prefixWord ++ tailWord_1483271).sum := by decide
  have hdescent : baseEnd_1483271 < baseStart_1483271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483274 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 1, 7, 2]
def baseStart_1483274 : Nat := 118140960795 + 1483274 * 2 ^ 59
def prefixEnd_1483274 : Nat := 4983230072969 + 3 ^ 40 * 1483274 * 2
def baseEnd_1483274 : Nat := 761632504317134917353553

theorem tailTrace_1483274 : CollatzResearch.WordTrace tailWord_1483274 prefixEnd_1483274 761632504317134917353553 := by
  unfold tailWord_1483274
  simp only [CollatzResearch.WordTrace]
  refine ⟨13524861807089773969058219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36066298152239397250821917 13524861807089773969058219)
  ·
    refine ⟨20287292710634660953587329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13524861807089773969058219 20287292710634660953587329)
    ·
      refine ⟨15215469532975995715190497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20287292710634660953587329 15215469532975995715190497)
      ·
        refine ⟨11411602149731996786392873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15215469532975995715190497 11411602149731996786392873)
        ·
          refine ⟨8558701612298997589794655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11411602149731996786392873 8558701612298997589794655)
          ·
            refine ⟨12838052418448496384691983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8558701612298997589794655 12838052418448496384691983)
            ·
              refine ⟨19257078627672744577037975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12838052418448496384691983 19257078627672744577037975)
              ·
                refine ⟨28885617941509116865556963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19257078627672744577037975 28885617941509116865556963)
                ·
                  refine ⟨43328426912263675298335445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28885617941509116865556963 43328426912263675298335445)
                  ·
                    refine ⟨1015510005756179889804737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43328426912263675298335445 1015510005756179889804737)
                    ·
                      refine ⟨761632504317134917353553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1015510005756179889804737 761632504317134917353553)
                      ·
                        rfl

theorem cell23_1483274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 1, 7, 2].length) (baseStart_1483274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1483274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1483274 prefixEnd_1483274 := by exact prefixLift 1483274
  have htrace : WordTrace (prefixWord ++ tailWord_1483274) baseStart_1483274 baseEnd_1483274 := by
    simpa [prefixWord, tailWord_1483274, baseEnd_1483274] using wordTrace_append hprefix tailTrace_1483274
  have hstable : (prefixWord ++ tailWord_1483274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483274).length < 2 ^ (prefixWord ++ tailWord_1483274).sum := by decide
  have hdescent : baseEnd_1483274 < baseStart_1483274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483317 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 1, 3, 6]
def baseStart_1483317 : Nat := 118140960795 + 1483317 * 2 ^ 59
def prefixEnd_1483317 : Nat := 4983230072969 + 3 ^ 40 * 1483317 * 2
def baseEnd_1483317 : Nat := 761654583985278249115855

theorem tailTrace_1483317 : CollatzResearch.WordTrace tailWord_1483317 prefixEnd_1483317 761654583985278249115855 := by
  unfold tailWord_1483317
  simp only [CollatzResearch.WordTrace]
  refine ⟨54101015567203314220048205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36067343711468876146698803 54101015567203314220048205)
  ·
    refine ⟨20287880837701242832518077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54101015567203314220048205 20287880837701242832518077)
    ·
      refine ⟨7607955314137966062194279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20287880837701242832518077 7607955314137966062194279)
      ·
        refine ⟨11411932971206949093291419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7607955314137966062194279 11411932971206949093291419)
        ·
          refine ⟨17117899456810423639937129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11411932971206949093291419 17117899456810423639937129)
          ·
            refine ⟨12838424592607817729952847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17117899456810423639937129 12838424592607817729952847)
            ·
              refine ⟨19257636888911726594929271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12838424592607817729952847 19257636888911726594929271)
              ·
                refine ⟨28886455333367589892393907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19257636888911726594929271 28886455333367589892393907)
                ·
                  refine ⟨43329683000051384838590861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28886455333367589892393907 43329683000051384838590861)
                  ·
                    refine ⟨16248631125019269314471573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43329683000051384838590861 16248631125019269314471573)
                    ·
                      refine ⟨761654583985278249115855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16248631125019269314471573 761654583985278249115855)
                      ·
                        rfl

theorem cell23_1483317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_1483317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1483317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1483317 prefixEnd_1483317 := by exact prefixLift 1483317
  have htrace : WordTrace (prefixWord ++ tailWord_1483317) baseStart_1483317 baseEnd_1483317 := by
    simpa [prefixWord, tailWord_1483317, baseEnd_1483317] using wordTrace_append hprefix tailTrace_1483317
  have hstable : (prefixWord ++ tailWord_1483317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483317).length < 2 ^ (prefixWord ++ tailWord_1483317).sum := by decide
  have hdescent : baseEnd_1483317 < baseStart_1483317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483327 : List Nat := [1, 1, 2, 2, 3, 2, 3, 1, 8]
def baseStart_1483327 : Nat := 118140960795 + 1483327 * 2 ^ 59
def prefixEnd_1483327 : Nat := 4983230072969 + 3 ^ 40 * 1483327 * 2
def baseEnd_1483327 : Nat := 84628857643535912221201

theorem tailTrace_1483327 : CollatzResearch.WordTrace tailWord_1483327 prefixEnd_1483327 84628857643535912221201 := by
  unfold tailWord_1483327
  simp only [CollatzResearch.WordTrace]
  refine ⟨54101380297167085927912235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36067586864778057285274823 54101380297167085927912235)
  ·
    refine ⟨81152070445750628891868353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54101380297167085927912235 81152070445750628891868353)
    ·
      refine ⟨60864052834312971668901265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81152070445750628891868353 60864052834312971668901265)
      ·
        refine ⟨45648039625734728751675949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60864052834312971668901265 45648039625734728751675949)
        ·
          refine ⟨17118014859650523281878481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45648039625734728751675949 17118014859650523281878481)
          ·
            refine ⟨12838511144737892461408861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17118014859650523281878481 12838511144737892461408861)
            ·
              refine ⟨4814441679276709673028323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12838511144737892461408861 4814441679276709673028323)
              ·
                refine ⟨7221662518915064509542485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4814441679276709673028323 7221662518915064509542485)
                ·
                  refine ⟨84628857643535912221201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7221662518915064509542485 84628857643535912221201)
                  ·
                    rfl

theorem cell23_1483327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 8].length) (baseStart_1483327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1483327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1483327 prefixEnd_1483327 := by exact prefixLift 1483327
  have htrace : WordTrace (prefixWord ++ tailWord_1483327) baseStart_1483327 baseEnd_1483327 := by
    simpa [prefixWord, tailWord_1483327, baseEnd_1483327] using wordTrace_append hprefix tailTrace_1483327
  have hstable : (prefixWord ++ tailWord_1483327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483327).length < 2 ^ (prefixWord ++ tailWord_1483327).sum := by decide
  have hdescent : baseEnd_1483327 < baseStart_1483327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483341 : List Nat := [1, 6, 1, 1, 2, 1, 1, 2, 1, 4, 3]
def baseStart_1483341 : Nat := 118140960795 + 1483341 * 2 ^ 59
def prefixEnd_1483341 : Nat := 4983230072969 + 3 ^ 40 * 1483341 * 2
def baseEnd_1483341 : Nat := 761666907520986155215745

theorem tailTrace_1483341 : CollatzResearch.WordTrace tailWord_1483341 prefixEnd_1483341 761666907520986155215745 := by
  unfold tailWord_1483341
  simp only [CollatzResearch.WordTrace]
  refine ⟨54101890919116366318921877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36067927279410910879281251 54101890919116366318921877)
  ·
    refine ⟨2536026136833579671199463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 54101890919116366318921877 2536026136833579671199463)
    ·
      refine ⟨3804039205250369506799195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2536026136833579671199463 3804039205250369506799195)
      ·
        refine ⟨5706058807875554260198793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3804039205250369506799195 5706058807875554260198793)
        ·
          refine ⟨4279544105906665695149095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5706058807875554260198793 4279544105906665695149095)
          ·
            refine ⟨6419316158859998542723643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4279544105906665695149095 6419316158859998542723643)
            ·
              refine ⟨9628974238289997814085465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6419316158859998542723643 9628974238289997814085465)
              ·
                refine ⟨7221730678717498360564099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9628974238289997814085465 7221730678717498360564099)
                ·
                  refine ⟨10832596018076247540846149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7221730678717498360564099 10832596018076247540846149)
                  ·
                    refine ⟨2031111753389296413908653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10832596018076247540846149 2031111753389296413908653)
                    ·
                      refine ⟨761666907520986155215745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2031111753389296413908653 761666907520986155215745)
                      ·
                        rfl

theorem cell23_1483341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_1483341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1483341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1483341 prefixEnd_1483341 := by exact prefixLift 1483341
  have htrace : WordTrace (prefixWord ++ tailWord_1483341) baseStart_1483341 baseEnd_1483341 := by
    simpa [prefixWord, tailWord_1483341, baseEnd_1483341] using wordTrace_append hprefix tailTrace_1483341
  have hstable : (prefixWord ++ tailWord_1483341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483341).length < 2 ^ (prefixWord ++ tailWord_1483341).sum := by decide
  have hdescent : baseEnd_1483341 < baseStart_1483341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483365 : List Nat := [1, 3, 1, 3, 4, 2, 1, 3, 1, 4]
def baseStart_1483365 : Nat := 118140960795 + 1483365 * 2 ^ 59
def prefixEnd_1483365 : Nat := 4983230072969 + 3 ^ 40 * 1483365 * 2
def baseEnd_1483365 : Nat := 253893077018898020438545

theorem tailTrace_1483365 : CollatzResearch.WordTrace tailWord_1483365 prefixEnd_1483365 253893077018898020438545 := by
  unfold tailWord_1483365
  simp only [CollatzResearch.WordTrace]
  refine ⟨54102766271029418417795549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36068510847352945611863699 54102766271029418417795549)
  ·
    refine ⟨20288537351636031906673331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54102766271029418417795549 20288537351636031906673331)
    ·
      refine ⟨30432806027454047860009997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20288537351636031906673331 30432806027454047860009997)
      ·
        refine ⟨11412302260295267947503749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30432806027454047860009997 11412302260295267947503749)
        ·
          refine ⟨2139806673805362740156953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11412302260295267947503749 2139806673805362740156953)
          ·
            refine ⟨1604855005354022055117715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2139806673805362740156953 1604855005354022055117715)
            ·
              refine ⟨2407282508031033082676573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1604855005354022055117715 2407282508031033082676573)
              ·
                refine ⟨902730940511637406003715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2407282508031033082676573 902730940511637406003715)
                ·
                  refine ⟨1354096410767456109005573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 902730940511637406003715 1354096410767456109005573)
                  ·
                    refine ⟨253893077018898020438545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1354096410767456109005573 253893077018898020438545)
                    ·
                      rfl

theorem cell23_1483365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 3, 1, 4].length) (baseStart_1483365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1483365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1483365 prefixEnd_1483365 := by exact prefixLift 1483365
  have htrace : WordTrace (prefixWord ++ tailWord_1483365) baseStart_1483365 baseEnd_1483365 := by
    simpa [prefixWord, tailWord_1483365, baseEnd_1483365] using wordTrace_append hprefix tailTrace_1483365
  have hstable : (prefixWord ++ tailWord_1483365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483365).length < 2 ^ (prefixWord ++ tailWord_1483365).sum := by decide
  have hdescent : baseEnd_1483365 < baseStart_1483365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483382 : List Nat := [5, 1, 1, 2, 3, 1, 3, 2, 1, 4]
def baseStart_1483382 : Nat := 118140960795 + 1483382 * 2 ^ 59
def prefixEnd_1483382 : Nat := 4983230072969 + 3 ^ 40 * 1483382 * 2
def baseEnd_1483382 : Nat := 253895986742606831601019

theorem tailTrace_1483382 : CollatzResearch.WordTrace tailWord_1483382 prefixEnd_1483382 253895986742606831601019 := by
  unfold tailWord_1483382
  simp only [CollatzResearch.WordTrace]
  refine ⟨3381461644497989395072775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36068924207978553547442933 3381461644497989395072775)
  ·
    refine ⟨5072192466746984092609163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3381461644497989395072775 5072192466746984092609163)
    ·
      refine ⟨7608288700120476138913745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5072192466746984092609163 7608288700120476138913745)
      ·
        refine ⟨5706216525090357104185309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7608288700120476138913745 5706216525090357104185309)
        ·
          refine ⟨2139831196908883914069491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5706216525090357104185309 2139831196908883914069491)
          ·
            refine ⟨3209746795363325871104237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2139831196908883914069491 3209746795363325871104237)
            ·
              refine ⟨1203655048261247201664089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3209746795363325871104237 1203655048261247201664089)
              ·
                refine ⟨902741286195935401248067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1203655048261247201664089 902741286195935401248067)
                ·
                  refine ⟨1354111929293903101872101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 902741286195935401248067 1354111929293903101872101)
                  ·
                    refine ⟨253895986742606831601019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1354111929293903101872101 253895986742606831601019)
                    ·
                      rfl

theorem cell23_1483382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_1483382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1483382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1483382 prefixEnd_1483382 := by exact prefixLift 1483382
  have htrace : WordTrace (prefixWord ++ tailWord_1483382) baseStart_1483382 baseEnd_1483382 := by
    simpa [prefixWord, tailWord_1483382, baseEnd_1483382] using wordTrace_append hprefix tailTrace_1483382
  have hstable : (prefixWord ++ tailWord_1483382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483382).length < 2 ^ (prefixWord ++ tailWord_1483382).sum := by decide
  have hdescent : baseEnd_1483382 < baseStart_1483382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483387 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 5, 6]
def baseStart_1483387 : Nat := 118140960795 + 1483387 * 2 ^ 59
def prefixEnd_1483387 : Nat := 4983230072969 + 3 ^ 40 * 1483387 * 2
def baseEnd_1483387 : Nat := 253896842543697658413511

theorem tailTrace_1483387 : CollatzResearch.WordTrace tailWord_1483387 prefixEnd_1483387 253896842543697658413511 := by
  unfold tailWord_1483387
  simp only [CollatzResearch.WordTrace]
  refine ⟨54103568676949716175096415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36069045784633144116730943 54103568676949716175096415)
  ·
    refine ⟨81155353015424574262644623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54103568676949716175096415 81155353015424574262644623)
    ·
      refine ⟨121733029523136861393966935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81155353015424574262644623 121733029523136861393966935)
      ·
        refine ⟨182599544284705292090950403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121733029523136861393966935 182599544284705292090950403)
        ·
          refine ⟨273899316427057938136425605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182599544284705292090950403 273899316427057938136425605)
          ·
            refine ⟨51356121830073363400579801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 273899316427057938136425605 51356121830073363400579801)
            ·
              refine ⟨38517091372555022550434851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51356121830073363400579801 38517091372555022550434851)
              ·
                refine ⟨57775637058832533825652277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38517091372555022550434851 57775637058832533825652277)
                ·
                  refine ⟨5416465974265550046154901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57775637058832533825652277 5416465974265550046154901)
                  ·
                    refine ⟨253896842543697658413511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5416465974265550046154901 253896842543697658413511)
                    ·
                      rfl

theorem cell23_1483387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 6].length) (baseStart_1483387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1483387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1483387 prefixEnd_1483387 := by exact prefixLift 1483387
  have htrace : WordTrace (prefixWord ++ tailWord_1483387) baseStart_1483387 baseEnd_1483387 := by
    simpa [prefixWord, tailWord_1483387, baseEnd_1483387] using wordTrace_append hprefix tailTrace_1483387
  have hstable : (prefixWord ++ tailWord_1483387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483387).length < 2 ^ (prefixWord ++ tailWord_1483387).sum := by decide
  have hdescent : baseEnd_1483387 < baseStart_1483387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483388 : List Nat := [2, 2, 2, 1, 1, 2, 2, 6, 1, 1, 3]
def baseStart_1483388 : Nat := 118140960795 + 1483388 * 2 ^ 59
def prefixEnd_1483388 : Nat := 4983230072969 + 3 ^ 40 * 1483388 * 2
def baseEnd_1483388 : Nat := 761691041111747471328029

theorem tailTrace_1483388 : CollatzResearch.WordTrace tailWord_1483388 prefixEnd_1483388 761691041111747471328029 := by
  unfold tailWord_1483388
  simp only [CollatzResearch.WordTrace]
  refine ⟨27051802574973046672941409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36069070099964062230588545 27051802574973046672941409)
  ·
    refine ⟨20288851931229785004706057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27051802574973046672941409 20288851931229785004706057)
    ·
      refine ⟨15216638948422338753529543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20288851931229785004706057 15216638948422338753529543)
      ·
        refine ⟨22824958422633508130294315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15216638948422338753529543 22824958422633508130294315)
        ·
          refine ⟨34237437633950262195441473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22824958422633508130294315 34237437633950262195441473)
          ·
            refine ⟨25678078225462696646581105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34237437633950262195441473 25678078225462696646581105)
            ·
              refine ⟨19258558669097022484935829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25678078225462696646581105 19258558669097022484935829)
              ·
                refine ⟨902744937613922928981367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19258558669097022484935829 902744937613922928981367)
                ·
                  refine ⟨1354117406420884393472051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 902744937613922928981367 1354117406420884393472051)
                  ·
                    refine ⟨2031176109631326590208077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1354117406420884393472051 2031176109631326590208077)
                    ·
                      refine ⟨761691041111747471328029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2031176109631326590208077 761691041111747471328029)
                      ·
                        rfl

theorem cell23_1483388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 6, 1, 1, 3].length) (baseStart_1483388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1483388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1483388 prefixEnd_1483388 := by exact prefixLift 1483388
  have htrace : WordTrace (prefixWord ++ tailWord_1483388) baseStart_1483388 baseEnd_1483388 := by
    simpa [prefixWord, tailWord_1483388, baseEnd_1483388] using wordTrace_append hprefix tailTrace_1483388
  have hstable : (prefixWord ++ tailWord_1483388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483388).length < 2 ^ (prefixWord ++ tailWord_1483388).sum := by decide
  have hdescent : baseEnd_1483388 < baseStart_1483388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483404 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 6, 4]
def baseStart_1483404 : Nat := 118140960795 + 1483404 * 2 ^ 59
def prefixEnd_1483404 : Nat := 4983230072969 + 3 ^ 40 * 1483404 * 2
def baseEnd_1483404 : Nat := 253899752267406469575985

theorem tailTrace_1483404 : CollatzResearch.WordTrace tailWord_1483404 prefixEnd_1483404 253899752267406469575985 := by
  unfold tailWord_1483404
  simp only [CollatzResearch.WordTrace]
  refine ⟨27052094358944064039232633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36069459145258752052310177 27052094358944064039232633)
  ·
    refine ⟨20289070769208048029424475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27052094358944064039232633 20289070769208048029424475)
    ·
      refine ⟨30433606153812072044136713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20289070769208048029424475 30433606153812072044136713)
      ·
        refine ⟨22825204615359054033102535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30433606153812072044136713 22825204615359054033102535)
        ·
          refine ⟨34237806923038581049653803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22825204615359054033102535 34237806923038581049653803)
          ·
            refine ⟨51356710384557871574480705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34237806923038581049653803 51356710384557871574480705)
            ·
              refine ⟨38517532788418403680860529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51356710384557871574480705 38517532788418403680860529)
              ·
                refine ⟨28888149591313802760645397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38517532788418403680860529 28888149591313802760645397)
                ·
                  refine ⟨1354132012092834504405253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 28888149591313802760645397 1354132012092834504405253)
                  ·
                    refine ⟨253899752267406469575985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1354132012092834504405253 253899752267406469575985)
                    ·
                      rfl

theorem cell23_1483404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 6, 4].length) (baseStart_1483404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1483404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1483404 prefixEnd_1483404 := by exact prefixLift 1483404
  have htrace : WordTrace (prefixWord ++ tailWord_1483404) baseStart_1483404 baseEnd_1483404 := by
    simpa [prefixWord, tailWord_1483404, baseEnd_1483404] using wordTrace_append hprefix tailTrace_1483404
  have hstable : (prefixWord ++ tailWord_1483404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483404).length < 2 ^ (prefixWord ++ tailWord_1483404).sum := by decide
  have hdescent : baseEnd_1483404 < baseStart_1483404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483417 : List Nat := [1, 2, 1, 2, 1, 2, 3, 11]
def baseStart_1483417 : Nat := 118140960795 + 1483417 * 2 ^ 59
def prefixEnd_1483417 : Nat := 4983230072969 + 3 ^ 40 * 1483417 * 2
def baseEnd_1483417 : Nat := 28211330816693624365385

theorem tailTrace_1483417 : CollatzResearch.WordTrace tailWord_1483417 prefixEnd_1483417 28211330816693624365385 := by
  unfold tailWord_1483417
  simp only [CollatzResearch.WordTrace]
  refine ⟨54104662866841031298688505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36069775244560687532459003 54104662866841031298688505)
  ·
    refine ⟨40578497150130773474016379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54104662866841031298688505 40578497150130773474016379)
    ·
      refine ⟨60867745725196160211024569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40578497150130773474016379 60867745725196160211024569)
      ·
        refine ⟨45650809293897120158268427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60867745725196160211024569 45650809293897120158268427)
        ·
          refine ⟨68476213940845680237402641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45650809293897120158268427 68476213940845680237402641)
          ·
            refine ⟨51357160455634260178051981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68476213940845680237402641 51357160455634260178051981)
            ·
              refine ⟨19258935170862847566769493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51357160455634260178051981 19258935170862847566769493)
              ·
                refine ⟨28211330816693624365385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 19258935170862847566769493 28211330816693624365385)
                ·
                  rfl

theorem cell23_1483417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 11].length) (baseStart_1483417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1483417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1483417 prefixEnd_1483417 := by exact prefixLift 1483417
  have htrace : WordTrace (prefixWord ++ tailWord_1483417) baseStart_1483417 baseEnd_1483417 := by
    simpa [prefixWord, tailWord_1483417, baseEnd_1483417] using wordTrace_append hprefix tailTrace_1483417
  have hstable : (prefixWord ++ tailWord_1483417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483417).length < 2 ^ (prefixWord ++ tailWord_1483417).sum := by decide
  have hdescent : baseEnd_1483417 < baseStart_1483417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483428 : List Nat := [2, 3, 1, 2, 2, 1, 5, 1, 1, 1, 4]
def baseStart_1483428 : Nat := 118140960795 + 1483428 * 2 ^ 59
def prefixEnd_1483428 : Nat := 4983230072969 + 3 ^ 40 * 1483428 * 2
def baseEnd_1483428 : Nat := 761711580337927314827845

theorem tailTrace_1483428 : CollatzResearch.WordTrace tailWord_1483428 prefixEnd_1483428 761711580337927314827845 := by
  unfold tailWord_1483428
  simp only [CollatzResearch.WordTrace]
  refine ⟨27052532034900590088669469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36070042713200786784892625 27052532034900590088669469)
  ·
    refine ⟨10144699513087721283251051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27052532034900590088669469 10144699513087721283251051)
    ·
      refine ⟨15217049269631581924876577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10144699513087721283251051 15217049269631581924876577)
      ·
        refine ⟨11412786952223686443657433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15217049269631581924876577 11412786952223686443657433)
        ·
          refine ⟨8559590214167764832743075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11412786952223686443657433 8559590214167764832743075)
          ·
            refine ⟨12839385321251647249114613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8559590214167764832743075 12839385321251647249114613)
            ·
              refine ⟨1203692373867341929604495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12839385321251647249114613 1203692373867341929604495)
              ·
                refine ⟨1805538560801012894406743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1203692373867341929604495 1805538560801012894406743)
                ·
                  refine ⟨2708307841201519341610115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1805538560801012894406743 2708307841201519341610115)
                  ·
                    refine ⟨4062461761802279012415173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2708307841201519341610115 4062461761802279012415173)
                    ·
                      refine ⟨761711580337927314827845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4062461761802279012415173 761711580337927314827845)
                      ·
                        rfl

theorem cell23_1483428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 1, 1, 1, 4].length) (baseStart_1483428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1483428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1483428 prefixEnd_1483428 := by exact prefixLift 1483428
  have htrace : WordTrace (prefixWord ++ tailWord_1483428) baseStart_1483428 baseEnd_1483428 := by
    simpa [prefixWord, tailWord_1483428, baseEnd_1483428] using wordTrace_append hprefix tailTrace_1483428
  have hstable : (prefixWord ++ tailWord_1483428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483428).length < 2 ^ (prefixWord ++ tailWord_1483428).sum := by decide
  have hdescent : baseEnd_1483428 < baseStart_1483428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483509 : List Nat := [1, 3, 6, 1, 2, 1, 1, 1, 1, 2, 4]
def baseStart_1483509 : Nat := 118140960795 + 1483509 * 2 ^ 59
def prefixEnd_1483509 : Nat := 4983230072969 + 3 ^ 40 * 1483509 * 2
def baseEnd_1483509 : Nat := 761753172270941497914973

theorem tailTrace_1483509 : CollatzResearch.WordTrace tailWord_1483509 prefixEnd_1483509 761753172270941497914973 := by
  unfold tailWord_1483509
  simp only [CollatzResearch.WordTrace]
  refine ⟨54108018382507731011037581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36072012255005154007358387 54108018382507731011037581)
  ·
    refine ⟨20290506893440399129139093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54108018382507731011037581 20290506893440399129139093)
    ·
      refine ⟨951117510630018709178395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20290506893440399129139093 951117510630018709178395)
      ·
        refine ⟨1426676265945028063767593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 951117510630018709178395 1426676265945028063767593)
        ·
          refine ⟨1070007199458771047825695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1426676265945028063767593 1070007199458771047825695)
          ·
            refine ⟨1605010799188156571738543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1070007199458771047825695 1605010799188156571738543)
            ·
              refine ⟨2407516198782234857607815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1605010799188156571738543 2407516198782234857607815)
              ·
                refine ⟨3611274298173352286411723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2407516198782234857607815 3611274298173352286411723)
                ·
                  refine ⟨5416911447260028429617585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3611274298173352286411723 5416911447260028429617585)
                  ·
                    refine ⟨4062683585445021322213189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5416911447260028429617585 4062683585445021322213189)
                    ·
                      refine ⟨761753172270941497914973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4062683585445021322213189 761753172270941497914973)
                      ·
                        rfl

theorem cell23_1483509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_1483509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1483509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1483509 prefixEnd_1483509 := by exact prefixLift 1483509
  have htrace : WordTrace (prefixWord ++ tailWord_1483509) baseStart_1483509 baseEnd_1483509 := by
    simpa [prefixWord, tailWord_1483509, baseEnd_1483509] using wordTrace_append hprefix tailTrace_1483509
  have hstable : (prefixWord ++ tailWord_1483509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483509).length < 2 ^ (prefixWord ++ tailWord_1483509).sum := by decide
  have hdescent : baseEnd_1483509 < baseStart_1483509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483522 : List Nat := [3, 4, 1, 1, 1, 3, 2, 2, 1, 3, 2]
def baseStart_1483522 : Nat := 118140960795 + 1483522 * 2 ^ 59
def prefixEnd_1483522 : Nat := 4983230072969 + 3 ^ 40 * 1483522 * 2
def baseEnd_1483522 : Nat := 761759847519449947052413

theorem tailTrace_1483522 : CollatzResearch.WordTrace tailWord_1483522 prefixEnd_1483522 761759847519449947052413 := by
  unfold tailWord_1483522
  simp only [CollatzResearch.WordTrace]
  refine ⟨13527123132865158557815205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36072328354307089487507213 13527123132865158557815205)
  ·
    refine ⟨2536335587412217229590351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13527123132865158557815205 2536335587412217229590351)
    ·
      refine ⟨3804503381118325844385527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2536335587412217229590351 3804503381118325844385527)
      ·
        refine ⟨5706755071677488766578291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3804503381118325844385527 5706755071677488766578291)
        ·
          refine ⟨8560132607516233149867437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5706755071677488766578291 8560132607516233149867437)
          ·
            refine ⟨3210049727818587431200289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8560132607516233149867437 3210049727818587431200289)
            ·
              refine ⟨2407537295863940573400217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3210049727818587431200289 2407537295863940573400217)
              ·
                refine ⟨1805652971897955430050163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2407537295863940573400217 1805652971897955430050163)
                ·
                  refine ⟨2708479457846933145075245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1805652971897955430050163 2708479457846933145075245)
                  ·
                    refine ⟨1015679796692599929403217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2708479457846933145075245 1015679796692599929403217)
                    ·
                      refine ⟨761759847519449947052413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1015679796692599929403217 761759847519449947052413)
                      ·
                        rfl

theorem cell23_1483522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_1483522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1483522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1483522 prefixEnd_1483522 := by exact prefixLift 1483522
  have htrace : WordTrace (prefixWord ++ tailWord_1483522) baseStart_1483522 baseEnd_1483522 := by
    simpa [prefixWord, tailWord_1483522, baseEnd_1483522] using wordTrace_append hprefix tailTrace_1483522
  have hstable : (prefixWord ++ tailWord_1483522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483522).length < 2 ^ (prefixWord ++ tailWord_1483522).sum := by decide
  have hdescent : baseEnd_1483522 < baseStart_1483522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483561 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 1, 7, 2]
def baseStart_1483561 : Nat := 118140960795 + 1483561 * 2 ^ 59
def prefixEnd_1483561 : Nat := 4983230072969 + 3 ^ 40 * 1483561 * 2
def baseEnd_1483561 : Nat := 761779873264975294464733

theorem tailTrace_1483561 : CollatzResearch.WordTrace tailWord_1483561 prefixEnd_1483561 761779873264975294464733 := by
  unfold tailWord_1483561
  simp only [CollatzResearch.WordTrace]
  refine ⟨54109914978319343891930537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36073276652212895927953691 54109914978319343891930537)
  ·
    refine ⟨40582436233739507918947903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54109914978319343891930537 40582436233739507918947903)
    ·
      refine ⟨60873654350609261878421855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40582436233739507918947903 60873654350609261878421855)
      ·
        refine ⟨91310481525913892817632783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60873654350609261878421855 91310481525913892817632783)
        ·
          refine ⟨136965722288870839226449175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91310481525913892817632783 136965722288870839226449175)
          ·
            refine ⟨205448583433306258839673763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136965722288870839226449175 205448583433306258839673763)
            ·
              refine ⟨308172875149959388259510645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205448583433306258839673763 308172875149959388259510645)
              ·
                refine ⟨28891207045308692649329123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 308172875149959388259510645 28891207045308692649329123)
                ·
                  refine ⟨43336810567963038973993685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28891207045308692649329123 43336810567963038973993685)
                  ·
                    refine ⟨1015706497686633725952977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43336810567963038973993685 1015706497686633725952977)
                    ·
                      refine ⟨761779873264975294464733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1015706497686633725952977 761779873264975294464733)
                      ·
                        rfl

theorem cell23_1483561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 7, 2].length) (baseStart_1483561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1483561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1483561 prefixEnd_1483561 := by exact prefixLift 1483561
  have htrace : WordTrace (prefixWord ++ tailWord_1483561) baseStart_1483561 baseEnd_1483561 := by
    simpa [prefixWord, tailWord_1483561, baseEnd_1483561] using wordTrace_append hprefix tailTrace_1483561
  have hstable : (prefixWord ++ tailWord_1483561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483561).length < 2 ^ (prefixWord ++ tailWord_1483561).sum := by decide
  have hdescent : baseEnd_1483561 < baseStart_1483561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483584 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 2, 8]
def baseStart_1483584 : Nat := 118140960795 + 1483584 * 2 ^ 59
def prefixEnd_1483584 : Nat := 4983230072969 + 3 ^ 40 * 1483584 * 2
def baseEnd_1483584 : Nat := 253930561106676234825709

theorem tailTrace_1483584 : CollatzResearch.WordTrace tailWord_1483584 prefixEnd_1483584 253930561106676234825709 := by
  unfold tailWord_1483584
  simp only [CollatzResearch.WordTrace]
  refine ⟨27055376928618009410008903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36073835904824012546678537 27055376928618009410008903)
  ·
    refine ⟨40583065392927014115013355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27055376928618009410008903 40583065392927014115013355)
    ·
      refine ⟨60874598089390521172520033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40583065392927014115013355 60874598089390521172520033)
      ·
        refine ⟨45655948567042890879390025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60874598089390521172520033 45655948567042890879390025)
        ·
          refine ⟨34241961425282168159542519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45655948567042890879390025 34241961425282168159542519)
          ·
            refine ⟨51362942137923252239313779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34241961425282168159542519 51362942137923252239313779)
            ·
              refine ⟨77044413206884878358970669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51362942137923252239313779 77044413206884878358970669)
              ·
                refine ⟨28891654952581829384614001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77044413206884878358970669 28891654952581829384614001)
                ·
                  refine ⟨21668741214436372038460501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28891654952581829384614001 21668741214436372038460501)
                  ·
                    refine ⟨253930561106676234825709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 21668741214436372038460501 253930561106676234825709)
                    ·
                      rfl

theorem cell23_1483584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 2, 8].length) (baseStart_1483584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1483584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1483584 prefixEnd_1483584 := by exact prefixLift 1483584
  have htrace : WordTrace (prefixWord ++ tailWord_1483584) baseStart_1483584 baseEnd_1483584 := by
    simpa [prefixWord, tailWord_1483584, baseEnd_1483584] using wordTrace_append hprefix tailTrace_1483584
  have hstable : (prefixWord ++ tailWord_1483584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483584).length < 2 ^ (prefixWord ++ tailWord_1483584).sum := by decide
  have hdescent : baseEnd_1483584 < baseStart_1483584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483611 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 10, 2, 3]
def baseStart_1483611 : Nat := 118140960795 + 1483611 * 2 ^ 59
def prefixEnd_1483611 : Nat := 4983230072969 + 3 ^ 40 * 1483611 * 2
def baseEnd_1483611 : Nat := 761805547297700098839503

theorem tailTrace_1483611 : CollatzResearch.WordTrace tailWord_1483611 prefixEnd_1483611 761805547297700098839503 := by
  unfold tailWord_1483611
  simp only [CollatzResearch.WordTrace]
  refine ⟨54111738628138202431250687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36074492418758801620833791 54111738628138202431250687)
  ·
    refine ⟨81167607942207303646876031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54111738628138202431250687 81167607942207303646876031)
    ·
      refine ⟨121751411913310955470314047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81167607942207303646876031 121751411913310955470314047)
      ·
        refine ⟨182627117869966433205471071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121751411913310955470314047 182627117869966433205471071)
        ·
          refine ⟨273940676804949649808206607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182627117869966433205471071 273940676804949649808206607)
          ·
            refine ⟨410911015207424474712309911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273940676804949649808206607 410911015207424474712309911)
            ·
              refine ⟨616366522811136712068464867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 410911015207424474712309911 616366522811136712068464867)
              ·
                refine ⟨924549784216705068102697301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 616366522811136712068464867 924549784216705068102697301)
                ·
                  refine ⟨2708641945947378129207121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 924549784216705068102697301 2708641945947378129207121)
                  ·
                    refine ⟨2031481459460533596905341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2708641945947378129207121 2031481459460533596905341)
                    ·
                      refine ⟨761805547297700098839503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2031481459460533596905341 761805547297700098839503)
                      ·
                        rfl

theorem cell23_1483611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 2, 3].length) (baseStart_1483611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1483611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1483611 prefixEnd_1483611 := by exact prefixLift 1483611
  have htrace : WordTrace (prefixWord ++ tailWord_1483611) baseStart_1483611 baseEnd_1483611 := by
    simpa [prefixWord, tailWord_1483611, baseEnd_1483611] using wordTrace_append hprefix tailTrace_1483611
  have hstable : (prefixWord ++ tailWord_1483611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483611).length < 2 ^ (prefixWord ++ tailWord_1483611).sum := by decide
  have hdescent : baseEnd_1483611 < baseStart_1483611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483738 : List Nat := [3, 1, 1, 2, 4, 2, 2, 8]
def baseStart_1483738 : Nat := 118140960795 + 1483738 * 2 ^ 59
def prefixEnd_1483738 : Nat := 4983230072969 + 3 ^ 40 * 1483738 * 2
def baseEnd_1483738 : Nat := 28217435531141522294497

theorem tailTrace_1483738 : CollatzResearch.WordTrace tailWord_1483738 prefixEnd_1483738 28217435531141522294497 := by
  unfold tailWord_1483738
  simp only [CollatzResearch.WordTrace]
  refine ⟨13529092674669525780280967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36077580465785402080749245 13529092674669525780280967)
  ·
    refine ⟨20293639012004288670421451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13529092674669525780280967 20293639012004288670421451)
    ·
      refine ⟨30440458518006433005632177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20293639012004288670421451 30440458518006433005632177)
      ·
        refine ⟨22830343888504824754224133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30440458518006433005632177 22830343888504824754224133)
        ·
          refine ⟨4280689479094654641417025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22830343888504824754224133 4280689479094654641417025)
          ·
            refine ⟨3210517109320990981062769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4280689479094654641417025 3210517109320990981062769)
            ·
              refine ⟨2407887831990743235797077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3210517109320990981062769 2407887831990743235797077)
              ·
                refine ⟨28217435531141522294497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2407887831990743235797077 28217435531141522294497)
                ·
                  rfl

theorem cell23_1483738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 8].length) (baseStart_1483738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1483738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1483738 prefixEnd_1483738 := by exact prefixLift 1483738
  have htrace : WordTrace (prefixWord ++ tailWord_1483738) baseStart_1483738 baseEnd_1483738 := by
    simpa [prefixWord, tailWord_1483738, baseEnd_1483738] using wordTrace_append hprefix tailTrace_1483738
  have hstable : (prefixWord ++ tailWord_1483738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483738).length < 2 ^ (prefixWord ++ tailWord_1483738).sum := by decide
  have hdescent : baseEnd_1483738 < baseStart_1483738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483749 : List Nat := [1, 3, 1, 6, 1, 2, 1, 2, 1, 1, 4]
def baseStart_1483749 : Nat := 118140960795 + 1483749 * 2 ^ 59
def prefixEnd_1483749 : Nat := 4983230072969 + 3 ^ 40 * 1483749 * 2
def baseEnd_1483749 : Nat := 761876407628020558913869

theorem tailTrace_1483749 : CollatzResearch.WordTrace tailWord_1483749 prefixEnd_1483749 761876407628020558913869 := by
  unfold tailWord_1483749
  simp only [CollatzResearch.WordTrace]
  refine ⟨54116771901638251999774301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36077847934425501333182867 54116771901638251999774301)
  ·
    refine ⟨20293789463114344499915363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54116771901638251999774301 20293789463114344499915363)
    ·
      refine ⟨30440684194671516749873045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20293789463114344499915363 30440684194671516749873045)
      ·
        refine ⟨1426907071625227347650299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 30440684194671516749873045 1426907071625227347650299)
        ·
          refine ⟨2140360607437841021475449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1426907071625227347650299 2140360607437841021475449)
          ·
            refine ⟨1605270455578380766106587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2140360607437841021475449 1605270455578380766106587)
            ·
              refine ⟨2407905683367571149159881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1605270455578380766106587 2407905683367571149159881)
              ·
                refine ⟨1805929262525678361869911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2407905683367571149159881 1805929262525678361869911)
                ·
                  refine ⟨2708893893788517542804867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1805929262525678361869911 2708893893788517542804867)
                  ·
                    refine ⟨4063340840682776314207301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2708893893788517542804867 4063340840682776314207301)
                    ·
                      refine ⟨761876407628020558913869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4063340840682776314207301 761876407628020558913869)
                      ·
                        rfl

theorem cell23_1483749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_1483749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1483749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1483749 prefixEnd_1483749 := by exact prefixLift 1483749
  have htrace : WordTrace (prefixWord ++ tailWord_1483749) baseStart_1483749 baseEnd_1483749 := by
    simpa [prefixWord, tailWord_1483749, baseEnd_1483749] using wordTrace_append hprefix tailTrace_1483749
  have hstable : (prefixWord ++ tailWord_1483749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483749).length < 2 ^ (prefixWord ++ tailWord_1483749).sum := by decide
  have hdescent : baseEnd_1483749 < baseStart_1483749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483762 : List Nat := [3, 2, 1, 5, 1, 1, 1, 2, 1, 2, 4]
def baseStart_1483762 : Nat := 118140960795 + 1483762 * 2 ^ 59
def prefixEnd_1483762 : Nat := 4983230072969 + 3 ^ 40 * 1483762 * 2
def baseEnd_1483762 : Nat := 761883082876529008051309

theorem tailTrace_1483762 : CollatzResearch.WordTrace tailWord_1483762 prefixEnd_1483762 761883082876529008051309 := by
  unfold tailWord_1483762
  simp only [CollatzResearch.WordTrace]
  refine ⟨13529311512647788804999385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36078164033727436813331693 13529311512647788804999385)
  ·
    refine ⟨10146983634485841603749539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13529311512647788804999385 10146983634485841603749539)
    ·
      refine ⟨15220475451728762405624309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10146983634485841603749539 15220475451728762405624309)
      ·
        refine ⟨1426919573599571475527279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15220475451728762405624309 1426919573599571475527279)
        ·
          refine ⟨2140379360399357213290919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1426919573599571475527279 2140379360399357213290919)
          ·
            refine ⟨3210569040599035819936379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2140379360399357213290919 3210569040599035819936379)
            ·
              refine ⟨4815853560898553729904569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3210569040599035819936379 4815853560898553729904569)
              ·
                refine ⟨3611890170673915297428427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4815853560898553729904569 3611890170673915297428427)
                ·
                  refine ⟨5417835256010872946142641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3611890170673915297428427 5417835256010872946142641)
                  ·
                    refine ⟨4063376442008154709606981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5417835256010872946142641 4063376442008154709606981)
                    ·
                      refine ⟨761883082876529008051309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4063376442008154709606981 761883082876529008051309)
                      ·
                        rfl

theorem cell23_1483762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_1483762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1483762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1483762 prefixEnd_1483762 := by exact prefixLift 1483762
  have htrace : WordTrace (prefixWord ++ tailWord_1483762) baseStart_1483762 baseEnd_1483762 := by
    simpa [prefixWord, tailWord_1483762, baseEnd_1483762] using wordTrace_append hprefix tailTrace_1483762
  have hstable : (prefixWord ++ tailWord_1483762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483762).length < 2 ^ (prefixWord ++ tailWord_1483762).sum := by decide
  have hdescent : baseEnd_1483762 < baseStart_1483762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483788 : List Nat := [2, 2, 1, 2, 3, 2, 1, 1, 2, 3, 4]
def baseStart_1483788 : Nat := 118140960795 + 1483788 * 2 ^ 59
def prefixEnd_1483788 : Nat := 4983230072969 + 3 ^ 40 * 1483788 * 2
def baseEnd_1483788 : Nat := 761896433373545906326189

theorem tailTrace_1483788 : CollatzResearch.WordTrace tailWord_1483788 prefixEnd_1483788 761896433373545906326189 := by
  unfold tailWord_1483788
  simp only [CollatzResearch.WordTrace]
  refine ⟨27059097174248480830222009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36078796232331307773629345 27059097174248480830222009)
  ·
    refine ⟨20294322880686360622666507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27059097174248480830222009 20294322880686360622666507)
    ·
      refine ⟨30441484321029540933999761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20294322880686360622666507 30441484321029540933999761)
      ·
        refine ⟨22831113240772155700499821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30441484321029540933999761 22831113240772155700499821)
        ·
          refine ⟨8561667465289558387687433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22831113240772155700499821 8561667465289558387687433)
          ·
            refine ⟨6421250598967168790765575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8561667465289558387687433 6421250598967168790765575)
            ·
              refine ⟨9631875898450753186148363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6421250598967168790765575 9631875898450753186148363)
              ·
                refine ⟨14447813847676129779222545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9631875898450753186148363 14447813847676129779222545)
                ·
                  refine ⟨10835860385757097334416909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14447813847676129779222545 10835860385757097334416909)
                  ·
                    refine ⟨4063447644658911500406341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10835860385757097334416909 4063447644658911500406341)
                    ·
                      refine ⟨761896433373545906326189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4063447644658911500406341 761896433373545906326189)
                      ·
                        rfl

theorem cell23_1483788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_1483788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1483788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1483788 prefixEnd_1483788 := by exact prefixLift 1483788
  have htrace : WordTrace (prefixWord ++ tailWord_1483788) baseStart_1483788 baseEnd_1483788 := by
    simpa [prefixWord, tailWord_1483788, baseEnd_1483788] using wordTrace_append hprefix tailTrace_1483788
  have hstable : (prefixWord ++ tailWord_1483788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483788).length < 2 ^ (prefixWord ++ tailWord_1483788).sum := by decide
  have hdescent : baseEnd_1483788 < baseStart_1483788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483822 : List Nat := [4, 1, 3, 1, 1, 1, 1, 4, 1, 4, 2]
def baseStart_1483822 : Nat := 118140960795 + 1483822 * 2 ^ 59
def prefixEnd_1483822 : Nat := 4983230072969 + 3 ^ 40 * 1483822 * 2
def baseEnd_1483822 : Nat := 761913891715798773301033

theorem tailTrace_1483822 : CollatzResearch.WordTrace tailWord_1483822 prefixEnd_1483822 761913891715798773301033 := by
  unfold tailWord_1483822
  simp only [CollatzResearch.WordTrace]
  refine ⟨6764929303796723183397715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36079622953582523644787813 6764929303796723183397715)
  ·
    refine ⟨10147393955695084775096573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6764929303796723183397715 10147393955695084775096573)
    ·
      refine ⟨3805272733385656790661215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10147393955695084775096573 3805272733385656790661215)
      ·
        refine ⟨5707909100078485185991823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3805272733385656790661215 5707909100078485185991823)
        ·
          refine ⟨8561863650117727778987735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5707909100078485185991823 8561863650117727778987735)
          ·
            refine ⟨12842795475176591668481603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8561863650117727778987735 12842795475176591668481603)
            ·
              refine ⟨19264193212764887502722405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12842795475176591668481603 19264193212764887502722405)
              ·
                refine ⟨3612036227393416406760451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19264193212764887502722405 3612036227393416406760451)
                ·
                  refine ⟨5418054341090124610140677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3612036227393416406760451 5418054341090124610140677)
                  ·
                    refine ⟨1015885188954398364401377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5418054341090124610140677 1015885188954398364401377)
                    ·
                      refine ⟨761913891715798773301033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1015885188954398364401377 761913891715798773301033)
                      ·
                        rfl

theorem cell23_1483822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_1483822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1483822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1483822 prefixEnd_1483822 := by exact prefixLift 1483822
  have htrace : WordTrace (prefixWord ++ tailWord_1483822) baseStart_1483822 baseEnd_1483822 := by
    simpa [prefixWord, tailWord_1483822, baseEnd_1483822] using wordTrace_append hprefix tailTrace_1483822
  have hstable : (prefixWord ++ tailWord_1483822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483822).length < 2 ^ (prefixWord ++ tailWord_1483822).sum := by decide
  have hdescent : baseEnd_1483822 < baseStart_1483822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483845 : List Nat := [1, 3, 1, 1, 1, 3, 4, 4, 5]
def baseStart_1483845 : Nat := 118140960795 + 1483845 * 2 ^ 59
def prefixEnd_1483845 : Nat := 4983230072969 + 3 ^ 40 * 1483845 * 2
def baseEnd_1483845 : Nat := 84658411307872464812603

theorem tailTrace_1483845 : CollatzResearch.WordTrace tailWord_1483845 prefixEnd_1483845 84658411307872464812603 := by
  unfold tailWord_1483845
  simp only [CollatzResearch.WordTrace]
  refine ⟨54120273309290460395268989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36080182206193640263512659 54120273309290460395268989)
  ·
    refine ⟨20295102490983922648225871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54120273309290460395268989 20295102490983922648225871)
    ·
      refine ⟨30442653736475883972338807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20295102490983922648225871 30442653736475883972338807)
      ·
        refine ⟨45663980604713825958508211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30442653736475883972338807 45663980604713825958508211)
        ·
          refine ⟨68495970907070738937762317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45663980604713825958508211 68495970907070738937762317)
          ·
            refine ⟨25685989090151527101660869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68495970907070738937762317 25685989090151527101660869)
            ·
              refine ⟨4816122954403411331561413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25685989090151527101660869 4816122954403411331561413)
              ·
                refine ⟨903023053950639624667765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4816122954403411331561413 903023053950639624667765)
                ·
                  refine ⟨84658411307872464812603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 903023053950639624667765 84658411307872464812603)
                  ·
                    rfl

theorem cell23_1483845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 4, 5].length) (baseStart_1483845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1483845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1483845 prefixEnd_1483845 := by exact prefixLift 1483845
  have htrace : WordTrace (prefixWord ++ tailWord_1483845) baseStart_1483845 baseEnd_1483845 := by
    simpa [prefixWord, tailWord_1483845, baseEnd_1483845] using wordTrace_append hprefix tailTrace_1483845
  have hstable : (prefixWord ++ tailWord_1483845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483845).length < 2 ^ (prefixWord ++ tailWord_1483845).sum := by decide
  have hdescent : baseEnd_1483845 < baseStart_1483845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483895 : List Nat := [1, 1, 3, 1, 1, 4, 3, 2, 2, 1, 4]
def baseStart_1483895 : Nat := 118140960795 + 1483895 * 2 ^ 59
def prefixEnd_1483895 : Nat := 4983230072969 + 3 ^ 40 * 1483895 * 2
def baseEnd_1483895 : Nat := 761951375803576987688197

theorem tailTrace_1483895 : CollatzResearch.WordTrace tailWord_1483895 prefixEnd_1483895 761951375803576987688197 := by
  unfold tailWord_1483895
  simp only [CollatzResearch.WordTrace]
  refine ⟨54122096959109318934589139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36081397972739545956392759 54122096959109318934589139)
  ·
    refine ⟨81183145438663978401883709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54122096959109318934589139 81183145438663978401883709)
    ·
      refine ⟨30443679539498991900706391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81183145438663978401883709 30443679539498991900706391)
      ·
        refine ⟨45665519309248487851059587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30443679539498991900706391 45665519309248487851059587)
        ·
          refine ⟨68498278963872731776589381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45665519309248487851059587 68498278963872731776589381)
          ·
            refine ⟨12843427305726137208110509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68498278963872731776589381 12843427305726137208110509)
            ·
              refine ⟨4816285239647301453041441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12843427305726137208110509 4816285239647301453041441)
              ·
                refine ⟨3612213929735476089781081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4816285239647301453041441 3612213929735476089781081)
                ·
                  refine ⟨2709160447301607067335811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3612213929735476089781081 2709160447301607067335811)
                  ·
                    refine ⟨4063740670952410601003717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2709160447301607067335811 4063740670952410601003717)
                    ·
                      refine ⟨761951375803576987688197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4063740670952410601003717 761951375803576987688197)
                      ·
                        rfl

theorem cell23_1483895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 2, 1, 4].length) (baseStart_1483895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1483895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1483895 prefixEnd_1483895 := by exact prefixLift 1483895
  have htrace : WordTrace (prefixWord ++ tailWord_1483895) baseStart_1483895 baseEnd_1483895 := by
    simpa [prefixWord, tailWord_1483895, baseEnd_1483895] using wordTrace_append hprefix tailTrace_1483895
  have hstable : (prefixWord ++ tailWord_1483895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483895).length < 2 ^ (prefixWord ++ tailWord_1483895).sum := by decide
  have hdescent : baseEnd_1483895 < baseStart_1483895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483932 : List Nat := [2, 2, 3, 2, 1, 2, 1, 3, 2, 2, 3]
def baseStart_1483932 : Nat := 118140960795 + 1483932 * 2 ^ 59
def prefixEnd_1483932 : Nat := 4983230072969 + 3 ^ 40 * 1483932 * 2
def baseEnd_1483932 : Nat := 761970374587793342925527

theorem tailTrace_1483932 : CollatzResearch.WordTrace tailWord_1483932 prefixEnd_1483932 761970374587793342925527 := by
  unfold tailWord_1483932
  simp only [CollatzResearch.WordTrace]
  refine ⟨27061723229987637126843025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36082297639983516169124033 27061723229987637126843025)
  ·
    refine ⟨20296292422490727845132269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27061723229987637126843025 20296292422490727845132269)
    ·
      refine ⟨7611109658434022941924601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20296292422490727845132269 7611109658434022941924601)
      ·
        refine ⟨5708332243825517206443451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7611109658434022941924601 5708332243825517206443451)
        ·
          refine ⟨8562498365738275809665177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5708332243825517206443451 8562498365738275809665177)
          ·
            refine ⟨6421873774303706857248883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8562498365738275809665177 6421873774303706857248883)
            ·
              refine ⟨9632810661455560285873325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6421873774303706857248883 9632810661455560285873325)
              ·
                refine ⟨3612303998045835107202497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9632810661455560285873325 3612303998045835107202497)
                ·
                  refine ⟨2709227998534376330401873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3612303998045835107202497 2709227998534376330401873)
                  ·
                    refine ⟨2031920998900782247801405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2709227998534376330401873 2031920998900782247801405)
                    ·
                      refine ⟨761970374587793342925527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2031920998900782247801405 761970374587793342925527)
                      ·
                        rfl

theorem cell23_1483932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_1483932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1483932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1483932 prefixEnd_1483932 := by exact prefixLift 1483932
  have htrace : WordTrace (prefixWord ++ tailWord_1483932) baseStart_1483932 baseEnd_1483932 := by
    simpa [prefixWord, tailWord_1483932, baseEnd_1483932] using wordTrace_append hprefix tailTrace_1483932
  have hstable : (prefixWord ++ tailWord_1483932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483932).length < 2 ^ (prefixWord ++ tailWord_1483932).sum := by decide
  have hdescent : baseEnd_1483932 < baseStart_1483932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483962 : List Nat := [3, 1, 1, 1, 2, 2, 1, 5, 3, 1, 3]
def baseStart_1483962 : Nat := 118140960795 + 1483962 * 2 ^ 59
def prefixEnd_1483962 : Nat := 4983230072969 + 3 ^ 40 * 1483962 * 2
def baseEnd_1483962 : Nat := 761985779007428225550389

theorem tailTrace_1483962 : CollatzResearch.WordTrace tailWord_1483962 prefixEnd_1483962 761985779007428225550389 := by
  unfold tailWord_1483962
  simp only [CollatzResearch.WordTrace]
  refine ⟨13531135162466647344319535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36083027099911059584852093 13531135162466647344319535)
  ·
    refine ⟨20296702743699971016479303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13531135162466647344319535 20296702743699971016479303)
    ·
      refine ⟨30445054115549956524718955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20296702743699971016479303 30445054115549956524718955)
      ·
        refine ⟨45667581173324934787078433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30445054115549956524718955 45667581173324934787078433)
        ·
          refine ⟨34250685879993701090308825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45667581173324934787078433 34250685879993701090308825)
          ·
            refine ⟨25688014409995275817731619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34250685879993701090308825 25688014409995275817731619)
            ·
              refine ⟨38532021614992913726597429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25688014409995275817731619 38532021614992913726597429)
              ·
                refine ⟨3612377026405585661868509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38532021614992913726597429 3612377026405585661868509)
                ·
                  refine ⟨1354641384902094623200691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3612377026405585661868509 1354641384902094623200691)
                  ·
                    refine ⟨2031962077353141934801037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1354641384902094623200691 2031962077353141934801037)
                    ·
                      refine ⟨761985779007428225550389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2031962077353141934801037 761985779007428225550389)
                      ·
                        rfl

theorem cell23_1483962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 3, 1, 3].length) (baseStart_1483962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1483962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1483962 prefixEnd_1483962 := by exact prefixLift 1483962
  have htrace : WordTrace (prefixWord ++ tailWord_1483962) baseStart_1483962 baseEnd_1483962 := by
    simpa [prefixWord, tailWord_1483962, baseEnd_1483962] using wordTrace_append hprefix tailTrace_1483962
  have hstable : (prefixWord ++ tailWord_1483962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483962).length < 2 ^ (prefixWord ++ tailWord_1483962).sum := by decide
  have hdescent : baseEnd_1483962 < baseStart_1483962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483965 : List Nat := [1, 4, 1, 2, 1, 1, 3, 2, 3, 5]
def baseStart_1483965 : Nat := 118140960795 + 1483965 * 2 ^ 59
def prefixEnd_1483965 : Nat := 4983230072969 + 3 ^ 40 * 1483965 * 2
def baseEnd_1483965 : Nat := 253995773149797237937625

theorem tailTrace_1483965 : CollatzResearch.WordTrace tailWord_1483965 prefixEnd_1483965 253995773149797237937625 := by
  unfold tailWord_1483965
  simp only [CollatzResearch.WordTrace]
  refine ⟨54124650068855720889637349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36083100045903813926424899 54124650068855720889637349)
  ·
    refine ⟨10148371887910447666807003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54124650068855720889637349 10148371887910447666807003)
    ·
      refine ⟨15222557831865671500210505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10148371887910447666807003 15222557831865671500210505)
      ·
        refine ⟨11416918373899253625157879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15222557831865671500210505 11416918373899253625157879)
        ·
          refine ⟨17125377560848880437736819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11416918373899253625157879 17125377560848880437736819)
          ·
            refine ⟨25688066341273320656605229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17125377560848880437736819 25688066341273320656605229)
            ·
              refine ⟨9633024877977495246226961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25688066341273320656605229 9633024877977495246226961)
              ·
                refine ⟨7224768658483121434670221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9633024877977495246226961 7224768658483121434670221)
                ·
                  refine ⟨2709288246931170538001333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7224768658483121434670221 2709288246931170538001333)
                  ·
                    refine ⟨253995773149797237937625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2709288246931170538001333 253995773149797237937625)
                    ·
                      rfl

theorem cell23_1483965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_1483965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1483965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1483965 prefixEnd_1483965 := by exact prefixLift 1483965
  have htrace : WordTrace (prefixWord ++ tailWord_1483965) baseStart_1483965 baseEnd_1483965 := by
    simpa [prefixWord, tailWord_1483965, baseEnd_1483965] using wordTrace_append hprefix tailTrace_1483965
  have hstable : (prefixWord ++ tailWord_1483965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483965).length < 2 ^ (prefixWord ++ tailWord_1483965).sum := by decide
  have hdescent : baseEnd_1483965 < baseStart_1483965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483989 : List Nat := [1, 3, 2, 4, 1, 2, 1, 1, 1, 5, 2]
def baseStart_1483989 : Nat := 118140960795 + 1483989 * 2 ^ 59
def prefixEnd_1483989 : Nat := 4983230072969 + 3 ^ 40 * 1483989 * 2
def baseEnd_1483989 : Nat := 761999642985099619912765

theorem tailTrace_1483989 : CollatzResearch.WordTrace tailWord_1483989 prefixEnd_1483989 761999642985099619912765 := by
  unfold tailWord_1483989
  simp only [CollatzResearch.WordTrace]
  refine ⟨54125525420768772988511021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36083683613845848659007347 54125525420768772988511021)
  ·
    refine ⟨20297072032788289870691633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54125525420768772988511021 20297072032788289870691633)
    ·
      refine ⟨15222804024591217403018725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20297072032788289870691633 15222804024591217403018725)
      ·
        refine ⟨2854275754610853263066011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15222804024591217403018725 2854275754610853263066011)
        ·
          refine ⟨4281413631916279894599017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2854275754610853263066011 4281413631916279894599017)
          ·
            refine ⟨3211060223937209920949263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4281413631916279894599017 3211060223937209920949263)
            ·
              refine ⟨4816590335905814881423895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3211060223937209920949263 4816590335905814881423895)
              ·
                refine ⟨7224885503858722322135843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4816590335905814881423895 7224885503858722322135843)
                ·
                  refine ⟨10837328255788083483203765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7224885503858722322135843 10837328255788083483203765)
                  ·
                    refine ⟨1015999523980132826550353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10837328255788083483203765 1015999523980132826550353)
                    ·
                      refine ⟨761999642985099619912765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1015999523980132826550353 761999642985099619912765)
                      ·
                        rfl

theorem cell23_1483989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_1483989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1483989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1483989 prefixEnd_1483989 := by exact prefixLift 1483989
  have htrace : WordTrace (prefixWord ++ tailWord_1483989) baseStart_1483989 baseEnd_1483989 := by
    simpa [prefixWord, tailWord_1483989, baseEnd_1483989] using wordTrace_append hprefix tailTrace_1483989
  have hstable : (prefixWord ++ tailWord_1483989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483989).length < 2 ^ (prefixWord ++ tailWord_1483989).sum := by decide
  have hdescent : baseEnd_1483989 < baseStart_1483989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484012 : List Nat := [2, 2, 1, 1, 2, 5, 1, 1, 4, 4]
def baseStart_1484012 : Nat := 118140960795 + 1484012 * 2 ^ 59
def prefixEnd_1484012 : Nat := 4983230072969 + 3 ^ 40 * 1484012 * 2
def baseEnd_1484012 : Nat := 254003817680051009975053

theorem tailTrace_1484012 : CollatzResearch.WordTrace tailWord_1484012 prefixEnd_1484012 254003817680051009975053 := by
  unfold tailWord_1484012
  simp only [CollatzResearch.WordTrace]
  refine ⟨27063182149842723958299145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36084242866456965277732193 27063182149842723958299145)
  ·
    refine ⟨20297386612382042968724359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27063182149842723958299145 20297386612382042968724359)
    ·
      refine ⟨30446079918573064453086539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20297386612382042968724359 30446079918573064453086539)
      ·
        refine ⟨45669119877859596679629809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30446079918573064453086539 45669119877859596679629809)
        ·
          refine ⟨34251839908394697509722357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45669119877859596679629809 34251839908394697509722357)
          ·
            refine ⟨3211109991412002891536471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34251839908394697509722357 3211109991412002891536471)
            ·
              refine ⟨4816664987118004337304707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3211109991412002891536471 4816664987118004337304707)
              ·
                refine ⟨7224997480677006505957061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4816664987118004337304707 7224997480677006505957061)
                ·
                  refine ⟨1354687027626938719866949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7224997480677006505957061 1354687027626938719866949)
                  ·
                    refine ⟨254003817680051009975053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1354687027626938719866949 254003817680051009975053)
                    ·
                      rfl

theorem cell23_1484012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 4].length) (baseStart_1484012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1484012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1484012 prefixEnd_1484012 := by exact prefixLift 1484012
  have htrace : WordTrace (prefixWord ++ tailWord_1484012) baseStart_1484012 baseEnd_1484012 := by
    simpa [prefixWord, tailWord_1484012, baseEnd_1484012] using wordTrace_append hprefix tailTrace_1484012
  have hstable : (prefixWord ++ tailWord_1484012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484012).length < 2 ^ (prefixWord ++ tailWord_1484012).sum := by decide
  have hdescent : baseEnd_1484012 < baseStart_1484012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484019 : List Nat := [1, 1, 1, 2, 2, 5, 1, 3, 3, 2, 2]
def baseStart_1484019 : Nat := 118140960795 + 1484019 * 2 ^ 59
def prefixEnd_1484019 : Nat := 4983230072969 + 3 ^ 40 * 1484019 * 2
def baseEnd_1484019 : Nat := 762015047404734502537627

theorem tailTrace_1484019 : CollatzResearch.WordTrace tailWord_1484019 prefixEnd_1484019 762015047404734502537627 := by
  unfold tailWord_1484019
  simp only [CollatzResearch.WordTrace]
  refine ⟨54126619610660088112103111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36084413073773392074735407 54126619610660088112103111)
  ·
    refine ⟨81189929415990132168154667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54126619610660088112103111 81189929415990132168154667)
    ·
      refine ⟨121784894123985198252232001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81189929415990132168154667 121784894123985198252232001)
      ·
        refine ⟨91338670592988898689174001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121784894123985198252232001 91338670592988898689174001)
        ·
          refine ⟨68504002944741674016880501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91338670592988898689174001 68504002944741674016880501)
          ·
            refine ⟨6422250276069531939082547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68504002944741674016880501 6422250276069531939082547)
            ·
              refine ⟨9633375414104297908623821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6422250276069531939082547 9633375414104297908623821)
              ·
                refine ⟨3612515780289111715733933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9633375414104297908623821 3612515780289111715733933)
                ·
                  refine ⟨1354693417608416893400225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3612515780289111715733933 1354693417608416893400225)
                  ·
                    refine ⟨1016020063206312670050169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1354693417608416893400225 1016020063206312670050169)
                    ·
                      refine ⟨762015047404734502537627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1016020063206312670050169 762015047404734502537627)
                      ·
                        rfl

theorem cell23_1484019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 3, 2, 2].length) (baseStart_1484019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1484019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1484019 prefixEnd_1484019 := by exact prefixLift 1484019
  have htrace : WordTrace (prefixWord ++ tailWord_1484019) baseStart_1484019 baseEnd_1484019 := by
    simpa [prefixWord, tailWord_1484019, baseEnd_1484019] using wordTrace_append hprefix tailTrace_1484019
  have hstable : (prefixWord ++ tailWord_1484019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484019).length < 2 ^ (prefixWord ++ tailWord_1484019).sum := by decide
  have hdescent : baseEnd_1484019 < baseStart_1484019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484036 : List Nat := [2, 3, 2, 2, 2, 1, 2, 2, 3, 2, 2]
def baseStart_1484036 : Nat := 118140960795 + 1484036 * 2 ^ 59
def prefixEnd_1484036 : Nat := 4983230072969 + 3 ^ 40 * 1484036 * 2
def baseEnd_1484036 : Nat := 762023776575860936025049

theorem tailTrace_1484036 : CollatzResearch.WordTrace tailWord_1484036 prefixEnd_1484036 762023776575860936025049 := by
  unfold tailWord_1484036
  simp only [CollatzResearch.WordTrace]
  refine ⟨27063619825799250007735981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36084826434399000010314641 27063619825799250007735981)
  ·
    refine ⟨10148857434674718752900993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27063619825799250007735981 10148857434674718752900993)
    ·
      refine ⟨7611643076006039064675745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10148857434674718752900993 7611643076006039064675745)
      ·
        refine ⟨5708732307004529298506809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7611643076006039064675745 5708732307004529298506809)
        ·
          refine ⟨4281549230253396973880107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5708732307004529298506809 4281549230253396973880107)
          ·
            refine ⟨6422323845380095460820161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4281549230253396973880107 6422323845380095460820161)
            ·
              refine ⟨4816742884035071595615121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6422323845380095460820161 4816742884035071595615121)
              ·
                refine ⟨3612557163026303696711341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4816742884035071595615121 3612557163026303696711341)
                ·
                  refine ⟨1354708936134863886266753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3612557163026303696711341 1354708936134863886266753)
                  ·
                    refine ⟨1016031702101147914700065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1354708936134863886266753 1016031702101147914700065)
                    ·
                      refine ⟨762023776575860936025049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1016031702101147914700065 762023776575860936025049)
                      ·
                        rfl

theorem cell23_1484036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_1484036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1484036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1484036 prefixEnd_1484036 := by exact prefixLift 1484036
  have htrace : WordTrace (prefixWord ++ tailWord_1484036) baseStart_1484036 baseEnd_1484036 := by
    simpa [prefixWord, tailWord_1484036, baseEnd_1484036] using wordTrace_append hprefix tailTrace_1484036
  have hstable : (prefixWord ++ tailWord_1484036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484036).length < 2 ^ (prefixWord ++ tailWord_1484036).sum := by decide
  have hdescent : baseEnd_1484036 < baseStart_1484036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484065 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 4, 2, 5]
def baseStart_1484065 : Nat := 118140960795 + 1484065 * 2 ^ 59
def prefixEnd_1484065 : Nat := 4983230072969 + 3 ^ 40 * 1484065 * 2
def baseEnd_1484065 : Nat := 762038667514841322562415

theorem tailTrace_1484065 : CollatzResearch.WordTrace tailWord_1484065 prefixEnd_1484065 762038667514841322562415 := by
  unfold tailWord_1484065
  simp only [CollatzResearch.WordTrace]
  refine ⟨54128297368493437968277649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36085531578995625312185099 54128297368493437968277649)
  ·
    refine ⟨40596223026370078476208237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54128297368493437968277649 40596223026370078476208237)
    ·
      refine ⟨15223583634888779428578089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40596223026370078476208237 15223583634888779428578089)
      ·
        refine ⟨11417687726166584571433567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15223583634888779428578089 11417687726166584571433567)
        ·
          refine ⟨17126531589249876857150351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11417687726166584571433567 17126531589249876857150351)
          ·
            refine ⟨25689797383874815285725527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17126531589249876857150351 25689797383874815285725527)
            ·
              refine ⟨38534696075812222928588291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25689797383874815285725527 38534696075812222928588291)
              ·
                refine ⟨57802044113718334392882437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38534696075812222928588291 57802044113718334392882437)
                ·
                  refine ⟨10837883271322187698665457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57802044113718334392882437 10837883271322187698665457)
                  ·
                    refine ⟨8128412453491640773999093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10837883271322187698665457 8128412453491640773999093)
                    ·
                      refine ⟨762038667514841322562415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8128412453491640773999093 762038667514841322562415)
                      ·
                        rfl

theorem cell23_1484065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_1484065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1484065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1484065 prefixEnd_1484065 := by exact prefixLift 1484065
  have htrace : WordTrace (prefixWord ++ tailWord_1484065) baseStart_1484065 baseEnd_1484065 := by
    simpa [prefixWord, tailWord_1484065, baseEnd_1484065] using wordTrace_append hprefix tailTrace_1484065
  have hstable : (prefixWord ++ tailWord_1484065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484065).length < 2 ^ (prefixWord ++ tailWord_1484065).sum := by decide
  have hdescent : baseEnd_1484065 < baseStart_1484065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484069 : List Nat := [1, 3, 1, 2, 4, 1, 2, 1, 4, 1, 3]
def baseStart_1484069 : Nat := 118140960795 + 1484069 * 2 ^ 59
def prefixEnd_1484069 : Nat := 4983230072969 + 3 ^ 40 * 1484069 * 2
def baseEnd_1484069 : Nat := 762040721437459306912397

theorem tailTrace_1484069 : CollatzResearch.WordTrace tailWord_1484069 prefixEnd_1484069 762040721437459306912397 := by
  unfold tailWord_1484069
  simp only [CollatzResearch.WordTrace]
  refine ⟨54128443260478946651423261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36085628840319297767615507 54128443260478946651423261)
  ·
    refine ⟨20298166222679604994283723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54128443260478946651423261 20298166222679604994283723)
    ·
      refine ⟨30447249334019407491425585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20298166222679604994283723 30447249334019407491425585)
      ·
        refine ⟨22835437000514555618569189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30447249334019407491425585 22835437000514555618569189)
        ·
          refine ⟨4281644437596479178481723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22835437000514555618569189 4281644437596479178481723)
          ·
            refine ⟨6422466656394718767722585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4281644437596479178481723 6422466656394718767722585)
            ·
              refine ⟨4816849992296039075791939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6422466656394718767722585 4816849992296039075791939)
              ·
                refine ⟨7225274988444058613687909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4816849992296039075791939 7225274988444058613687909)
                ·
                  refine ⟨1354739060333260990066483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7225274988444058613687909 1354739060333260990066483)
                  ·
                    refine ⟨2032108590499891485099725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1354739060333260990066483 2032108590499891485099725)
                    ·
                      refine ⟨762040721437459306912397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2032108590499891485099725 762040721437459306912397)
                      ·
                        rfl

theorem cell23_1484069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 4, 1, 3].length) (baseStart_1484069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1484069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1484069 prefixEnd_1484069 := by exact prefixLift 1484069
  have htrace : WordTrace (prefixWord ++ tailWord_1484069) baseStart_1484069 baseEnd_1484069 := by
    simpa [prefixWord, tailWord_1484069, baseEnd_1484069] using wordTrace_append hprefix tailTrace_1484069
  have hstable : (prefixWord ++ tailWord_1484069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484069).length < 2 ^ (prefixWord ++ tailWord_1484069).sum := by decide
  have hdescent : baseEnd_1484069 < baseStart_1484069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484149 : List Nat := [1, 3, 4, 1, 3, 1, 1, 2, 7]
def baseStart_1484149 : Nat := 118140960795 + 1484149 * 2 ^ 59
def prefixEnd_1484149 : Nat := 4983230072969 + 3 ^ 40 * 1484149 * 2
def baseEnd_1484149 : Nat := 84675755543313221545781

theorem tailTrace_1484149 : CollatzResearch.WordTrace tailWord_1484149 prefixEnd_1484149 84675755543313221545781 := by
  unfold tailWord_1484149
  simp only [CollatzResearch.WordTrace]
  refine ⟨54131361100189120314335501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36087574066792746876223667 54131361100189120314335501)
  ·
    refine ⟨20299260412570920117875813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54131361100189120314335501 20299260412570920117875813)
    ·
      refine ⟨3806111327357047522101715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20299260412570920117875813 3806111327357047522101715)
      ·
        refine ⟨5709166991035571283152573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3806111327357047522101715 5709166991035571283152573)
        ·
          refine ⟨2140937621638339231182215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5709166991035571283152573 2140937621638339231182215)
          ·
            refine ⟨3211406432457508846773323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2140937621638339231182215 3211406432457508846773323)
            ·
              refine ⟨4817109648686263270159985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3211406432457508846773323 4817109648686263270159985)
              ·
                refine ⟨3612832236514697452619989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4817109648686263270159985 3612832236514697452619989)
                ·
                  refine ⟨84675755543313221545781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3612832236514697452619989 84675755543313221545781)
                  ·
                    rfl

theorem cell23_1484149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 7].length) (baseStart_1484149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1484149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1484149 prefixEnd_1484149 := by exact prefixLift 1484149
  have htrace : WordTrace (prefixWord ++ tailWord_1484149) baseStart_1484149 baseEnd_1484149 := by
    simpa [prefixWord, tailWord_1484149, baseEnd_1484149] using wordTrace_append hprefix tailTrace_1484149
  have hstable : (prefixWord ++ tailWord_1484149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484149).length < 2 ^ (prefixWord ++ tailWord_1484149).sum := by decide
  have hdescent : baseEnd_1484149 < baseStart_1484149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484209 : List Nat := [1, 2, 2, 4, 1, 1, 1, 4, 3, 4]
def baseStart_1484209 : Nat := 118140960795 + 1484209 * 2 ^ 59
def prefixEnd_1484209 : Nat := 4983230072969 + 3 ^ 40 * 1484209 * 2
def baseEnd_1484209 : Nat := 254037536243029586387251

theorem tailTrace_1484209 : CollatzResearch.WordTrace tailWord_1484209 prefixEnd_1484209 254037536243029586387251 := by
  unfold tailWord_1484209
  simp only [CollatzResearch.WordTrace]
  refine ⟨54133549479971750561519681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36089032986647833707679787 54133549479971750561519681)
  ·
    refine ⟨40600162109978812921139761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54133549479971750561519681 40600162109978812921139761)
    ·
      refine ⟨30450121582484109690854821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40600162109978812921139761 30450121582484109690854821)
      ·
        refine ⟨5709397796715770567035279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30450121582484109690854821 5709397796715770567035279)
        ·
          refine ⟨8564096695073655850552919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5709397796715770567035279 8564096695073655850552919)
          ·
            refine ⟨12846145042610483775829379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8564096695073655850552919 12846145042610483775829379)
            ·
              refine ⟨19269217563915725663744069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12846145042610483775829379 19269217563915725663744069)
              ·
                refine ⟨3612978293234198561952013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19269217563915725663744069 3612978293234198561952013)
                ·
                  refine ⟨1354866859962824460732005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3612978293234198561952013 1354866859962824460732005)
                  ·
                    refine ⟨254037536243029586387251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1354866859962824460732005 254037536243029586387251)
                    ·
                      rfl

theorem cell23_1484209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 3, 4].length) (baseStart_1484209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1484209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1484209 prefixEnd_1484209 := by exact prefixLift 1484209
  have htrace : WordTrace (prefixWord ++ tailWord_1484209) baseStart_1484209 baseEnd_1484209 := by
    simpa [prefixWord, tailWord_1484209, baseEnd_1484209] using wordTrace_append hprefix tailTrace_1484209
  have hstable : (prefixWord ++ tailWord_1484209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484209).length < 2 ^ (prefixWord ++ tailWord_1484209).sum := by decide
  have hdescent : baseEnd_1484209 < baseStart_1484209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484236 : List Nat := [2, 2, 1, 4, 2, 2, 1, 2, 2, 2, 3]
def baseStart_1484236 : Nat := 118140960795 + 1484236 * 2 ^ 59
def prefixEnd_1484236 : Nat := 4983230072969 + 3 ^ 40 * 1484236 * 2
def baseEnd_1484236 : Nat := 762126472706760153524129

theorem tailTrace_1484236 : CollatzResearch.WordTrace tailWord_1484236 prefixEnd_1484236 762126472706760153524129 := by
  unfold tailWord_1484236
  simp only [CollatzResearch.WordTrace]
  refine ⟨27067267125436967086376281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36089689500582622781835041 27067267125436967086376281)
  ·
    refine ⟨20300450344077725314782211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27067267125436967086376281 20300450344077725314782211)
    ·
      refine ⟨30450675516116587972173317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20300450344077725314782211 30450675516116587972173317)
      ·
        refine ⟨5709501659271860244782497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30450675516116587972173317 5709501659271860244782497)
        ·
          refine ⟨4282126244453895183586873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5709501659271860244782497 4282126244453895183586873)
          ·
            refine ⟨3211594683340421387690155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4282126244453895183586873 3211594683340421387690155)
            ·
              refine ⟨4817392025010632081535233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3211594683340421387690155 4817392025010632081535233)
              ·
                refine ⟨3613044018757974061151425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4817392025010632081535233 3613044018757974061151425)
                ·
                  refine ⟨2709783014068480545863569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3613044018757974061151425 2709783014068480545863569)
                  ·
                    refine ⟨2032337260551360409397677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2709783014068480545863569 2032337260551360409397677)
                    ·
                      refine ⟨762126472706760153524129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2032337260551360409397677 762126472706760153524129)
                      ·
                        rfl

theorem cell23_1484236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_1484236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1484236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1484236 prefixEnd_1484236 := by exact prefixLift 1484236
  have htrace : WordTrace (prefixWord ++ tailWord_1484236) baseStart_1484236 baseEnd_1484236 := by
    simpa [prefixWord, tailWord_1484236, baseEnd_1484236] using wordTrace_append hprefix tailTrace_1484236
  have hstable : (prefixWord ++ tailWord_1484236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484236).length < 2 ^ (prefixWord ++ tailWord_1484236).sum := by decide
  have hdescent : baseEnd_1484236 < baseStart_1484236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484294 : List Nat := [6, 2, 1, 1, 2, 1, 1, 4, 1, 4]
def baseStart_1484294 : Nat := 118140960795 + 1484294 * 2 ^ 59
def prefixEnd_1484294 : Nat := 4983230072969 + 3 ^ 40 * 1484294 * 2
def baseEnd_1484294 : Nat := 254052084861573642199621

theorem tailTrace_1484294 : CollatzResearch.WordTrace tailWord_1484294 prefixEnd_1484294 254052084861573642199621 := by
  unfold tailWord_1484294
  simp only [CollatzResearch.WordTrace]
  refine ⟨1691770302645744064948873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 36091099789775873385575957 1691770302645744064948873)
  ·
    refine ⟨1268827726984308048711655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1691770302645744064948873 1268827726984308048711655)
    ·
      refine ⟨1903241590476462073067483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1268827726984308048711655 1903241590476462073067483)
      ·
        refine ⟨2854862385714693109601225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1903241590476462073067483 2854862385714693109601225)
        ·
          refine ⟨2141146789286019832200919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2854862385714693109601225 2141146789286019832200919)
          ·
            refine ⟨3211720183929029748301379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2141146789286019832200919 3211720183929029748301379)
            ·
              refine ⟨4817580275893544622452069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3211720183929029748301379 4817580275893544622452069)
              ·
                refine ⟨903296301730039616709763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4817580275893544622452069 903296301730039616709763)
                ·
                  refine ⟨1354944452595059425064645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 903296301730039616709763 1354944452595059425064645)
                  ·
                    refine ⟨254052084861573642199621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1354944452595059425064645 254052084861573642199621)
                    ·
                      rfl

theorem cell23_1484294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_1484294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1484294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1484294 prefixEnd_1484294 := by exact prefixLift 1484294
  have htrace : WordTrace (prefixWord ++ tailWord_1484294) baseStart_1484294 baseEnd_1484294 := by
    simpa [prefixWord, tailWord_1484294, baseEnd_1484294] using wordTrace_append hprefix tailTrace_1484294
  have hstable : (prefixWord ++ tailWord_1484294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484294).length < 2 ^ (prefixWord ++ tailWord_1484294).sum := by decide
  have hdescent : baseEnd_1484294 < baseStart_1484294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484300 : List Nat := [2, 2, 1, 2, 5, 1, 1, 4, 1, 1, 3]
def baseStart_1484300 : Nat := 118140960795 + 1484300 * 2 ^ 59
def prefixEnd_1484300 : Nat := 4983230072969 + 3 ^ 40 * 1484300 * 2
def baseEnd_1484300 : Nat := 762159335468647903123835

theorem tailTrace_1484300 : CollatzResearch.WordTrace tailWord_1484300 prefixEnd_1484300 762159335468647903123835 := by
  unfold tailWord_1484300
  simp only [CollatzResearch.WordTrace]
  refine ⟨27068434261321036551541177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36091245681761382068721569 27068434261321036551541177)
  ·
    refine ⟨20301325695990777413655883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27068434261321036551541177 20301325695990777413655883)
    ·
      refine ⟨30451988543986166120483825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20301325695990777413655883 30451988543986166120483825)
      ·
        refine ⟨22838991407989624590362869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30451988543986166120483825 22838991407989624590362869)
        ·
          refine ⟨2141155444499027305346519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22838991407989624590362869 2141155444499027305346519)
          ·
            refine ⟨3211733166748540958019779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2141155444499027305346519 3211733166748540958019779)
            ·
              refine ⟨4817599750122811437029669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3211733166748540958019779 4817599750122811437029669)
              ·
                refine ⟨903299953148027144443063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4817599750122811437029669 903299953148027144443063)
                ·
                  refine ⟨1354949929722040716664595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 903299953148027144443063 1354949929722040716664595)
                  ·
                    refine ⟨2032424894583061074996893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1354949929722040716664595 2032424894583061074996893)
                    ·
                      refine ⟨762159335468647903123835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2032424894583061074996893 762159335468647903123835)
                      ·
                        rfl

theorem cell23_1484300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 4, 1, 1, 3].length) (baseStart_1484300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1484300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1484300 prefixEnd_1484300 := by exact prefixLift 1484300
  have htrace : WordTrace (prefixWord ++ tailWord_1484300) baseStart_1484300 baseEnd_1484300 := by
    simpa [prefixWord, tailWord_1484300, baseEnd_1484300] using wordTrace_append hprefix tailTrace_1484300
  have hstable : (prefixWord ++ tailWord_1484300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484300).length < 2 ^ (prefixWord ++ tailWord_1484300).sum := by decide
  have hdescent : baseEnd_1484300 < baseStart_1484300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484316 : List Nat := [2, 2, 3, 1, 2, 1, 1, 5, 2, 4]
def baseStart_1484316 : Nat := 118140960795 + 1484316 * 2 ^ 59
def prefixEnd_1484316 : Nat := 4983230072969 + 3 ^ 40 * 1484316 * 2
def baseEnd_1484316 : Nat := 254055850386373280174587

theorem tailTrace_1484316 : CollatzResearch.WordTrace tailWord_1484316 prefixEnd_1484316 254055850386373280174587 := by
  unfold tailWord_1484316
  simp only [CollatzResearch.WordTrace]
  refine ⟨27068726045292053917832401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36091634727056071890443201 27068726045292053917832401)
  ·
    refine ⟨20301544533969040438374301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27068726045292053917832401 20301544533969040438374301)
    ·
      refine ⟨7613079200238390164390363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20301544533969040438374301 7613079200238390164390363)
      ·
        refine ⟨11419618800357585246585545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7613079200238390164390363 11419618800357585246585545)
        ·
          refine ⟨8564714100268188934939159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11419618800357585246585545 8564714100268188934939159)
          ·
            refine ⟨12847071150402283402408739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8564714100268188934939159 12847071150402283402408739)
            ·
              refine ⟨19270606725603425103613109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12847071150402283402408739 19270606725603425103613109)
              ·
                refine ⟨1806619380525321103463729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19270606725603425103613109 1806619380525321103463729)
                ·
                  refine ⟨1354964535393990827597797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1806619380525321103463729 1354964535393990827597797)
                  ·
                    refine ⟨254055850386373280174587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1354964535393990827597797 254055850386373280174587)
                    ·
                      rfl

theorem cell23_1484316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_1484316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1484316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1484316 prefixEnd_1484316 := by exact prefixLift 1484316
  have htrace : WordTrace (prefixWord ++ tailWord_1484316) baseStart_1484316 baseEnd_1484316 := by
    simpa [prefixWord, tailWord_1484316, baseEnd_1484316] using wordTrace_append hprefix tailTrace_1484316
  have hstable : (prefixWord ++ tailWord_1484316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484316).length < 2 ^ (prefixWord ++ tailWord_1484316).sum := by decide
  have hdescent : baseEnd_1484316 < baseStart_1484316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484319 : List Nat := [1, 1, 2, 4, 1, 1, 3, 3, 1, 2, 4]
def baseStart_1484319 : Nat := 118140960795 + 1484319 * 2 ^ 59
def prefixEnd_1484319 : Nat := 4983230072969 + 3 ^ 40 * 1484319 * 2
def baseEnd_1484319 : Nat := 762169091601083328786247

theorem tailTrace_1484319 : CollatzResearch.WordTrace tailWord_1484319 prefixEnd_1484319 762169091601083328786247 := by
  unfold tailWord_1484319
  simp only [CollatzResearch.WordTrace]
  refine ⟨54137561509573239348024011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36091707673048826232016007 54137561509573239348024011)
  ·
    refine ⟨81206342264359859022036017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54137561509573239348024011 81206342264359859022036017)
    ·
      refine ⟨60904756698269894266527013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81206342264359859022036017 60904756698269894266527013)
      ·
        refine ⟨11419641880925605174973815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60904756698269894266527013 11419641880925605174973815)
        ·
          refine ⟨17129462821388407762460723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11419641880925605174973815 17129462821388407762460723)
          ·
            refine ⟨25694194232082611643691085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17129462821388407762460723 25694194232082611643691085)
            ·
              refine ⟨9635322837030979366384157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25694194232082611643691085 9635322837030979366384157)
              ·
                refine ⟨3613246063886617262394059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9635322837030979366384157 3613246063886617262394059)
                ·
                  refine ⟨5419869095829925893591089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3613246063886617262394059 5419869095829925893591089)
                  ·
                    refine ⟨4064901821872444420193317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5419869095829925893591089 4064901821872444420193317)
                    ·
                      refine ⟨762169091601083328786247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4064901821872444420193317 762169091601083328786247)
                      ·
                        rfl

theorem cell23_1484319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_1484319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1484319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1484319 prefixEnd_1484319 := by exact prefixLift 1484319
  have htrace : WordTrace (prefixWord ++ tailWord_1484319) baseStart_1484319 baseEnd_1484319 := by
    simpa [prefixWord, tailWord_1484319, baseEnd_1484319] using wordTrace_append hprefix tailTrace_1484319
  have hstable : (prefixWord ++ tailWord_1484319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484319).length < 2 ^ (prefixWord ++ tailWord_1484319).sum := by decide
  have hdescent : baseEnd_1484319 < baseStart_1484319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484343 : List Nat := [1, 1, 3, 1, 2, 4, 4, 1, 1, 2, 3]
def baseStart_1484343 : Nat := 118140960795 + 1484343 * 2 ^ 59
def prefixEnd_1484343 : Nat := 4983230072969 + 3 ^ 40 * 1484343 * 2
def baseEnd_1484343 : Nat := 762181415136791234886137

theorem tailTrace_1484343 : CollatzResearch.WordTrace tailWord_1484343 prefixEnd_1484343 762181415136791234886137 := by
  unfold tailWord_1484343
  simp only [CollatzResearch.WordTrace]
  refine ⟨54138436861486291446897683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36092291240990860964598455 54138436861486291446897683)
  ·
    refine ⟨81207655292229437170346525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54138436861486291446897683 81207655292229437170346525)
    ·
      refine ⟨30452870734586038938879947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81207655292229437170346525 30452870734586038938879947)
      ·
        refine ⟨45679306101879058408319921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30452870734586038938879947 45679306101879058408319921)
        ·
          refine ⟨34259479576409293806239941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45679306101879058408319921 34259479576409293806239941)
          ·
            refine ⟨6423652420576742588669989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34259479576409293806239941 6423652420576742588669989)
            ·
              refine ⟨1204434828858139235375623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6423652420576742588669989 1204434828858139235375623)
              ·
                refine ⟨1806652243287208853063435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1204434828858139235375623 1806652243287208853063435)
                ·
                  refine ⟨2709978364930813279595153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1806652243287208853063435 2709978364930813279595153)
                  ·
                    refine ⟨2032483773698109959696365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2709978364930813279595153 2032483773698109959696365)
                    ·
                      refine ⟨762181415136791234886137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2032483773698109959696365 762181415136791234886137)
                      ·
                        rfl

theorem cell23_1484343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 1, 1, 2, 3].length) (baseStart_1484343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1484343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1484343 prefixEnd_1484343 := by exact prefixLift 1484343
  have htrace : WordTrace (prefixWord ++ tailWord_1484343) baseStart_1484343 baseEnd_1484343 := by
    simpa [prefixWord, tailWord_1484343, baseEnd_1484343] using wordTrace_append hprefix tailTrace_1484343
  have hstable : (prefixWord ++ tailWord_1484343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484343).length < 2 ^ (prefixWord ++ tailWord_1484343).sum := by decide
  have hdescent : baseEnd_1484343 < baseStart_1484343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484396 : List Nat := [2, 2, 1, 1, 3, 1, 1, 3, 3, 4, 2]
def baseStart_1484396 : Nat := 118140960795 + 1484396 * 2 ^ 59
def prefixEnd_1484396 : Nat := 4983230072969 + 3 ^ 40 * 1484396 * 2
def baseEnd_1484396 : Nat := 762208629611479527523393

theorem tailTrace_1484396 : CollatzResearch.WordTrace tailWord_1484396 prefixEnd_1484396 762208629611479527523393 := by
  unfold tailWord_1484396
  simp only [CollatzResearch.WordTrace]
  refine ⟨27070184965147140749288521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36093579953529520999051361 27070184965147140749288521)
  ·
    refine ⟨20302638723860355561966391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27070184965147140749288521 20302638723860355561966391)
    ·
      refine ⟨30453958085790533342949587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20302638723860355561966391 30453958085790533342949587)
      ·
        refine ⟨45680937128685800014424381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30453958085790533342949587 45680937128685800014424381)
        ·
          refine ⟨17130351423257175005409143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45680937128685800014424381 17130351423257175005409143)
          ·
            refine ⟨25695527134885762508113715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17130351423257175005409143 25695527134885762508113715)
            ·
              refine ⟨38543290702328643762170573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25695527134885762508113715 38543290702328643762170573)
              ·
                refine ⟨14453734013373241410813965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38543290702328643762170573 14453734013373241410813965)
                ·
                  refine ⟨5420150255014965529055237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14453734013373241410813965 5420150255014965529055237)
                  ·
                    refine ⟨1016278172815306036697857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5420150255014965529055237 1016278172815306036697857)
                    ·
                      refine ⟨762208629611479527523393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1016278172815306036697857 762208629611479527523393)
                      ·
                        rfl

theorem cell23_1484396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 4, 2].length) (baseStart_1484396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1484396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1484396 prefixEnd_1484396 := by exact prefixLift 1484396
  have htrace : WordTrace (prefixWord ++ tailWord_1484396) baseStart_1484396 baseEnd_1484396 := by
    simpa [prefixWord, tailWord_1484396, baseEnd_1484396] using wordTrace_append hprefix tailTrace_1484396
  have hstable : (prefixWord ++ tailWord_1484396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484396).length < 2 ^ (prefixWord ++ tailWord_1484396).sum := by decide
  have hdescent : baseEnd_1484396 < baseStart_1484396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484399 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 1, 6, 3]
def baseStart_1484399 : Nat := 118140960795 + 1484399 * 2 ^ 59
def prefixEnd_1484399 : Nat := 4983230072969 + 3 ^ 40 * 1484399 * 2
def baseEnd_1484399 : Nat := 762210170053443015785879

theorem tailTrace_1484399 : CollatzResearch.WordTrace tailWord_1484399 prefixEnd_1484399 762210170053443015785879 := by
  unfold tailWord_1484399
  simp only [CollatzResearch.WordTrace]
  refine ⟨54140479349283413010936251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36093652899522275340624167 54140479349283413010936251)
  ·
    refine ⟨81210719023925119516404377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54140479349283413010936251 81210719023925119516404377)
    ·
      refine ⟨60908039267943839637303283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81210719023925119516404377 60908039267943839637303283)
      ·
        refine ⟨91362058901915759455954925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60908039267943839637303283 91362058901915759455954925)
        ·
          refine ⟨34260772088218409795983097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91362058901915759455954925 34260772088218409795983097)
          ·
            refine ⟨25695579066163807346987323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34260772088218409795983097 25695579066163807346987323)
            ·
              refine ⟨38543368599245711020480985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25695579066163807346987323 38543368599245711020480985)
              ·
                refine ⟨28907526449434283265360739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38543368599245711020480985 28907526449434283265360739)
                ·
                  refine ⟨43361289674151424898041109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28907526449434283265360739 43361289674151424898041109)
                  ·
                    refine ⟨2032560453475848042095677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 43361289674151424898041109 2032560453475848042095677)
                    ·
                      refine ⟨762210170053443015785879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2032560453475848042095677 762210170053443015785879)
                      ·
                        rfl

theorem cell23_1484399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 6, 3].length) (baseStart_1484399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1484399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1484399 prefixEnd_1484399 := by exact prefixLift 1484399
  have htrace : WordTrace (prefixWord ++ tailWord_1484399) baseStart_1484399 baseEnd_1484399 := by
    simpa [prefixWord, tailWord_1484399, baseEnd_1484399] using wordTrace_append hprefix tailTrace_1484399
  have hstable : (prefixWord ++ tailWord_1484399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484399).length < 2 ^ (prefixWord ++ tailWord_1484399).sum := by decide
  have hdescent : baseEnd_1484399 < baseStart_1484399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484424 : List Nat := [2, 1, 3, 5, 1, 2, 2, 1, 2, 1, 3]
def baseStart_1484424 : Nat := 118140960795 + 1484424 * 2 ^ 59
def prefixEnd_1484424 : Nat := 4983230072969 + 3 ^ 40 * 1484424 * 2
def baseEnd_1484424 : Nat := 762223007069805417973265

theorem tailTrace_1484424 : CollatzResearch.WordTrace tailWord_1484424 prefixEnd_1484424 762223007069805417973265 := by
  unfold tailWord_1484424
  simp only [CollatzResearch.WordTrace]
  refine ⟨27070695587096421140298163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36094260782795228187064217 27070695587096421140298163)
  ·
    refine ⟨40606043380644631710447245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27070695587096421140298163 40606043380644631710447245)
    ·
      refine ⟨15227266267741736891417717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40606043380644631710447245 15227266267741736891417717)
      ·
        refine ⟨1427556212600787833570411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15227266267741736891417717 1427556212600787833570411)
        ·
          refine ⟨2141334318901181750355617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1427556212600787833570411 2141334318901181750355617)
          ·
            refine ⟨1606000739175886312766713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2141334318901181750355617 1606000739175886312766713)
            ·
              refine ⟨1204500554381914734575035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1606000739175886312766713 1204500554381914734575035)
              ·
                refine ⟨1806750831572872101862553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1204500554381914734575035 1806750831572872101862553)
                ·
                  refine ⟨1355063123679654076396915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1806750831572872101862553 1355063123679654076396915)
                  ·
                    refine ⟨2032594685519481114595373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1355063123679654076396915 2032594685519481114595373)
                    ·
                      refine ⟨762223007069805417973265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2032594685519481114595373 762223007069805417973265)
                      ·
                        rfl

theorem cell23_1484424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_1484424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1484424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1484424 prefixEnd_1484424 := by exact prefixLift 1484424
  have htrace : WordTrace (prefixWord ++ tailWord_1484424) baseStart_1484424 baseEnd_1484424 := by
    simpa [prefixWord, tailWord_1484424, baseEnd_1484424] using wordTrace_append hprefix tailTrace_1484424
  have hstable : (prefixWord ++ tailWord_1484424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484424).length < 2 ^ (prefixWord ++ tailWord_1484424).sum := by decide
  have hdescent : baseEnd_1484424 < baseStart_1484424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484434 : List Nat := [3, 2, 3, 1, 4, 1, 1, 2, 1, 3, 2]
def baseStart_1484434 : Nat := 118140960795 + 1484434 * 2 ^ 59
def prefixEnd_1484434 : Nat := 4983230072969 + 3 ^ 40 * 1484434 * 2
def baseEnd_1484434 : Nat := 762228141876350378848219

theorem tailTrace_1484434 : CollatzResearch.WordTrace tailWord_1484434 prefixEnd_1484434 762228141876350378848219 := by
  unfold tailWord_1484434
  simp only [CollatzResearch.WordTrace]
  refine ⟨13535438976039153497115089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36094503936104409325640237 13535438976039153497115089)
  ·
    refine ⟨10151579232029365122836317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13535438976039153497115089 10151579232029365122836317)
    ·
      refine ⟨3806842212011011921063619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10151579232029365122836317 3806842212011011921063619)
      ·
        refine ⟨5710263318016517881595429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3806842212011011921063619 5710263318016517881595429)
        ·
          refine ⟨1070674372128097102799143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5710263318016517881595429 1070674372128097102799143)
          ·
            refine ⟨1606011558192145654198715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1070674372128097102799143 1606011558192145654198715)
            ·
              refine ⟨2409017337288218481298073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1606011558192145654198715 2409017337288218481298073)
              ·
                refine ⟨1806763002966163860973555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2409017337288218481298073 1806763002966163860973555)
                ·
                  refine ⟨2710144504449245791460333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1806763002966163860973555 2710144504449245791460333)
                  ·
                    refine ⟨1016304189168467171797625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2710144504449245791460333 1016304189168467171797625)
                    ·
                      refine ⟨762228141876350378848219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1016304189168467171797625 762228141876350378848219)
                      ·
                        rfl

theorem cell23_1484434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_1484434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1484434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1484434 prefixEnd_1484434 := by exact prefixLift 1484434
  have htrace : WordTrace (prefixWord ++ tailWord_1484434) baseStart_1484434 baseEnd_1484434 := by
    simpa [prefixWord, tailWord_1484434, baseEnd_1484434] using wordTrace_append hprefix tailTrace_1484434
  have hstable : (prefixWord ++ tailWord_1484434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484434).length < 2 ^ (prefixWord ++ tailWord_1484434).sum := by decide
  have hdescent : baseEnd_1484434 < baseStart_1484434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484466 : List Nat := [3, 2, 1, 1, 1, 2, 4, 2, 2, 5]
def baseStart_1484466 : Nat := 118140960795 + 1484466 * 2 ^ 59
def prefixEnd_1484466 : Nat := 4983230072969 + 3 ^ 40 * 1484466 * 2
def baseEnd_1484466 : Nat := 254081524419098084549357

theorem tailTrace_1484466 : CollatzResearch.WordTrace tailWord_1484466 prefixEnd_1484466 254081524419098084549357 := by
  unfold tailWord_1484466
  simp only [CollatzResearch.WordTrace]
  refine ⟨13535730760010170863406313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36095282026693788969083501 13535730760010170863406313)
  ·
    refine ⟨10151798070007628147554735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13535730760010170863406313 10151798070007628147554735)
    ·
      refine ⟨15227697105011442221332103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10151798070007628147554735 15227697105011442221332103)
      ·
        refine ⟨22841545657517163331998155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15227697105011442221332103 22841545657517163331998155)
        ·
          refine ⟨34262318486275744997997233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22841545657517163331998155 34262318486275744997997233)
          ·
            refine ⟨25696738864706808748497925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34262318486275744997997233 25696738864706808748497925)
            ·
              refine ⟨4818138537132526640343361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25696738864706808748497925 4818138537132526640343361)
              ·
                refine ⟨3613603902849394980257521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4818138537132526640343361 3613603902849394980257521)
                ·
                  refine ⟨2710202927137046235193141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3613603902849394980257521 2710202927137046235193141)
                  ·
                    refine ⟨254081524419098084549357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2710202927137046235193141 254081524419098084549357)
                    ·
                      rfl

theorem cell23_1484466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_1484466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1484466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1484466 prefixEnd_1484466 := by exact prefixLift 1484466
  have htrace : WordTrace (prefixWord ++ tailWord_1484466) baseStart_1484466 baseEnd_1484466 := by
    simpa [prefixWord, tailWord_1484466, baseEnd_1484466] using wordTrace_append hprefix tailTrace_1484466
  have hstable : (prefixWord ++ tailWord_1484466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484466).length < 2 ^ (prefixWord ++ tailWord_1484466).sum := by decide
  have hdescent : baseEnd_1484466 < baseStart_1484466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484476 : List Nat := [2, 2, 2, 3, 1, 2, 2, 1, 1, 2, 5]
def baseStart_1484476 : Nat := 118140960795 + 1484476 * 2 ^ 59
def prefixEnd_1484476 : Nat := 4983230072969 + 3 ^ 40 * 1484476 * 2
def baseEnd_1484476 : Nat := 762249708063839214523025

theorem tailTrace_1484476 : CollatzResearch.WordTrace tailWord_1484476 prefixEnd_1484476 762249708063839214523025 := by
  unfold tailWord_1484476
  simp only [CollatzResearch.WordTrace]
  refine ⟨27071643885002227580744641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36095525180002970107659521 27071643885002227580744641)
  ·
    refine ⟨20303732913751670685558481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27071643885002227580744641 20303732913751670685558481)
    ·
      refine ⟨15227799685313753014168861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20303732913751670685558481 15227799685313753014168861)
      ·
        refine ⟨5710424881992657380313323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15227799685313753014168861 5710424881992657380313323)
        ·
          refine ⟨8565637322988986070469985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5710424881992657380313323 8565637322988986070469985)
          ·
            refine ⟨6424227992241739552852489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8565637322988986070469985 6424227992241739552852489)
            ·
              refine ⟨4818170994181304664639367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6424227992241739552852489 4818170994181304664639367)
              ·
                refine ⟨7227256491271956996959051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4818170994181304664639367 7227256491271956996959051)
                ·
                  refine ⟨10840884736907935495438577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7227256491271956996959051 10840884736907935495438577)
                  ·
                    refine ⟨8130663552680951621578933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10840884736907935495438577 8130663552680951621578933)
                    ·
                      refine ⟨762249708063839214523025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8130663552680951621578933 762249708063839214523025)
                      ·
                        rfl

theorem cell23_1484476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_1484476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1484476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1484476 prefixEnd_1484476 := by exact prefixLift 1484476
  have htrace : WordTrace (prefixWord ++ tailWord_1484476) baseStart_1484476 baseEnd_1484476 := by
    simpa [prefixWord, tailWord_1484476, baseEnd_1484476] using wordTrace_append hprefix tailTrace_1484476
  have hstable : (prefixWord ++ tailWord_1484476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484476).length < 2 ^ (prefixWord ++ tailWord_1484476).sum := by decide
  have hdescent : baseEnd_1484476 < baseStart_1484476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484500 : List Nat := [2, 4, 1, 3, 1, 3, 1, 1, 2, 5]
def baseStart_1484500 : Nat := 118140960795 + 1484500 * 2 ^ 59
def prefixEnd_1484500 : Nat := 4983230072969 + 3 ^ 40 * 1484500 * 2
def baseEnd_1484500 : Nat := 254087343866515706874305

theorem tailTrace_1484500 : CollatzResearch.WordTrace tailWord_1484500 prefixEnd_1484500 254087343866515706874305 := by
  unfold tailWord_1484500
  simp only [CollatzResearch.WordTrace]
  refine ⟨27072081560958753630181477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36096108747945004840241969 27072081560958753630181477)
  ·
    refine ⟨5076015292679766305659027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27072081560958753630181477 5076015292679766305659027)
    ·
      refine ⟨7614022939019649458488541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5076015292679766305659027 7614022939019649458488541)
      ·
        refine ⟨2855258602132368546933203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7614022939019649458488541 2855258602132368546933203)
        ·
          refine ⟨4282887903198552820399805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2855258602132368546933203 4282887903198552820399805)
          ·
            refine ⟨1606082963699457307649927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4282887903198552820399805 1606082963699457307649927)
            ·
              refine ⟨2409124445549185961474891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1606082963699457307649927 2409124445549185961474891)
              ·
                refine ⟨3613686668323778942212337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2409124445549185961474891 3613686668323778942212337)
                ·
                  refine ⟨2710265001242834206659253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3613686668323778942212337 2710265001242834206659253)
                  ·
                    refine ⟨254087343866515706874305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2710265001242834206659253 254087343866515706874305)
                    ·
                      rfl

theorem cell23_1484500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_1484500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1484500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1484500 prefixEnd_1484500 := by exact prefixLift 1484500
  have htrace : WordTrace (prefixWord ++ tailWord_1484500) baseStart_1484500 baseEnd_1484500 := by
    simpa [prefixWord, tailWord_1484500, baseEnd_1484500] using wordTrace_append hprefix tailTrace_1484500
  have hstable : (prefixWord ++ tailWord_1484500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484500).length < 2 ^ (prefixWord ++ tailWord_1484500).sum := by decide
  have hdescent : baseEnd_1484500 < baseStart_1484500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484526 : List Nat := [4, 1, 2, 1, 1, 2, 3, 1, 8]
def baseStart_1484526 : Nat := 118140960795 + 1484526 * 2 ^ 59
def prefixEnd_1484526 : Nat := 4983230072969 + 3 ^ 40 * 1484526 * 2
def baseEnd_1484526 : Nat := 84697264677396002099755

theorem tailTrace_1484526 : CollatzResearch.WordTrace tailWord_1484526 prefixEnd_1484526 84697264677396002099755 := by
  unfold tailWord_1484526
  simp only [CollatzResearch.WordTrace]
  refine ⟨6768138927477914212601179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36096740946548875800539621 6768138927477914212601179)
  ·
    refine ⟨10152208391216871318901769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6768138927477914212601179 10152208391216871318901769)
    ·
      refine ⟨7614156293412653489176327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10152208391216871318901769 7614156293412653489176327)
      ·
        refine ⟨11421234440118980233764491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7614156293412653489176327 11421234440118980233764491)
        ·
          refine ⟨17131851660178470350646737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11421234440118980233764491 17131851660178470350646737)
          ·
            refine ⟨12848888745133852762985053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17131851660178470350646737 12848888745133852762985053)
            ·
              refine ⟨4818333279425194786119395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12848888745133852762985053 4818333279425194786119395)
              ·
                refine ⟨7227499919137792179179093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4818333279425194786119395 7227499919137792179179093)
                ·
                  refine ⟨84697264677396002099755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7227499919137792179179093 84697264677396002099755)
                  ·
                    rfl

theorem cell23_1484526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 8].length) (baseStart_1484526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1484526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1484526 prefixEnd_1484526 := by exact prefixLift 1484526
  have htrace : WordTrace (prefixWord ++ tailWord_1484526) baseStart_1484526 baseEnd_1484526 := by
    simpa [prefixWord, tailWord_1484526, baseEnd_1484526] using wordTrace_append hprefix tailTrace_1484526
  have hstable : (prefixWord ++ tailWord_1484526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484526).length < 2 ^ (prefixWord ++ tailWord_1484526).sum := by decide
  have hdescent : baseEnd_1484526 < baseStart_1484526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484530 : List Nat := [3, 2, 1, 3, 1, 1, 1, 6, 1, 4]
def baseStart_1484530 : Nat := 118140960795 + 1484530 * 2 ^ 59
def prefixEnd_1484530 : Nat := 4983230072969 + 3 ^ 40 * 1484530 * 2
def baseEnd_1484530 : Nat := 254092478673060667749259

theorem tailTrace_1484530 : CollatzResearch.WordTrace tailWord_1484530 prefixEnd_1484530 254092478673060667749259 := by
  unfold tailWord_1484530
  simp only [CollatzResearch.WordTrace]
  refine ⟨13536314327952205595988761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36096838207872548255970029 13536314327952205595988761)
  ·
    refine ⟨10152235745964154196991571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13536314327952205595988761 10152235745964154196991571)
    ·
      refine ⟨15228353618946231295487357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10152235745964154196991571 15228353618946231295487357)
      ·
        refine ⟨5710632607104836735807759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15228353618946231295487357 5710632607104836735807759)
        ·
          refine ⟨8565948910657255103711639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5710632607104836735807759 8565948910657255103711639)
          ·
            refine ⟨12848923365985882655567459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8565948910657255103711639 12848923365985882655567459)
            ·
              refine ⟨19273385048978823983351189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12848923365985882655567459 19273385048978823983351189)
              ·
                refine ⟨903439924170882374219587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19273385048978823983351189 903439924170882374219587)
                ·
                  refine ⟨1355159886256323561329381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 903439924170882374219587 1355159886256323561329381)
                  ·
                    refine ⟨254092478673060667749259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1355159886256323561329381 254092478673060667749259)
                    ·
                      rfl

theorem cell23_1484530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 6, 1, 4].length) (baseStart_1484530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1484530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1484530 prefixEnd_1484530 := by exact prefixLift 1484530
  have htrace : WordTrace (prefixWord ++ tailWord_1484530) baseStart_1484530 baseEnd_1484530 := by
    simpa [prefixWord, tailWord_1484530, baseEnd_1484530] using wordTrace_append hprefix tailTrace_1484530
  have hstable : (prefixWord ++ tailWord_1484530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484530).length < 2 ^ (prefixWord ++ tailWord_1484530).sum := by decide
  have hdescent : baseEnd_1484530 < baseStart_1484530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484539 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 2, 9]
def baseStart_1484539 : Nat := 118140960795 + 1484539 * 2 ^ 59
def prefixEnd_1484539 : Nat := 4983230072969 + 3 ^ 40 * 1484539 * 2
def baseEnd_1484539 : Nat := 254094019115024156011745

theorem tailTrace_1484539 : CollatzResearch.WordTrace tailWord_1484539 prefixEnd_1484539 254094019115024156011745 := by
  unfold tailWord_1484539
  simp only [CollatzResearch.WordTrace]
  refine ⟨54145585568776216921032671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36097057045850811280688447 54145585568776216921032671)
  ·
    refine ⟨81218378353164325381549007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54145585568776216921032671 81218378353164325381549007)
    ·
      refine ⟨121827567529746488072323511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81218378353164325381549007 121827567529746488072323511)
      ·
        refine ⟨182741351294619732108485267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121827567529746488072323511 182741351294619732108485267)
        ·
          refine ⟨274112026941929598162727901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182741351294619732108485267 274112026941929598162727901)
          ·
            refine ⟨102792010103223599311022963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 274112026941929598162727901 102792010103223599311022963)
            ·
              refine ⟨154188015154835398966534445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102792010103223599311022963 154188015154835398966534445)
              ·
                refine ⟨57820505683063274612450417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154188015154835398966534445 57820505683063274612450417)
                ·
                  refine ⟨43365379262297455959337813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57820505683063274612450417 43365379262297455959337813)
                  ·
                    refine ⟨254094019115024156011745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 43365379262297455959337813 254094019115024156011745)
                    ·
                      rfl

theorem cell23_1484539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 9].length) (baseStart_1484539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1484539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1484539 prefixEnd_1484539 := by exact prefixLift 1484539
  have htrace : WordTrace (prefixWord ++ tailWord_1484539) baseStart_1484539 baseEnd_1484539 := by
    simpa [prefixWord, tailWord_1484539, baseEnd_1484539] using wordTrace_append hprefix tailTrace_1484539
  have hstable : (prefixWord ++ tailWord_1484539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484539).length < 2 ^ (prefixWord ++ tailWord_1484539).sum := by decide
  have hdescent : baseEnd_1484539 < baseStart_1484539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484556 : List Nat := [2, 2, 1, 2, 2, 1, 2, 3, 3, 5]
def baseStart_1484556 : Nat := 118140960795 + 1484556 * 2 ^ 59
def prefixEnd_1484556 : Nat := 4983230072969 + 3 ^ 40 * 1484556 * 2
def baseEnd_1484556 : Nat := 254096928838732967174219

theorem tailTrace_1484556 : CollatzResearch.WordTrace tailWord_1484556 prefixEnd_1484556 254096928838732967174219 := by
  unfold tailWord_1484556
  simp only [CollatzResearch.WordTrace]
  refine ⟨27073102804857314412200761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36097470406476419216267681 27073102804857314412200761)
  ·
    refine ⟨20304827103642985809150571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27073102804857314412200761 20304827103642985809150571)
    ·
      refine ⟨30457240655464478713725857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20304827103642985809150571 30457240655464478713725857)
      ·
        refine ⟨22842930491598359035294393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30457240655464478713725857 22842930491598359035294393)
        ·
          refine ⟨17132197868698769276470795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22842930491598359035294393 17132197868698769276470795)
          ·
            refine ⟨25698296803048153914706193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17132197868698769276470795 25698296803048153914706193)
            ·
              refine ⟨19273722602286115436029645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25698296803048153914706193 19273722602286115436029645)
              ·
                refine ⟨7227645975857293288511117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19273722602286115436029645 7227645975857293288511117)
                ·
                  refine ⟨2710367240946484983191669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7227645975857293288511117 2710367240946484983191669)
                  ·
                    refine ⟨254096928838732967174219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2710367240946484983191669 254096928838732967174219)
                    ·
                      rfl

theorem cell23_1484556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 3, 5].length) (baseStart_1484556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1484556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1484556 prefixEnd_1484556 := by exact prefixLift 1484556
  have htrace : WordTrace (prefixWord ++ tailWord_1484556) baseStart_1484556 baseEnd_1484556 := by
    simpa [prefixWord, tailWord_1484556, baseEnd_1484556] using wordTrace_append hprefix tailTrace_1484556
  have hstable : (prefixWord ++ tailWord_1484556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484556).length < 2 ^ (prefixWord ++ tailWord_1484556).sum := by decide
  have hdescent : baseEnd_1484556 < baseStart_1484556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484574 : List Nat := [4, 3, 2, 2, 1, 1, 1, 2, 2, 2, 3]
def baseStart_1484574 : Nat := 118140960795 + 1484574 * 2 ^ 59
def prefixEnd_1484574 : Nat := 4983230072969 + 3 ^ 40 * 1484574 * 2
def baseEnd_1484574 : Nat := 762300029167979831097575

theorem tailTrace_1484574 : CollatzResearch.WordTrace tailWord_1484574 prefixEnd_1484574 762300029167979831097575 := by
  unfold tailWord_1484574
  simp only [CollatzResearch.WordTrace]
  refine ⟨6768357765456177237319597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36097908082432945265704517 6768357765456177237319597)
  ·
    refine ⟨2538134162046066463994849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6768357765456177237319597 2538134162046066463994849)
    ·
      refine ⟨1903600621534549847996137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2538134162046066463994849 1903600621534549847996137)
      ·
        refine ⟨1427700466150912385997103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1903600621534549847996137 1427700466150912385997103)
        ·
          refine ⟨2141550699226368578995655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1427700466150912385997103 2141550699226368578995655)
          ·
            refine ⟨3212326048839552868493483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2141550699226368578995655 3212326048839552868493483)
            ·
              refine ⟨4818489073259329302740225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3212326048839552868493483 4818489073259329302740225)
              ·
                refine ⟨3613866804944496977055169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4818489073259329302740225 3613866804944496977055169)
                ·
                  refine ⟨2710400103708372732791377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3613866804944496977055169 2710400103708372732791377)
                  ·
                    refine ⟨2032800077781279549593533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2710400103708372732791377 2032800077781279549593533)
                    ·
                      refine ⟨762300029167979831097575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2032800077781279549593533 762300029167979831097575)
                      ·
                        rfl

theorem cell23_1484574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_1484574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1484574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1484574 prefixEnd_1484574 := by exact prefixLift 1484574
  have htrace : WordTrace (prefixWord ++ tailWord_1484574) baseStart_1484574 baseEnd_1484574 := by
    simpa [prefixWord, tailWord_1484574, baseEnd_1484574] using wordTrace_append hprefix tailTrace_1484574
  have hstable : (prefixWord ++ tailWord_1484574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484574).length < 2 ^ (prefixWord ++ tailWord_1484574).sum := by decide
  have hdescent : baseEnd_1484574 < baseStart_1484574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484580 : List Nat := [2, 3, 1, 3, 2, 1, 1, 1, 4, 3, 2]
def baseStart_1484580 : Nat := 118140960795 + 1484580 * 2 ^ 59
def prefixEnd_1484580 : Nat := 4983230072969 + 3 ^ 40 * 1484580 * 2
def baseEnd_1484580 : Nat := 762303110051906807622547

theorem tailTrace_1484580 : CollatzResearch.WordTrace tailWord_1484580 prefixEnd_1484580 762303110051906807622547 := by
  unfold tailWord_1484580
  simp only [CollatzResearch.WordTrace]
  refine ⟨27073540480813840461637597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36098053974418453948850129 27073540480813840461637597)
  ·
    refine ⟨10152577680305190173114099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27073540480813840461637597 10152577680305190173114099)
    ·
      refine ⟨15228866520457785259671149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10152577680305190173114099 15228866520457785259671149)
      ·
        refine ⟨5710824945171669472376681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15228866520457785259671149 5710824945171669472376681)
        ·
          refine ⟨4283118708878752104282511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5710824945171669472376681 4283118708878752104282511)
          ·
            refine ⟨6424678063318128156423767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4283118708878752104282511 6424678063318128156423767)
            ·
              refine ⟨9637017094977192234635651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6424678063318128156423767 9637017094977192234635651)
              ·
                refine ⟨14455525642465788351953477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9637017094977192234635651 14455525642465788351953477)
                ·
                  refine ⟨2710411057962335315991277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14455525642465788351953477 2710411057962335315991277)
                  ·
                    refine ⟨1016404146735875743496729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2710411057962335315991277 1016404146735875743496729)
                    ·
                      refine ⟨762303110051906807622547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1016404146735875743496729 762303110051906807622547)
                      ·
                        rfl

theorem cell23_1484580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_1484580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1484580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1484580 prefixEnd_1484580 := by exact prefixLift 1484580
  have htrace : WordTrace (prefixWord ++ tailWord_1484580) baseStart_1484580 baseEnd_1484580 := by
    simpa [prefixWord, tailWord_1484580, baseEnd_1484580] using wordTrace_append hprefix tailTrace_1484580
  have hstable : (prefixWord ++ tailWord_1484580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484580).length < 2 ^ (prefixWord ++ tailWord_1484580).sum := by decide
  have hdescent : baseEnd_1484580 < baseStart_1484580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484607 : List Nat := [1, 1, 2, 2, 7, 1, 1, 2, 1, 5]
def baseStart_1484607 : Nat := 118140960795 + 1484607 * 2 ^ 59
def prefixEnd_1484607 : Nat := 4983230072969 + 3 ^ 40 * 1484607 * 2
def baseEnd_1484607 : Nat := 254105658009859400661641

theorem tailTrace_1484607 : CollatzResearch.WordTrace tailWord_1484607 prefixEnd_1484607 254105658009859400661641 := by
  unfold tailWord_1484607
  simp only [CollatzResearch.WordTrace]
  refine ⟨54148065732529864534508075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36098710488353243023005383 54148065732529864534508075)
  ·
    refine ⟨81222098598794796801762113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54148065732529864534508075 81222098598794796801762113)
    ·
      refine ⟨60916573949096097601321585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81222098598794796801762113 60916573949096097601321585)
      ·
        refine ⟨45687430461822073200991189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60916573949096097601321585 45687430461822073200991189)
        ·
          refine ⟨1070799151448954840648231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 45687430461822073200991189 1070799151448954840648231)
          ·
            refine ⟨1606198727173432260972347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1070799151448954840648231 1606198727173432260972347)
            ·
              refine ⟨2409298090760148391458521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1606198727173432260972347 2409298090760148391458521)
              ·
                refine ⟨1806973568070111293593891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2409298090760148391458521 1806973568070111293593891)
                ·
                  refine ⟨2710460352105166940390837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1806973568070111293593891 2710460352105166940390837)
                  ·
                    refine ⟨254105658009859400661641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2710460352105166940390837 254105658009859400661641)
                    ·
                      rfl

theorem cell23_1484607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 2, 1, 5].length) (baseStart_1484607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1484607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1484607 prefixEnd_1484607 := by exact prefixLift 1484607
  have htrace : WordTrace (prefixWord ++ tailWord_1484607) baseStart_1484607 baseEnd_1484607 := by
    simpa [prefixWord, tailWord_1484607, baseEnd_1484607] using wordTrace_append hprefix tailTrace_1484607
  have hstable : (prefixWord ++ tailWord_1484607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484607).length < 2 ^ (prefixWord ++ tailWord_1484607).sum := by decide
  have hdescent : baseEnd_1484607 < baseStart_1484607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484613 : List Nat := [1, 3, 1, 1, 1, 2, 5, 1, 3, 2, 3]
def baseStart_1484613 : Nat := 118140960795 + 1484613 * 2 ^ 59
def prefixEnd_1484613 : Nat := 4983230072969 + 3 ^ 40 * 1484613 * 2
def baseEnd_1484613 : Nat := 762320054913505178509895

theorem tailTrace_1484613 : CollatzResearch.WordTrace tailWord_1484613 prefixEnd_1484613 762320054913505178509895 := by
  unfold tailWord_1484613
  simp only [CollatzResearch.WordTrace]
  refine ⟨54148284570508127559226493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36098856380338751706150995 54148284570508127559226493)
  ·
    refine ⟨20305606713940547834709935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54148284570508127559226493 20305606713940547834709935)
    ·
      refine ⟨30458410070910821752064903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20305606713940547834709935 30458410070910821752064903)
      ·
        refine ⟨45687615106366232628097355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30458410070910821752064903 45687615106366232628097355)
        ·
          refine ⟨68531422659549348942146033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45687615106366232628097355 68531422659549348942146033)
          ·
            refine ⟨51398566994662011706609525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68531422659549348942146033 51398566994662011706609525)
            ·
              refine ⟨4818615655749563597494643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51398566994662011706609525 4818615655749563597494643)
              ·
                refine ⟨7227923483624345396241965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4818615655749563597494643 7227923483624345396241965)
                ·
                  refine ⟨2710471306359129523590737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7227923483624345396241965 2710471306359129523590737)
                  ·
                    refine ⟨2032853479769347142693053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2710471306359129523590737 2032853479769347142693053)
                    ·
                      refine ⟨762320054913505178509895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2032853479769347142693053 762320054913505178509895)
                      ·
                        rfl

theorem cell23_1484613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 3, 2, 3].length) (baseStart_1484613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1484613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1484613 prefixEnd_1484613 := by exact prefixLift 1484613
  have htrace : WordTrace (prefixWord ++ tailWord_1484613) baseStart_1484613 baseEnd_1484613 := by
    simpa [prefixWord, tailWord_1484613, baseEnd_1484613] using wordTrace_append hprefix tailTrace_1484613
  have hstable : (prefixWord ++ tailWord_1484613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484613).length < 2 ^ (prefixWord ++ tailWord_1484613).sum := by decide
  have hdescent : baseEnd_1484613 < baseStart_1484613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484614 : List Nat := [6, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2]
def baseStart_1484614 : Nat := 118140960795 + 1484614 * 2 ^ 59
def prefixEnd_1484614 : Nat := 4983230072969 + 3 ^ 40 * 1484614 * 2
def baseEnd_1484614 : Nat := 762320568394159674597391

theorem tailTrace_1484614 : CollatzResearch.WordTrace tailWord_1484614 prefixEnd_1484614 762320568394159674597391 := by
  unfold tailWord_1484614
  simp only [CollatzResearch.WordTrace]
  refine ⟨1692135032609515772812903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 36098880695669669820008597 1692135032609515772812903)
  ·
    refine ⟨2538202548914273659219355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1692135032609515772812903 2538202548914273659219355)
    ·
      refine ⟨3807303823371410488829033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2538202548914273659219355 3807303823371410488829033)
      ·
        refine ⟨2855477867528557866621775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3807303823371410488829033 2855477867528557866621775)
        ·
          refine ⟨4283216801292836799932663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2855477867528557866621775 4283216801292836799932663)
          ·
            refine ⟨6424825201939255199898995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4283216801292836799932663 6424825201939255199898995)
            ·
              refine ⟨9637237802908882799848493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6424825201939255199898995 9637237802908882799848493)
              ·
                refine ⟨3613964176090831049943185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9637237802908882799848493 3613964176090831049943185)
                ·
                  refine ⟨2710473132068123287457389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3613964176090831049943185 2710473132068123287457389)
                  ·
                    refine ⟨1016427424525546232796521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2710473132068123287457389 1016427424525546232796521)
                    ·
                      refine ⟨762320568394159674597391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1016427424525546232796521 762320568394159674597391)
                      ·
                        rfl

theorem cell23_1484614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_1484614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1484614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1484614 prefixEnd_1484614 := by exact prefixLift 1484614
  have htrace : WordTrace (prefixWord ++ tailWord_1484614) baseStart_1484614 baseEnd_1484614 := by
    simpa [prefixWord, tailWord_1484614, baseEnd_1484614] using wordTrace_append hprefix tailTrace_1484614
  have hstable : (prefixWord ++ tailWord_1484614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484614).length < 2 ^ (prefixWord ++ tailWord_1484614).sum := by decide
  have hdescent : baseEnd_1484614 < baseStart_1484614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484616 : List Nat := [2, 1, 3, 1, 1, 4, 2, 9]
def baseStart_1484616 : Nat := 118140960795 + 1484616 * 2 ^ 59
def prefixEnd_1484616 : Nat := 4983230072969 + 3 ^ 40 * 1484616 * 2
def baseEnd_1484616 : Nat := 28234133161313654324903

theorem tailTrace_1484616 : CollatzResearch.WordTrace tailWord_1484616 prefixEnd_1484616 28234133161313654324903 := by
  unfold tailWord_1484616
  simp only [CollatzResearch.WordTrace]
  refine ⟨27074196994748629535792851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36098929326331506047723801 27074196994748629535792851)
  ·
    refine ⟨40611295492122944303689277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27074196994748629535792851 40611295492122944303689277)
    ·
      refine ⟨15229235809546104113883479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40611295492122944303689277 15229235809546104113883479)
      ·
        refine ⟨22843853714319156170825219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15229235809546104113883479 22843853714319156170825219)
        ·
          refine ⟨34265780571478734256237829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22843853714319156170825219 34265780571478734256237829)
          ·
            refine ⟨6424833857152262673044593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34265780571478734256237829 6424833857152262673044593)
            ·
              refine ⟨4818625392864197004783445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6424833857152262673044593 4818625392864197004783445)
              ·
                refine ⟨28234133161313654324903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4818625392864197004783445 28234133161313654324903)
                ·
                  rfl

theorem cell23_1484616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 9].length) (baseStart_1484616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1484616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1484616 prefixEnd_1484616 := by exact prefixLift 1484616
  have htrace : WordTrace (prefixWord ++ tailWord_1484616) baseStart_1484616 baseEnd_1484616 := by
    simpa [prefixWord, tailWord_1484616, baseEnd_1484616] using wordTrace_append hprefix tailTrace_1484616
  have hstable : (prefixWord ++ tailWord_1484616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484616).length < 2 ^ (prefixWord ++ tailWord_1484616).sum := by decide
  have hdescent : baseEnd_1484616 < baseStart_1484616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484656 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 5]
def baseStart_1484656 : Nat := 118140960795 + 1484656 * 2 ^ 59
def prefixEnd_1484656 : Nat := 4983230072969 + 3 ^ 40 * 1484656 * 2
def baseEnd_1484656 : Nat := 762342134581648510272197

theorem tailTrace_1484656 : CollatzResearch.WordTrace tailWord_1484656 prefixEnd_1484656 762342134581648510272197 := by
  unfold tailWord_1484656
  simp only [CollatzResearch.WordTrace]
  refine ⟨27074926454676172951520911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36099901939568230602027881 27074926454676172951520911)
  ·
    refine ⟨40612389682014259427281367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27074926454676172951520911 40612389682014259427281367)
    ·
      refine ⟨60918584523021389140922051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40612389682014259427281367 60918584523021389140922051)
      ·
        refine ⟨91377876784532083711383077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60918584523021389140922051 91377876784532083711383077)
        ·
          refine ⟨17133351897099765695884327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91377876784532083711383077 17133351897099765695884327)
          ·
            refine ⟨25700027845649648543826491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17133351897099765695884327 25700027845649648543826491)
            ·
              refine ⟨38550041768474472815739737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25700027845649648543826491 38550041768474472815739737)
              ·
                refine ⟨28912531326355854611804803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38550041768474472815739737 28912531326355854611804803)
                ·
                  refine ⟨43368796989533781917707205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28912531326355854611804803 43368796989533781917707205)
                  ·
                    refine ⟨8131649435537584109570101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43368796989533781917707205 8131649435537584109570101)
                    ·
                      refine ⟨762342134581648510272197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8131649435537584109570101 762342134581648510272197)
                      ·
                        rfl

theorem cell23_1484656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 5].length) (baseStart_1484656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1484656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1484656 prefixEnd_1484656 := by exact prefixLift 1484656
  have htrace : WordTrace (prefixWord ++ tailWord_1484656) baseStart_1484656 baseEnd_1484656 := by
    simpa [prefixWord, tailWord_1484656, baseEnd_1484656] using wordTrace_append hprefix tailTrace_1484656
  have hstable : (prefixWord ++ tailWord_1484656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484656).length < 2 ^ (prefixWord ++ tailWord_1484656).sum := by decide
  have hdescent : baseEnd_1484656 < baseStart_1484656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484760 : List Nat := [2, 1, 2, 2, 2, 2, 2, 1, 2, 5, 2]
def baseStart_1484760 : Nat := 118140960795 + 1484760 * 2 ^ 59
def prefixEnd_1484760 : Nat := 4983230072969 + 3 ^ 40 * 1484760 * 2
def baseEnd_1484760 : Nat := 762395536569716103371719

theorem tailTrace_1484760 : CollatzResearch.WordTrace tailWord_1484760 prefixEnd_1484760 762395536569716103371719 := by
  unfold tailWord_1484760
  simp only [CollatzResearch.WordTrace]
  refine ⟨27076823050487785832413867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36102430733983714443218489 27076823050487785832413867)
  ·
    refine ⟨40615234575731678748620801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27076823050487785832413867 40615234575731678748620801)
    ·
      refine ⟨30461425931798759061465601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40615234575731678748620801 30461425931798759061465601)
      ·
        refine ⟨22846069448849069296099201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30461425931798759061465601 22846069448849069296099201)
        ·
          refine ⟨17134552086636801972074401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22846069448849069296099201 17134552086636801972074401)
          ·
            refine ⟨12850914064977601479055801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17134552086636801972074401 12850914064977601479055801)
            ·
              refine ⟨9638185548733201109291851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12850914064977601479055801 9638185548733201109291851)
              ·
                refine ⟨14457278323099801663937777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9638185548733201109291851 14457278323099801663937777)
                ·
                  refine ⟨10842958742324851247953333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14457278323099801663937777 10842958742324851247953333)
                  ·
                    refine ⟨1016527382092954804495625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10842958742324851247953333 1016527382092954804495625)
                    ·
                      refine ⟨762395536569716103371719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1016527382092954804495625 762395536569716103371719)
                      ·
                        rfl

theorem cell23_1484760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 2, 5, 2].length) (baseStart_1484760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1484760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1484760 prefixEnd_1484760 := by exact prefixLift 1484760
  have htrace : WordTrace (prefixWord ++ tailWord_1484760) baseStart_1484760 baseEnd_1484760 := by
    simpa [prefixWord, tailWord_1484760, baseEnd_1484760] using wordTrace_append hprefix tailTrace_1484760
  have hstable : (prefixWord ++ tailWord_1484760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484760).length < 2 ^ (prefixWord ++ tailWord_1484760).sum := by decide
  have hdescent : baseEnd_1484760 < baseStart_1484760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484883 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 5]
def baseStart_1484883 : Nat := 118140960795 + 1484883 * 2 ^ 59
def prefixEnd_1484883 : Nat := 4983230072969 + 3 ^ 40 * 1484883 * 2
def baseEnd_1484883 : Nat := 762458694690219122133653

theorem tailTrace_1484883 : CollatzResearch.WordTrace tailWord_1484883 prefixEnd_1484883 762458694690219122133653 := by
  unfold tailWord_1484883
  simp only [CollatzResearch.WordTrace]
  refine ⟨54158132279529963671555303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36105421519686642447703535 54158132279529963671555303)
  ·
    refine ⟨81237198419294945507332955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54158132279529963671555303 81237198419294945507332955)
    ·
      refine ⟨121855797628942418260999433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81237198419294945507332955 121855797628942418260999433)
      ·
        refine ⟨91391848221706813695749575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121855797628942418260999433 91391848221706813695749575)
        ·
          refine ⟨137087772332560220543624363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91391848221706813695749575 137087772332560220543624363)
          ·
            refine ⟨205631658498840330815436545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137087772332560220543624363 205631658498840330815436545)
            ·
              refine ⟨154223743874130248111577409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205631658498840330815436545 154223743874130248111577409)
              ·
                refine ⟨115667807905597686083683057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154223743874130248111577409 115667807905597686083683057)
                ·
                  refine ⟨86750855929198264562762293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115667807905597686083683057 86750855929198264562762293)
                  ·
                    refine ⟨8132892743362337302758965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 86750855929198264562762293 8132892743362337302758965)
                    ·
                      refine ⟨762458694690219122133653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8132892743362337302758965 762458694690219122133653)
                      ·
                        rfl

theorem cell23_1484883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 5].length) (baseStart_1484883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1484883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1484883 prefixEnd_1484883 := by exact prefixLift 1484883
  have htrace : WordTrace (prefixWord ++ tailWord_1484883) baseStart_1484883 baseEnd_1484883 := by
    simpa [prefixWord, tailWord_1484883, baseEnd_1484883] using wordTrace_append hprefix tailTrace_1484883
  have hstable : (prefixWord ++ tailWord_1484883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484883).length < 2 ^ (prefixWord ++ tailWord_1484883).sum := by decide
  have hdescent : baseEnd_1484883 < baseStart_1484883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484931 : List Nat := [1, 1, 1, 3, 3, 5, 1, 1, 3, 2, 2]
def baseStart_1484931 : Nat := 118140960795 + 1484931 * 2 ^ 59
def prefixEnd_1484931 : Nat := 4983230072969 + 3 ^ 40 * 1484931 * 2
def baseEnd_1484931 : Nat := 762483341761634934333433

theorem tailTrace_1484931 : CollatzResearch.WordTrace tailWord_1484931 prefixEnd_1484931 762483341761634934333433 := by
  unfold tailWord_1484931
  simp only [CollatzResearch.WordTrace]
  refine ⟨54159882983356067869302647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36106588655570711912868431 54159882983356067869302647)
  ·
    refine ⟨81239824475034101803953971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54159882983356067869302647 81239824475034101803953971)
    ·
      refine ⟨121859736712551152705930957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81239824475034101803953971 121859736712551152705930957)
      ·
        refine ⟨45697401267206682264724109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121859736712551152705930957 45697401267206682264724109)
        ·
          refine ⟨17136525475202505849271541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45697401267206682264724109 17136525475202505849271541)
          ·
            refine ⟨1606549263300234923369207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17136525475202505849271541 1606549263300234923369207)
            ·
              refine ⟨2409823894950352385053811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1606549263300234923369207 2409823894950352385053811)
              ·
                refine ⟨3614735842425528577580717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2409823894950352385053811 3614735842425528577580717)
                ·
                  refine ⟨1355525940909573216592769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3614735842425528577580717 1355525940909573216592769)
                  ·
                    refine ⟨1016644455682179912444577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1355525940909573216592769 1016644455682179912444577)
                    ·
                      refine ⟨762483341761634934333433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1016644455682179912444577 762483341761634934333433)
                      ·
                        rfl

theorem cell23_1484931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 3, 2, 2].length) (baseStart_1484931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1484931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1484931 prefixEnd_1484931 := by exact prefixLift 1484931
  have htrace : WordTrace (prefixWord ++ tailWord_1484931) baseStart_1484931 baseEnd_1484931 := by
    simpa [prefixWord, tailWord_1484931, baseEnd_1484931] using wordTrace_append hprefix tailTrace_1484931
  have hstable : (prefixWord ++ tailWord_1484931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484931).length < 2 ^ (prefixWord ++ tailWord_1484931).sum := by decide
  have hdescent : baseEnd_1484931 < baseStart_1484931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484948 : List Nat := [2, 4, 2, 3, 1, 2, 1, 2, 1, 1, 4]
def baseStart_1484948 : Nat := 118140960795 + 1484948 * 2 ^ 59
def prefixEnd_1484948 : Nat := 4983230072969 + 3 ^ 40 * 1484948 * 2
def baseEnd_1484948 : Nat := 762492070932761367820855

theorem tailTrace_1484948 : CollatzResearch.WordTrace tailWord_1484948 prefixEnd_1484948 762492070932761367820855 := by
  unfold tailWord_1484948
  simp only [CollatzResearch.WordTrace]
  refine ⟨27080251512147239886335749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36107002016196319848447665 27080251512147239886335749)
  ·
    refine ⟨5077547158527607478687953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27080251512147239886335749 5077547158527607478687953)
    ·
      refine ⟨3808160368895705609015965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5077547158527607478687953 3808160368895705609015965)
      ·
        refine ⟨1428060138335889603380987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3808160368895705609015965 1428060138335889603380987)
        ·
          refine ⟨2142090207503834405071481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1428060138335889603380987 2142090207503834405071481)
          ·
            refine ⟨1606567655627875803803611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2142090207503834405071481 1606567655627875803803611)
            ·
              refine ⟨2409851483441813705705417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1606567655627875803803611 2409851483441813705705417)
              ·
                refine ⟨1807388612581360279279063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2409851483441813705705417 1807388612581360279279063)
                ·
                  refine ⟨2711082918872040418918595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1807388612581360279279063 2711082918872040418918595)
                  ·
                    refine ⟨4066624378308060628377893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2711082918872040418918595 4066624378308060628377893)
                    ·
                      refine ⟨762492070932761367820855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4066624378308060628377893 762492070932761367820855)
                      ·
                        rfl

theorem cell23_1484948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_1484948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1484948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1484948 prefixEnd_1484948 := by exact prefixLift 1484948
  have htrace : WordTrace (prefixWord ++ tailWord_1484948) baseStart_1484948 baseEnd_1484948 := by
    simpa [prefixWord, tailWord_1484948, baseEnd_1484948] using wordTrace_append hprefix tailTrace_1484948
  have hstable : (prefixWord ++ tailWord_1484948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484948).length < 2 ^ (prefixWord ++ tailWord_1484948).sum := by decide
  have hdescent : baseEnd_1484948 < baseStart_1484948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484951 : List Nat := [1, 1, 3, 3, 4, 2, 1, 2, 1, 2, 3]
def baseStart_1484951 : Nat := 118140960795 + 1484951 * 2 ^ 59
def prefixEnd_1484951 : Nat := 4983230072969 + 3 ^ 40 * 1484951 * 2
def baseEnd_1484951 : Nat := 762493611374724856083341

theorem tailTrace_1484951 : CollatzResearch.WordTrace tailWord_1484951 prefixEnd_1484951 762493611374724856083341 := by
  unfold tailWord_1484951
  simp only [CollatzResearch.WordTrace]
  refine ⟨54160612443283611285030707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36107074962189074190020471 54160612443283611285030707)
  ·
    refine ⟨81240918664925416927546061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54160612443283611285030707 81240918664925416927546061)
    ·
      refine ⟨30465344499347031347829773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81240918664925416927546061 30465344499347031347829773)
      ·
        refine ⟨11424504187255136755436165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30465344499347031347829773 11424504187255136755436165)
        ·
          refine ⟨2142094535110338141644281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11424504187255136755436165 2142094535110338141644281)
          ·
            refine ⟨1606570901332753606233211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2142094535110338141644281 1606570901332753606233211)
            ·
              refine ⟨2409856351999130409349817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1606570901332753606233211 2409856351999130409349817)
              ·
                refine ⟨1807392263999347807012363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2409856351999130409349817 1807392263999347807012363)
                ·
                  refine ⟨2711088395999021710518545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1807392263999347807012363 2711088395999021710518545)
                  ·
                    refine ⟨2033316296999266282888909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2711088395999021710518545 2033316296999266282888909)
                    ·
                      refine ⟨762493611374724856083341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2033316296999266282888909 762493611374724856083341)
                      ·
                        rfl

theorem cell23_1484951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_1484951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1484951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1484951 prefixEnd_1484951 := by exact prefixLift 1484951
  have htrace : WordTrace (prefixWord ++ tailWord_1484951) baseStart_1484951 baseEnd_1484951 := by
    simpa [prefixWord, tailWord_1484951, baseEnd_1484951] using wordTrace_append hprefix tailTrace_1484951
  have hstable : (prefixWord ++ tailWord_1484951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484951).length < 2 ^ (prefixWord ++ tailWord_1484951).sum := by decide
  have hdescent : baseEnd_1484951 < baseStart_1484951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484964 : List Nat := [2, 3, 1, 2, 4, 1, 1, 2, 1, 3, 3]
def baseStart_1484964 : Nat := 118140960795 + 1484964 * 2 ^ 59
def prefixEnd_1484964 : Nat := 4983230072969 + 3 ^ 40 * 1484964 * 2
def baseEnd_1484964 : Nat := 762500286623233305220781

theorem tailTrace_1484964 : CollatzResearch.WordTrace tailWord_1484964 prefixEnd_1484964 762500286623233305220781 := by
  unfold tailWord_1484964
  simp only [CollatzResearch.WordTrace]
  refine ⟨27080543296118257252626973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36107391061491009670169297 27080543296118257252626973)
  ·
    refine ⟨10155203736044346469735115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27080543296118257252626973 10155203736044346469735115)
    ·
      refine ⟨15232805604066519704602673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10155203736044346469735115 15232805604066519704602673)
      ·
        refine ⟨11424604203049889778452005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15232805604066519704602673 11424604203049889778452005)
        ·
          refine ⟨2142113288071854333459751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11424604203049889778452005 2142113288071854333459751)
          ·
            refine ⟨3213169932107781500189627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2142113288071854333459751 3213169932107781500189627)
            ·
              refine ⟨4819754898161672250284441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3213169932107781500189627 4819754898161672250284441)
              ·
                refine ⟨3614816173621254187713331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4819754898161672250284441 3614816173621254187713331)
                ·
                  refine ⟨5422224260431881281569997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3614816173621254187713331 5422224260431881281569997)
                  ·
                    refine ⟨2033334097661955480588749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5422224260431881281569997 2033334097661955480588749)
                    ·
                      refine ⟨762500286623233305220781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2033334097661955480588749 762500286623233305220781)
                      ·
                        rfl

theorem cell23_1484964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_1484964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1484964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1484964 prefixEnd_1484964 := by exact prefixLift 1484964
  have htrace : WordTrace (prefixWord ++ tailWord_1484964) baseStart_1484964 baseEnd_1484964 := by
    simpa [prefixWord, tailWord_1484964, baseEnd_1484964] using wordTrace_append hprefix tailTrace_1484964
  have hstable : (prefixWord ++ tailWord_1484964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484964).length < 2 ^ (prefixWord ++ tailWord_1484964).sum := by decide
  have hdescent : baseEnd_1484964 < baseStart_1484964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484987 : List Nat := [1, 1, 1, 1, 1, 2, 5, 2, 3, 4, 2]
def baseStart_1484987 : Nat := 118140960795 + 1484987 * 2 ^ 59
def prefixEnd_1484987 : Nat := 4983230072969 + 3 ^ 40 * 1484987 * 2
def baseEnd_1484987 : Nat := 762512096678286715233175

theorem tailTrace_1484987 : CollatzResearch.WordTrace tailWord_1484987 prefixEnd_1484987 762512096678286715233175 := by
  unfold tailWord_1484987
  simp only [CollatzResearch.WordTrace]
  refine ⟨54161925471153189433341215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36107950314102126288894143 54161925471153189433341215)
  ·
    refine ⟨81242888206729784150011823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54161925471153189433341215 81242888206729784150011823)
    ·
      refine ⟨121864332310094676225017735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81242888206729784150011823 121864332310094676225017735)
      ·
        refine ⟨182796498465142014337526603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121864332310094676225017735 182796498465142014337526603)
        ·
          refine ⟨274194747697713021506289905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182796498465142014337526603 274194747697713021506289905)
          ·
            refine ⟨205646060773284766129717429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274194747697713021506289905 205646060773284766129717429)
            ·
              refine ⟨19279318197495446824661009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 205646060773284766129717429 19279318197495446824661009)
              ·
                refine ⟨14459488648121585118495757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19279318197495446824661009 14459488648121585118495757)
                ·
                  refine ⟨5422308243045594419435909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14459488648121585118495757 5422308243045594419435909)
                  ·
                    refine ⟨1016682795571048953644233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5422308243045594419435909 1016682795571048953644233)
                    ·
                      refine ⟨762512096678286715233175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1016682795571048953644233 762512096678286715233175)
                      ·
                        rfl

theorem cell23_1484987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 4, 2].length) (baseStart_1484987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1484987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1484987 prefixEnd_1484987 := by exact prefixLift 1484987
  have htrace : WordTrace (prefixWord ++ tailWord_1484987) baseStart_1484987 baseEnd_1484987 := by
    simpa [prefixWord, tailWord_1484987, baseEnd_1484987] using wordTrace_append hprefix tailTrace_1484987
  have hstable : (prefixWord ++ tailWord_1484987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484987).length < 2 ^ (prefixWord ++ tailWord_1484987).sum := by decide
  have hdescent : baseEnd_1484987 < baseStart_1484987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485021 : List Nat := [1, 4, 3, 2, 1, 1, 2, 2, 1, 4, 2]
def baseStart_1485021 : Nat := 118140960795 + 1485021 * 2 ^ 59
def prefixEnd_1485021 : Nat := 4983230072969 + 3 ^ 40 * 1485021 * 2
def baseEnd_1485021 : Nat := 762529555020539582208019

theorem tailTrace_1485021 : CollatzResearch.WordTrace tailWord_1485021 prefixEnd_1485021 762529555020539582208019 := by
  unfold tailWord_1485021
  simp only [CollatzResearch.WordTrace]
  refine ⟨54163165553030013240078917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36108777035353342160052611 54163165553030013240078917)
  ·
    refine ⟨10155593541193127482514797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54163165553030013240078917 10155593541193127482514797)
    ·
      refine ⟨3808347577947422805943049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10155593541193127482514797 3808347577947422805943049)
      ·
        refine ⟨2856260683460567104457287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3808347577947422805943049 2856260683460567104457287)
        ·
          refine ⟨4284391025190850656685931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2856260683460567104457287 4284391025190850656685931)
          ·
            refine ⟨6426586537786275985028897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4284391025190850656685931 6426586537786275985028897)
            ·
              refine ⟨4819939903339706988771673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6426586537786275985028897 4819939903339706988771673)
              ·
                refine ⟨3614954927504780241578755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4819939903339706988771673 3614954927504780241578755)
                ·
                  refine ⟨5422432391257170362368133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3614954927504780241578755 5422432391257170362368133)
                  ·
                    refine ⟨1016706073360719442944025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5422432391257170362368133 1016706073360719442944025)
                    ·
                      refine ⟨762529555020539582208019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1016706073360719442944025 762529555020539582208019)
                      ·
                        rfl

theorem cell23_1485021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_1485021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485021 prefixEnd_1485021 := by exact prefixLift 1485021
  have htrace : WordTrace (prefixWord ++ tailWord_1485021) baseStart_1485021 baseEnd_1485021 := by
    simpa [prefixWord, tailWord_1485021, baseEnd_1485021] using wordTrace_append hprefix tailTrace_1485021
  have hstable : (prefixWord ++ tailWord_1485021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485021).length < 2 ^ (prefixWord ++ tailWord_1485021).sum := by decide
  have hdescent : baseEnd_1485021 < baseStart_1485021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485054 : List Nat := [4, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3]
def baseStart_1485054 : Nat := 118140960795 + 1485054 * 2 ^ 59
def prefixEnd_1485054 : Nat := 4983230072969 + 3 ^ 40 * 1485054 * 2
def baseEnd_1485054 : Nat := 762546499882137953095367

theorem tailTrace_1485054 : CollatzResearch.WordTrace tailWord_1485054 prefixEnd_1485054 762546499882137953095367 := by
  unfold tailWord_1485054
  simp only [CollatzResearch.WordTrace]
  refine ⟨6770546145238807484503777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36109579441273639917353477 6770546145238807484503777)
  ·
    refine ⟨5077909608929105613377833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6770546145238807484503777 5077909608929105613377833)
    ·
      refine ⟨3808432206696829210033375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5077909608929105613377833 3808432206696829210033375)
      ·
        refine ⟨5712648310045243815050063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3808432206696829210033375 5712648310045243815050063)
        ·
          refine ⟨8568972465067865722575095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5712648310045243815050063 8568972465067865722575095)
          ·
            refine ⟨12853458697601798583862643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8568972465067865722575095 12853458697601798583862643)
            ·
              refine ⟨19280188046402697875793965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12853458697601798583862643 19280188046402697875793965)
              ·
                refine ⟨7230070517401011703422737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19280188046402697875793965 7230070517401011703422737)
                ·
                  refine ⟨5422552888050758777567053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7230070517401011703422737 5422552888050758777567053)
                  ·
                    refine ⟨2033457333019034541587645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5422552888050758777567053 2033457333019034541587645)
                    ·
                      refine ⟨762546499882137953095367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2033457333019034541587645 762546499882137953095367)
                      ·
                        rfl

theorem cell23_1485054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_1485054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485054 prefixEnd_1485054 := by exact prefixLift 1485054
  have htrace : WordTrace (prefixWord ++ tailWord_1485054) baseStart_1485054 baseEnd_1485054 := by
    simpa [prefixWord, tailWord_1485054, baseEnd_1485054] using wordTrace_append hprefix tailTrace_1485054
  have hstable : (prefixWord ++ tailWord_1485054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485054).length < 2 ^ (prefixWord ++ tailWord_1485054).sum := by decide
  have hdescent : baseEnd_1485054 < baseStart_1485054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485077 : List Nat := [1, 3, 2, 1, 2, 1, 4, 1, 1, 3, 4]
def baseStart_1485077 : Nat := 118140960795 + 1485077 * 2 ^ 59
def prefixEnd_1485077 : Nat := 4983230072969 + 3 ^ 40 * 1485077 * 2
def baseEnd_1485077 : Nat := 762558309937191363107761

theorem tailTrace_1485077 : CollatzResearch.WordTrace tailWord_1485077 prefixEnd_1485077 762558309937191363107761 := by
  unfold tailWord_1485077
  simp only [CollatzResearch.WordTrace]
  refine ⟨54165208040827134804117485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36110138693884756536078323 54165208040827134804117485)
  ·
    refine ⟨20311953015310175551544057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54165208040827134804117485 20311953015310175551544057)
    ·
      refine ⟨15233964761482631663658043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20311953015310175551544057 15233964761482631663658043)
      ·
        refine ⟨22850947142223947495487065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15233964761482631663658043 22850947142223947495487065)
        ·
          refine ⟨17138210356667960621615299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22850947142223947495487065 17138210356667960621615299)
          ·
            refine ⟨25707315535001940932422949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17138210356667960621615299 25707315535001940932422949)
            ·
              refine ⟨4820121662812863924829303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25707315535001940932422949 4820121662812863924829303)
              ·
                refine ⟨7230182494219295887243955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4820121662812863924829303 7230182494219295887243955)
                ·
                  refine ⟨10845273741328943830865933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7230182494219295887243955 10845273741328943830865933)
                  ·
                    refine ⟨4066977652998353936574725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10845273741328943830865933 4066977652998353936574725)
                    ·
                      refine ⟨762558309937191363107761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4066977652998353936574725 762558309937191363107761)
                      ·
                        rfl

theorem cell23_1485077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_1485077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485077 prefixEnd_1485077 := by exact prefixLift 1485077
  have htrace : WordTrace (prefixWord ++ tailWord_1485077) baseStart_1485077 baseEnd_1485077 := by
    simpa [prefixWord, tailWord_1485077, baseEnd_1485077] using wordTrace_append hprefix tailTrace_1485077
  have hstable : (prefixWord ++ tailWord_1485077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485077).length < 2 ^ (prefixWord ++ tailWord_1485077).sum := by decide
  have hdescent : baseEnd_1485077 < baseStart_1485077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485095 : List Nat := [1, 1, 8, 1, 2, 1, 1, 1, 7]
def baseStart_1485095 : Nat := 118140960795 + 1485095 * 2 ^ 59
def prefixEnd_1485095 : Nat := 4983230072969 + 3 ^ 40 * 1485095 * 2
def baseEnd_1485095 : Nat := 84729728065441365853631

theorem tailTrace_1485095 : CollatzResearch.WordTrace tailWord_1485095 prefixEnd_1485095 84729728065441365853631 := by
  unfold tailWord_1485095
  simp only [CollatzResearch.WordTrace]
  refine ⟨54165864554761923878272739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36110576369841282585515159 54165864554761923878272739)
  ·
    refine ⟨81248796832142885817409109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54165864554761923878272739 81248796832142885817409109)
    ·
      refine ⟨952134337876674443172763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 81248796832142885817409109 952134337876674443172763)
      ·
        refine ⟨1428201506815011664759145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 952134337876674443172763 1428201506815011664759145)
        ·
          refine ⟨1071151130111258748569359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1428201506815011664759145 1071151130111258748569359)
          ·
            refine ⟨1606726695166888122854039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1071151130111258748569359 1606726695166888122854039)
            ·
              refine ⟨2410090042750332184281059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1606726695166888122854039 2410090042750332184281059)
              ·
                refine ⟨3615135064125498276421589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2410090042750332184281059 3615135064125498276421589)
                ·
                  refine ⟨84729728065441365853631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3615135064125498276421589 84729728065441365853631)
                  ·
                    rfl

theorem cell23_1485095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 7].length) (baseStart_1485095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485095 prefixEnd_1485095 := by exact prefixLift 1485095
  have htrace : WordTrace (prefixWord ++ tailWord_1485095) baseStart_1485095 baseEnd_1485095 := by
    simpa [prefixWord, tailWord_1485095, baseEnd_1485095] using wordTrace_append hprefix tailTrace_1485095
  have hstable : (prefixWord ++ tailWord_1485095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485095).length < 2 ^ (prefixWord ++ tailWord_1485095).sum := by decide
  have hdescent : baseEnd_1485095 < baseStart_1485095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485101 : List Nat := [1, 5, 3, 1, 2, 1, 1, 1, 1, 2, 5]
def baseStart_1485101 : Nat := 118140960795 + 1485101 * 2 ^ 59
def prefixEnd_1485101 : Nat := 4983230072969 + 3 ^ 40 * 1485101 * 2
def baseEnd_1485101 : Nat := 762570633472899269207651

theorem tailTrace_1485101 : CollatzResearch.WordTrace tailWord_1485101 prefixEnd_1485101 762570633472899269207651 := by
  unfold tailWord_1485101
  simp only [CollatzResearch.WordTrace]
  refine ⟨54166083392740186902991157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36110722261826791268660771 54166083392740186902991157)
  ·
    refine ⟨5078070318069392522155421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54166083392740186902991157 5078070318069392522155421)
    ·
      refine ⟨1904276369276022195808283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5078070318069392522155421 1904276369276022195808283)
      ·
        refine ⟨2856414553914033293712425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1904276369276022195808283 2856414553914033293712425)
        ·
          refine ⟨2142310915435524970284319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2856414553914033293712425 2142310915435524970284319)
          ·
            refine ⟨3213466373153287455426479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2142310915435524970284319 3213466373153287455426479)
            ·
              refine ⟨4820199559729931183139719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3213466373153287455426479 4820199559729931183139719)
              ·
                refine ⟨7230299339594896774709579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4820199559729931183139719 7230299339594896774709579)
                ·
                  refine ⟨10845449009392345162064369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7230299339594896774709579 10845449009392345162064369)
                  ·
                    refine ⟨8134086757044258871548277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10845449009392345162064369 8134086757044258871548277)
                    ·
                      refine ⟨762570633472899269207651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8134086757044258871548277 762570633472899269207651)
                      ·
                        rfl

theorem cell23_1485101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_1485101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485101 prefixEnd_1485101 := by exact prefixLift 1485101
  have htrace : WordTrace (prefixWord ++ tailWord_1485101) baseStart_1485101 baseEnd_1485101 := by
    simpa [prefixWord, tailWord_1485101, baseEnd_1485101] using wordTrace_append hprefix tailTrace_1485101
  have hstable : (prefixWord ++ tailWord_1485101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485101).length < 2 ^ (prefixWord ++ tailWord_1485101).sum := by decide
  have hdescent : baseEnd_1485101 < baseStart_1485101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485144 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 7, 1, 3]
def baseStart_1485144 : Nat := 118140960795 + 1485144 * 2 ^ 59
def prefixEnd_1485144 : Nat := 4983230072969 + 3 ^ 40 * 1485144 * 2
def baseEnd_1485144 : Nat := 762592713141042600969953

theorem tailTrace_1485144 : CollatzResearch.WordTrace tailWord_1485144 prefixEnd_1485144 762592713141042600969953 := by
  unfold tailWord_1485144
  simp only [CollatzResearch.WordTrace]
  refine ⟨27083825865792202623403243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36111767821056270164537657 27083825865792202623403243)
  ·
    refine ⟨40625738798688303935104865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27083825865792202623403243 40625738798688303935104865)
    ·
      refine ⟨30469304099016227951328649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40625738798688303935104865 30469304099016227951328649)
      ·
        refine ⟨22851978074262170963496487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30469304099016227951328649 22851978074262170963496487)
        ·
          refine ⟨34277967111393256445244731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22851978074262170963496487 34277967111393256445244731)
          ·
            refine ⟨51416950667089884667867097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34277967111393256445244731 51416950667089884667867097)
            ·
              refine ⟨38562713000317413500900323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51416950667089884667867097 38562713000317413500900323)
              ·
                refine ⟨57844069500476120251350485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38562713000317413500900323 57844069500476120251350485)
                ·
                  refine ⟨1355720378917409068391027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 57844069500476120251350485 1355720378917409068391027)
                  ·
                    refine ⟨2033580568376113602586541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1355720378917409068391027 2033580568376113602586541)
                    ·
                      refine ⟨762592713141042600969953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2033580568376113602586541 762592713141042600969953)
                      ·
                        rfl

theorem cell23_1485144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 7, 1, 3].length) (baseStart_1485144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485144 prefixEnd_1485144 := by exact prefixLift 1485144
  have htrace : WordTrace (prefixWord ++ tailWord_1485144) baseStart_1485144 baseEnd_1485144 := by
    simpa [prefixWord, tailWord_1485144, baseEnd_1485144] using wordTrace_append hprefix tailTrace_1485144
  have hstable : (prefixWord ++ tailWord_1485144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485144).length < 2 ^ (prefixWord ++ tailWord_1485144).sum := by decide
  have hdescent : baseEnd_1485144 < baseStart_1485144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485198 : List Nat := [4, 1, 1, 4, 1, 1, 4, 1, 1, 5]
def baseStart_1485198 : Nat := 118140960795 + 1485198 * 2 ^ 59
def prefixEnd_1485198 : Nat := 4983230072969 + 3 ^ 40 * 1485198 * 2
def baseEnd_1485198 : Nat := 254206813698795129898235

theorem tailTrace_1485198 : CollatzResearch.WordTrace tailWord_1485198 prefixEnd_1485198 254206813698795129898235 := by
  unfold tailWord_1485198
  simp only [CollatzResearch.WordTrace]
  refine ⟨6771202659173596558659031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36113080848925848312848165 6771202659173596558659031)
  ·
    refine ⟨10156803988760394837988547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6771202659173596558659031 10156803988760394837988547)
    ·
      refine ⟨15235205983140592256982821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10156803988760394837988547 15235205983140592256982821)
      ·
        refine ⟨2856601121838861048184279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15235205983140592256982821 2856601121838861048184279)
        ·
          refine ⟨4284901682758291572276419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2856601121838861048184279 4284901682758291572276419)
          ·
            refine ⟨6427352524137437358414629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4284901682758291572276419 6427352524137437358414629)
            ·
              refine ⟨1205128598275769504702743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6427352524137437358414629 1205128598275769504702743)
              ·
                refine ⟨1807692897413654257054115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1205128598275769504702743 1807692897413654257054115)
                ·
                  refine ⟨2711539346120481385581173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1807692897413654257054115 2711539346120481385581173)
                  ·
                    refine ⟨254206813698795129898235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2711539346120481385581173 254206813698795129898235)
                    ·
                      rfl

theorem cell23_1485198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 1, 5].length) (baseStart_1485198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485198 prefixEnd_1485198 := by exact prefixLift 1485198
  have htrace : WordTrace (prefixWord ++ tailWord_1485198) baseStart_1485198 baseEnd_1485198 := by
    simpa [prefixWord, tailWord_1485198, baseEnd_1485198] using wordTrace_append hprefix tailTrace_1485198
  have hstable : (prefixWord ++ tailWord_1485198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485198).length < 2 ^ (prefixWord ++ tailWord_1485198).sum := by decide
  have hdescent : baseEnd_1485198 < baseStart_1485198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485241 : List Nat := [1, 2, 1, 4, 3, 3, 2, 7]
def baseStart_1485241 : Nat := 118140960795 + 1485241 * 2 ^ 59
def prefixEnd_1485241 : Nat := 4983230072969 + 3 ^ 40 * 1485241 * 2
def baseEnd_1485241 : Nat := 28246019287575137831741

theorem tailTrace_1485241 : CollatzResearch.WordTrace tailWord_1485241 prefixEnd_1485241 28246019287575137831741 := by
  unfold tailWord_1485241
  simp only [CollatzResearch.WordTrace]
  refine ⟨54171189612232990813087577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36114126408155327208725051 54171189612232990813087577)
  ·
    refine ⟨40628392209174743109815683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54171189612232990813087577 40628392209174743109815683)
    ·
      refine ⟨60942588313762114664723525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40628392209174743109815683 60942588313762114664723525)
      ·
        refine ⟨11426735308830396499635661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60942588313762114664723525 11426735308830396499635661)
        ·
          refine ⟨4285025740811398687363373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11426735308830396499635661 4285025740811398687363373)
          ·
            refine ⟨1606884652804274507761265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4285025740811398687363373 1606884652804274507761265)
            ·
              refine ⟨1205163489603205880820949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1606884652804274507761265 1205163489603205880820949)
              ·
                refine ⟨28246019287575137831741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1205163489603205880820949 28246019287575137831741)
                ·
                  rfl

theorem cell23_1485241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 7].length) (baseStart_1485241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485241 prefixEnd_1485241 := by exact prefixLift 1485241
  have htrace : WordTrace (prefixWord ++ tailWord_1485241) baseStart_1485241 baseEnd_1485241 := by
    simpa [prefixWord, tailWord_1485241, baseEnd_1485241] using wordTrace_append hprefix tailTrace_1485241
  have hstable : (prefixWord ++ tailWord_1485241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485241).length < 2 ^ (prefixWord ++ tailWord_1485241).sum := by decide
  have hdescent : baseEnd_1485241 < baseStart_1485241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485268 : List Nat := [2, 4, 1, 2, 2, 1, 2, 1, 4, 1, 3]
def baseStart_1485268 : Nat := 118140960795 + 1485268 * 2 ^ 59
def prefixEnd_1485268 : Nat := 4983230072969 + 3 ^ 40 * 1485268 * 2
def baseEnd_1485268 : Nat := 762656384742200115819383

theorem tailTrace_1485268 : CollatzResearch.WordTrace tailWord_1485268 prefixEnd_1485268 762656384742200115819383 := by
  unfold tailWord_1485268
  simp only [CollatzResearch.WordTrace]
  refine ⟨27086087191567587212160229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36114782922090116282880305 27086087191567587212160229)
  ·
    refine ⟨5078641348418922602280043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27086087191567587212160229 5078641348418922602280043)
    ·
      refine ⟨7617962022628383903420065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5078641348418922602280043 7617962022628383903420065)
      ·
        refine ⟨5713471516971287927565049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7617962022628383903420065 5713471516971287927565049)
        ·
          refine ⟨4285103637728465945673787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5713471516971287927565049 4285103637728465945673787)
          ·
            refine ⟨6427655456592698918510681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4285103637728465945673787 6427655456592698918510681)
            ·
              refine ⟨4820741592444524188883011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6427655456592698918510681 4820741592444524188883011)
              ·
                refine ⟨7231112388666786283324517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4820741592444524188883011 7231112388666786283324517)
                ·
                  refine ⟨1355833572875022428123347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7231112388666786283324517 1355833572875022428123347)
                  ·
                    refine ⟨2033750359312533642185021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1355833572875022428123347 2033750359312533642185021)
                    ·
                      refine ⟨762656384742200115819383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2033750359312533642185021 762656384742200115819383)
                      ·
                        rfl

theorem cell23_1485268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_1485268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485268 prefixEnd_1485268 := by exact prefixLift 1485268
  have htrace : WordTrace (prefixWord ++ tailWord_1485268) baseStart_1485268 baseEnd_1485268 := by
    simpa [prefixWord, tailWord_1485268, baseEnd_1485268] using wordTrace_append hprefix tailTrace_1485268
  have hstable : (prefixWord ++ tailWord_1485268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485268).length < 2 ^ (prefixWord ++ tailWord_1485268).sum := by decide
  have hdescent : baseEnd_1485268 < baseStart_1485268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485274 : List Nat := [3, 1, 1, 2, 3, 1, 2, 1, 2, 3, 4]
def baseStart_1485274 : Nat := 118140960795 + 1485274 * 2 ^ 59
def prefixEnd_1485274 : Nat := 4983230072969 + 3 ^ 40 * 1485274 * 2
def baseEnd_1485274 : Nat := 762659465626127092344355

theorem tailTrace_1485274 : CollatzResearch.WordTrace tailWord_1485274 prefixEnd_1485274 762659465626127092344355 := by
  unfold tailWord_1485274
  simp only [CollatzResearch.WordTrace]
  refine ⟨13543098305278359362259719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36114928814075624966025917 13543098305278359362259719)
  ·
    refine ⟨20314647457917539043389579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13543098305278359362259719 20314647457917539043389579)
    ·
      refine ⟨30471971186876308565084369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20314647457917539043389579 30471971186876308565084369)
      ·
        refine ⟨22853978390157231423813277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30471971186876308565084369 22853978390157231423813277)
        ·
          refine ⟨8570241896308961783929979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22853978390157231423813277 8570241896308961783929979)
          ·
            refine ⟨12855362844463442675894969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8570241896308961783929979 12855362844463442675894969)
            ·
              refine ⟨9641522133347582006921227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12855362844463442675894969 9641522133347582006921227)
              ·
                refine ⟨14462283200021373010381841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9641522133347582006921227 14462283200021373010381841)
                ·
                  refine ⟨10846712400016029757786381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14462283200021373010381841 10846712400016029757786381)
                  ·
                    refine ⟨4067517150006011159169893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10846712400016029757786381 4067517150006011159169893)
                    ·
                      refine ⟨762659465626127092344355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4067517150006011159169893 762659465626127092344355)
                      ·
                        rfl

theorem cell23_1485274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_1485274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485274 prefixEnd_1485274 := by exact prefixLift 1485274
  have htrace : WordTrace (prefixWord ++ tailWord_1485274) baseStart_1485274 baseEnd_1485274 := by
    simpa [prefixWord, tailWord_1485274, baseEnd_1485274] using wordTrace_append hprefix tailTrace_1485274
  have hstable : (prefixWord ++ tailWord_1485274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485274).length < 2 ^ (prefixWord ++ tailWord_1485274).sum := by decide
  have hdescent : baseEnd_1485274 < baseStart_1485274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485285 : List Nat := [1, 3, 1, 5, 2, 1, 1, 3, 2, 1, 3]
def baseStart_1485285 : Nat := 118140960795 + 1485285 * 2 ^ 59
def prefixEnd_1485285 : Nat := 4983230072969 + 3 ^ 40 * 1485285 * 2
def baseEnd_1485285 : Nat := 762665113913326549306805

theorem tailTrace_1485285 : CollatzResearch.WordTrace tailWord_1485285 prefixEnd_1485285 762665113913326549306805 := by
  unfold tailWord_1485285
  simp only [CollatzResearch.WordTrace]
  refine ⟨54172794424073586327689309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36115196282715724218459539 54172794424073586327689309)
  ·
    refine ⟨20314797909027594872883491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54172794424073586327689309 20314797909027594872883491)
    ·
      refine ⟨30472196863541392309325237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20314797909027594872883491 30472196863541392309325237)
      ·
        refine ⟨2856768455957005528999241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30472196863541392309325237 2856768455957005528999241)
        ·
          refine ⟨2142576341967754146749431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2856768455957005528999241 2142576341967754146749431)
          ·
            refine ⟨3213864512951631220124147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2142576341967754146749431 3213864512951631220124147)
            ·
              refine ⟨4820796769427446830186221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3213864512951631220124147 4820796769427446830186221)
              ·
                refine ⟨1807798788535292561319833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4820796769427446830186221 1807798788535292561319833)
                ·
                  refine ⟨1355849091401469420989875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1807798788535292561319833 1355849091401469420989875)
                  ·
                    refine ⟨2033773637102204131484813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1355849091401469420989875 2033773637102204131484813)
                    ·
                      refine ⟨762665113913326549306805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2033773637102204131484813 762665113913326549306805)
                      ·
                        rfl

theorem cell23_1485285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_1485285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485285 prefixEnd_1485285 := by exact prefixLift 1485285
  have htrace : WordTrace (prefixWord ++ tailWord_1485285) baseStart_1485285 baseEnd_1485285 := by
    simpa [prefixWord, tailWord_1485285, baseEnd_1485285] using wordTrace_append hprefix tailTrace_1485285
  have hstable : (prefixWord ++ tailWord_1485285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485285).length < 2 ^ (prefixWord ++ tailWord_1485285).sum := by decide
  have hdescent : baseEnd_1485285 < baseStart_1485285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485291 : List Nat := [1, 1, 1, 1, 2, 3, 4, 3, 1, 4, 2]
def baseStart_1485291 : Nat := 118140960795 + 1485291 * 2 ^ 59
def prefixEnd_1485291 : Nat := 4983230072969 + 3 ^ 40 * 1485291 * 2
def baseEnd_1485291 : Nat := 762668194797253525831777

theorem tailTrace_1485291 : CollatzResearch.WordTrace tailWord_1485291 prefixEnd_1485291 762668194797253525831777 := by
  unfold tailWord_1485291
  simp only [CollatzResearch.WordTrace]
  refine ⟨54173013262051849352407727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36115342174701232901605151 54173013262051849352407727)
  ·
    refine ⟨81259519893077774028611591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54173013262051849352407727 81259519893077774028611591)
    ·
      refine ⟨121889279839616661042917387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81259519893077774028611591 121889279839616661042917387)
      ·
        refine ⟨182833919759424991564376081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121889279839616661042917387 182833919759424991564376081)
        ·
          refine ⟨137125439819568743673282061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182833919759424991564376081 137125439819568743673282061)
          ·
            refine ⟨51422039932338278877480773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137125439819568743673282061 51422039932338278877480773)
            ·
              refine ⟨9641632487313427289527645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51422039932338278877480773 9641632487313427289527645)
              ·
                refine ⟨3615612182742535233572867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9641632487313427289527645 3615612182742535233572867)
                ·
                  refine ⟨5423418274113802850359301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3615612182742535233572867 5423418274113802850359301)
                  ·
                    refine ⟨1016890926396338034442369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5423418274113802850359301 1016890926396338034442369)
                    ·
                      refine ⟨762668194797253525831777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1016890926396338034442369 762668194797253525831777)
                      ·
                        rfl

theorem cell23_1485291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 4, 2].length) (baseStart_1485291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485291 prefixEnd_1485291 := by exact prefixLift 1485291
  have htrace : WordTrace (prefixWord ++ tailWord_1485291) baseStart_1485291 baseEnd_1485291 := by
    simpa [prefixWord, tailWord_1485291, baseEnd_1485291] using wordTrace_append hprefix tailTrace_1485291
  have hstable : (prefixWord ++ tailWord_1485291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485291).length < 2 ^ (prefixWord ++ tailWord_1485291).sum := by decide
  have hdescent : baseEnd_1485291 < baseStart_1485291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485331 : List Nat := [1, 1, 1, 2, 1, 5, 3, 4, 5]
def baseStart_1485331 : Nat := 118140960795 + 1485331 * 2 ^ 59
def prefixEnd_1485331 : Nat := 4983230072969 + 3 ^ 40 * 1485331 * 2
def baseEnd_1485331 : Nat := 84743192669270374370177

theorem tailTrace_1485331 : CollatzResearch.WordTrace tailWord_1485331 prefixEnd_1485331 84743192669270374370177 := by
  unfold tailWord_1485331
  simp only [CollatzResearch.WordTrace]
  refine ⟨54174472181906936183863847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36116314787937957455909231 54174472181906936183863847)
  ·
    refine ⟨81261708272860404275795771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54174472181906936183863847 81261708272860404275795771)
    ·
      refine ⟨121892562409290606413693657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81261708272860404275795771 121892562409290606413693657)
      ·
        refine ⟨91419421806967954810270243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121892562409290606413693657 91419421806967954810270243)
        ·
          refine ⟨137129132710451932215405365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91419421806967954810270243 137129132710451932215405365)
          ·
            refine ⟨12855856191604868645194253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 137129132710451932215405365 12855856191604868645194253)
            ·
              refine ⟨4820946071851825741947845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12855856191604868645194253 4820946071851825741947845)
              ·
                refine ⟨903927388472217326615221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4820946071851825741947845 903927388472217326615221)
                ·
                  refine ⟨84743192669270374370177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 903927388472217326615221 84743192669270374370177)
                  ·
                    rfl

theorem cell23_1485331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 4, 5].length) (baseStart_1485331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485331 prefixEnd_1485331 := by exact prefixLift 1485331
  have htrace : WordTrace (prefixWord ++ tailWord_1485331) baseStart_1485331 baseEnd_1485331 := by
    simpa [prefixWord, tailWord_1485331, baseEnd_1485331] using wordTrace_append hprefix tailTrace_1485331
  have hstable : (prefixWord ++ tailWord_1485331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485331).length < 2 ^ (prefixWord ++ tailWord_1485331).sum := by decide
  have hdescent : baseEnd_1485331 < baseStart_1485331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485341 : List Nat := [1, 4, 2, 2, 1, 2, 1, 1, 1, 5, 3]
def baseStart_1485341 : Nat := 118140960795 + 1485341 * 2 ^ 59
def prefixEnd_1485341 : Nat := 4983230072969 + 3 ^ 40 * 1485341 * 2
def baseEnd_1485341 : Nat := 762693868829978330206547

theorem tailTrace_1485341 : CollatzResearch.WordTrace tailWord_1485341 prefixEnd_1485341 762693868829978330206547 := by
  unfold tailWord_1485341
  simp only [CollatzResearch.WordTrace]
  refine ⟨54174836911870707891727877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36116557941247138594485251 54174836911870707891727877)
  ·
    refine ⟨10157781920975757729698977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54174836911870707891727877 10157781920975757729698977)
    ·
      refine ⟨7618336440731818297274233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10157781920975757729698977 7618336440731818297274233)
      ·
        refine ⟨5713752330548863722955675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7618336440731818297274233 5713752330548863722955675)
        ·
          refine ⟨8570628495823295584433513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5713752330548863722955675 8570628495823295584433513)
          ·
            refine ⟨6427971371867471688325135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8570628495823295584433513 6427971371867471688325135)
            ·
              refine ⟨9641957057801207532487703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6427971371867471688325135 9641957057801207532487703)
              ·
                refine ⟨14462935586701811298731555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9641957057801207532487703 14462935586701811298731555)
                ·
                  refine ⟨21694403380052716948097333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14462935586701811298731555 21694403380052716948097333)
                  ·
                    refine ⟨2033850316879942213884125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21694403380052716948097333 2033850316879942213884125)
                    ·
                      refine ⟨762693868829978330206547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2033850316879942213884125 762693868829978330206547)
                      ·
                        rfl

theorem cell23_1485341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_1485341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485341 prefixEnd_1485341 := by exact prefixLift 1485341
  have htrace : WordTrace (prefixWord ++ tailWord_1485341) baseStart_1485341 baseEnd_1485341 := by
    simpa [prefixWord, tailWord_1485341, baseEnd_1485341] using wordTrace_append hprefix tailTrace_1485341
  have hstable : (prefixWord ++ tailWord_1485341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485341).length < 2 ^ (prefixWord ++ tailWord_1485341).sum := by decide
  have hdescent : baseEnd_1485341 < baseStart_1485341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
