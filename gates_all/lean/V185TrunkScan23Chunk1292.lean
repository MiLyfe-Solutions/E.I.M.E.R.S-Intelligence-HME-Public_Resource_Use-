import V185TrunkScan23Chunk1291

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7652460 : List Nat := [2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 4]
def baseStart_7652460 : Nat := 118140960795 + 7652460 * 2 ^ 59
def prefixEnd_7652460 : Nat := 4983230072969 + 3 ^ 40 * 7652460 * 2
def baseEnd_7652460 : Nat := 3929390169305234948756983

theorem tailTrace_7652460 : CollatzResearch.WordTrace tailWord_7652460 prefixEnd_7652460 3929390169305234948756983 := by
  unfold tailWord_7652460
  simp only [CollatzResearch.WordTrace]
  refine ⟨139554072928225915481305417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186072097237634553975073889 139554072928225915481305417)
  ·
    refine ⟨104665554696169436610979063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139554072928225915481305417 104665554696169436610979063)
    ·
      refine ⟨156998332044254154916468595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104665554696169436610979063 156998332044254154916468595)
      ·
        refine ⟨235497498066381232374702893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156998332044254154916468595 235497498066381232374702893)
        ·
          refine ⟨88311561774892962140513585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235497498066381232374702893 88311561774892962140513585)
          ·
            refine ⟨66233671331169721605385189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88311561774892962140513585 66233671331169721605385189)
            ·
              refine ⟨12418813374594322801009723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66233671331169721605385189 12418813374594322801009723)
              ·
                refine ⟨18628220061891484201514585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12418813374594322801009723 18628220061891484201514585)
                ·
                  refine ⟨13971165046418613151135939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18628220061891484201514585 13971165046418613151135939)
                  ·
                    refine ⟨20956747569627919726703909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13971165046418613151135939 20956747569627919726703909)
                    ·
                      refine ⟨3929390169305234948756983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20956747569627919726703909 3929390169305234948756983)
                      ·
                        rfl

theorem cell23_7652460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 4].length) (baseStart_7652460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652460 prefixEnd_7652460 := by exact prefixLift 7652460
  have htrace : WordTrace (prefixWord ++ tailWord_7652460) baseStart_7652460 baseEnd_7652460 := by
    simpa [prefixWord, tailWord_7652460, baseEnd_7652460] using wordTrace_append hprefix tailTrace_7652460
  have hstable : (prefixWord ++ tailWord_7652460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652460).length < 2 ^ (prefixWord ++ tailWord_7652460).sum := by decide
  have hdescent : baseEnd_7652460 < baseStart_7652460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652480 : List Nat := [2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 3]
def baseStart_7652480 : Nat := 118140960795 + 7652480 * 2 ^ 59
def prefixEnd_7652480 : Nat := 4983230072969 + 3 ^ 40 * 7652480 * 2
def baseEnd_7652480 : Nat := 3929400438918324870506891

theorem tailTrace_7652480 : CollatzResearch.WordTrace tailWord_7652480 prefixEnd_7652480 3929400438918324870506891 := by
  unfold tailWord_7652480
  simp only [CollatzResearch.WordTrace]
  refine ⟨139554437658189687189169447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186072583544252916252225929 139554437658189687189169447)
  ·
    refine ⟨209331656487284530783754171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139554437658189687189169447 209331656487284530783754171)
    ·
      refine ⟨313997484730926796175631257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209331656487284530783754171 313997484730926796175631257)
      ·
        refine ⟨235498113548195097131723443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313997484730926796175631257 235498113548195097131723443)
        ·
          refine ⟨353247170322292645697585165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235498113548195097131723443 353247170322292645697585165)
          ·
            refine ⟨132467688870859742136594437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 353247170322292645697585165 132467688870859742136594437)
            ·
              refine ⟨24837691663286201650611457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132467688870859742136594437 24837691663286201650611457)
              ·
                refine ⟨18628268747464651237958593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24837691663286201650611457 18628268747464651237958593)
                ·
                  refine ⟨13971201560598488428468945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18628268747464651237958593 13971201560598488428468945)
                  ·
                    refine ⟨10478401170448866321351709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13971201560598488428468945 10478401170448866321351709)
                    ·
                      refine ⟨3929400438918324870506891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10478401170448866321351709 3929400438918324870506891)
                      ·
                        rfl

theorem cell23_7652480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 3].length) (baseStart_7652480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652480 prefixEnd_7652480 := by exact prefixLift 7652480
  have htrace : WordTrace (prefixWord ++ tailWord_7652480) baseStart_7652480 baseEnd_7652480 := by
    simpa [prefixWord, tailWord_7652480, baseEnd_7652480] using wordTrace_append hprefix tailTrace_7652480
  have hstable : (prefixWord ++ tailWord_7652480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652480).length < 2 ^ (prefixWord ++ tailWord_7652480).sum := by decide
  have hdescent : baseEnd_7652480 < baseStart_7652480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652534 : List Nat := [5, 1, 3, 2, 1, 1, 1, 1, 8]
def baseStart_7652534 : Nat := 118140960795 + 7652534 * 2 ^ 59
def prefixEnd_7652534 : Nat := 4983230072969 + 3 ^ 40 * 7652534 * 2
def baseEnd_7652534 : Nat := 436603129652629739914627

theorem tailTrace_7652534 : CollatzResearch.WordTrace tailWord_7652534 prefixEnd_7652534 436603129652629739914627 := by
  unfold tailWord_7652534
  simp only [CollatzResearch.WordTrace]
  refine ⟨17444427803636483850050291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186073896572122494400536437 17444427803636483850050291)
  ·
    refine ⟨26166641705454725775075437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17444427803636483850050291 26166641705454725775075437)
    ·
      refine ⟨9812490639545522165653289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26166641705454725775075437 9812490639545522165653289)
      ·
        refine ⟨7359367979659141624239967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9812490639545522165653289 7359367979659141624239967)
        ·
          refine ⟨11039051969488712436359951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7359367979659141624239967 11039051969488712436359951)
          ·
            refine ⟨16558577954233068654539927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11039051969488712436359951 16558577954233068654539927)
            ·
              refine ⟨24837866931349602981809891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16558577954233068654539927 24837866931349602981809891)
              ·
                refine ⟨37256800397024404472714837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24837866931349602981809891 37256800397024404472714837)
                ·
                  refine ⟨436603129652629739914627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37256800397024404472714837 436603129652629739914627)
                  ·
                    rfl

theorem cell23_7652534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_7652534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652534 prefixEnd_7652534 := by exact prefixLift 7652534
  have htrace : WordTrace (prefixWord ++ tailWord_7652534) baseStart_7652534 baseEnd_7652534 := by
    simpa [prefixWord, tailWord_7652534, baseEnd_7652534] using wordTrace_append hprefix tailTrace_7652534
  have hstable : (prefixWord ++ tailWord_7652534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652534).length < 2 ^ (prefixWord ++ tailWord_7652534).sum := by decide
  have hdescent : baseEnd_7652534 < baseStart_7652534 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652543 : List Nat := [1, 1, 2, 2, 2, 2, 2, 2, 3, 6]
def baseStart_7652543 : Nat := 118140960795 + 7652543 * 2 ^ 59
def prefixEnd_7652543 : Nat := 4983230072969 + 3 ^ 40 * 7652543 * 2
def baseEnd_7652543 : Nat := 1309810929399852708006367

theorem tailTrace_7652543 : CollatzResearch.WordTrace tailWord_7652543 prefixEnd_7652543 1309810929399852708006367 := by
  unfold tailWord_7652543
  simp only [CollatzResearch.WordTrace]
  refine ⟨279111173115151136137882283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186074115410100757425254855 279111173115151136137882283)
  ·
    refine ⟨418666759672726704206823425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279111173115151136137882283 418666759672726704206823425)
    ·
      refine ⟨314000069754545028155117569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418666759672726704206823425 314000069754545028155117569)
      ·
        refine ⟨235500052315908771116338177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314000069754545028155117569 235500052315908771116338177)
        ·
          refine ⟨176625039236931578337253633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235500052315908771116338177 176625039236931578337253633)
          ·
            refine ⟨132468779427698683752940225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176625039236931578337253633 132468779427698683752940225)
            ·
              refine ⟨99351584570774012814705169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132468779427698683752940225 99351584570774012814705169)
              ·
                refine ⟨74513688428080509611028877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99351584570774012814705169 74513688428080509611028877)
                ·
                  refine ⟨27942633160530191104135829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74513688428080509611028877 27942633160530191104135829)
                  ·
                    refine ⟨1309810929399852708006367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27942633160530191104135829 1309810929399852708006367)
                    ·
                      rfl

theorem cell23_7652543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 6].length) (baseStart_7652543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652543 prefixEnd_7652543 := by exact prefixLift 7652543
  have htrace : WordTrace (prefixWord ++ tailWord_7652543) baseStart_7652543 baseEnd_7652543 := by
    simpa [prefixWord, tailWord_7652543, baseEnd_7652543] using wordTrace_append hprefix tailTrace_7652543
  have hstable : (prefixWord ++ tailWord_7652543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652543).length < 2 ^ (prefixWord ++ tailWord_7652543).sum := by decide
  have hdescent : baseEnd_7652543 < baseStart_7652543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652544 : List Nat := [2, 1, 1, 2, 6, 1, 2, 1, 3, 1, 3]
def baseStart_7652544 : Nat := 118140960795 + 7652544 * 2 ^ 59
def prefixEnd_7652544 : Nat := 4983230072969 + 3 ^ 40 * 7652544 * 2
def baseEnd_7652544 : Nat := 3929433301680212620106597

theorem tailTrace_7652544 : CollatzResearch.WordTrace tailWord_7652544 prefixEnd_7652544 3929433301680212620106597 := by
  unfold tailWord_7652544
  simp only [CollatzResearch.WordTrace]
  refine ⟨139555604794073756654334343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186074139725431675539112457 139555604794073756654334343)
  ·
    refine ⟨209333407191110634981501515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139555604794073756654334343 209333407191110634981501515)
    ·
      refine ⟨314000110786665952472252273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209333407191110634981501515 314000110786665952472252273)
      ·
        refine ⟨235500083089999464354189205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314000110786665952472252273 235500083089999464354189205)
        ·
          refine ⟨11039066394843724891602619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 235500083089999464354189205 11039066394843724891602619)
          ·
            refine ⟨16558599592265587337403929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11039066394843724891602619 16558599592265587337403929)
            ·
              refine ⟨12418949694199190503052947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16558599592265587337403929 12418949694199190503052947)
              ·
                refine ⟨18628424541298785754579421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12418949694199190503052947 18628424541298785754579421)
                ·
                  refine ⟨6985659202987044657967283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18628424541298785754579421 6985659202987044657967283)
                  ·
                    refine ⟨10478488804480566986950925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6985659202987044657967283 10478488804480566986950925)
                    ·
                      refine ⟨3929433301680212620106597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10478488804480566986950925 3929433301680212620106597)
                      ·
                        rfl

theorem cell23_7652544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 3, 1, 3].length) (baseStart_7652544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652544 prefixEnd_7652544 := by exact prefixLift 7652544
  have htrace : WordTrace (prefixWord ++ tailWord_7652544) baseStart_7652544 baseEnd_7652544 := by
    simpa [prefixWord, tailWord_7652544, baseEnd_7652544] using wordTrace_append hprefix tailTrace_7652544
  have hstable : (prefixWord ++ tailWord_7652544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652544).length < 2 ^ (prefixWord ++ tailWord_7652544).sum := by decide
  have hdescent : baseEnd_7652544 < baseStart_7652544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652563 : List Nat := [1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 6]
def baseStart_7652563 : Nat := 118140960795 + 7652563 * 2 ^ 59
def prefixEnd_7652563 : Nat := 4983230072969 + 3 ^ 40 * 7652563 * 2
def baseEnd_7652563 : Nat := 3929443057812648045769009

theorem tailTrace_7652563 : CollatzResearch.WordTrace tailWord_7652563 prefixEnd_7652563 3929443057812648045769009 := by
  unfold tailWord_7652563
  simp only [CollatzResearch.WordTrace]
  refine ⟨279111902575078679553610343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186074601716719119702406895 279111902575078679553610343)
  ·
    refine ⟨418667853862618019330415515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279111902575078679553610343 418667853862618019330415515)
    ·
      refine ⟨628001780793927028995623273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418667853862618019330415515 628001780793927028995623273)
      ·
        refine ⟨471001335595445271746717455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 628001780793927028995623273 471001335595445271746717455)
        ·
          refine ⟨706502003393167907620076183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471001335595445271746717455 706502003393167907620076183)
          ·
            refine ⟨1059753005089751861430114275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706502003393167907620076183 1059753005089751861430114275)
            ·
              refine ⟨1589629507634627792145171413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1059753005089751861430114275 1589629507634627792145171413)
              ·
                refine ⟨37256941585186588878402455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1589629507634627792145171413 37256941585186588878402455)
                ·
                  refine ⟨55885412377779883317603683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37256941585186588878402455 55885412377779883317603683)
                  ·
                    refine ⟨83828118566669824976405525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55885412377779883317603683 83828118566669824976405525)
                    ·
                      refine ⟨3929443057812648045769009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83828118566669824976405525 3929443057812648045769009)
                      ·
                        rfl

theorem cell23_7652563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 6].length) (baseStart_7652563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652563 prefixEnd_7652563 := by exact prefixLift 7652563
  have htrace : WordTrace (prefixWord ++ tailWord_7652563) baseStart_7652563 baseEnd_7652563 := by
    simpa [prefixWord, tailWord_7652563, baseEnd_7652563] using wordTrace_append hprefix tailTrace_7652563
  have hstable : (prefixWord ++ tailWord_7652563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652563).length < 2 ^ (prefixWord ++ tailWord_7652563).sum := by decide
  have hdescent : baseEnd_7652563 < baseStart_7652563 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652580 : List Nat := [2, 3, 1, 1, 1, 2, 2, 4, 1, 2, 4]
def baseStart_7652580 : Nat := 118140960795 + 7652580 * 2 ^ 59
def prefixEnd_7652580 : Nat := 4983230072969 + 3 ^ 40 * 7652580 * 2
def baseEnd_7652580 : Nat := 3929451786983774479256431

theorem tailTrace_7652580 : CollatzResearch.WordTrace tailWord_7652580 prefixEnd_7652580 3929451786983774479256431 := by
  unfold tailWord_7652580
  simp only [CollatzResearch.WordTrace]
  refine ⟨139556261308008545728489597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186075015077344727637986129 139556261308008545728489597)
  ·
    refine ⟨52333597990503204648183599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139556261308008545728489597 52333597990503204648183599)
    ·
      refine ⟨78500396985754806972275399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52333597990503204648183599 78500396985754806972275399)
      ·
        refine ⟨117750595478632210458413099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78500396985754806972275399 117750595478632210458413099)
        ·
          refine ⟨176625893217948315687619649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117750595478632210458413099 176625893217948315687619649)
          ·
            refine ⟨132469419913461236765714737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176625893217948315687619649 132469419913461236765714737)
            ·
              refine ⟨99352064935095927574286053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132469419913461236765714737 99352064935095927574286053)
              ·
                refine ⟨18628512175330486420178635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99352064935095927574286053 18628512175330486420178635)
                ·
                  refine ⟨27942768262995729630267953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18628512175330486420178635 27942768262995729630267953)
                  ·
                    refine ⟨20957076197246797222700965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27942768262995729630267953 20957076197246797222700965)
                    ·
                      refine ⟨3929451786983774479256431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20957076197246797222700965 3929451786983774479256431)
                      ·
                        rfl

theorem cell23_7652580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_7652580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652580 prefixEnd_7652580 := by exact prefixLift 7652580
  have htrace : WordTrace (prefixWord ++ tailWord_7652580) baseStart_7652580 baseEnd_7652580 := by
    simpa [prefixWord, tailWord_7652580, baseEnd_7652580] using wordTrace_append hprefix tailTrace_7652580
  have hstable : (prefixWord ++ tailWord_7652580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652580).length < 2 ^ (prefixWord ++ tailWord_7652580).sum := by decide
  have hdescent : baseEnd_7652580 < baseStart_7652580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652587 : List Nat := [1, 1, 1, 1, 2, 6, 2, 3, 1, 2, 3]
def baseStart_7652587 : Nat := 118140960795 + 7652587 * 2 ^ 59
def prefixEnd_7652587 : Nat := 4983230072969 + 3 ^ 40 * 7652587 * 2
def baseEnd_7652587 : Nat := 3929455381348355951868899

theorem tailTrace_7652587 : CollatzResearch.WordTrace tailWord_7652587 prefixEnd_7652587 3929455381348355951868899 := by
  unfold tailWord_7652587
  simp only [CollatzResearch.WordTrace]
  refine ⟨279112777926991731652484015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186075185284661154434989343 279112777926991731652484015)
  ·
    refine ⟨418669166890487597478726023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279112777926991731652484015 418669166890487597478726023)
    ·
      refine ⟨628003750335731396218089035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418669166890487597478726023 628003750335731396218089035)
      ·
        refine ⟨942005625503597094327133553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 628003750335731396218089035 942005625503597094327133553)
        ·
          refine ⟨706504219127697820745350165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 942005625503597094327133553 706504219127697820745350165)
          ·
            refine ⟨33117385271610835347438289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 706504219127697820745350165 33117385271610835347438289)
            ·
              refine ⟨24838038953708126510578717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33117385271610835347438289 24838038953708126510578717)
              ·
                refine ⟨9314264607640547441467019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24838038953708126510578717 9314264607640547441467019)
                ·
                  refine ⟨13971396911460821162200529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9314264607640547441467019 13971396911460821162200529)
                  ·
                    refine ⟨10478547683595615871650397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13971396911460821162200529 10478547683595615871650397)
                    ·
                      refine ⟨3929455381348355951868899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10478547683595615871650397 3929455381348355951868899)
                      ·
                        rfl

theorem cell23_7652587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 3, 1, 2, 3].length) (baseStart_7652587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652587 prefixEnd_7652587 := by exact prefixLift 7652587
  have htrace : WordTrace (prefixWord ++ tailWord_7652587) baseStart_7652587 baseEnd_7652587 := by
    simpa [prefixWord, tailWord_7652587, baseEnd_7652587] using wordTrace_append hprefix tailTrace_7652587
  have hstable : (prefixWord ++ tailWord_7652587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652587).length < 2 ^ (prefixWord ++ tailWord_7652587).sum := by decide
  have hdescent : baseEnd_7652587 < baseStart_7652587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652623 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 10]
def baseStart_7652623 : Nat := 118140960795 + 7652623 * 2 ^ 59
def prefixEnd_7652623 : Nat := 4983230072969 + 3 ^ 40 * 7652623 * 2
def baseEnd_7652623 : Nat := 3929473866651917811018733

theorem tailTrace_7652623 : CollatzResearch.WordTrace tailWord_7652623 prefixEnd_7652623 3929473866651917811018733 := by
  unfold tailWord_7652623
  simp only [CollatzResearch.WordTrace]
  refine ⟨279114090954861309800794523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186076060636574206533863015 279114090954861309800794523)
  ·
    refine ⟨418671136432291964701191785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279114090954861309800794523 418671136432291964701191785)
    ·
      refine ⟨314003352324218973525893839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418671136432291964701191785 314003352324218973525893839)
      ·
        refine ⟨471005028486328460288840759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314003352324218973525893839 471005028486328460288840759)
        ·
          refine ⟨706507542729492690433261139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471005028486328460288840759 706507542729492690433261139)
          ·
            refine ⟨1059761314094239035649891709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706507542729492690433261139 1059761314094239035649891709)
            ·
              refine ⟨397410492785339638368709391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1059761314094239035649891709 397410492785339638368709391)
              ·
                refine ⟨596115739178009457553064087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 397410492785339638368709391 596115739178009457553064087)
                ·
                  refine ⟨894173608767014186329596131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 596115739178009457553064087 894173608767014186329596131)
                  ·
                    refine ⟨1341260413150521279494394197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 894173608767014186329596131 1341260413150521279494394197)
                    ·
                      refine ⟨3929473866651917811018733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1341260413150521279494394197 3929473866651917811018733)
                      ·
                        rfl

theorem cell23_7652623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 10].length) (baseStart_7652623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652623 prefixEnd_7652623 := by exact prefixLift 7652623
  have htrace : WordTrace (prefixWord ++ tailWord_7652623) baseStart_7652623 baseEnd_7652623 := by
    simpa [prefixWord, tailWord_7652623, baseEnd_7652623] using wordTrace_append hprefix tailTrace_7652623
  have hstable : (prefixWord ++ tailWord_7652623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652623).length < 2 ^ (prefixWord ++ tailWord_7652623).sum := by decide
  have hdescent : baseEnd_7652623 < baseStart_7652623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652638 : List Nat := [4, 3, 2, 1, 3, 1, 1, 1, 1, 1, 5]
def baseStart_7652638 : Nat := 118140960795 + 7652638 * 2 ^ 59
def prefixEnd_7652638 : Nat := 4983230072969 + 3 ^ 40 * 7652638 * 2
def baseEnd_7652638 : Nat := 3929481568861735252331165

theorem tailTrace_7652638 : CollatzResearch.WordTrace tailWord_7652638 prefixEnd_7652638 3929481568861735252331165 := by
  unfold tailWord_7652638
  simp only [CollatzResearch.WordTrace]
  refine ⟨34889329756225870920323821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186076425366537978241727045 34889329756225870920323821)
  ·
    refine ⟨13083498658584701595121433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34889329756225870920323821 13083498658584701595121433)
    ·
      refine ⟨9812623993938526196341075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13083498658584701595121433 9812623993938526196341075)
      ·
        refine ⟨14718935990907789294511613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9812623993938526196341075 14718935990907789294511613)
        ·
          refine ⟨5519600996590420985441855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14718935990907789294511613 5519600996590420985441855)
          ·
            refine ⟨8279401494885631478162783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5519600996590420985441855 8279401494885631478162783)
            ·
              refine ⟨12419102242328447217244175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8279401494885631478162783 12419102242328447217244175)
              ·
                refine ⟨18628653363492670825866263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12419102242328447217244175 18628653363492670825866263)
                ·
                  refine ⟨27942980045239006238799395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18628653363492670825866263 27942980045239006238799395)
                  ·
                    refine ⟨41914470067858509358199093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27942980045239006238799395 41914470067858509358199093)
                    ·
                      refine ⟨3929481568861735252331165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41914470067858509358199093 3929481568861735252331165)
                      ·
                        rfl

theorem cell23_7652638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_7652638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652638 prefixEnd_7652638 := by exact prefixLift 7652638
  have htrace : WordTrace (prefixWord ++ tailWord_7652638) baseStart_7652638 baseEnd_7652638 := by
    simpa [prefixWord, tailWord_7652638, baseEnd_7652638] using wordTrace_append hprefix tailTrace_7652638
  have hstable : (prefixWord ++ tailWord_7652638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652638).length < 2 ^ (prefixWord ++ tailWord_7652638).sum := by decide
  have hdescent : baseEnd_7652638 < baseStart_7652638 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652690 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7]
def baseStart_7652690 : Nat := 118140960795 + 7652690 * 2 ^ 59
def prefixEnd_7652690 : Nat := 4983230072969 + 3 ^ 40 * 7652690 * 2
def baseEnd_7652690 : Nat := 3929508269855769048880925

theorem tailTrace_7652690 : CollatzResearch.WordTrace tailWord_7652690 prefixEnd_7652690 3929508269855769048880925 := by
  unfold tailWord_7652690
  simp only [CollatzResearch.WordTrace]
  refine ⟨69779133661404645060870881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186077689763745720162322349 69779133661404645060870881)
  ·
    refine ⟨52334350246053483795653161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69779133661404645060870881 52334350246053483795653161)
    ·
      refine ⟨39250762684540112846739871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52334350246053483795653161 39250762684540112846739871)
      ·
        refine ⟨58876144026810169270109807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39250762684540112846739871 58876144026810169270109807)
        ·
          refine ⟨88314216040215253905164711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58876144026810169270109807 88314216040215253905164711)
          ·
            refine ⟨132471324060322880857747067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88314216040215253905164711 132471324060322880857747067)
            ·
              refine ⟨198706986090484321286620601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132471324060322880857747067 198706986090484321286620601)
              ·
                refine ⟨149030239567863240964965451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198706986090484321286620601 149030239567863240964965451)
                ·
                  refine ⟨223545359351794861447448177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149030239567863240964965451 223545359351794861447448177)
                  ·
                    refine ⟨167659019513846146085586133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 223545359351794861447448177 167659019513846146085586133)
                    ·
                      refine ⟨3929508269855769048880925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 167659019513846146085586133 3929508269855769048880925)
                      ·
                        rfl

theorem cell23_7652690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_7652690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652690 prefixEnd_7652690 := by exact prefixLift 7652690
  have htrace : WordTrace (prefixWord ++ tailWord_7652690) baseStart_7652690 baseEnd_7652690 := by
    simpa [prefixWord, tailWord_7652690, baseEnd_7652690] using wordTrace_append hprefix tailTrace_7652690
  have hstable : (prefixWord ++ tailWord_7652690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652690).length < 2 ^ (prefixWord ++ tailWord_7652690).sum := by decide
  have hdescent : baseEnd_7652690 < baseStart_7652690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652697 : List Nat := [1, 2, 1, 2, 2, 2, 3, 5, 5]
def baseStart_7652697 : Nat := 118140960795 + 7652697 * 2 ^ 59
def prefixEnd_7652697 : Nat := 4983230072969 + 3 ^ 40 * 7652697 * 2
def baseEnd_7652697 : Nat := 436612429357816724610377

theorem tailTrace_7652697 : CollatzResearch.WordTrace tailWord_7652697 prefixEnd_7652697 436612429357816724610377 := by
  unfold tailWord_7652697
  simp only [CollatzResearch.WordTrace]
  refine ⟨279116789956593220438988345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186077859971062146959325563 279116789956593220438988345)
  ·
    refine ⟨209337592467444915329241259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279116789956593220438988345 209337592467444915329241259)
    ·
      refine ⟨314006388701167372993861889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209337592467444915329241259 314006388701167372993861889)
      ·
        refine ⟨235504791525875529745396417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314006388701167372993861889 235504791525875529745396417)
        ·
          refine ⟨176628593644406647309047313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235504791525875529745396417 176628593644406647309047313)
          ·
            refine ⟨132471445233304985481785485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176628593644406647309047313 132471445233304985481785485)
            ·
              refine ⟨49676791962489369555669557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132471445233304985481785485 49676791962489369555669557)
              ·
                refine ⟨4657199246483378395844021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49676791962489369555669557 4657199246483378395844021)
                ·
                  refine ⟨436612429357816724610377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4657199246483378395844021 436612429357816724610377)
                  ·
                    rfl

theorem cell23_7652697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 5, 5].length) (baseStart_7652697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652697 prefixEnd_7652697 := by exact prefixLift 7652697
  have htrace : WordTrace (prefixWord ++ tailWord_7652697) baseStart_7652697 baseEnd_7652697 := by
    simpa [prefixWord, tailWord_7652697, baseEnd_7652697] using wordTrace_append hprefix tailTrace_7652697
  have hstable : (prefixWord ++ tailWord_7652697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652697).length < 2 ^ (prefixWord ++ tailWord_7652697).sum := by decide
  have hdescent : baseEnd_7652697 < baseStart_7652697 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652707 : List Nat := [1, 1, 1, 5, 2, 2, 1, 2, 2, 3, 3]
def baseStart_7652707 : Nat := 118140960795 + 7652707 * 2 ^ 59
def prefixEnd_7652707 : Nat := 4983230072969 + 3 ^ 40 * 7652707 * 2
def baseEnd_7652707 : Nat := 3929516999026895482368347

theorem tailTrace_7652707 : CollatzResearch.WordTrace tailWord_7652707 prefixEnd_7652707 3929516999026895482368347 := by
  unfold tailWord_7652707
  simp only [CollatzResearch.WordTrace]
  refine ⟨279117154686556992146852375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186078103124371328097901583 279117154686556992146852375)
  ·
    refine ⟨418675732029835488220278563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279117154686556992146852375 418675732029835488220278563)
    ·
      refine ⟨628013598044753232330417845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418675732029835488220278563 628013598044753232330417845)
      ·
        refine ⟨58876274816695615530976673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 628013598044753232330417845 58876274816695615530976673)
        ·
          refine ⟨44157206112521711648232505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58876274816695615530976673 44157206112521711648232505)
          ·
            refine ⟨33117904584391283736174379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44157206112521711648232505 33117904584391283736174379)
            ·
              refine ⟨49676856876586925604261569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33117904584391283736174379 49676856876586925604261569)
              ·
                refine ⟨37257642657440194203196177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49676856876586925604261569 37257642657440194203196177)
                ·
                  refine ⟨27943231993080145652397133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37257642657440194203196177 27943231993080145652397133)
                  ·
                    refine ⟨10478711997405054619648925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27943231993080145652397133 10478711997405054619648925)
                    ·
                      refine ⟨3929516999026895482368347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10478711997405054619648925 3929516999026895482368347)
                      ·
                        rfl

theorem cell23_7652707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_7652707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652707 prefixEnd_7652707 := by exact prefixLift 7652707
  have htrace : WordTrace (prefixWord ++ tailWord_7652707) baseStart_7652707 baseEnd_7652707 := by
    simpa [prefixWord, tailWord_7652707, baseEnd_7652707] using wordTrace_append hprefix tailTrace_7652707
  have hstable : (prefixWord ++ tailWord_7652707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652707).length < 2 ^ (prefixWord ++ tailWord_7652707).sum := by decide
  have hdescent : baseEnd_7652707 < baseStart_7652707 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652708 : List Nat := [2, 3, 1, 1, 3, 4, 1, 2, 2, 2, 2]
def baseStart_7652708 : Nat := 118140960795 + 7652708 * 2 ^ 59
def prefixEnd_7652708 : Nat := 4983230072969 + 3 ^ 40 * 7652708 * 2
def baseEnd_7652708 : Nat := 3929517512507549978455843

theorem tailTrace_7652708 : CollatzResearch.WordTrace tailWord_7652708 prefixEnd_7652708 3929517512507549978455843 := by
  unfold tailWord_7652708
  simp only [CollatzResearch.WordTrace]
  refine ⟨139558595579776684658819389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186078127439702246211759185 139558595579776684658819389)
  ·
    refine ⟨52334473342416256747057271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139558595579776684658819389 52334473342416256747057271)
    ·
      refine ⟨78501710013624385120585907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52334473342416256747057271 78501710013624385120585907)
      ·
        refine ⟨117752565020436577680878861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78501710013624385120585907 117752565020436577680878861)
        ·
          refine ⟨44157211882663716630329573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117752565020436577680878861 44157211882663716630329573)
          ·
            refine ⟨8279477227999446868186795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44157211882663716630329573 8279477227999446868186795)
            ·
              refine ⟨12419215841999170302280193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8279477227999446868186795 12419215841999170302280193)
              ·
                refine ⟨9314411881499377726710145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12419215841999170302280193 9314411881499377726710145)
                ·
                  refine ⟨6985808911124533295032609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9314411881499377726710145 6985808911124533295032609)
                  ·
                    refine ⟨5239356683343399971274457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6985808911124533295032609 5239356683343399971274457)
                    ·
                      refine ⟨3929517512507549978455843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5239356683343399971274457 3929517512507549978455843)
                      ·
                        rfl

theorem cell23_7652708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 2, 2, 2, 2].length) (baseStart_7652708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652708 prefixEnd_7652708 := by exact prefixLift 7652708
  have htrace : WordTrace (prefixWord ++ tailWord_7652708) baseStart_7652708 baseEnd_7652708 := by
    simpa [prefixWord, tailWord_7652708, baseEnd_7652708] using wordTrace_append hprefix tailTrace_7652708
  have hstable : (prefixWord ++ tailWord_7652708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652708).length < 2 ^ (prefixWord ++ tailWord_7652708).sum := by decide
  have hdescent : baseEnd_7652708 < baseStart_7652708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652714 : List Nat := [3, 1, 3, 3, 2, 1, 2, 1, 7]
def baseStart_7652714 : Nat := 118140960795 + 7652714 * 2 ^ 59
def prefixEnd_7652714 : Nat := 4983230072969 + 3 ^ 40 * 7652714 * 2
def baseEnd_7652714 : Nat := 436613399265719661664535

theorem tailTrace_7652714 : CollatzResearch.WordTrace tailWord_7652714 prefixEnd_7652714 436613399265719661664535 := by
  unfold tailWord_7652714
  simp only [CollatzResearch.WordTrace]
  refine ⟨69779352499382908085589299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186078273331687754894904797 69779352499382908085589299)
  ·
    refine ⟨104669028749074362128383949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69779352499382908085589299 104669028749074362128383949)
    ·
      refine ⟨39250885780902885798143981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104669028749074362128383949 39250885780902885798143981)
      ·
        refine ⟨14719082167838582174303993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39250885780902885798143981 14719082167838582174303993)
        ·
          refine ⟨11039311625878936630727995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14719082167838582174303993 11039311625878936630727995)
          ·
            refine ⟨16558967438818404946091993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11039311625878936630727995 16558967438818404946091993)
            ·
              refine ⟨12419225579113803709568995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16558967438818404946091993 12419225579113803709568995)
              ·
                refine ⟨18628838368670705564353493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12419225579113803709568995 18628838368670705564353493)
                ·
                  refine ⟨436613399265719661664535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18628838368670705564353493 436613399265719661664535)
                  ·
                    rfl

theorem cell23_7652714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 7].length) (baseStart_7652714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652714 prefixEnd_7652714 := by exact prefixLift 7652714
  have htrace : WordTrace (prefixWord ++ tailWord_7652714) baseStart_7652714 baseEnd_7652714 := by
    simpa [prefixWord, tailWord_7652714, baseEnd_7652714] using wordTrace_append hprefix tailTrace_7652714
  have hstable : (prefixWord ++ tailWord_7652714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652714).length < 2 ^ (prefixWord ++ tailWord_7652714).sum := by decide
  have hdescent : baseEnd_7652714 < baseStart_7652714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652720 : List Nat := [2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 7]
def baseStart_7652720 : Nat := 118140960795 + 7652720 * 2 ^ 59
def prefixEnd_7652720 : Nat := 4983230072969 + 3 ^ 40 * 7652720 * 2
def baseEnd_7652720 : Nat := 3929523674275403931505787

theorem tailTrace_7652720 : CollatzResearch.WordTrace tailWord_7652720 prefixEnd_7652720 3929523674275403931505787 := by
  unfold tailWord_7652720
  simp only [CollatzResearch.WordTrace]
  refine ⟨139558814417754947683537807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186078419223673263578050409 139558814417754947683537807)
  ·
    refine ⟨209338221626632421525306711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139558814417754947683537807 209338221626632421525306711)
    ·
      refine ⟨314007332439948632287960067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209338221626632421525306711 314007332439948632287960067)
      ·
        refine ⟨471010998659922948431940101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314007332439948632287960067 471010998659922948431940101)
        ·
          refine ⟨88314562248735552830988769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 471010998659922948431940101 88314562248735552830988769)
          ·
            refine ⟨66235921686551664623241577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88314562248735552830988769 66235921686551664623241577)
            ·
              refine ⟨49676941264913748467431183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66235921686551664623241577 49676941264913748467431183)
              ·
                refine ⟨74515411897370622701146775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49676941264913748467431183 74515411897370622701146775)
                ·
                  refine ⟨111773117846055934051720163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74515411897370622701146775 111773117846055934051720163)
                  ·
                    refine ⟨167659676769083901077580245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111773117846055934051720163 167659676769083901077580245)
                    ·
                      refine ⟨3929523674275403931505787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 167659676769083901077580245 3929523674275403931505787)
                      ·
                        rfl

theorem cell23_7652720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 7].length) (baseStart_7652720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652720 prefixEnd_7652720 := by exact prefixLift 7652720
  have htrace : WordTrace (prefixWord ++ tailWord_7652720) baseStart_7652720 baseEnd_7652720 := by
    simpa [prefixWord, tailWord_7652720, baseEnd_7652720] using wordTrace_append hprefix tailTrace_7652720
  have hstable : (prefixWord ++ tailWord_7652720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652720).length < 2 ^ (prefixWord ++ tailWord_7652720).sum := by decide
  have hdescent : baseEnd_7652720 < baseStart_7652720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652725 : List Nat := [1, 3, 4, 1, 3, 1, 3, 1, 2, 2, 2]
def baseStart_7652725 : Nat := 118140960795 + 7652725 * 2 ^ 59
def prefixEnd_7652725 : Nat := 4983230072969 + 3 ^ 40 * 7652725 * 2
def baseEnd_7652725 : Nat := 3929526241678676411943265

theorem tailTrace_7652725 : CollatzResearch.WordTrace tailWord_7652725 prefixEnd_7652725 3929526241678676411943265 := by
  unfold tailWord_7652725
  simp only [CollatzResearch.WordTrace]
  refine ⟨279117811200491781221007629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186078540800327854147338419 279117811200491781221007629)
  ·
    refine ⟨104669179200184417957877861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279117811200491781221007629 104669179200184417957877861)
    ·
      refine ⟨19625471100034578367102099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104669179200184417957877861 19625471100034578367102099)
      ·
        refine ⟨29438206650051867550653149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19625471100034578367102099 29438206650051867550653149)
        ·
          refine ⟨11039327493769450331494931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29438206650051867550653149 11039327493769450331494931)
          ·
            refine ⟨16558991240654175497242397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11039327493769450331494931 16558991240654175497242397)
            ·
              refine ⟨6209621715245315811465899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16558991240654175497242397 6209621715245315811465899)
              ·
                refine ⟨9314432572867973717198849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6209621715245315811465899 9314432572867973717198849)
                ·
                  refine ⟨6985824429650980287899137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9314432572867973717198849 6985824429650980287899137)
                  ·
                    refine ⟨5239368322238235215924353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6985824429650980287899137 5239368322238235215924353)
                    ·
                      refine ⟨3929526241678676411943265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5239368322238235215924353 3929526241678676411943265)
                      ·
                        rfl

theorem cell23_7652725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_7652725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652725 prefixEnd_7652725 := by exact prefixLift 7652725
  have htrace : WordTrace (prefixWord ++ tailWord_7652725) baseStart_7652725 baseEnd_7652725 := by
    simpa [prefixWord, tailWord_7652725, baseEnd_7652725] using wordTrace_append hprefix tailTrace_7652725
  have hstable : (prefixWord ++ tailWord_7652725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652725).length < 2 ^ (prefixWord ++ tailWord_7652725).sum := by decide
  have hdescent : baseEnd_7652725 < baseStart_7652725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652747 : List Nat := [1, 1, 1, 1, 4, 3, 2, 3, 2, 1, 4]
def baseStart_7652747 : Nat := 118140960795 + 7652747 * 2 ^ 59
def prefixEnd_7652747 : Nat := 4983230072969 + 3 ^ 40 * 7652747 * 2
def baseEnd_7652747 : Nat := 3929537538253075325868163

theorem tailTrace_7652747 : CollatzResearch.WordTrace tailWord_7652747 prefixEnd_7652747 3929537538253075325868163 := by
  unfold tailWord_7652747
  simp only [CollatzResearch.WordTrace]
  refine ⟨279118613606412078978308495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186079075737608052652205663 279118613606412078978308495)
  ·
    refine ⟨418677920409618118467462743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279118613606412078978308495 418677920409618118467462743)
    ·
      refine ⟨628016880614427177701194115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418677920409618118467462743 628016880614427177701194115)
      ·
        refine ⟨942025320921640766551791173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 628016880614427177701194115 942025320921640766551791173)
        ·
          refine ⟨176629747672807643728460845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 942025320921640766551791173 176629747672807643728460845)
          ·
            refine ⟨66236155377302866398172817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176629747672807643728460845 66236155377302866398172817)
            ·
              refine ⟨49677116532977149798629613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66236155377302866398172817 49677116532977149798629613)
              ·
                refine ⟨18628918699866431174486105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49677116532977149798629613 18628918699866431174486105)
                ·
                  refine ⟨13971689024899823380864579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18628918699866431174486105 13971689024899823380864579)
                  ·
                    refine ⟨20957533537349735071296869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13971689024899823380864579 20957533537349735071296869)
                    ·
                      refine ⟨3929537538253075325868163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20957533537349735071296869 3929537538253075325868163)
                      ·
                        rfl

theorem cell23_7652747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 2, 1, 4].length) (baseStart_7652747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652747 prefixEnd_7652747 := by exact prefixLift 7652747
  have htrace : WordTrace (prefixWord ++ tailWord_7652747) baseStart_7652747 baseEnd_7652747 := by
    simpa [prefixWord, tailWord_7652747, baseEnd_7652747] using wordTrace_append hprefix tailTrace_7652747
  have hstable : (prefixWord ++ tailWord_7652747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652747).length < 2 ^ (prefixWord ++ tailWord_7652747).sum := by decide
  have hdescent : baseEnd_7652747 < baseStart_7652747 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652757 : List Nat := [1, 3, 2, 1, 1, 2, 2, 2, 5, 4]
def baseStart_7652757 : Nat := 118140960795 + 7652757 * 2 ^ 59
def prefixEnd_7652757 : Nat := 4983230072969 + 3 ^ 40 * 7652757 * 2
def baseEnd_7652757 : Nat := 1309847557686540095581039

theorem tailTrace_7652757 : CollatzResearch.WordTrace tailWord_7652757 prefixEnd_7652757 1309847557686540095581039 := by
  unfold tailWord_7652757
  simp only [CollatzResearch.WordTrace]
  refine ⟨279118978336375850686172525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186079318890917233790781683 279118978336375850686172525)
  ·
    refine ⟨104669616876140944007314697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279118978336375850686172525 104669616876140944007314697)
    ·
      refine ⟨78502212657105708005486023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104669616876140944007314697 78502212657105708005486023)
      ·
        refine ⟨117753318985658562008229035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78502212657105708005486023 117753318985658562008229035)
        ·
          refine ⟨176629978478487843012343553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117753318985658562008229035 176629978478487843012343553)
          ·
            refine ⟨132472483858865882259257665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176629978478487843012343553 132472483858865882259257665)
            ·
              refine ⟨99354362894149411694443249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132472483858865882259257665 99354362894149411694443249)
              ·
                refine ⟨74515772170612058770832437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99354362894149411694443249 74515772170612058770832437)
                ·
                  refine ⟨6985853640994880509765541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74515772170612058770832437 6985853640994880509765541)
                  ·
                    refine ⟨1309847557686540095581039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6985853640994880509765541 1309847557686540095581039)
                    ·
                      rfl

theorem cell23_7652757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 5, 4].length) (baseStart_7652757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652757 prefixEnd_7652757 := by exact prefixLift 7652757
  have htrace : WordTrace (prefixWord ++ tailWord_7652757) baseStart_7652757 baseEnd_7652757 := by
    simpa [prefixWord, tailWord_7652757, baseEnd_7652757] using wordTrace_append hprefix tailTrace_7652757
  have hstable : (prefixWord ++ tailWord_7652757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652757).length < 2 ^ (prefixWord ++ tailWord_7652757).sum := by decide
  have hdescent : baseEnd_7652757 < baseStart_7652757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652847 : List Nat := [1, 1, 2, 1, 4, 1, 3, 3, 1, 6]
def baseStart_7652847 : Nat := 118140960795 + 7652847 * 2 ^ 59
def prefixEnd_7652847 : Nat := 4983230072969 + 3 ^ 40 * 7652847 * 2
def baseEnd_7652847 : Nat := 1309862962106174978205901

theorem tailTrace_7652847 : CollatzResearch.WordTrace tailWord_7652847 prefixEnd_7652847 1309862962106174978205901 := by
  unfold tailWord_7652847
  simp only [CollatzResearch.WordTrace]
  refine ⟨279122260906049796056948795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186081507270699864037965863 279122260906049796056948795)
  ·
    refine ⟨418683391359074694085423193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279122260906049796056948795 418683391359074694085423193)
    ·
      refine ⟨314012543519306020564067395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418683391359074694085423193 314012543519306020564067395)
      ·
        refine ⟨471018815278959030846101093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314012543519306020564067395 471018815278959030846101093)
        ·
          refine ⟨88316027864804818283643955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 471018815278959030846101093 88316027864804818283643955)
          ·
            refine ⟨132474041797207227425465933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88316027864804818283643955 132474041797207227425465933)
            ·
              refine ⟨49677765673952710284549725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132474041797207227425465933 49677765673952710284549725)
              ·
                refine ⟨18629162127732266356706147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49677765673952710284549725 18629162127732266356706147)
                ·
                  refine ⟨27943743191598399535059221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18629162127732266356706147 27943743191598399535059221)
                  ·
                    refine ⟨1309862962106174978205901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27943743191598399535059221 1309862962106174978205901)
                    ·
                      rfl

theorem cell23_7652847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 6].length) (baseStart_7652847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652847 prefixEnd_7652847 := by exact prefixLift 7652847
  have htrace : WordTrace (prefixWord ++ tailWord_7652847) baseStart_7652847 baseEnd_7652847 := by
    simpa [prefixWord, tailWord_7652847, baseEnd_7652847] using wordTrace_append hprefix tailTrace_7652847
  have hstable : (prefixWord ++ tailWord_7652847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652847).length < 2 ^ (prefixWord ++ tailWord_7652847).sum := by decide
  have hdescent : baseEnd_7652847 < baseStart_7652847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652865 : List Nat := [1, 2, 4, 1, 4, 1, 2, 3, 1, 1, 3]
def baseStart_7652865 : Nat := 118140960795 + 7652865 * 2 ^ 59
def prefixEnd_7652865 : Nat := 4983230072969 + 3 ^ 40 * 7652865 * 2
def baseEnd_7652865 : Nat := 3929598128970305864192621

theorem tailTrace_7652865 : CollatzResearch.WordTrace tailWord_7652865 prefixEnd_7652865 3929598128970305864192621 := by
  unfold tailWord_7652865
  simp only [CollatzResearch.WordTrace]
  refine ⟨279122917419984585131104049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186081944946656390087402699 279122917419984585131104049)
  ·
    refine ⟨209342188064988438848328037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279122917419984585131104049 209342188064988438848328037)
    ·
      refine ⟨39251660262185332284061507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209342188064988438848328037 39251660262185332284061507)
      ·
        refine ⟨58877490393277998426092261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39251660262185332284061507 58877490393277998426092261)
        ·
          refine ⟨11039529448739624704892299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58877490393277998426092261 11039529448739624704892299)
          ·
            refine ⟨16559294173109437057338449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11039529448739624704892299 16559294173109437057338449)
            ·
              refine ⟨12419470629832077793003837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16559294173109437057338449 12419470629832077793003837)
              ·
                refine ⟨4657301486187029172376439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12419470629832077793003837 4657301486187029172376439)
                ·
                  refine ⟨6985952229280543758564659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4657301486187029172376439 6985952229280543758564659)
                  ·
                    refine ⟨10478928343920815637846989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6985952229280543758564659 10478928343920815637846989)
                    ·
                      refine ⟨3929598128970305864192621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10478928343920815637846989 3929598128970305864192621)
                      ·
                        rfl

theorem cell23_7652865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 3, 1, 1, 3].length) (baseStart_7652865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652865 prefixEnd_7652865 := by exact prefixLift 7652865
  have htrace : WordTrace (prefixWord ++ tailWord_7652865) baseStart_7652865 baseEnd_7652865 := by
    simpa [prefixWord, tailWord_7652865, baseEnd_7652865] using wordTrace_append hprefix tailTrace_7652865
  have hstable : (prefixWord ++ tailWord_7652865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652865).length < 2 ^ (prefixWord ++ tailWord_7652865).sum := by decide
  have hdescent : baseEnd_7652865 < baseStart_7652865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652867 : List Nat := [1, 1, 1, 3, 2, 1, 2, 3, 3, 2, 4]
def baseStart_7652867 : Nat := 118140960795 + 7652867 * 2 ^ 59
def prefixEnd_7652867 : Nat := 4983230072969 + 3 ^ 40 * 7652867 * 2
def baseEnd_7652867 : Nat := 3929599155931614856367611

theorem tailTrace_7652867 : CollatzResearch.WordTrace tailWord_7652867 prefixEnd_7652867 3929599155931614856367611 := by
  unfold tailWord_7652867
  simp only [CollatzResearch.WordTrace]
  refine ⟨279122990365977339472676855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186081993577318226315117903 279122990365977339472676855)
  ·
    refine ⟨418684485548966009209015283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279122990365977339472676855 418684485548966009209015283)
    ·
      refine ⟨628026728323449013813522925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418684485548966009209015283 628026728323449013813522925)
      ·
        refine ⟨235510023121293380180071097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 628026728323449013813522925 235510023121293380180071097)
        ·
          refine ⟨176632517340970035135053323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235510023121293380180071097 176632517340970035135053323)
          ·
            refine ⟨264948776011455052702579985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176632517340970035135053323 264948776011455052702579985)
            ·
              refine ⟨198711582008591289526934989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264948776011455052702579985 198711582008591289526934989)
              ·
                refine ⟨74516843253221733572600621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198711582008591289526934989 74516843253221733572600621)
                ·
                  refine ⟨27943816219958150089725233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74516843253221733572600621 27943816219958150089725233)
                  ·
                    refine ⟨20957862164968612567293925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27943816219958150089725233 20957862164968612567293925)
                    ·
                      refine ⟨3929599155931614856367611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20957862164968612567293925 3929599155931614856367611)
                      ·
                        rfl

theorem cell23_7652867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 2, 4].length) (baseStart_7652867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652867 prefixEnd_7652867 := by exact prefixLift 7652867
  have htrace : WordTrace (prefixWord ++ tailWord_7652867) baseStart_7652867 baseEnd_7652867 := by
    simpa [prefixWord, tailWord_7652867, baseEnd_7652867] using wordTrace_append hprefix tailTrace_7652867
  have hstable : (prefixWord ++ tailWord_7652867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652867).length < 2 ^ (prefixWord ++ tailWord_7652867).sum := by decide
  have hdescent : baseEnd_7652867 < baseStart_7652867 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652871 : List Nat := [1, 1, 4, 3, 2, 2, 1, 3, 1, 1, 4]
def baseStart_7652871 : Nat := 118140960795 + 7652871 * 2 ^ 59
def prefixEnd_7652871 : Nat := 4983230072969 + 3 ^ 40 * 7652871 * 2
def baseEnd_7652871 : Nat := 3929601209854232840717593

theorem tailTrace_7652871 : CollatzResearch.WordTrace tailWord_7652871 prefixEnd_7652871 3929601209854232840717593 := by
  unfold tailWord_7652871
  simp only [CollatzResearch.WordTrace]
  refine ⟨279123136257962848155822467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186082090838641898770548311 279123136257962848155822467)
  ·
    refine ⟨418684704386944272233733701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279123136257962848155822467 418684704386944272233733701)
    ·
      refine ⟨78503382072552051043825069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 418684704386944272233733701 78503382072552051043825069)
      ·
        refine ⟨29438768277207019141434401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78503382072552051043825069 29438768277207019141434401)
        ·
          refine ⟨22079076207905264356075801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29438768277207019141434401 22079076207905264356075801)
          ·
            refine ⟨16559307155928948267056851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22079076207905264356075801 16559307155928948267056851)
            ·
              refine ⟨24838960733893422400585277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16559307155928948267056851 24838960733893422400585277)
              ·
                refine ⟨9314610275210033400219479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24838960733893422400585277 9314610275210033400219479)
                ·
                  refine ⟨13971915412815050100329219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9314610275210033400219479 13971915412815050100329219)
                  ·
                    refine ⟨20957873119222575150493829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13971915412815050100329219 20957873119222575150493829)
                    ·
                      refine ⟨3929601209854232840717593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20957873119222575150493829 3929601209854232840717593)
                      ·
                        rfl

theorem cell23_7652871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_7652871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652871 prefixEnd_7652871 := by exact prefixLift 7652871
  have htrace : WordTrace (prefixWord ++ tailWord_7652871) baseStart_7652871 baseEnd_7652871 := by
    simpa [prefixWord, tailWord_7652871, baseEnd_7652871] using wordTrace_append hprefix tailTrace_7652871
  have hstable : (prefixWord ++ tailWord_7652871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652871).length < 2 ^ (prefixWord ++ tailWord_7652871).sum := by decide
  have hdescent : baseEnd_7652871 < baseStart_7652871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652921 : List Nat := [1, 2, 1, 5, 1, 2, 1, 2, 4, 1, 3]
def baseStart_7652921 : Nat := 118140960795 + 7652921 * 2 ^ 59
def prefixEnd_7652921 : Nat := 4983230072969 + 3 ^ 40 * 7652921 * 2
def baseEnd_7652921 : Nat := 3929626883886957645092363

theorem tailTrace_7652921 : CollatzResearch.WordTrace tailWord_7652921 prefixEnd_7652921 3929626883886957645092363 := by
  unfold tailWord_7652921
  simp only [CollatzResearch.WordTrace]
  refine ⟨279124959907781706695142617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186083306605187804463428411 279124959907781706695142617)
  ·
    refine ⟨209343719930836280021356963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279124959907781706695142617 209343719930836280021356963)
    ·
      refine ⟨314015579896254420032035445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209343719930836280021356963 314015579896254420032035445)
      ·
        refine ⟨29438960615273851878003323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 314015579896254420032035445 29438960615273851878003323)
        ·
          refine ⟨44158440922910777817004985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29438960615273851878003323 44158440922910777817004985)
          ·
            refine ⟨33118830692183083362753739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44158440922910777817004985 33118830692183083362753739)
            ·
              refine ⟨49678246038274625044130609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33118830692183083362753739 49678246038274625044130609)
              ·
                refine ⟨37258684528705968783097957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49678246038274625044130609 37258684528705968783097957)
                ·
                  refine ⟨6986003349132369146830867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37258684528705968783097957 6986003349132369146830867)
                  ·
                    refine ⟨10479005023698553720246301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6986003349132369146830867 10479005023698553720246301)
                    ·
                      refine ⟨3929626883886957645092363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10479005023698553720246301 3929626883886957645092363)
                      ·
                        rfl

theorem cell23_7652921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_7652921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652921 prefixEnd_7652921 := by exact prefixLift 7652921
  have htrace : WordTrace (prefixWord ++ tailWord_7652921) baseStart_7652921 baseEnd_7652921 := by
    simpa [prefixWord, tailWord_7652921, baseEnd_7652921] using wordTrace_append hprefix tailTrace_7652921
  have hstable : (prefixWord ++ tailWord_7652921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652921).length < 2 ^ (prefixWord ++ tailWord_7652921).sum := by decide
  have hdescent : baseEnd_7652921 < baseStart_7652921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652937 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 4, 6]
def baseStart_7652937 : Nat := 118140960795 + 7652937 * 2 ^ 59
def prefixEnd_7652937 : Nat := 4983230072969 + 3 ^ 40 * 7652937 * 2
def baseEnd_7652937 : Nat := 1309878366525809860830763

theorem tailTrace_7652937 : CollatzResearch.WordTrace tailWord_7652937 prefixEnd_7652937 1309878366525809860830763 := by
  unfold tailWord_7652937
  simp only [CollatzResearch.WordTrace]
  refine ⟨279125543475723741427725065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186083695650482494285150043 279125543475723741427725065)
  ·
    refine ⟨209344157606792806070793799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279125543475723741427725065 209344157606792806070793799)
    ·
      refine ⟨314016236410189209106190699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209344157606792806070793799 314016236410189209106190699)
      ·
        refine ⟨471024354615283813659286049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314016236410189209106190699 471024354615283813659286049)
        ·
          refine ⟨353268265961462860244464537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 471024354615283813659286049 353268265961462860244464537)
          ·
            refine ⟨264951199471097145183348403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 353268265961462860244464537 264951199471097145183348403)
            ·
              refine ⟨397426799206645717775022605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264951199471097145183348403 397426799206645717775022605)
              ·
                refine ⟨149035049702492144165633477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 397426799206645717775022605 149035049702492144165633477)
                ·
                  refine ⟨27944071819217277031056277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149035049702492144165633477 27944071819217277031056277)
                  ·
                    refine ⟨1309878366525809860830763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27944071819217277031056277 1309878366525809860830763)
                    ·
                      rfl

theorem cell23_7652937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 6].length) (baseStart_7652937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652937 prefixEnd_7652937 := by exact prefixLift 7652937
  have htrace : WordTrace (prefixWord ++ tailWord_7652937) baseStart_7652937 baseEnd_7652937 := by
    simpa [prefixWord, tailWord_7652937, baseEnd_7652937] using wordTrace_append hprefix tailTrace_7652937
  have hstable : (prefixWord ++ tailWord_7652937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652937).length < 2 ^ (prefixWord ++ tailWord_7652937).sum := by decide
  have hdescent : baseEnd_7652937 < baseStart_7652937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652961 : List Nat := [1, 2, 3, 1, 1, 3, 2, 3, 1, 4, 2]
def baseStart_7652961 : Nat := 118140960795 + 7652961 * 2 ^ 59
def prefixEnd_7652961 : Nat := 4983230072969 + 3 ^ 40 * 7652961 * 2
def baseEnd_7652961 : Nat := 3929647423113137488592179

theorem tailTrace_7652961 : CollatzResearch.WordTrace tailWord_7652961 prefixEnd_7652961 3929647423113137488592179 := by
  unfold tailWord_7652961
  simp only [CollatzResearch.WordTrace]
  refine ⟨279126418827636793526598737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186084279218424529017732491 279126418827636793526598737)
  ·
    refine ⟨209344814120727595144949053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279126418827636793526598737 209344814120727595144949053)
    ·
      refine ⟨78504305295272848179355895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209344814120727595144949053 78504305295272848179355895)
      ·
        refine ⟨117756457942909272269033843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78504305295272848179355895 117756457942909272269033843)
        ·
          refine ⟨176634686914363908403550765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117756457942909272269033843 176634686914363908403550765)
          ·
            refine ⟨66238007592886465651331537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176634686914363908403550765 66238007592886465651331537)
            ·
              refine ⟨49678505694664849238498653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66238007592886465651331537 49678505694664849238498653)
              ·
                refine ⟨18629439635499318464436995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49678505694664849238498653 18629439635499318464436995)
                ·
                  refine ⟨27944159453248977696655493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18629439635499318464436995 27944159453248977696655493)
                  ·
                    refine ⟨5239529897484183318122905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27944159453248977696655493 5239529897484183318122905)
                    ·
                      refine ⟨3929647423113137488592179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5239529897484183318122905 3929647423113137488592179)
                      ·
                        rfl

theorem cell23_7652961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 4, 2].length) (baseStart_7652961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652961 prefixEnd_7652961 := by exact prefixLift 7652961
  have htrace : WordTrace (prefixWord ++ tailWord_7652961) baseStart_7652961 baseEnd_7652961 := by
    simpa [prefixWord, tailWord_7652961, baseEnd_7652961] using wordTrace_append hprefix tailTrace_7652961
  have hstable : (prefixWord ++ tailWord_7652961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652961).length < 2 ^ (prefixWord ++ tailWord_7652961).sum := by decide
  have hdescent : baseEnd_7652961 < baseStart_7652961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652964 : List Nat := [2, 3, 1, 1, 2, 3, 1, 2, 2, 1, 5]
def baseStart_7652964 : Nat := 118140960795 + 7652964 * 2 ^ 59
def prefixEnd_7652964 : Nat := 4983230072969 + 3 ^ 40 * 7652964 * 2
def baseEnd_7652964 : Nat := 3929648963555100976854665

theorem tailTrace_7652964 : CollatzResearch.WordTrace tailWord_7652964 prefixEnd_7652964 3929648963555100976854665 := by
  unfold tailWord_7652964
  simp only [CollatzResearch.WordTrace]
  refine ⟨139563264123312962519478973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186084352164417283359305297 139563264123312962519478973)
  ·
    refine ⟨52336224046242360944804615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139563264123312962519478973 52336224046242360944804615)
    ·
      refine ⟨78504336069363541417206923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52336224046242360944804615 78504336069363541417206923)
      ·
        refine ⟨117756504104045312125810385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78504336069363541417206923 117756504104045312125810385)
        ·
          refine ⟨88317378078033984094357789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117756504104045312125810385 88317378078033984094357789)
          ·
            refine ⟨33119016779262744035384171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88317378078033984094357789 33119016779262744035384171)
            ·
              refine ⟨49678525168894116053076257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33119016779262744035384171 49678525168894116053076257)
              ·
                refine ⟨37258893876670587039807193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49678525168894116053076257 37258893876670587039807193)
                ·
                  refine ⟨27944170407502940279855395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37258893876670587039807193 27944170407502940279855395)
                  ·
                    refine ⟨41916255611254410419783093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27944170407502940279855395 41916255611254410419783093)
                    ·
                      refine ⟨3929648963555100976854665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41916255611254410419783093 3929648963555100976854665)
                      ·
                        rfl

theorem cell23_7652964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_7652964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652964 prefixEnd_7652964 := by exact prefixLift 7652964
  have htrace : WordTrace (prefixWord ++ tailWord_7652964) baseStart_7652964 baseEnd_7652964 := by
    simpa [prefixWord, tailWord_7652964, baseEnd_7652964] using wordTrace_append hprefix tailTrace_7652964
  have hstable : (prefixWord ++ tailWord_7652964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652964).length < 2 ^ (prefixWord ++ tailWord_7652964).sum := by decide
  have hdescent : baseEnd_7652964 < baseStart_7652964 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652965 : List Nat := [1, 3, 1, 3, 3, 3, 1, 2, 1, 3, 2]
def baseStart_7652965 : Nat := 118140960795 + 7652965 * 2 ^ 59
def prefixEnd_7652965 : Nat := 4983230072969 + 3 ^ 40 * 7652965 * 2
def baseEnd_7652965 : Nat := 3929649477035755472942161

theorem tailTrace_7652965 : CollatzResearch.WordTrace tailWord_7652965 prefixEnd_7652965 3929649477035755472942161 := by
  unfold tailWord_7652965
  simp only [CollatzResearch.WordTrace]
  refine ⟨279126564719622302209744349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186084376479748201473162899 279126564719622302209744349)
  ·
    refine ⟨104672461769858363328654131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279126564719622302209744349 104672461769858363328654131)
    ·
      refine ⟨157008692654787544992981197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104672461769858363328654131 157008692654787544992981197)
      ·
        refine ⟨58878259745545329372367949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157008692654787544992981197 58878259745545329372367949)
        ·
          refine ⟨22079347404579498514637981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58878259745545329372367949 22079347404579498514637981)
          ·
            refine ⟨8279755276717311942989243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22079347404579498514637981 8279755276717311942989243)
            ·
              refine ⟨12419632915075967914483865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8279755276717311942989243 12419632915075967914483865)
              ·
                refine ⟨9314724686306975935862899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12419632915075967914483865 9314724686306975935862899)
                ·
                  refine ⟨13972087029460463903794349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9314724686306975935862899 13972087029460463903794349)
                  ·
                    refine ⟨5239532636047673963922881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13972087029460463903794349 5239532636047673963922881)
                    ·
                      refine ⟨3929649477035755472942161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5239532636047673963922881 3929649477035755472942161)
                      ·
                        rfl

theorem cell23_7652965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 2, 1, 3, 2].length) (baseStart_7652965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652965 prefixEnd_7652965 := by exact prefixLift 7652965
  have htrace : WordTrace (prefixWord ++ tailWord_7652965) baseStart_7652965 baseEnd_7652965 := by
    simpa [prefixWord, tailWord_7652965, baseEnd_7652965] using wordTrace_append hprefix tailTrace_7652965
  have hstable : (prefixWord ++ tailWord_7652965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652965).length < 2 ^ (prefixWord ++ tailWord_7652965).sum := by decide
  have hdescent : baseEnd_7652965 < baseStart_7652965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652978 : List Nat := [3, 2, 1, 2, 3, 2, 1, 2, 1, 4, 2]
def baseStart_7652978 : Nat := 118140960795 + 7652978 * 2 ^ 59
def prefixEnd_7652978 : Nat := 4983230072969 + 3 ^ 40 * 7652978 * 2
def baseEnd_7652978 : Nat := 3929656152284263922079601

theorem tailTrace_7652978 : CollatzResearch.WordTrace tailWord_7652978 prefixEnd_7652978 3929656152284263922079601 := by
  unfold tailWord_7652978
  simp only [CollatzResearch.WordTrace]
  refine ⟨69781759717143801357491897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186084692579050136953311725 69781759717143801357491897)
  ·
    refine ⟨52336319787857851018118923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69781759717143801357491897 52336319787857851018118923)
    ·
      refine ⟨78504479681786776527178385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52336319787857851018118923 78504479681786776527178385)
      ·
        refine ⟨58878359761340082395383789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78504479681786776527178385 58878359761340082395383789)
        ·
          refine ⟨22079384910502530898268921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58878359761340082395383789 22079384910502530898268921)
          ·
            refine ⟨16559538682876898173701691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22079384910502530898268921 16559538682876898173701691)
            ·
              refine ⟨24839308024315347260552537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16559538682876898173701691 24839308024315347260552537)
              ·
                refine ⟨18629481018236510445414403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24839308024315347260552537 18629481018236510445414403)
                ·
                  refine ⟨27944221527354765668121605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18629481018236510445414403 27944221527354765668121605)
                  ·
                    refine ⟨5239541536379018562772801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27944221527354765668121605 5239541536379018562772801)
                    ·
                      refine ⟨3929656152284263922079601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5239541536379018562772801 3929656152284263922079601)
                      ·
                        rfl

theorem cell23_7652978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 1, 4, 2].length) (baseStart_7652978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652978 prefixEnd_7652978 := by exact prefixLift 7652978
  have htrace : WordTrace (prefixWord ++ tailWord_7652978) baseStart_7652978 baseEnd_7652978 := by
    simpa [prefixWord, tailWord_7652978, baseEnd_7652978] using wordTrace_append hprefix tailTrace_7652978
  have hstable : (prefixWord ++ tailWord_7652978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652978).length < 2 ^ (prefixWord ++ tailWord_7652978).sum := by decide
  have hdescent : baseEnd_7652978 < baseStart_7652978 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652981 : List Nat := [1, 3, 4, 2, 1, 1, 2, 1, 2, 1, 5]
def baseStart_7652981 : Nat := 118140960795 + 7652981 * 2 ^ 59
def prefixEnd_7652981 : Nat := 4983230072969 + 3 ^ 40 * 7652981 * 2
def baseEnd_7652981 : Nat := 3929657692726227410342087

theorem tailTrace_7652981 : CollatzResearch.WordTrace tailWord_7652981 prefixEnd_7652981 3929657692726227410342087 := by
  unfold tailWord_7652981
  simp only [CollatzResearch.WordTrace]
  refine ⟨279127148287564336942326797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186084765525042891294884531 279127148287564336942326797)
  ·
    refine ⟨104672680607836626353372549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279127148287564336942326797 104672680607836626353372549)
    ·
      refine ⟨19626127613969367441257353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104672680607836626353372549 19626127613969367441257353)
      ·
        refine ⟨14719595710477025580943015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19626127613969367441257353 14719595710477025580943015)
        ·
          refine ⟨22079393565715538371414523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14719595710477025580943015 22079393565715538371414523)
          ·
            refine ⟨33119090348573307557121785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22079393565715538371414523 33119090348573307557121785)
            ·
              refine ⟨24839317761429980667841339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33119090348573307557121785 24839317761429980667841339)
              ·
                refine ⟨37258976642144971001762009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24839317761429980667841339 37258976642144971001762009)
                ·
                  refine ⟨27944232481608728251321507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37258976642144971001762009 27944232481608728251321507)
                  ·
                    refine ⟨41916348722413092376982261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27944232481608728251321507 41916348722413092376982261)
                    ·
                      refine ⟨3929657692726227410342087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41916348722413092376982261 3929657692726227410342087)
                      ·
                        rfl

theorem cell23_7652981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_7652981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652981 prefixEnd_7652981 := by exact prefixLift 7652981
  have htrace : WordTrace (prefixWord ++ tailWord_7652981) baseStart_7652981 baseEnd_7652981 := by
    simpa [prefixWord, tailWord_7652981, baseEnd_7652981] using wordTrace_append hprefix tailTrace_7652981
  have hstable : (prefixWord ++ tailWord_7652981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652981).length < 2 ^ (prefixWord ++ tailWord_7652981).sum := by decide
  have hdescent : baseEnd_7652981 < baseStart_7652981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652982 : List Nat := [5, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2]
def baseStart_7652982 : Nat := 118140960795 + 7652982 * 2 ^ 59
def prefixEnd_7652982 : Nat := 4983230072969 + 3 ^ 40 * 7652982 * 2
def baseEnd_7652982 : Nat := 3929658206206881906429583

theorem tailTrace_7652982 : CollatzResearch.WordTrace tailWord_7652982 prefixEnd_7652982 3929658206206881906429583 := by
  unfold tailWord_7652982
  simp only [CollatzResearch.WordTrace]
  refine ⟨17445449047535044632069575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186084789840373809408742133 17445449047535044632069575)
  ·
    refine ⟨26168173571302566948104363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17445449047535044632069575 26168173571302566948104363)
    ·
      refine ⟨39252260356953850422156545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26168173571302566948104363 39252260356953850422156545)
      ·
        refine ⟨29439195267715387816617409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39252260356953850422156545 29439195267715387816617409)
        ·
          refine ⟨22079396450786540862463057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29439195267715387816617409 22079396450786540862463057)
          ·
            refine ⟨16559547338089905646847293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22079396450786540862463057 16559547338089905646847293)
            ·
              refine ⟨6209830251783714617567735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16559547338089905646847293 6209830251783714617567735)
              ·
                refine ⟨9314745377675571926351603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6209830251783714617567735 9314745377675571926351603)
                ·
                  refine ⟨13972118066513357889527405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9314745377675571926351603 13972118066513357889527405)
                  ·
                    refine ⟨5239544274942509208572777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13972118066513357889527405 5239544274942509208572777)
                    ·
                      refine ⟨3929658206206881906429583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5239544274942509208572777 3929658206206881906429583)
                      ·
                        rfl

theorem cell23_7652982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_7652982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652982 prefixEnd_7652982 := by exact prefixLift 7652982
  have htrace : WordTrace (prefixWord ++ tailWord_7652982) baseStart_7652982 baseEnd_7652982 := by
    simpa [prefixWord, tailWord_7652982, baseEnd_7652982] using wordTrace_append hprefix tailTrace_7652982
  have hstable : (prefixWord ++ tailWord_7652982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652982).length < 2 ^ (prefixWord ++ tailWord_7652982).sum := by decide
  have hdescent : baseEnd_7652982 < baseStart_7652982 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7653021 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 4, 5, 2]
def baseStart_7653021 : Nat := 118140960795 + 7653021 * 2 ^ 59
def prefixEnd_7653021 : Nat := 4983230072969 + 3 ^ 40 * 7653021 * 2
def baseEnd_7653021 : Nat := 3929678231952407253841903

theorem tailTrace_7653021 : CollatzResearch.WordTrace tailWord_7653021 prefixEnd_7653021 3929678231952407253841903 := by
  unfold tailWord_7653021
  simp only [CollatzResearch.WordTrace]
  refine ⟨279128607207419423773782917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186085738138279615849188611 279128607207419423773782917)
  ·
    refine ⟨52336613851391141957584297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 279128607207419423773782917 52336613851391141957584297)
    ·
      refine ⟨39252460388543356468188223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52336613851391141957584297 39252460388543356468188223)
      ·
        refine ⟨58878690582815034702282335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39252460388543356468188223 58878690582815034702282335)
        ·
          refine ⟨88318035874222552053423503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58878690582815034702282335 88318035874222552053423503)
          ·
            refine ⟨132477053811333828080135255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88318035874222552053423503 132477053811333828080135255)
            ·
              refine ⟨198715580717000742120202883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132477053811333828080135255 198715580717000742120202883)
              ·
                refine ⟨298073371075501113180304325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198715580717000742120202883 298073371075501113180304325)
                ·
                  refine ⟨55888757076656458721307061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 298073371075501113180304325 55888757076656458721307061)
                  ·
                    refine ⟨5239570975936543005122537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55888757076656458721307061 5239570975936543005122537)
                    ·
                      refine ⟨3929678231952407253841903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5239570975936543005122537 3929678231952407253841903)
                      ·
                        rfl

theorem cell23_7653021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 5, 2].length) (baseStart_7653021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7653021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7653021 prefixEnd_7653021 := by exact prefixLift 7653021
  have htrace : WordTrace (prefixWord ++ tailWord_7653021) baseStart_7653021 baseEnd_7653021 := by
    simpa [prefixWord, tailWord_7653021, baseEnd_7653021] using wordTrace_append hprefix tailTrace_7653021
  have hstable : (prefixWord ++ tailWord_7653021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7653021).length < 2 ^ (prefixWord ++ tailWord_7653021).sum := by decide
  have hdescent : baseEnd_7653021 < baseStart_7653021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7653021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7653064 : List Nat := [2, 1, 3, 1, 2, 2, 1, 2, 2, 1, 6]
def baseStart_7653064 : Nat := 118140960795 + 7653064 * 2 ^ 59
def prefixEnd_7653064 : Nat := 4983230072969 + 3 ^ 40 * 7653064 * 2
def baseEnd_7653064 : Nat := 3929700311620550585604205

theorem tailTrace_7653064 : CollatzResearch.WordTrace tailWord_7653064 prefixEnd_7653064 3929700311620550585604205 := by
  unfold tailWord_7653064
  simp only [CollatzResearch.WordTrace]
  refine ⟨139565087773131821058799123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186086783697509094745065497 139565087773131821058799123)
  ·
    refine ⟨209347631659697731588198685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139565087773131821058799123 209347631659697731588198685)
    ·
      refine ⟨78505361872386649345574507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209347631659697731588198685 78505361872386649345574507)
      ·
        refine ⟨117758042808579974018361761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78505361872386649345574507 117758042808579974018361761)
        ·
          refine ⟨88318532106434980513771321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117758042808579974018361761 88318532106434980513771321)
          ·
            refine ⟨66238899079826235385328491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88318532106434980513771321 66238899079826235385328491)
            ·
              refine ⟨99358348619739353077992737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66238899079826235385328491 99358348619739353077992737)
              ·
                refine ⟨74518761464804514808494553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99358348619739353077992737 74518761464804514808494553)
                ·
                  refine ⟨55889071098603386106370915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74518761464804514808494553 55889071098603386106370915)
                  ·
                    refine ⟨83833606647905079159556373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55889071098603386106370915 83833606647905079159556373)
                    ·
                      refine ⟨3929700311620550585604205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83833606647905079159556373 3929700311620550585604205)
                      ·
                        rfl

theorem cell23_7653064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_7653064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7653064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7653064 prefixEnd_7653064 := by exact prefixLift 7653064
  have htrace : WordTrace (prefixWord ++ tailWord_7653064) baseStart_7653064 baseEnd_7653064 := by
    simpa [prefixWord, tailWord_7653064, baseEnd_7653064] using wordTrace_append hprefix tailTrace_7653064
  have hstable : (prefixWord ++ tailWord_7653064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7653064).length < 2 ^ (prefixWord ++ tailWord_7653064).sum := by decide
  have hdescent : baseEnd_7653064 < baseStart_7653064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7653064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7653114 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 2, 1, 7]
def baseStart_7653114 : Nat := 118140960795 + 7653114 * 2 ^ 59
def prefixEnd_7653114 : Nat := 4983230072969 + 3 ^ 40 * 7653114 * 2
def baseEnd_7653114 : Nat := 3929725985653275389978975

theorem tailTrace_7653114 : CollatzResearch.WordTrace tailWord_7653114 prefixEnd_7653114 3929725985653275389978975 := by
  unfold tailWord_7653114
  simp only [CollatzResearch.WordTrace]
  refine ⟨69782999799020625164229599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186087999464055000437945597 69782999799020625164229599)
  ·
    refine ⟨104674499698530937746344399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69782999799020625164229599 104674499698530937746344399)
    ·
      refine ⟨157011749547796406619516599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104674499698530937746344399 157011749547796406619516599)
      ·
        refine ⟨235517624321694609929274899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157011749547796406619516599 235517624321694609929274899)
        ·
          refine ⟨353276436482541914893912349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235517624321694609929274899 353276436482541914893912349)
          ·
            refine ⟨132478663680953218085217131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 353276436482541914893912349 132478663680953218085217131)
            ·
              refine ⟨198717995521429827127825697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132478663680953218085217131 198717995521429827127825697)
              ·
                refine ⟨149038496641072370345869273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198717995521429827127825697 149038496641072370345869273)
                ·
                  refine ⟨111778872480804277759401955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149038496641072370345869273 111778872480804277759401955)
                  ·
                    refine ⟨167668308721206416639102933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111778872480804277759401955 167668308721206416639102933)
                    ·
                      refine ⟨3929725985653275389978975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 167668308721206416639102933 3929725985653275389978975)
                      ·
                        rfl

theorem cell23_7653114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_7653114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7653114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7653114 prefixEnd_7653114 := by exact prefixLift 7653114
  have htrace : WordTrace (prefixWord ++ tailWord_7653114) baseStart_7653114 baseEnd_7653114 := by
    simpa [prefixWord, tailWord_7653114, baseEnd_7653114] using wordTrace_append hprefix tailTrace_7653114
  have hstable : (prefixWord ++ tailWord_7653114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7653114).length < 2 ^ (prefixWord ++ tailWord_7653114).sum := by decide
  have hdescent : baseEnd_7653114 < baseStart_7653114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7653114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7653128 : List Nat := [2, 1, 3, 2, 2, 1, 1, 2, 4, 3, 2]
def baseStart_7653128 : Nat := 118140960795 + 7653128 * 2 ^ 59
def prefixEnd_7653128 : Nat := 4983230072969 + 3 ^ 40 * 7653128 * 2
def baseEnd_7653128 : Nat := 3929733174382438335203911

theorem tailTrace_7653128 : CollatzResearch.WordTrace tailWord_7653128 prefixEnd_7653128 3929733174382438335203911 := by
  unfold tailWord_7653128
  simp only [CollatzResearch.WordTrace]
  refine ⟨139566254909015890523964019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186088339878687854031952025 139566254909015890523964019)
  ·
    refine ⟨209349382363523835785946029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139566254909015890523964019 209349382363523835785946029)
    ·
      refine ⟨78506018386321438419729761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209349382363523835785946029 78506018386321438419729761)
      ·
        refine ⟨58879513789741078814797321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78506018386321438419729761 58879513789741078814797321)
        ·
          refine ⟨44159635342305809111097991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58879513789741078814797321 44159635342305809111097991)
          ·
            refine ⟨66239453013458713666646987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44159635342305809111097991 66239453013458713666646987)
            ·
              refine ⟨99359179520188070499970481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66239453013458713666646987 99359179520188070499970481)
              ·
                refine ⟨74519384640141052874977861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99359179520188070499970481 74519384640141052874977861)
                ·
                  refine ⟨13972384620026447414058349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74519384640141052874977861 13972384620026447414058349)
                  ·
                    refine ⟨5239644232509917780271881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13972384620026447414058349 5239644232509917780271881)
                    ·
                      refine ⟨3929733174382438335203911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5239644232509917780271881 3929733174382438335203911)
                      ·
                        rfl

theorem cell23_7653128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 4, 3, 2].length) (baseStart_7653128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7653128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7653128 prefixEnd_7653128 := by exact prefixLift 7653128
  have htrace : WordTrace (prefixWord ++ tailWord_7653128) baseStart_7653128 baseEnd_7653128 := by
    simpa [prefixWord, tailWord_7653128, baseEnd_7653128] using wordTrace_append hprefix tailTrace_7653128
  have hstable : (prefixWord ++ tailWord_7653128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7653128).length < 2 ^ (prefixWord ++ tailWord_7653128).sum := by decide
  have hdescent : baseEnd_7653128 < baseStart_7653128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7653128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7653151 : List Nat := [1, 1, 2, 4, 2, 1, 3, 2, 1, 6]
def baseStart_7653151 : Nat := 118140960795 + 7653151 * 2 ^ 59
def prefixEnd_7653151 : Nat := 4983230072969 + 3 ^ 40 * 7653151 * 2
def baseEnd_7653151 : Nat := 1309914994812497248405435

theorem tailTrace_7653151 : CollatzResearch.WordTrace tailWord_7653151 prefixEnd_7653151 1309914994812497248405435 := by
  unfold tailWord_7653151
  simp only [CollatzResearch.WordTrace]
  refine ⟨279133348696948455976015307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186088899131298970650676871 279133348696948455976015307)
  ·
    refine ⟨418700023045422683964022961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279133348696948455976015307 418700023045422683964022961)
    ·
      refine ⟨314025017284067012973017221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418700023045422683964022961 314025017284067012973017221)
      ·
        refine ⟨58879690740762564932440729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 314025017284067012973017221 58879690740762564932440729)
        ·
          refine ⟨44159768055571923699330547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58879690740762564932440729 44159768055571923699330547)
          ·
            refine ⟨66239652083357885548995821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44159768055571923699330547 66239652083357885548995821)
            ·
              refine ⟨24839869531259207080873433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66239652083357885548995821 24839869531259207080873433)
              ·
                refine ⟨18629902148444405310655075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24839869531259207080873433 18629902148444405310655075)
                ·
                  refine ⟨27944853222666607965982613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18629902148444405310655075 27944853222666607965982613)
                  ·
                    refine ⟨1309914994812497248405435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27944853222666607965982613 1309914994812497248405435)
                    ·
                      rfl

theorem cell23_7653151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 6].length) (baseStart_7653151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7653151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7653151 prefixEnd_7653151 := by exact prefixLift 7653151
  have htrace : WordTrace (prefixWord ++ tailWord_7653151) baseStart_7653151 baseEnd_7653151 := by
    simpa [prefixWord, tailWord_7653151, baseEnd_7653151] using wordTrace_append hprefix tailTrace_7653151
  have hstable : (prefixWord ++ tailWord_7653151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7653151).length < 2 ^ (prefixWord ++ tailWord_7653151).sum := by decide
  have hdescent : baseEnd_7653151 < baseStart_7653151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7653151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7653161 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 7, 2, 3]
def baseStart_7653161 : Nat := 118140960795 + 7653161 * 2 ^ 59
def prefixEnd_7653161 : Nat := 4983230072969 + 3 ^ 40 * 7653161 * 2
def baseEnd_7653161 : Nat := 3929750119244036706091259

theorem tailTrace_7653161 : CollatzResearch.WordTrace tailWord_7653161 prefixEnd_7653161 3929750119244036706091259 := by
  unfold tailWord_7653161
  simp only [CollatzResearch.WordTrace]
  refine ⟨279133713426912227683879337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186089142284608151789252891 279133713426912227683879337)
  ·
    refine ⟨209350285070184170762909503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279133713426912227683879337 209350285070184170762909503)
    ·
      refine ⟨314025427605276256144364255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209350285070184170762909503 314025427605276256144364255)
      ·
        refine ⟨471038141407914384216546383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314025427605276256144364255 471038141407914384216546383)
        ·
          refine ⟨706557212111871576324819575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471038141407914384216546383 706557212111871576324819575)
          ·
            refine ⟨1059835818167807364487229363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706557212111871576324819575 1059835818167807364487229363)
            ·
              refine ⟨1589753727251711046730844045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1059835818167807364487229363 1589753727251711046730844045)
              ·
                refine ⟨596157647719391642524066517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1589753727251711046730844045 596157647719391642524066517)
                ·
                  refine ⟨13972444868423241621657809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 596157647719391642524066517 13972444868423241621657809)
                  ·
                    refine ⟨10479333651317431216243357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13972444868423241621657809 10479333651317431216243357)
                    ·
                      refine ⟨3929750119244036706091259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10479333651317431216243357 3929750119244036706091259)
                      ·
                        rfl

theorem cell23_7653161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 7, 2, 3].length) (baseStart_7653161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7653161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7653161 prefixEnd_7653161 := by exact prefixLift 7653161
  have htrace : WordTrace (prefixWord ++ tailWord_7653161) baseStart_7653161 baseEnd_7653161 := by
    simpa [prefixWord, tailWord_7653161, baseEnd_7653161] using wordTrace_append hprefix tailTrace_7653161
  have hstable : (prefixWord ++ tailWord_7653161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7653161).length < 2 ^ (prefixWord ++ tailWord_7653161).sum := by decide
  have hdescent : baseEnd_7653161 < baseStart_7653161 := by decide
  rcases family_descends (prefixWord ++ tailWord_7653161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7653164 : List Nat := [2, 2, 1, 1, 1, 16]
def baseStart_7653164 : Nat := 118140960795 + 7653164 * 2 ^ 59
def prefixEnd_7653164 : Nat := 4983230072969 + 3 ^ 40 * 7653164 * 2
def baseEnd_7653164 : Nat := 16171817529572017260715

theorem tailTrace_7653164 : CollatzResearch.WordTrace tailWord_7653164 prefixEnd_7653164 16171817529572017260715 := by
  unfold tailWord_7653164
  simp only [CollatzResearch.WordTrace]
  refine ⟨139566911422950679598119273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186089215230600906130825697 139566911422950679598119273)
  ·
    refine ⟨104675183567213009698589455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139566911422950679598119273 104675183567213009698589455)
    ·
      refine ⟨157012775350819514547884183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104675183567213009698589455 157012775350819514547884183)
      ·
        refine ⟨235519163026229271821826275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157012775350819514547884183 235519163026229271821826275)
        ·
          refine ⟨353278744539343907732739413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235519163026229271821826275 353278744539343907732739413)
          ·
            refine ⟨16171817529572017260715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 16 353278744539343907732739413 16171817529572017260715)
            ·
              rfl

theorem cell23_7653164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 16].length) (baseStart_7653164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7653164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7653164 prefixEnd_7653164 := by exact prefixLift 7653164
  have htrace : WordTrace (prefixWord ++ tailWord_7653164) baseStart_7653164 baseEnd_7653164 := by
    simpa [prefixWord, tailWord_7653164, baseEnd_7653164] using wordTrace_append hprefix tailTrace_7653164
  have hstable : (prefixWord ++ tailWord_7653164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7653164).length < 2 ^ (prefixWord ++ tailWord_7653164).sum := by decide
  have hdescent : baseEnd_7653164 < baseStart_7653164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7653164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7653169 : List Nat := [1, 2, 2, 3, 2, 4, 2, 2, 1, 1, 3]
def baseStart_7653169 : Nat := 118140960795 + 7653169 * 2 ^ 59
def prefixEnd_7653169 : Nat := 4983230072969 + 3 ^ 40 * 7653169 * 2
def baseEnd_7653169 : Nat := 3929754227089272674791223

theorem tailTrace_7653169 : CollatzResearch.WordTrace tailWord_7653169 prefixEnd_7653169 3929754227089272674791223 := by
  unfold tailWord_7653169
  simp only [CollatzResearch.WordTrace]
  refine ⟨279134005210883245050170561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186089336807255496700113707 279134005210883245050170561)
  ·
    refine ⟨209350503908162433787627921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279134005210883245050170561 209350503908162433787627921)
    ·
      refine ⟨157012877931121825340720941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209350503908162433787627921 157012877931121825340720941)
      ·
        refine ⟨58879829224170684502770353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157012877931121825340720941 58879829224170684502770353)
        ·
          refine ⟨44159871918128013377077765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58879829224170684502770353 44159871918128013377077765)
          ·
            refine ⟨8279975984649002508202081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44159871918128013377077765 8279975984649002508202081)
            ·
              refine ⟨6209981988486751881151561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8279975984649002508202081 6209981988486751881151561)
              ·
                refine ⟨4657486491365063910863671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6209981988486751881151561 4657486491365063910863671)
                ·
                  refine ⟨6986229737047595866295507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4657486491365063910863671 6986229737047595866295507)
                  ·
                    refine ⟨10479344605571393799443261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6986229737047595866295507 10479344605571393799443261)
                    ·
                      refine ⟨3929754227089272674791223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10479344605571393799443261 3929754227089272674791223)
                      ·
                        rfl

theorem cell23_7653169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 2, 1, 1, 3].length) (baseStart_7653169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7653169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7653169 prefixEnd_7653169 := by exact prefixLift 7653169
  have htrace : WordTrace (prefixWord ++ tailWord_7653169) baseStart_7653169 baseEnd_7653169 := by
    simpa [prefixWord, tailWord_7653169, baseEnd_7653169] using wordTrace_append hprefix tailTrace_7653169
  have hstable : (prefixWord ++ tailWord_7653169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7653169).length < 2 ^ (prefixWord ++ tailWord_7653169).sum := by decide
  have hdescent : baseEnd_7653169 < baseStart_7653169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7653169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7653178 : List Nat := [3, 1, 1, 1, 5, 1, 1, 2, 3, 2, 3]
def baseStart_7653178 : Nat := 118140960795 + 7653178 * 2 ^ 59
def prefixEnd_7653178 : Nat := 4983230072969 + 3 ^ 40 * 7653178 * 2
def baseEnd_7653178 : Nat := 3929758848415163139578681

theorem tailTrace_7653178 : CollatzResearch.WordTrace tailWord_7653178 prefixEnd_7653178 3929758848415163139578681 := by
  unfold tailWord_7653178
  simp only [CollatzResearch.WordTrace]
  refine ⟨69783583366962659896812047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186089555645233759724832125 69783583366962659896812047)
  ·
    refine ⟨104675375050443989845218071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69783583366962659896812047 104675375050443989845218071)
    ·
      refine ⟨157013062575665984767827107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104675375050443989845218071 157013062575665984767827107)
      ·
        refine ⟨235519593863498977151740661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157013062575665984767827107 235519593863498977151740661)
        ·
          refine ⟨22079961924703029107975687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 235519593863498977151740661 22079961924703029107975687)
          ·
            refine ⟨33119942887054543661963531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22079961924703029107975687 33119942887054543661963531)
            ·
              refine ⟨49679914330581815492945297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33119942887054543661963531 49679914330581815492945297)
              ·
                refine ⟨37259935747936361619708973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49679914330581815492945297 37259935747936361619708973)
                ·
                  refine ⟨13972475905476135607390865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37259935747936361619708973 13972475905476135607390865)
                  ·
                    refine ⟨10479356929107101705543149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13972475905476135607390865 10479356929107101705543149)
                    ·
                      refine ⟨3929758848415163139578681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10479356929107101705543149 3929758848415163139578681)
                      ·
                        rfl

theorem cell23_7653178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 3, 2, 3].length) (baseStart_7653178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7653178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7653178 prefixEnd_7653178 := by exact prefixLift 7653178
  have htrace : WordTrace (prefixWord ++ tailWord_7653178) baseStart_7653178 baseEnd_7653178 := by
    simpa [prefixWord, tailWord_7653178, baseEnd_7653178] using wordTrace_append hprefix tailTrace_7653178
  have hstable : (prefixWord ++ tailWord_7653178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7653178).length < 2 ^ (prefixWord ++ tailWord_7653178).sum := by decide
  have hdescent : baseEnd_7653178 < baseStart_7653178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7653178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7653212 : List Nat := [2, 2, 4, 2, 2, 1, 1, 3, 1, 2, 3]
def baseStart_7653212 : Nat := 118140960795 + 7653212 * 2 ^ 59
def prefixEnd_7653212 : Nat := 4983230072969 + 3 ^ 40 * 7653212 * 2
def baseEnd_7653212 : Nat := 3929776306757416006553525

theorem tailTrace_7653212 : CollatzResearch.WordTrace tailWord_7653212 prefixEnd_7653212 3929776306757416006553525 := by
  unfold tailWord_7653212
  simp only [CollatzResearch.WordTrace]
  refine ⟨139567786774863731696992945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186090382366484975595990593 139567786774863731696992945)
  ·
    refine ⟨104675840081147798772744709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139567786774863731696992945 104675840081147798772744709)
    ·
      refine ⟨19626720015215212269889633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104675840081147798772744709 19626720015215212269889633)
      ·
        refine ⟨14720040011411409202417225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19626720015215212269889633 14720040011411409202417225)
        ·
          refine ⟨11040030008558556901812919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14720040011411409202417225 11040030008558556901812919)
          ·
            refine ⟨16560045012837835352719379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11040030008558556901812919 16560045012837835352719379)
            ·
              refine ⟨24840067519256753029079069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16560045012837835352719379 24840067519256753029079069)
              ·
                refine ⟨9315025319721282385904651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24840067519256753029079069 9315025319721282385904651)
                ·
                  refine ⟨13972537979581923578856977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9315025319721282385904651 13972537979581923578856977)
                  ·
                    refine ⟨10479403484686442684142733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13972537979581923578856977 10479403484686442684142733)
                    ·
                      refine ⟨3929776306757416006553525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10479403484686442684142733 3929776306757416006553525)
                      ·
                        rfl

theorem cell23_7653212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_7653212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7653212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7653212 prefixEnd_7653212 := by exact prefixLift 7653212
  have htrace : WordTrace (prefixWord ++ tailWord_7653212) baseStart_7653212 baseEnd_7653212 := by
    simpa [prefixWord, tailWord_7653212, baseEnd_7653212] using wordTrace_append hprefix tailTrace_7653212
  have hstable : (prefixWord ++ tailWord_7653212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7653212).length < 2 ^ (prefixWord ++ tailWord_7653212).sum := by decide
  have hdescent : baseEnd_7653212 < baseStart_7653212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7653212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7653241 : List Nat := [1, 2, 1, 3, 2, 2, 1, 3, 2, 6]
def baseStart_7653241 : Nat := 118140960795 + 7653241 * 2 ^ 59
def prefixEnd_7653241 : Nat := 4983230072969 + 3 ^ 40 * 7653241 * 2
def baseEnd_7653241 : Nat := 1309930399232132131030297

theorem tailTrace_7653241 : CollatzResearch.WordTrace tailWord_7653241 prefixEnd_7653241 1309930399232132131030297 := by
  unfold tailWord_7653241
  simp only [CollatzResearch.WordTrace]
  refine ⟨279136631266622401346791577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186091087511081600897861051 279136631266622401346791577)
  ·
    refine ⟨209352473449966801010093683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279136631266622401346791577 209352473449966801010093683)
    ·
      refine ⟨314028710174950201515140525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209352473449966801010093683 314028710174950201515140525)
      ·
        refine ⟨117760766315606325568177697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314028710174950201515140525 117760766315606325568177697)
        ·
          refine ⟨88320574736704744176133273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117760766315606325568177697 88320574736704744176133273)
          ·
            refine ⟨66240431052528558132099955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88320574736704744176133273 66240431052528558132099955)
            ·
              refine ⟨99360646578792837198149933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66240431052528558132099955 99360646578792837198149933)
              ·
                refine ⟨37260242467047313949306225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99360646578792837198149933 37260242467047313949306225)
                ·
                  refine ⟨27945181850285485461979669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37260242467047313949306225 27945181850285485461979669)
                  ·
                    refine ⟨1309930399232132131030297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27945181850285485461979669 1309930399232132131030297)
                    ·
                      rfl

theorem cell23_7653241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 6].length) (baseStart_7653241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7653241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7653241 prefixEnd_7653241 := by exact prefixLift 7653241
  have htrace : WordTrace (prefixWord ++ tailWord_7653241) baseStart_7653241 baseEnd_7653241 := by
    simpa [prefixWord, tailWord_7653241, baseEnd_7653241] using wordTrace_append hprefix tailTrace_7653241
  have hstable : (prefixWord ++ tailWord_7653241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7653241).length < 2 ^ (prefixWord ++ tailWord_7653241).sum := by decide
  have hdescent : baseEnd_7653241 < baseStart_7653241 := by decide
  rcases family_descends (prefixWord ++ tailWord_7653241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7653265 : List Nat := [1, 2, 2, 1, 1, 1, 5, 2, 4, 2, 2]
def baseStart_7653265 : Nat := 118140960795 + 7653265 * 2 ^ 59
def prefixEnd_7653265 : Nat := 4983230072969 + 3 ^ 40 * 7653265 * 2
def baseEnd_7653265 : Nat := 3929803521232104299190781

theorem tailTrace_7653265 : CollatzResearch.WordTrace tailWord_7653265 prefixEnd_7653265 3929803521232104299190781 := by
  unfold tailWord_7653265
  simp only [CollatzResearch.WordTrace]
  refine ⟨279137506618535453445665249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186091671079023635630443499 279137506618535453445665249)
  ·
    refine ⟨209353129963901590084248937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279137506618535453445665249 209353129963901590084248937)
    ·
      refine ⟨157014847472926192563186703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209353129963901590084248937 157014847472926192563186703)
      ·
        refine ⟨235522271209389288844780055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157014847472926192563186703 235522271209389288844780055)
        ·
          refine ⟨353283406814083933267170083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235522271209389288844780055 353283406814083933267170083)
          ·
            refine ⟨529925110221125899900755125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353283406814083933267170083 529925110221125899900755125)
            ·
              refine ⟨49680479083230553115695793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 529925110221125899900755125 49680479083230553115695793)
              ·
                refine ⟨37260359312422914836771845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49680479083230553115695793 37260359312422914836771845)
                ·
                  refine ⟨6986317371079296531894721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37260359312422914836771845 6986317371079296531894721)
                  ·
                    refine ⟨5239738028309472398921041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6986317371079296531894721 5239738028309472398921041)
                    ·
                      refine ⟨3929803521232104299190781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5239738028309472398921041 3929803521232104299190781)
                      ·
                        rfl

theorem cell23_7653265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 4, 2, 2].length) (baseStart_7653265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7653265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7653265 prefixEnd_7653265 := by exact prefixLift 7653265
  have htrace : WordTrace (prefixWord ++ tailWord_7653265) baseStart_7653265 baseEnd_7653265 := by
    simpa [prefixWord, tailWord_7653265, baseEnd_7653265] using wordTrace_append hprefix tailTrace_7653265
  have hstable : (prefixWord ++ tailWord_7653265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7653265).length < 2 ^ (prefixWord ++ tailWord_7653265).sum := by decide
  have hdescent : baseEnd_7653265 < baseStart_7653265 := by decide
  rcases family_descends (prefixWord ++ tailWord_7653265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7653268 : List Nat := [2, 4, 2, 1, 1, 2, 1, 1, 1, 3, 5]
def baseStart_7653268 : Nat := 118140960795 + 7653268 * 2 ^ 59
def prefixEnd_7653268 : Nat := 4983230072969 + 3 ^ 40 * 7653268 * 2
def baseEnd_7653268 : Nat := 3929805061674067787453267

theorem tailTrace_7653268 : CollatzResearch.WordTrace tailWord_7653268 prefixEnd_7653268 3929805061674067787453267 := by
  unfold tailWord_7653268
  simp only [CollatzResearch.WordTrace]
  refine ⟨139568808018762292479012229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186091744025016389972016305 139568808018762292479012229)
  ·
    refine ⟨26169151503517929839814793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139568808018762292479012229 26169151503517929839814793)
    ·
      refine ⟨19626863627638447379861095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26169151503517929839814793 19626863627638447379861095)
      ·
        refine ⟨29440295441457671069791643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19626863627638447379861095 29440295441457671069791643)
        ·
          refine ⟨44160443162186506604687465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29440295441457671069791643 44160443162186506604687465)
          ·
            refine ⟨33120332371639879953515599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44160443162186506604687465 33120332371639879953515599)
            ·
              refine ⟨49680498557459819930273399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33120332371639879953515599 49680498557459819930273399)
              ·
                refine ⟨74520747836189729895410099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49680498557459819930273399 74520747836189729895410099)
                ·
                  refine ⟨111781121754284594843115149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74520747836189729895410099 111781121754284594843115149)
                  ·
                    refine ⟨41917920657856723066168181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 111781121754284594843115149 41917920657856723066168181)
                    ·
                      refine ⟨3929805061674067787453267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41917920657856723066168181 3929805061674067787453267)
                      ·
                        rfl

theorem cell23_7653268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_7653268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7653268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7653268 prefixEnd_7653268 := by exact prefixLift 7653268
  have htrace : WordTrace (prefixWord ++ tailWord_7653268) baseStart_7653268 baseEnd_7653268 := by
    simpa [prefixWord, tailWord_7653268, baseEnd_7653268] using wordTrace_append hprefix tailTrace_7653268
  have hstable : (prefixWord ++ tailWord_7653268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7653268).length < 2 ^ (prefixWord ++ tailWord_7653268).sum := by decide
  have hdescent : baseEnd_7653268 < baseStart_7653268 := by decide
  rcases family_descends (prefixWord ++ tailWord_7653268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7653298 : List Nat := [3, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3]
def baseStart_7653298 : Nat := 118140960795 + 7653298 * 2 ^ 59
def prefixEnd_7653298 : Nat := 4983230072969 + 3 ^ 40 * 7653298 * 2
def baseEnd_7653298 : Nat := 3929820466093702670078129

theorem tailTrace_7653298 : CollatzResearch.WordTrace tailWord_7653298 prefixEnd_7653298 3929820466093702670078129 := by
  unfold tailWord_7653298
  simp only [CollatzResearch.WordTrace]
  refine ⟨69784677556853975020404137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186092473484943933387744365 69784677556853975020404137)
  ·
    refine ⟨52338508167640481265303103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69784677556853975020404137 52338508167640481265303103)
    ·
      refine ⟨78507762251460721897954655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52338508167640481265303103 78507762251460721897954655)
      ·
        refine ⟨117761643377191082846931983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78507762251460721897954655 117761643377191082846931983)
        ·
          refine ⟨176642465065786624270397975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117761643377191082846931983 176642465065786624270397975)
          ·
            refine ⟨264963697598679936405596963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176642465065786624270397975 264963697598679936405596963)
            ·
              refine ⟨397445546398019904608395445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264963697598679936405596963 397445546398019904608395445)
              ·
                refine ⟨37260519974814366057037073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 397445546398019904608395445 37260519974814366057037073)
                ·
                  refine ⟨27945389981110774542777805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37260519974814366057037073 27945389981110774542777805)
                  ·
                    refine ⟨10479521242916540453541677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27945389981110774542777805 10479521242916540453541677)
                    ·
                      refine ⟨3929820466093702670078129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10479521242916540453541677 3929820466093702670078129)
                      ·
                        rfl

theorem cell23_7653298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3].length) (baseStart_7653298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7653298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7653298 prefixEnd_7653298 := by exact prefixLift 7653298
  have htrace : WordTrace (prefixWord ++ tailWord_7653298) baseStart_7653298 baseEnd_7653298 := by
    simpa [prefixWord, tailWord_7653298, baseEnd_7653298] using wordTrace_append hprefix tailTrace_7653298
  have hstable : (prefixWord ++ tailWord_7653298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7653298).length < 2 ^ (prefixWord ++ tailWord_7653298).sum := by decide
  have hdescent : baseEnd_7653298 < baseStart_7653298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7653298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7653311 : List Nat := [1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 7]
def baseStart_7653311 : Nat := 118140960795 + 7653311 * 2 ^ 59
def prefixEnd_7653311 : Nat := 4983230072969 + 3 ^ 40 * 7653311 * 2
def baseEnd_7653311 : Nat := 3929827141342211119215569

theorem tailTrace_7653311 : CollatzResearch.WordTrace tailWord_7653311 prefixEnd_7653311 3929827141342211119215569 := by
  unfold tailWord_7653311
  simp only [CollatzResearch.WordTrace]
  refine ⟨279139184376368803301839787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186092789584245868867893191 279139184376368803301839787)
  ·
    refine ⟨418708776564553204952759681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279139184376368803301839787 418708776564553204952759681)
    ·
      refine ⟨314031582423414903714569761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418708776564553204952759681 314031582423414903714569761)
      ·
        refine ⟨235523686817561177785927321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314031582423414903714569761 235523686817561177785927321)
        ·
          refine ⟨176642765113170883339445491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235523686817561177785927321 176642765113170883339445491)
          ·
            refine ⟨264964147669756325009168237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176642765113170883339445491 264964147669756325009168237)
            ·
              refine ⟨99361555376158621878438089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 264964147669756325009168237 99361555376158621878438089)
              ·
                refine ⟨74521166532118966408828567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99361555376158621878438089 74521166532118966408828567)
                ·
                  refine ⟨111781749798178449613242851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74521166532118966408828567 111781749798178449613242851)
                  ·
                    refine ⟨167672624697267674419864277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111781749798178449613242851 167672624697267674419864277)
                    ·
                      refine ⟨3929827141342211119215569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 167672624697267674419864277 3929827141342211119215569)
                      ·
                        rfl

theorem cell23_7653311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_7653311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7653311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7653311 prefixEnd_7653311 := by exact prefixLift 7653311
  have htrace : WordTrace (prefixWord ++ tailWord_7653311) baseStart_7653311 baseEnd_7653311 := by
    simpa [prefixWord, tailWord_7653311, baseEnd_7653311] using wordTrace_append hprefix tailTrace_7653311
  have hstable : (prefixWord ++ tailWord_7653311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7653311).length < 2 ^ (prefixWord ++ tailWord_7653311).sum := by decide
  have hdescent : baseEnd_7653311 < baseStart_7653311 := by decide
  rcases family_descends (prefixWord ++ tailWord_7653311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7653425 : List Nat := [1, 2, 2, 3, 1, 3, 1, 4, 1, 5]
def baseStart_7653425 : Nat := 118140960795 + 7653425 * 2 ^ 59
def prefixEnd_7653425 : Nat := 4983230072969 + 3 ^ 40 * 7653425 * 2
def baseEnd_7653425 : Nat := 1309961892712274557730015

theorem tailTrace_7653425 : CollatzResearch.WordTrace tailWord_7653425 prefixEnd_7653425 1309961892712274557730015 := by
  unfold tailWord_7653425
  simp only [CollatzResearch.WordTrace]
  refine ⟨279143342297955800771489729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186095561531970533847659819 279143342297955800771489729)
  ·
    refine ⟨209357506723466850578617297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279143342297955800771489729 209357506723466850578617297)
    ·
      refine ⟨157018130042600137933962973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209357506723466850578617297 157018130042600137933962973)
      ·
        refine ⟨58881798765975051725236115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157018130042600137933962973 58881798765975051725236115)
        ·
          refine ⟨88322698148962577587854173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58881798765975051725236115 88322698148962577587854173)
          ·
            refine ⟨33121011805860966595445315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88322698148962577587854173 33121011805860966595445315)
            ·
              refine ⟨49681517708791449893167973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33121011805860966595445315 49681517708791449893167973)
              ·
                refine ⟨9315284570398396854968995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49681517708791449893167973 9315284570398396854968995)
                ·
                  refine ⟨13972926855597595282453493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9315284570398396854968995 13972926855597595282453493)
                  ·
                    refine ⟨1309961892712274557730015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13972926855597595282453493 1309961892712274557730015)
                    ·
                      rfl

theorem cell23_7653425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 4, 1, 5].length) (baseStart_7653425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7653425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7653425 prefixEnd_7653425 := by exact prefixLift 7653425
  have htrace : WordTrace (prefixWord ++ tailWord_7653425) baseStart_7653425 baseEnd_7653425 := by
    simpa [prefixWord, tailWord_7653425, baseEnd_7653425] using wordTrace_append hprefix tailTrace_7653425
  have hstable : (prefixWord ++ tailWord_7653425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7653425).length < 2 ^ (prefixWord ++ tailWord_7653425).sum := by decide
  have hdescent : baseEnd_7653425 < baseStart_7653425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7653425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7653439 : List Nat := [1, 1, 2, 2, 3, 1, 5, 3, 1, 1, 3]
def baseStart_7653439 : Nat := 118140960795 + 7653439 * 2 ^ 59
def prefixEnd_7653439 : Nat := 4983230072969 + 3 ^ 40 * 7653439 * 2
def baseEnd_7653439 : Nat := 3929892866865986618414981

theorem tailTrace_7653439 : CollatzResearch.WordTrace tailWord_7653439 prefixEnd_7653439 3929892866865986618414981 := by
  unfold tailWord_7653439
  simp only [CollatzResearch.WordTrace]
  refine ⟨279143852919905081162499371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186095901946603387441666247 279143852919905081162499371)
  ·
    refine ⟨418715779379857621743749057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279143852919905081162499371 418715779379857621743749057)
    ·
      refine ⟨314036834534893216307811793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418715779379857621743749057 314036834534893216307811793)
      ·
        refine ⟨235527625901169912230858845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314036834534893216307811793 235527625901169912230858845)
        ·
          refine ⟨88322859712938717086572067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235527625901169912230858845 88322859712938717086572067)
          ·
            refine ⟨132484289569408075629858101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88322859712938717086572067 132484289569408075629858101)
            ·
              refine ⟨12420402147132007090299197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132484289569408075629858101 12420402147132007090299197)
              ·
                refine ⟨4657650805174502658862199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12420402147132007090299197 4657650805174502658862199)
                ·
                  refine ⟨6986476207761753988293299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4657650805174502658862199 6986476207761753988293299)
                  ·
                    refine ⟨10479714311642630982439949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6986476207761753988293299 10479714311642630982439949)
                    ·
                      refine ⟨3929892866865986618414981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10479714311642630982439949 3929892866865986618414981)
                      ·
                        rfl

theorem cell23_7653439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 3, 1, 1, 3].length) (baseStart_7653439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7653439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7653439 prefixEnd_7653439 := by exact prefixLift 7653439
  have htrace : WordTrace (prefixWord ++ tailWord_7653439) baseStart_7653439 baseEnd_7653439 := by
    simpa [prefixWord, tailWord_7653439, baseEnd_7653439] using wordTrace_append hprefix tailTrace_7653439
  have hstable : (prefixWord ++ tailWord_7653439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7653439).length < 2 ^ (prefixWord ++ tailWord_7653439).sum := by decide
  have hdescent : baseEnd_7653439 < baseStart_7653439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7653439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7653465 : List Nat := [1, 2, 1, 2, 2, 1, 4, 2, 3, 2, 3]
def baseStart_7653465 : Nat := 118140960795 + 7653465 * 2 ^ 59
def prefixEnd_7653465 : Nat := 4983230072969 + 3 ^ 40 * 7653465 * 2
def baseEnd_7653465 : Nat := 3929906217363003516689861

theorem tailTrace_7653465 : CollatzResearch.WordTrace tailWord_7653465 prefixEnd_7653465 3929906217363003516689861 := by
  unfold tailWord_7653465
  simp only [CollatzResearch.WordTrace]
  refine ⟨279144801217810887602945849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186096534145207258401963899 279144801217810887602945849)
  ·
    refine ⟨209358600913358165702209387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279144801217810887602945849 209358600913358165702209387)
    ·
      refine ⟨314037901370037248553314081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209358600913358165702209387 314037901370037248553314081)
      ·
        refine ⟨235528426027527936414985561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314037901370037248553314081 235528426027527936414985561)
        ·
          refine ⟨176646319520645952311239171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235528426027527936414985561 176646319520645952311239171)
          ·
            refine ⟨264969479280968928466858757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176646319520645952311239171 264969479280968928466858757)
            ·
              refine ⟨49681777365181674087536017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 264969479280968928466858757 49681777365181674087536017)
              ·
                refine ⟨37261333023886255565652013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49681777365181674087536017 37261333023886255565652013)
                ·
                  refine ⟨13972999883957345837119505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37261333023886255565652013 13972999883957345837119505)
                  ·
                    refine ⟨10479749912968009377839629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13972999883957345837119505 10479749912968009377839629)
                    ·
                      refine ⟨3929906217363003516689861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10479749912968009377839629 3929906217363003516689861)
                      ·
                        rfl

theorem cell23_7653465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 3, 2, 3].length) (baseStart_7653465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7653465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7653465 prefixEnd_7653465 := by exact prefixLift 7653465
  have htrace : WordTrace (prefixWord ++ tailWord_7653465) baseStart_7653465 baseEnd_7653465 := by
    simpa [prefixWord, tailWord_7653465, baseEnd_7653465] using wordTrace_append hprefix tailTrace_7653465
  have hstable : (prefixWord ++ tailWord_7653465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7653465).length < 2 ^ (prefixWord ++ tailWord_7653465).sum := by decide
  have hdescent : baseEnd_7653465 < baseStart_7653465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7653465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7653472 : List Nat := [2, 1, 1, 3, 2, 4, 1, 3, 2, 4]
def baseStart_7653472 : Nat := 118140960795 + 7653472 * 2 ^ 59
def prefixEnd_7653472 : Nat := 4983230072969 + 3 ^ 40 * 7653472 * 2
def baseEnd_7653472 : Nat := 1309969937242528329767443

theorem tailTrace_7653472 : CollatzResearch.WordTrace tailWord_7653472 prefixEnd_7653472 1309969937242528329767443 := by
  unfold tailWord_7653472
  simp only [CollatzResearch.WordTrace]
  refine ⟨139572528264392763899225335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186096704352523685198967113 139572528264392763899225335)
  ·
    refine ⟨209358792396589145848838003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139572528264392763899225335 209358792396589145848838003)
    ·
      refine ⟨314038188594883718773257005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209358792396589145848838003 314038188594883718773257005)
      ·
        refine ⟨117764320723081394539971377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314038188594883718773257005 117764320723081394539971377)
        ·
          refine ⟨88323240542311045904978533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117764320723081394539971377 88323240542311045904978533)
          ·
            refine ⟨16560607601683321107183475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88323240542311045904978533 16560607601683321107183475)
            ·
              refine ⟨24840911402524981660775213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16560607601683321107183475 24840911402524981660775213)
              ·
                refine ⟨9315341775946868122790705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24840911402524981660775213 9315341775946868122790705)
                ·
                  refine ⟨6986506331960151092093029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9315341775946868122790705 6986506331960151092093029)
                  ·
                    refine ⟨1309969937242528329767443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6986506331960151092093029 1309969937242528329767443)
                    ·
                      rfl

theorem cell23_7653472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 3, 2, 4].length) (baseStart_7653472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7653472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7653472 prefixEnd_7653472 := by exact prefixLift 7653472
  have htrace : WordTrace (prefixWord ++ tailWord_7653472) baseStart_7653472 baseEnd_7653472 := by
    simpa [prefixWord, tailWord_7653472, baseEnd_7653472] using wordTrace_append hprefix tailTrace_7653472
  have hstable : (prefixWord ++ tailWord_7653472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7653472).length < 2 ^ (prefixWord ++ tailWord_7653472).sum := by decide
  have hdescent : baseEnd_7653472 < baseStart_7653472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7653472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7653495 : List Nat := [1, 1, 3, 1, 1, 5, 1, 1, 3, 3, 3]
def baseStart_7653495 : Nat := 118140960795 + 7653495 * 2 ^ 59
def prefixEnd_7653495 : Nat := 4983230072969 + 3 ^ 40 * 7653495 * 2
def baseEnd_7653495 : Nat := 3929921621782638399314723

theorem tailTrace_7653495 : CollatzResearch.WordTrace tailWord_7653495 prefixEnd_7653495 3929921621782638399314723 := by
  unfold tailWord_7653495
  simp only [CollatzResearch.WordTrace]
  refine ⟨279145895407702202726537939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186097263605134801817691959 279145895407702202726537939)
  ·
    refine ⟨418718843111553304089806909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279145895407702202726537939 418718843111553304089806909)
    ·
      refine ⟨157019566166832489033677591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 418718843111553304089806909 157019566166832489033677591)
      ·
        refine ⟨235529349250248733550516387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157019566166832489033677591 235529349250248733550516387)
        ·
          refine ⟨353294023875373100325774581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235529349250248733550516387 353294023875373100325774581)
          ·
            refine ⟨33121314738316228155541367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 353294023875373100325774581 33121314738316228155541367)
            ·
              refine ⟨49681972107474342233312051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33121314738316228155541367 49681972107474342233312051)
              ·
                refine ⟨74522958161211513349968077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49681972107474342233312051 74522958161211513349968077)
                ·
                  refine ⟨27946109310454317506238029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74522958161211513349968077 27946109310454317506238029)
                  ·
                    refine ⟨10479790991420369064839261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27946109310454317506238029 10479790991420369064839261)
                    ·
                      refine ⟨3929921621782638399314723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10479790991420369064839261 3929921621782638399314723)
                      ·
                        rfl

theorem cell23_7653495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 3, 3].length) (baseStart_7653495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7653495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7653495 prefixEnd_7653495 := by exact prefixLift 7653495
  have htrace : WordTrace (prefixWord ++ tailWord_7653495) baseStart_7653495 baseEnd_7653495 := by
    simpa [prefixWord, tailWord_7653495, baseEnd_7653495] using wordTrace_append hprefix tailTrace_7653495
  have hstable : (prefixWord ++ tailWord_7653495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7653495).length < 2 ^ (prefixWord ++ tailWord_7653495).sum := by decide
  have hdescent : baseEnd_7653495 < baseStart_7653495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7653495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7653498 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 6, 7]
def baseStart_7653498 : Nat := 118140960795 + 7653498 * 2 ^ 59
def prefixEnd_7653498 : Nat := 4983230072969 + 3 ^ 40 * 7653498 * 2
def baseEnd_7653498 : Nat := 1309974387408200629192403

theorem tailTrace_7653498 : CollatzResearch.WordTrace tailWord_7653498 prefixEnd_7653498 1309974387408200629192403 := by
  unfold tailWord_7653498
  simp only [CollatzResearch.WordTrace]
  refine ⟨69786501206672833559724287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186097336551127556159264765 69786501206672833559724287)
  ·
    refine ⟨104679751810009250339586431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69786501206672833559724287 104679751810009250339586431)
    ·
      refine ⟨157019627715013875509379647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104679751810009250339586431 157019627715013875509379647)
      ·
        refine ⟨235529441572520813264069471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157019627715013875509379647 235529441572520813264069471)
        ·
          refine ⟨353294162358781219896104207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235529441572520813264069471 353294162358781219896104207)
          ·
            refine ⟨529941243538171829844156311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353294162358781219896104207 529941243538171829844156311)
            ·
              refine ⟨794911865307257744766234467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 529941243538171829844156311 794911865307257744766234467)
              ·
                refine ⟨1192367797960886617149351701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 794911865307257744766234467 1192367797960886617149351701)
                ·
                  refine ⟨55892240529416560178875861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1192367797960886617149351701 55892240529416560178875861)
                  ·
                    refine ⟨1309974387408200629192403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55892240529416560178875861 1309974387408200629192403)
                    ·
                      rfl

theorem cell23_7653498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 6, 7].length) (baseStart_7653498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7653498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7653498 prefixEnd_7653498 := by exact prefixLift 7653498
  have htrace : WordTrace (prefixWord ++ tailWord_7653498) baseStart_7653498 baseEnd_7653498 := by
    simpa [prefixWord, tailWord_7653498, baseEnd_7653498] using wordTrace_append hprefix tailTrace_7653498
  have hstable : (prefixWord ++ tailWord_7653498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7653498).length < 2 ^ (prefixWord ++ tailWord_7653498).sum := by decide
  have hdescent : baseEnd_7653498 < baseStart_7653498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7653498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7653550 : List Nat := [4, 1, 4, 2, 1, 2, 2, 1, 1, 2, 3]
def baseStart_7653550 : Nat := 118140960795 + 7653550 * 2 ^ 59
def prefixEnd_7653550 : Nat := 4983230072969 + 3 ^ 40 * 7653550 * 2
def baseEnd_7653550 : Nat := 3929949863218635684126971

theorem tailTrace_7653550 : CollatzResearch.WordTrace tailWord_7653550 prefixEnd_7653550 3929949863218635684126971 := by
  unfold tailWord_7653550
  simp only [CollatzResearch.WordTrace]
  refine ⟨34893487677812868389973763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186098600948335298079860069 34893487677812868389973763)
  ·
    refine ⟨52340231516719302584960645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34893487677812868389973763 52340231516719302584960645)
    ·
      refine ⟨9813793409384869234680121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52340231516719302584960645 9813793409384869234680121)
      ·
        refine ⟨7360345057038651926010091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9813793409384869234680121 7360345057038651926010091)
        ·
          refine ⟨11040517585557977889015137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7360345057038651926010091 11040517585557977889015137)
          ·
            refine ⟨8280388189168483416761353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11040517585557977889015137 8280388189168483416761353)
            ·
              refine ⟨6210291141876362562571015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8280388189168483416761353 6210291141876362562571015)
              ·
                refine ⟨9315436712814543843856523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6210291141876362562571015 9315436712814543843856523)
                ·
                  refine ⟨13973155069221815765784785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9315436712814543843856523 13973155069221815765784785)
                  ·
                    refine ⟨10479866301916361824338589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13973155069221815765784785 10479866301916361824338589)
                    ·
                      refine ⟨3929949863218635684126971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10479866301916361824338589 3929949863218635684126971)
                      ·
                        rfl

theorem cell23_7653550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_7653550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7653550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7653550 prefixEnd_7653550 := by exact prefixLift 7653550
  have htrace : WordTrace (prefixWord ++ tailWord_7653550) baseStart_7653550 baseEnd_7653550 := by
    simpa [prefixWord, tailWord_7653550, baseEnd_7653550] using wordTrace_append hprefix tailTrace_7653550
  have hstable : (prefixWord ++ tailWord_7653550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7653550).length < 2 ^ (prefixWord ++ tailWord_7653550).sum := by decide
  have hdescent : baseEnd_7653550 < baseStart_7653550 := by decide
  rcases family_descends (prefixWord ++ tailWord_7653550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7653582 : List Nat := [4, 1, 1, 1, 4, 1, 2, 1, 2, 2, 4]
def baseStart_7653582 : Nat := 118140960795 + 7653582 * 2 ^ 59
def prefixEnd_7653582 : Nat := 4983230072969 + 3 ^ 40 * 7653582 * 2
def baseEnd_7653582 : Nat := 3929966294599579558926823

theorem tailTrace_7653582 : CollatzResearch.WordTrace tailWord_7653582 prefixEnd_7653582 3929966294599579558926823 := by
  unfold tailWord_7653582
  simp only [CollatzResearch.WordTrace]
  refine ⟨34893633569798377073119375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186099379038924677723303333 34893633569798377073119375)
  ·
    refine ⟨52340450354697565609679063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34893633569798377073119375 52340450354697565609679063)
    ·
      refine ⟨78510675532046348414518595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52340450354697565609679063 78510675532046348414518595)
      ·
        refine ⟨117766013298069522621777893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78510675532046348414518595 117766013298069522621777893)
        ·
          refine ⟨22081127493388035491583355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117766013298069522621777893 22081127493388035491583355)
          ·
            refine ⟨33121691240082053237375033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22081127493388035491583355 33121691240082053237375033)
            ·
              refine ⟨24841268430061539928031275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33121691240082053237375033 24841268430061539928031275)
              ·
                refine ⟨37261902645092309892046913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24841268430061539928031275 37261902645092309892046913)
                ·
                  refine ⟨27946426983819232419035185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37261902645092309892046913 27946426983819232419035185)
                  ·
                    refine ⟨20959820237864424314276389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27946426983819232419035185 20959820237864424314276389)
                    ·
                      refine ⟨3929966294599579558926823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20959820237864424314276389 3929966294599579558926823)
                      ·
                        rfl

theorem cell23_7653582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_7653582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7653582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7653582 prefixEnd_7653582 := by exact prefixLift 7653582
  have htrace : WordTrace (prefixWord ++ tailWord_7653582) baseStart_7653582 baseEnd_7653582 := by
    simpa [prefixWord, tailWord_7653582, baseEnd_7653582] using wordTrace_append hprefix tailTrace_7653582
  have hstable : (prefixWord ++ tailWord_7653582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7653582).length < 2 ^ (prefixWord ++ tailWord_7653582).sum := by decide
  have hdescent : baseEnd_7653582 < baseStart_7653582 := by decide
  rcases family_descends (prefixWord ++ tailWord_7653582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7653586 : List Nat := [3, 2, 2, 2, 1, 4, 1, 1, 1, 4, 2]
def baseStart_7653586 : Nat := 118140960795 + 7653586 * 2 ^ 59
def prefixEnd_7653586 : Nat := 4983230072969 + 3 ^ 40 * 7653586 * 2
def baseEnd_7653586 : Nat := 3929968348522197543276805

theorem tailTrace_7653586 : CollatzResearch.WordTrace tailWord_7653586 prefixEnd_7653586 3929968348522197543276805 := by
  unfold tailWord_7653586
  simp only [CollatzResearch.WordTrace]
  refine ⟨69787303612593131317025153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186099476300248350178733741 69787303612593131317025153)
  ·
    refine ⟨52340477709444848487768865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69787303612593131317025153 52340477709444848487768865)
    ·
      refine ⟨39255358282083636365826649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52340477709444848487768865 39255358282083636365826649)
      ·
        refine ⟨29441518711562727274369987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39255358282083636365826649 29441518711562727274369987)
        ·
          refine ⟨44162278067344090911554981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29441518711562727274369987 44162278067344090911554981)
          ·
            refine ⟨8280427137627017045916559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44162278067344090911554981 8280427137627017045916559)
            ·
              refine ⟨12420640706440525568874839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8280427137627017045916559 12420640706440525568874839)
              ·
                refine ⟨18630961059660788353312259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12420640706440525568874839 18630961059660788353312259)
                ·
                  refine ⟨27946441589491182529968389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18630961059660788353312259 27946441589491182529968389)
                  ·
                    refine ⟨5239957798029596724369073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27946441589491182529968389 5239957798029596724369073)
                    ·
                      refine ⟨3929968348522197543276805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5239957798029596724369073 3929968348522197543276805)
                      ·
                        rfl

theorem cell23_7653586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_7653586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7653586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7653586 prefixEnd_7653586 := by exact prefixLift 7653586
  have htrace : WordTrace (prefixWord ++ tailWord_7653586) baseStart_7653586 baseEnd_7653586 := by
    simpa [prefixWord, tailWord_7653586, baseEnd_7653586] using wordTrace_append hprefix tailTrace_7653586
  have hstable : (prefixWord ++ tailWord_7653586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7653586).length < 2 ^ (prefixWord ++ tailWord_7653586).sum := by decide
  have hdescent : baseEnd_7653586 < baseStart_7653586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7653586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7653622 : List Nat := [5, 1, 1, 1, 1, 1, 3, 1, 4, 5]
def baseStart_7653622 : Nat := 118140960795 + 7653622 * 2 ^ 59
def prefixEnd_7653622 : Nat := 4983230072969 + 3 ^ 40 * 7653622 * 2
def baseEnd_7653622 : Nat := 1309995611275253134142213

theorem tailTrace_7653622 : CollatzResearch.WordTrace tailWord_7653622 prefixEnd_7653622 1309995611275253134142213 := by
  unfold tailWord_7653622
  simp only [CollatzResearch.WordTrace]
  refine ⟨17446907967390131463525695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186100351652161402277607413 17446907967390131463525695)
  ·
    refine ⟨26170361951085197195288543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17446907967390131463525695 26170361951085197195288543)
    ·
      refine ⟨39255542926627795792932815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26170361951085197195288543 39255542926627795792932815)
      ·
        refine ⟨58883314389941693689399223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39255542926627795792932815 58883314389941693689399223)
        ·
          refine ⟨88324971584912540534098835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58883314389941693689399223 88324971584912540534098835)
          ·
            refine ⟨132487457377368810801148253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88324971584912540534098835 132487457377368810801148253)
            ·
              refine ⟨49682796516513304050430595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132487457377368810801148253 49682796516513304050430595)
              ·
                refine ⟨74524194774769956075645893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49682796516513304050430595 74524194774769956075645893)
                ·
                  refine ⟨13973286520269366764183605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74524194774769956075645893 13973286520269366764183605)
                  ·
                    refine ⟨1309995611275253134142213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13973286520269366764183605 1309995611275253134142213)
                    ·
                      rfl

theorem cell23_7653622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_7653622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7653622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7653622 prefixEnd_7653622 := by exact prefixLift 7653622
  have htrace : WordTrace (prefixWord ++ tailWord_7653622) baseStart_7653622 baseEnd_7653622 := by
    simpa [prefixWord, tailWord_7653622, baseEnd_7653622] using wordTrace_append hprefix tailTrace_7653622
  have hstable : (prefixWord ++ tailWord_7653622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7653622).length < 2 ^ (prefixWord ++ tailWord_7653622).sum := by decide
  have hdescent : baseEnd_7653622 < baseStart_7653622 := by decide
  rcases family_descends (prefixWord ++ tailWord_7653622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7653625 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 3, 3, 4]
def baseStart_7653625 : Nat := 118140960795 + 7653625 * 2 ^ 59
def prefixEnd_7653625 : Nat := 4983230072969 + 3 ^ 40 * 7653625 * 2
def baseEnd_7653625 : Nat := 3929988374267722890689125

theorem tailTrace_7653625 : CollatzResearch.WordTrace tailWord_7653625 prefixEnd_7653625 3929988374267722890689125 := by
  unfold tailWord_7653625
  simp only [CollatzResearch.WordTrace]
  refine ⟨279150636897231234928770329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186100424598154156619180219 279150636897231234928770329)
  ·
    refine ⟨209362977672923426196577747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279150636897231234928770329 209362977672923426196577747)
    ·
      refine ⟨314044466509385139294866621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209362977672923426196577747 314044466509385139294866621)
      ·
        refine ⟨117766674941019427235574983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314044466509385139294866621 117766674941019427235574983)
        ·
          refine ⟨176650012411529140853362475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117766674941019427235574983 176650012411529140853362475)
          ·
            refine ⟨264975018617293711280043713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176650012411529140853362475 264975018617293711280043713)
            ·
              refine ⟨198731263962970283460032785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264975018617293711280043713 198731263962970283460032785)
              ·
                refine ⟨149048447972227712595024589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198731263962970283460032785 149048447972227712595024589)
                ·
                  refine ⟨55893167989585392223134221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149048447972227712595024589 55893167989585392223134221)
                  ·
                    refine ⟨20959937996094522083675333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55893167989585392223134221 20959937996094522083675333)
                    ·
                      refine ⟨3929988374267722890689125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20959937996094522083675333 3929988374267722890689125)
                      ·
                        rfl

theorem cell23_7653625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_7653625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7653625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7653625 prefixEnd_7653625 := by exact prefixLift 7653625
  have htrace : WordTrace (prefixWord ++ tailWord_7653625) baseStart_7653625 baseEnd_7653625 := by
    simpa [prefixWord, tailWord_7653625, baseEnd_7653625] using wordTrace_append hprefix tailTrace_7653625
  have hstable : (prefixWord ++ tailWord_7653625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7653625).length < 2 ^ (prefixWord ++ tailWord_7653625).sum := by decide
  have hdescent : baseEnd_7653625 < baseStart_7653625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7653625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7653665 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 10]
def baseStart_7653665 : Nat := 118140960795 + 7653665 * 2 ^ 59
def prefixEnd_7653665 : Nat := 4983230072969 + 3 ^ 40 * 7653665 * 2
def baseEnd_7653665 : Nat := 436667657054878081576549

theorem tailTrace_7653665 : CollatzResearch.WordTrace tailWord_7653665 prefixEnd_7653665 436667657054878081576549 := by
  unfold tailWord_7653665
  simp only [CollatzResearch.WordTrace]
  refine ⟨279152095817086321760226449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186101397211390881173484299 279152095817086321760226449)
  ·
    refine ⟨209364071862814741320169837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279152095817086321760226449 209364071862814741320169837)
    ·
      refine ⟨78511526948555527995063689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209364071862814741320169837 78511526948555527995063689)
      ·
        refine ⟨58883645211416645996297767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78511526948555527995063689 58883645211416645996297767)
        ·
          refine ⟨88325467817124968994446651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58883645211416645996297767 88325467817124968994446651)
          ·
            refine ⟨132488201725687453491669977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88325467817124968994446651 132488201725687453491669977)
            ·
              refine ⟨99366151294265590118752483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132488201725687453491669977 99366151294265590118752483)
              ·
                refine ⟨149049226941398385178128725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99366151294265590118752483 149049226941398385178128725)
                ·
                  refine ⟨436667657054878081576549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 149049226941398385178128725 436667657054878081576549)
                  ·
                    rfl

theorem cell23_7653665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 10].length) (baseStart_7653665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7653665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7653665 prefixEnd_7653665 := by exact prefixLift 7653665
  have htrace : WordTrace (prefixWord ++ tailWord_7653665) baseStart_7653665 baseEnd_7653665 := by
    simpa [prefixWord, tailWord_7653665, baseEnd_7653665] using wordTrace_append hprefix tailTrace_7653665
  have hstable : (prefixWord ++ tailWord_7653665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7653665).length < 2 ^ (prefixWord ++ tailWord_7653665).sum := by decide
  have hdescent : baseEnd_7653665 < baseStart_7653665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7653665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7653705 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 1, 3, 7]
def baseStart_7653705 : Nat := 118140960795 + 7653705 * 2 ^ 59
def prefixEnd_7653705 : Nat := 4983230072969 + 3 ^ 40 * 7653705 * 2
def baseEnd_7653705 : Nat := 3930029452720082577688757

theorem tailTrace_7653705 : CollatzResearch.WordTrace tailWord_7653705 prefixEnd_7653705 3930029452720082577688757 := by
  unfold tailWord_7653705
  simp only [CollatzResearch.WordTrace]
  refine ⟨279153554736941408591682569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186102369824627605727788379 279153554736941408591682569)
  ·
    refine ⟨209365166052706056443761927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279153554736941408591682569 209365166052706056443761927)
    ·
      refine ⟨314047749079059084665642891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209365166052706056443761927 314047749079059084665642891)
      ·
        refine ⟨471071623618588626998464337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314047749079059084665642891 471071623618588626998464337)
        ·
          refine ⟨353303717713941470248848253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 471071623618588626998464337 353303717713941470248848253)
          ·
            refine ⟨132488894142728051343318095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 353303717713941470248848253 132488894142728051343318095)
            ·
              refine ⟨198733341214092077014977143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132488894142728051343318095 198733341214092077014977143)
              ·
                refine ⟨298100011821138115522465715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198733341214092077014977143 298100011821138115522465715)
                ·
                  refine ⟨447150017731707173283698573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 298100011821138115522465715 447150017731707173283698573)
                  ·
                    refine ⟨167681256649390189981386965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 447150017731707173283698573 167681256649390189981386965)
                    ·
                      refine ⟨3930029452720082577688757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 167681256649390189981386965 3930029452720082577688757)
                      ·
                        rfl

theorem cell23_7653705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 3, 7].length) (baseStart_7653705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7653705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7653705 prefixEnd_7653705 := by exact prefixLift 7653705
  have htrace : WordTrace (prefixWord ++ tailWord_7653705) baseStart_7653705 baseEnd_7653705 := by
    simpa [prefixWord, tailWord_7653705, baseEnd_7653705] using wordTrace_append hprefix tailTrace_7653705
  have hstable : (prefixWord ++ tailWord_7653705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7653705).length < 2 ^ (prefixWord ++ tailWord_7653705).sum := by decide
  have hdescent : baseEnd_7653705 < baseStart_7653705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7653705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7653712 : List Nat := [2, 1, 1, 1, 1, 6, 2, 1, 3, 5]
def baseStart_7653712 : Nat := 118140960795 + 7653712 * 2 ^ 59
def prefixEnd_7653712 : Nat := 4983230072969 + 3 ^ 40 * 7653712 * 2
def baseEnd_7653712 : Nat := 1310011015694888016767075

theorem tailTrace_7653712 : CollatzResearch.WordTrace tailWord_7653712 prefixEnd_7653712 1310011015694888016767075 := by
  unfold tailWord_7653712
  simp only [CollatzResearch.WordTrace]
  refine ⟨139576905023958024393593695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186102540031944032524791593 139576905023958024393593695)
  ·
    refine ⟨209365357535937036590390543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139576905023958024393593695 209365357535937036590390543)
    ·
      refine ⟨314048036303905554885585815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209365357535937036590390543 314048036303905554885585815)
      ·
        refine ⟨471072054455858332328378723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314048036303905554885585815 471072054455858332328378723)
        ·
          refine ⟨706608081683787498492568085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471072054455858332328378723 706608081683787498492568085)
          ·
            refine ⟨33122253828927538991839129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 706608081683787498492568085 33122253828927538991839129)
            ·
              refine ⟨24841690371695654243879347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33122253828927538991839129 24841690371695654243879347)
              ·
                refine ⟨37262535557543481365819021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24841690371695654243879347 37262535557543481365819021)
                ·
                  refine ⟨13973450834078805512182133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37262535557543481365819021 13973450834078805512182133)
                  ·
                    refine ⟨1310011015694888016767075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13973450834078805512182133 1310011015694888016767075)
                    ·
                      rfl

theorem cell23_7653712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 3, 5].length) (baseStart_7653712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7653712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7653712 prefixEnd_7653712 := by exact prefixLift 7653712
  have htrace : WordTrace (prefixWord ++ tailWord_7653712) baseStart_7653712 baseEnd_7653712 := by
    simpa [prefixWord, tailWord_7653712, baseEnd_7653712] using wordTrace_append hprefix tailTrace_7653712
  have hstable : (prefixWord ++ tailWord_7653712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7653712).length < 2 ^ (prefixWord ++ tailWord_7653712).sum := by decide
  have hdescent : baseEnd_7653712 < baseStart_7653712 := by decide
  rcases family_descends (prefixWord ++ tailWord_7653712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7653719 : List Nat := [1, 1, 3, 2, 3, 1, 3, 1, 1, 5, 2]
def baseStart_7653719 : Nat := 118140960795 + 7653719 * 2 ^ 59
def prefixEnd_7653719 : Nat := 4983230072969 + 3 ^ 40 * 7653719 * 2
def baseEnd_7653719 : Nat := 3930036641449245522913693

theorem tailTrace_7653719 : CollatzResearch.WordTrace tailWord_7653719 prefixEnd_7653719 3930036641449245522913693 := by
  unfold tailWord_7653719
  simp only [CollatzResearch.WordTrace]
  refine ⟨279154065358890688982692211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186102710239260459321794807 279154065358890688982692211)
  ·
    refine ⟨418731098038336033474038317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279154065358890688982692211 418731098038336033474038317)
    ·
      refine ⟨157024161764376012552764369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 418731098038336033474038317 157024161764376012552764369)
      ·
        refine ⟨117768121323282009414573277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157024161764376012552764369 117768121323282009414573277)
        ·
          refine ⟨44163045496230753530464979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117768121323282009414573277 44163045496230753530464979)
          ·
            refine ⟨66244568244346130295697469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44163045496230753530464979 66244568244346130295697469)
            ·
              refine ⟨24841713091629798860886551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66244568244346130295697469 24841713091629798860886551)
              ·
                refine ⟨37262569637444698291329827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24841713091629798860886551 37262569637444698291329827)
                ·
                  refine ⟨55893854456167047436994741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37262569637444698291329827 55893854456167047436994741)
                  ·
                    refine ⟨5240048855265660697218257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55893854456167047436994741 5240048855265660697218257)
                    ·
                      refine ⟨3930036641449245522913693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5240048855265660697218257 3930036641449245522913693)
                      ·
                        rfl

theorem cell23_7653719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 5, 2].length) (baseStart_7653719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7653719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7653719 prefixEnd_7653719 := by exact prefixLift 7653719
  have htrace : WordTrace (prefixWord ++ tailWord_7653719) baseStart_7653719 baseEnd_7653719 := by
    simpa [prefixWord, tailWord_7653719, baseEnd_7653719] using wordTrace_append hprefix tailTrace_7653719
  have hstable : (prefixWord ++ tailWord_7653719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7653719).length < 2 ^ (prefixWord ++ tailWord_7653719).sum := by decide
  have hdescent : baseEnd_7653719 < baseStart_7653719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7653719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7653772 : List Nat := [2, 2, 1, 2, 1, 5, 1, 9]
def baseStart_7653772 : Nat := 118140960795 + 7653772 * 2 ^ 59
def prefixEnd_7653772 : Nat := 4983230072969 + 3 ^ 40 * 7653772 * 2
def baseEnd_7653772 : Nat := 145557920589775326501887

theorem tailTrace_7653772 : CollatzResearch.WordTrace tailWord_7653772 prefixEnd_7653772 145557920589775326501887 := by
  unfold tailWord_7653772
  simp only [CollatzResearch.WordTrace]
  refine ⟨139577999213849339517185785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186103998951799119356247713 139577999213849339517185785)
  ·
    refine ⟨104683499410387004637889339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139577999213849339517185785 104683499410387004637889339)
    ·
      refine ⟨157025249115580506956834009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104683499410387004637889339 157025249115580506956834009)
      ·
        refine ⟨117768936836685380217625507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157025249115580506956834009 117768936836685380217625507)
        ·
          refine ⟨176653405255028070326438261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117768936836685380217625507 176653405255028070326438261)
          ·
            refine ⟨16561256742658881593103587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 176653405255028070326438261 16561256742658881593103587)
            ·
              refine ⟨24841885113988322389655381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16561256742658881593103587 24841885113988322389655381)
              ·
                refine ⟨145557920589775326501887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24841885113988322389655381 145557920589775326501887)
                ·
                  rfl

theorem cell23_7653772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 9].length) (baseStart_7653772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7653772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7653772 prefixEnd_7653772 := by exact prefixLift 7653772
  have htrace : WordTrace (prefixWord ++ tailWord_7653772) baseStart_7653772 baseEnd_7653772 := by
    simpa [prefixWord, tailWord_7653772, baseEnd_7653772] using wordTrace_append hprefix tailTrace_7653772
  have hstable : (prefixWord ++ tailWord_7653772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7653772).length < 2 ^ (prefixWord ++ tailWord_7653772).sum := by decide
  have hdescent : baseEnd_7653772 < baseStart_7653772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7653772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7653786 : List Nat := [3, 1, 1, 4, 1, 2, 2, 3, 1, 2, 3]
def baseStart_7653786 : Nat := 118140960795 + 7653786 * 2 ^ 59
def prefixEnd_7653786 : Nat := 4983230072969 + 3 ^ 40 * 7653786 * 2
def baseEnd_7653786 : Nat := 3930071044653096760775885

theorem tailTrace_7653786 : CollatzResearch.WordTrace tailWord_7653786 prefixEnd_7653786 3930071044653096760775885 := by
  unfold tailWord_7653786
  simp only [CollatzResearch.WordTrace]
  refine ⟨69789127262411989856345303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186104339366431972950254141 69789127262411989856345303)
  ·
    refine ⟨104683690893617984784517955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69789127262411989856345303 104683690893617984784517955)
    ·
      refine ⟨157025536340426977176776933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104683690893617984784517955 157025536340426977176776933)
      ·
        refine ⟨29442288063830058220645675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157025536340426977176776933 29442288063830058220645675)
        ·
          refine ⟨44163432095745087330968513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29442288063830058220645675 44163432095745087330968513)
          ·
            refine ⟨33122574071808815498226385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44163432095745087330968513 33122574071808815498226385)
            ·
              refine ⟨24841930553856611623669789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33122574071808815498226385 24841930553856611623669789)
              ·
                refine ⟨9315723957696229358876171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24841930553856611623669789 9315723957696229358876171)
                ·
                  refine ⟨13973585936544344038314257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9315723957696229358876171 13973585936544344038314257)
                  ·
                    refine ⟨10480189452408258028735693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13973585936544344038314257 10480189452408258028735693)
                    ·
                      refine ⟨3930071044653096760775885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10480189452408258028735693 3930071044653096760775885)
                      ·
                        rfl

theorem cell23_7653786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_7653786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7653786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7653786 prefixEnd_7653786 := by exact prefixLift 7653786
  have htrace : WordTrace (prefixWord ++ tailWord_7653786) baseStart_7653786 baseEnd_7653786 := by
    simpa [prefixWord, tailWord_7653786, baseEnd_7653786] using wordTrace_append hprefix tailTrace_7653786
  have hstable : (prefixWord ++ tailWord_7653786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7653786).length < 2 ^ (prefixWord ++ tailWord_7653786).sum := by decide
  have hdescent : baseEnd_7653786 < baseStart_7653786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7653786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7653789 : List Nat := [1, 4, 2, 1, 4, 2, 9]
def baseStart_7653789 : Nat := 118140960795 + 7653789 * 2 ^ 59
def prefixEnd_7653789 : Nat := 4983230072969 + 3 ^ 40 * 7653789 * 2
def baseEnd_7653789 : Nat := 48519414630803212951091

theorem tailTrace_7653789 : CollatzResearch.WordTrace tailWord_7653789 prefixEnd_7653789 48519414630803212951091 := by
  unfold tailWord_7653789
  simp only [CollatzResearch.WordTrace]
  refine ⟨279156618468637090937740421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186104412312424727291826947 279156618468637090937740421)
  ·
    refine ⟨52341865962869454550826329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 279156618468637090937740421 52341865962869454550826329)
    ·
      refine ⟨39256399472152090913119747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52341865962869454550826329 39256399472152090913119747)
      ·
        refine ⟨58884599208228136369679621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39256399472152090913119747 58884599208228136369679621)
        ·
          refine ⟨11040862351542775569314929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58884599208228136369679621 11040862351542775569314929)
          ·
            refine ⟨8280646763657081676986197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11040862351542775569314929 8280646763657081676986197)
            ·
              refine ⟨48519414630803212951091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8280646763657081676986197 48519414630803212951091)
              ·
                rfl

theorem cell23_7653789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 9].length) (baseStart_7653789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7653789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7653789 prefixEnd_7653789 := by exact prefixLift 7653789
  have htrace : WordTrace (prefixWord ++ tailWord_7653789) baseStart_7653789 baseEnd_7653789 := by
    simpa [prefixWord, tailWord_7653789, baseEnd_7653789] using wordTrace_append hprefix tailTrace_7653789
  have hstable : (prefixWord ++ tailWord_7653789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7653789).length < 2 ^ (prefixWord ++ tailWord_7653789).sum := by decide
  have hdescent : baseEnd_7653789 < baseStart_7653789 := by decide
  rcases family_descends (prefixWord ++ tailWord_7653789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7653800 : List Nat := [2, 1, 6, 1, 1, 1, 3, 1, 3, 2, 2]
def baseStart_7653800 : Nat := 118140960795 + 7653800 * 2 ^ 59
def prefixEnd_7653800 : Nat := 4983230072969 + 3 ^ 40 * 7653800 * 2
def baseEnd_7653800 : Nat := 3930078233382259706000821

theorem tailTrace_7653800 : CollatzResearch.WordTrace tailWord_7653800 prefixEnd_7653800 3930078233382259706000821 := by
  unfold tailWord_7653800
  simp only [CollatzResearch.WordTrace]
  refine ⟨139578509835798619908195427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186104679781064826544260569 139578509835798619908195427)
  ·
    refine ⟨209367764753697929862293141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139578509835798619908195427 209367764753697929862293141)
    ·
      refine ⟨9814113972829590462294991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 209367764753697929862293141 9814113972829590462294991)
      ·
        refine ⟨14721170959244385693442487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9814113972829590462294991 14721170959244385693442487)
        ·
          refine ⟨22081756438866578540163731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14721170959244385693442487 22081756438866578540163731)
          ·
            refine ⟨33122634658299867810245597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22081756438866578540163731 33122634658299867810245597)
            ·
              refine ⟨12420987996862450428842099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33122634658299867810245597 12420987996862450428842099)
              ·
                refine ⟨18631481995293675643263149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12420987996862450428842099 18631481995293675643263149)
                ·
                  refine ⟨6986805748235128366223681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18631481995293675643263149 6986805748235128366223681)
                  ·
                    refine ⟨5240104311176346274667761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6986805748235128366223681 5240104311176346274667761)
                    ·
                      refine ⟨3930078233382259706000821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5240104311176346274667761 3930078233382259706000821)
                      ·
                        rfl

theorem cell23_7653800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_7653800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7653800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7653800 prefixEnd_7653800 := by exact prefixLift 7653800
  have htrace : WordTrace (prefixWord ++ tailWord_7653800) baseStart_7653800 baseEnd_7653800 := by
    simpa [prefixWord, tailWord_7653800, baseEnd_7653800] using wordTrace_append hprefix tailTrace_7653800
  have hstable : (prefixWord ++ tailWord_7653800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7653800).length < 2 ^ (prefixWord ++ tailWord_7653800).sum := by decide
  have hdescent : baseEnd_7653800 < baseStart_7653800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7653800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7653873 : List Nat := [1, 2, 2, 2, 3, 1, 1, 5, 2, 2, 2]
def baseStart_7653873 : Nat := 118140960795 + 7653873 * 2 ^ 59
def prefixEnd_7653873 : Nat := 4983230072969 + 3 ^ 40 * 7653873 * 2
def baseEnd_7653873 : Nat := 3930115717470037920387985

theorem tailTrace_7653873 : CollatzResearch.WordTrace tailWord_7653873 prefixEnd_7653873 3930115717470037920387985 := by
  unfold tailWord_7653873
  simp only [CollatzResearch.WordTrace]
  refine ⟨279159682200332773283798273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186106454800221848855865515 279159682200332773283798273)
  ·
    refine ⟨209369761650249579962848705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279159682200332773283798273 209369761650249579962848705)
    ·
      refine ⟨157027321237687184972136529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209369761650249579962848705 157027321237687184972136529)
      ·
        refine ⟨117770490928265388729102397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157027321237687184972136529 117770490928265388729102397)
        ·
          refine ⟨44163934098099520773413399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117770490928265388729102397 44163934098099520773413399)
          ·
            refine ⟨66245901147149281160120099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44163934098099520773413399 66245901147149281160120099)
            ·
              refine ⟨99368851720723921740180149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66245901147149281160120099 99368851720723921740180149)
              ·
                refine ⟨9315829848817867663141889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99368851720723921740180149 9315829848817867663141889)
                ·
                  refine ⟨6986872386613400747356417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9315829848817867663141889 6986872386613400747356417)
                  ·
                    refine ⟨5240154289960050560517313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6986872386613400747356417 5240154289960050560517313)
                    ·
                      refine ⟨3930115717470037920387985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5240154289960050560517313 3930115717470037920387985)
                      ·
                        rfl

theorem cell23_7653873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 5, 2, 2, 2].length) (baseStart_7653873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7653873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7653873 prefixEnd_7653873 := by exact prefixLift 7653873
  have htrace : WordTrace (prefixWord ++ tailWord_7653873) baseStart_7653873 baseEnd_7653873 := by
    simpa [prefixWord, tailWord_7653873, baseEnd_7653873] using wordTrace_append hprefix tailTrace_7653873
  have hstable : (prefixWord ++ tailWord_7653873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7653873).length < 2 ^ (prefixWord ++ tailWord_7653873).sum := by decide
  have hdescent : baseEnd_7653873 < baseStart_7653873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7653873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7653894 : List Nat := [6, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2]
def baseStart_7653894 : Nat := 118140960795 + 7653894 * 2 ^ 59
def prefixEnd_7653894 : Nat := 4983230072969 + 3 ^ 40 * 7653894 * 2
def baseEnd_7653894 : Nat := 3930126500563782338225389

theorem tailTrace_7653894 : CollatzResearch.WordTrace tailWord_7653894 prefixEnd_7653894 3930126500563782338225389 := by
  unfold tailWord_7653894
  simp only [CollatzResearch.WordTrace]
  refine ⟨8723764004164271683447273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 186106965422171129246875157 8723764004164271683447273)
  ·
    refine ⟨6542823003123203762585455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8723764004164271683447273 6542823003123203762585455)
    ·
      refine ⟨9814234504684805643878183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6542823003123203762585455 9814234504684805643878183)
      ·
        refine ⟨14721351757027208465817275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9814234504684805643878183 14721351757027208465817275)
        ·
          refine ⟨22082027635540812698725913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14721351757027208465817275 22082027635540812698725913)
          ·
            refine ⟨16561520726655609524044435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22082027635540812698725913 16561520726655609524044435)
            ·
              refine ⟨24842281089983414286066653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16561520726655609524044435 24842281089983414286066653)
              ·
                refine ⟨9315855408743780357274995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24842281089983414286066653 9315855408743780357274995)
                ·
                  refine ⟨13973783113115670535912493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9315855408743780357274995 13973783113115670535912493)
                  ·
                    refine ⟨5240168667418376450967185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13973783113115670535912493 5240168667418376450967185)
                    ·
                      refine ⟨3930126500563782338225389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5240168667418376450967185 3930126500563782338225389)
                      ·
                        rfl

theorem cell23_7653894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_7653894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7653894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7653894 prefixEnd_7653894 := by exact prefixLift 7653894
  have htrace : WordTrace (prefixWord ++ tailWord_7653894) baseStart_7653894 baseEnd_7653894 := by
    simpa [prefixWord, tailWord_7653894, baseEnd_7653894] using wordTrace_append hprefix tailTrace_7653894
  have hstable : (prefixWord ++ tailWord_7653894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7653894).length < 2 ^ (prefixWord ++ tailWord_7653894).sum := by decide
  have hdescent : baseEnd_7653894 < baseStart_7653894 := by decide
  rcases family_descends (prefixWord ++ tailWord_7653894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7653909 : List Nat := [1, 3, 2, 1, 3, 1, 2, 1, 4, 5]
def baseStart_7653909 : Nat := 118140960795 + 7653909 * 2 ^ 59
def prefixEnd_7653909 : Nat := 4983230072969 + 3 ^ 40 * 7653909 * 2
def baseEnd_7653909 : Nat := 1310044734257866593179273

theorem tailTrace_7653909 : CollatzResearch.WordTrace tailWord_7653909 prefixEnd_7653909 1310044734257866593179273 := by
  unfold tailWord_7653909
  simp only [CollatzResearch.WordTrace]
  refine ⟨279160995228202351432108781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186107330152134900954739187 279160995228202351432108781)
  ·
    refine ⟨104685373210575881787040793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279160995228202351432108781 104685373210575881787040793)
    ·
      refine ⟨78514029907931911340280595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104685373210575881787040793 78514029907931911340280595)
      ·
        refine ⟨117771044861897867010420893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78514029907931911340280595 117771044861897867010420893)
        ·
          refine ⟨44164141823211700128907835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117771044861897867010420893 44164141823211700128907835)
          ·
            refine ⟨66246212734817550193361753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44164141823211700128907835 66246212734817550193361753)
            ·
              refine ⟨49684659551113162645021315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66246212734817550193361753 49684659551113162645021315)
              ·
                refine ⟨74526989326669743967531973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49684659551113162645021315 74526989326669743967531973)
                ·
                  refine ⟨13973810498750576993912245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74526989326669743967531973 13973810498750576993912245)
                  ·
                    refine ⟨1310044734257866593179273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13973810498750576993912245 1310044734257866593179273)
                    ·
                      rfl

theorem cell23_7653909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_7653909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7653909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7653909 prefixEnd_7653909 := by exact prefixLift 7653909
  have htrace : WordTrace (prefixWord ++ tailWord_7653909) baseStart_7653909 baseEnd_7653909 := by
    simpa [prefixWord, tailWord_7653909, baseEnd_7653909] using wordTrace_append hprefix tailTrace_7653909
  have hstable : (prefixWord ++ tailWord_7653909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7653909).length < 2 ^ (prefixWord ++ tailWord_7653909).sum := by decide
  have hdescent : baseEnd_7653909 < baseStart_7653909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7653909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7653924 : List Nat := [2, 3, 1, 5, 1, 1, 3, 1, 2, 2, 2]
def baseStart_7653924 : Nat := 118140960795 + 7653924 * 2 ^ 59
def prefixEnd_7653924 : Nat := 4983230072969 + 3 ^ 40 * 7653924 * 2
def baseEnd_7653924 : Nat := 3930141904983417220850251

theorem tailTrace_7653924 : CollatzResearch.WordTrace tailWord_7653924 prefixEnd_7653924 3930141904983417220850251 := by
  unfold tailWord_7653924
  simp only [CollatzResearch.WordTrace]
  refine ⟨139580771161574004496952413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186107694882098672662603217 139580771161574004496952413)
  ·
    refine ⟨52342789185590251686357155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139580771161574004496952413 52342789185590251686357155)
    ·
      refine ⟨78514183778385377529535733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52342789185590251686357155 78514183778385377529535733)
      ·
        refine ⟨7360704729223629143393975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78514183778385377529535733 7360704729223629143393975)
        ·
          refine ⟨11041057093835443715090963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7360704729223629143393975 11041057093835443715090963)
          ·
            refine ⟨16561585640753165572636445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11041057093835443715090963 16561585640753165572636445)
            ·
              refine ⟨6210594615282437089738667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16561585640753165572636445 6210594615282437089738667)
              ·
                refine ⟨9315891922923655634608001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6210594615282437089738667 9315891922923655634608001)
                ·
                  refine ⟨6986918942192741725956001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9315891922923655634608001 6986918942192741725956001)
                  ·
                    refine ⟨5240189206644556294467001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6986918942192741725956001 5240189206644556294467001)
                    ·
                      refine ⟨3930141904983417220850251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5240189206644556294467001 3930141904983417220850251)
                      ·
                        rfl

theorem cell23_7653924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_7653924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7653924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7653924 prefixEnd_7653924 := by exact prefixLift 7653924
  have htrace : WordTrace (prefixWord ++ tailWord_7653924) baseStart_7653924 baseEnd_7653924 := by
    simpa [prefixWord, tailWord_7653924, baseEnd_7653924] using wordTrace_append hprefix tailTrace_7653924
  have hstable : (prefixWord ++ tailWord_7653924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7653924).length < 2 ^ (prefixWord ++ tailWord_7653924).sum := by decide
  have hdescent : baseEnd_7653924 < baseStart_7653924 := by decide
  rcases family_descends (prefixWord ++ tailWord_7653924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7653966 : List Nat := [4, 1, 1, 1, 1, 2, 3, 1, 4, 2, 3]
def baseStart_7653966 : Nat := 118140960795 + 7653966 * 2 ^ 59
def prefixEnd_7653966 : Nat := 4983230072969 + 3 ^ 40 * 7653966 * 2
def baseEnd_7653966 : Nat := 3930163471170906056525057

theorem tailTrace_7653966 : CollatzResearch.WordTrace tailWord_7653966 prefixEnd_7653966 3930163471170906056525057 := by
  unfold tailWord_7653966
  simp only [CollatzResearch.WordTrace]
  refine ⟨34895384273624481270866719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186108716125997233444622501 34895384273624481270866719)
  ·
    refine ⟨52343076410436721906300079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34895384273624481270866719 52343076410436721906300079)
    ·
      refine ⟨78514614615655082859450119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52343076410436721906300079 78514614615655082859450119)
      ·
        refine ⟨117771921923482624289175179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78514614615655082859450119 117771921923482624289175179)
        ·
          refine ⟨176657882885223936433762769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117771921923482624289175179 176657882885223936433762769)
          ·
            refine ⟨132493412163917952325322077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176657882885223936433762769 132493412163917952325322077)
            ·
              refine ⟨49685029561469232121995779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132493412163917952325322077 49685029561469232121995779)
              ·
                refine ⟨74527544342203848182993669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49685029561469232121995779 74527544342203848182993669)
                ·
                  refine ⟨13973914564163221534311313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74527544342203848182993669 13973914564163221534311313)
                  ·
                    refine ⟨10480435923122416150733485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13973914564163221534311313 10480435923122416150733485)
                    ·
                      refine ⟨3930163471170906056525057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10480435923122416150733485 3930163471170906056525057)
                      ·
                        rfl

theorem cell23_7653966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 4, 2, 3].length) (baseStart_7653966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7653966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7653966 prefixEnd_7653966 := by exact prefixLift 7653966
  have htrace : WordTrace (prefixWord ++ tailWord_7653966) baseStart_7653966 baseEnd_7653966 := by
    simpa [prefixWord, tailWord_7653966, baseEnd_7653966] using wordTrace_append hprefix tailTrace_7653966
  have hstable : (prefixWord ++ tailWord_7653966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7653966).length < 2 ^ (prefixWord ++ tailWord_7653966).sum := by decide
  have hdescent : baseEnd_7653966 < baseStart_7653966 := by decide
  rcases family_descends (prefixWord ++ tailWord_7653966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7653969 : List Nat := [1, 2, 2, 1, 3, 3, 2, 1, 8]
def baseStart_7653969 : Nat := 118140960795 + 7653969 * 2 ^ 59
def prefixEnd_7653969 : Nat := 4983230072969 + 3 ^ 40 * 7653969 * 2
def baseEnd_7653969 : Nat := 436685001290318838309727

theorem tailTrace_7653969 : CollatzResearch.WordTrace tailWord_7653969 prefixEnd_7653969 436685001290318838309727 := by
  unfold tailWord_7653969
  simp only [CollatzResearch.WordTrace]
  refine ⟨279163183607984981679292961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186108789071989987786195307 279163183607984981679292961)
  ·
    refine ⟨209372387705988736259469721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279163183607984981679292961 209372387705988736259469721)
    ·
      refine ⟨157029290779491552194602291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209372387705988736259469721 157029290779491552194602291)
      ·
        refine ⟨235543936169237328291903437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157029290779491552194602291 235543936169237328291903437)
        ·
          refine ⟨88328976063463998109463789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235543936169237328291903437 88328976063463998109463789)
          ·
            refine ⟨33123366023798999291048921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88328976063463998109463789 33123366023798999291048921)
            ·
              refine ⟨24842524517849249468286691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33123366023798999291048921 24842524517849249468286691)
              ·
                refine ⟨37263786776773874202430037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24842524517849249468286691 37263786776773874202430037)
                ·
                  refine ⟨436685001290318838309727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37263786776773874202430037 436685001290318838309727)
                  ·
                    rfl

theorem cell23_7653969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 8].length) (baseStart_7653969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7653969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7653969 prefixEnd_7653969 := by exact prefixLift 7653969
  have htrace : WordTrace (prefixWord ++ tailWord_7653969) baseStart_7653969 baseEnd_7653969 := by
    simpa [prefixWord, tailWord_7653969, baseEnd_7653969] using wordTrace_append hprefix tailTrace_7653969
  have hstable : (prefixWord ++ tailWord_7653969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7653969).length < 2 ^ (prefixWord ++ tailWord_7653969).sum := by decide
  have hdescent : baseEnd_7653969 < baseStart_7653969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7653969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7653973 : List Nat := [1, 3, 2, 2, 1, 1, 2, 6, 1, 4]
def baseStart_7653973 : Nat := 118140960795 + 7653973 * 2 ^ 59
def prefixEnd_7653973 : Nat := 4983230072969 + 3 ^ 40 * 7653973 * 2
def baseEnd_7653973 : Nat := 1310055688511829176379175

theorem tailTrace_7653973 : CollatzResearch.WordTrace tailWord_7653973 prefixEnd_7653973 1310055688511829176379175 := by
  unfold tailWord_7653973
  simp only [CollatzResearch.WordTrace]
  refine ⟨279163329499970490362438573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186108886333313660241625715 279163329499970490362438573)
  ·
    refine ⟨104686248562488933885914465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279163329499970490362438573 104686248562488933885914465)
    ·
      refine ⟨78514686421866700414435849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104686248562488933885914465 78514686421866700414435849)
      ·
        refine ⟨58886014816400025310826887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78514686421866700414435849 58886014816400025310826887)
        ·
          refine ⟨88329022224600037966240331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58886014816400025310826887 88329022224600037966240331)
          ·
            refine ⟨132493533336900056949360497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88329022224600037966240331 132493533336900056949360497)
            ·
              refine ⟨99370150002675042712020373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132493533336900056949360497 99370150002675042712020373)
              ·
                refine ⟨4657975781375392627125955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99370150002675042712020373 4657975781375392627125955)
                ·
                  refine ⟨6986963672063088940688933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4657975781375392627125955 6986963672063088940688933)
                  ·
                    refine ⟨1310055688511829176379175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6986963672063088940688933 1310055688511829176379175)
                    ·
                      rfl

theorem cell23_7653973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 6, 1, 4].length) (baseStart_7653973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7653973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7653973 prefixEnd_7653973 := by exact prefixLift 7653973
  have htrace : WordTrace (prefixWord ++ tailWord_7653973) baseStart_7653973 baseEnd_7653973 := by
    simpa [prefixWord, tailWord_7653973, baseEnd_7653973] using wordTrace_append hprefix tailTrace_7653973
  have hstable : (prefixWord ++ tailWord_7653973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7653973).length < 2 ^ (prefixWord ++ tailWord_7653973).sum := by decide
  have hdescent : baseEnd_7653973 < baseStart_7653973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7653973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654023 : List Nat := [1, 1, 4, 2, 1, 2, 1, 4, 2, 3, 2]
def baseStart_7654023 : Nat := 118140960795 + 7654023 * 2 ^ 59
def prefixEnd_7654023 : Nat := 4983230072969 + 3 ^ 40 * 7654023 * 2
def baseEnd_7654023 : Nat := 3930192739568212333512295

theorem tailTrace_7654023 : CollatzResearch.WordTrace tailWord_7654023 prefixEnd_7654023 3930192739568212333512295 := by
  unfold tailWord_7654023
  simp only [CollatzResearch.WordTrace]
  refine ⟨279165153149789348901758723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186110102099859565934505815 279165153149789348901758723)
  ·
    refine ⟨418747729724684023352638085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279165153149789348901758723 418747729724684023352638085)
    ·
      refine ⟨78515199323378254378619641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 418747729724684023352638085 78515199323378254378619641)
      ·
        refine ⟨58886399492533690783964731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78515199323378254378619641 58886399492533690783964731)
        ·
          refine ⟨88329599238800536175947097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58886399492533690783964731 88329599238800536175947097)
          ·
            refine ⟨66247199429100402131960323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88329599238800536175947097 66247199429100402131960323)
            ·
              refine ⟨99370799143650603197940485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66247199429100402131960323 99370799143650603197940485)
              ·
                refine ⟨18632024839434488099613841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99370799143650603197940485 18632024839434488099613841)
                ·
                  refine ⟨13974018629575866074710381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18632024839434488099613841 13974018629575866074710381)
                  ·
                    refine ⟨5240256986090949778016393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13974018629575866074710381 5240256986090949778016393)
                    ·
                      refine ⟨3930192739568212333512295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5240256986090949778016393 3930192739568212333512295)
                      ·
                        rfl

theorem cell23_7654023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 2, 3, 2].length) (baseStart_7654023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654023 prefixEnd_7654023 := by exact prefixLift 7654023
  have htrace : WordTrace (prefixWord ++ tailWord_7654023) baseStart_7654023 baseEnd_7654023 := by
    simpa [prefixWord, tailWord_7654023, baseEnd_7654023] using wordTrace_append hprefix tailTrace_7654023
  have hstable : (prefixWord ++ tailWord_7654023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654023).length < 2 ^ (prefixWord ++ tailWord_7654023).sum := by decide
  have hdescent : baseEnd_7654023 < baseStart_7654023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654080 : List Nat := [2, 1, 1, 2, 4, 4, 1, 2, 2, 4]
def baseStart_7654080 : Nat := 118140960795 + 7654080 * 2 ^ 59
def prefixEnd_7654080 : Nat := 4983230072969 + 3 ^ 40 * 7654080 * 2
def baseEnd_7654080 : Nat := 1310074002655172870166511

theorem tailTrace_7654080 : CollatzResearch.WordTrace tailWord_7654080 prefixEnd_7654080 1310074002655172870166511 := by
  unfold tailWord_7654080
  simp only [CollatzResearch.WordTrace]
  refine ⟨139583616055291423818291847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186111488073721898424389129 139583616055291423818291847)
  ·
    refine ⟨209375424082937135727437771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139583616055291423818291847 209375424082937135727437771)
    ·
      refine ⟨314063136124405703591156657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209375424082937135727437771 314063136124405703591156657)
      ·
        refine ⟨235547352093304277693367493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314063136124405703591156657 235547352093304277693367493)
        ·
          refine ⟨44165128517494552067506405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 235547352093304277693367493 44165128517494552067506405)
          ·
            refine ⟨8280961597030228512657451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44165128517494552067506405 8280961597030228512657451)
            ·
              refine ⟨12421442395545342768986177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8280961597030228512657451 12421442395545342768986177)
              ·
                refine ⟨9316081796659007076739633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12421442395545342768986177 9316081796659007076739633)
                ·
                  refine ⟨6987061347494255307554725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9316081796659007076739633 6987061347494255307554725)
                  ·
                    refine ⟨1310074002655172870166511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6987061347494255307554725 1310074002655172870166511)
                    ·
                      rfl

theorem cell23_7654080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 2, 2, 4].length) (baseStart_7654080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654080 prefixEnd_7654080 := by exact prefixLift 7654080
  have htrace : WordTrace (prefixWord ++ tailWord_7654080) baseStart_7654080 baseEnd_7654080 := by
    simpa [prefixWord, tailWord_7654080, baseEnd_7654080] using wordTrace_append hprefix tailTrace_7654080
  have hstable : (prefixWord ++ tailWord_7654080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654080).length < 2 ^ (prefixWord ++ tailWord_7654080).sum := by decide
  have hdescent : baseEnd_7654080 < baseStart_7654080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654099 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 7]
def baseStart_7654099 : Nat := 118140960795 + 7654099 * 2 ^ 59
def prefixEnd_7654099 : Nat := 4983230072969 + 3 ^ 40 * 7654099 * 2
def baseEnd_7654099 : Nat := 3930231764097954036161945

theorem tailTrace_7654099 : CollatzResearch.WordTrace tailWord_7654099 prefixEnd_7654099 3930231764097954036161945 := by
  unfold tailWord_7654099
  simp only [CollatzResearch.WordTrace]
  refine ⟨279167925097514013881525351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186111950065009342587683567 279167925097514013881525351)
  ·
    refine ⟨418751887646271020822288027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279167925097514013881525351 418751887646271020822288027)
    ·
      refine ⟨628127831469406531233432041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418751887646271020822288027 628127831469406531233432041)
      ·
        refine ⟨471095873602054898425074031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 628127831469406531233432041 471095873602054898425074031)
        ·
          refine ⟨706643810403082347637611047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471095873602054898425074031 706643810403082347637611047)
          ·
            refine ⟨1059965715604623521456416571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706643810403082347637611047 1059965715604623521456416571)
            ·
              refine ⟨1589948573406935282184624857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1059965715604623521456416571 1589948573406935282184624857)
              ·
                refine ⟨1192461430055201461638468643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1589948573406935282184624857 1192461430055201461638468643)
                ·
                  refine ⟨1788692145082802192457702965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1192461430055201461638468643 1788692145082802192457702965)
                  ·
                    refine ⟨167689888601512705542909653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1788692145082802192457702965 167689888601512705542909653)
                    ·
                      refine ⟨3930231764097954036161945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 167689888601512705542909653 3930231764097954036161945)
                      ·
                        rfl

theorem cell23_7654099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 7].length) (baseStart_7654099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654099 prefixEnd_7654099 := by exact prefixLift 7654099
  have htrace : WordTrace (prefixWord ++ tailWord_7654099) baseStart_7654099 baseEnd_7654099 := by
    simpa [prefixWord, tailWord_7654099, baseEnd_7654099] using wordTrace_append hprefix tailTrace_7654099
  have hstable : (prefixWord ++ tailWord_7654099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654099).length < 2 ^ (prefixWord ++ tailWord_7654099).sum := by decide
  have hdescent : baseEnd_7654099 < baseStart_7654099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654103 : List Nat := [1, 1, 3, 2, 1, 4, 3, 1, 1, 3, 3]
def baseStart_7654103 : Nat := 118140960795 + 7654103 * 2 ^ 59
def prefixEnd_7654103 : Nat := 4983230072969 + 3 ^ 40 * 7654103 * 2
def baseEnd_7654103 : Nat := 3930233818020572020511927

theorem tailTrace_7654103 : CollatzResearch.WordTrace tailWord_7654103 prefixEnd_7654103 3930233818020572020511927 := by
  unfold tailWord_7654103
  simp only [CollatzResearch.WordTrace]
  refine ⟨279168070989499522564670963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186112047326333015043113975 279168070989499522564670963)
  ·
    refine ⟨418752106484249283847006445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279168070989499522564670963 418752106484249283847006445)
    ·
      refine ⟨157032039931593481442627417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 418752106484249283847006445 157032039931593481442627417)
      ·
        refine ⟨117774029948695111081970563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157032039931593481442627417 117774029948695111081970563)
        ·
          refine ⟨176661044923042666622955845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117774029948695111081970563 176661044923042666622955845)
          ·
            refine ⟨33123945923070499991804221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176661044923042666622955845 33123945923070499991804221)
            ·
              refine ⟨12421479721151437496926583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33123945923070499991804221 12421479721151437496926583)
              ·
                refine ⟨18632219581727156245389875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12421479721151437496926583 18632219581727156245389875)
                ·
                  refine ⟨27948329372590734368084813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18632219581727156245389875 27948329372590734368084813)
                  ·
                    refine ⟨10480623514721525388031805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27948329372590734368084813 10480623514721525388031805)
                    ·
                      refine ⟨3930233818020572020511927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10480623514721525388031805 3930233818020572020511927)
                      ·
                        rfl

theorem cell23_7654103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 3, 3].length) (baseStart_7654103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654103 prefixEnd_7654103 := by exact prefixLift 7654103
  have htrace : WordTrace (prefixWord ++ tailWord_7654103) baseStart_7654103 baseEnd_7654103 := by
    simpa [prefixWord, tailWord_7654103, baseEnd_7654103] using wordTrace_append hprefix tailTrace_7654103
  have hstable : (prefixWord ++ tailWord_7654103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654103).length < 2 ^ (prefixWord ++ tailWord_7654103).sum := by decide
  have hdescent : baseEnd_7654103 < baseStart_7654103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654116 : List Nat := [2, 3, 1, 1, 1, 4, 1, 1, 2, 2, 5]
def baseStart_7654116 : Nat := 118140960795 + 7654116 * 2 ^ 59
def prefixEnd_7654116 : Nat := 4983230072969 + 3 ^ 40 * 7654116 * 2
def baseEnd_7654116 : Nat := 3930240493269080469649367

theorem tailTrace_7654116 : CollatzResearch.WordTrace tailWord_7654116 prefixEnd_7654116 3930240493269080469649367 := by
  unfold tailWord_7654116
  simp only [CollatzResearch.WordTrace]
  refine ⟨139584272569226212892447101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186112363425634950523262801 139584272569226212892447101)
  ·
    refine ⟨52344102213459829834667663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139584272569226212892447101 52344102213459829834667663)
    ·
      refine ⟨78516153320189744752001495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52344102213459829834667663 78516153320189744752001495)
      ·
        refine ⟨117774229980284617128002243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78516153320189744752001495 117774229980284617128002243)
        ·
          refine ⟨176661344970426925692003365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117774229980284617128002243 176661344970426925692003365)
          ·
            refine ⟨33124002181955048567250631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176661344970426925692003365 33124002181955048567250631)
            ·
              refine ⟨49686003272932572850875947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33124002181955048567250631 49686003272932572850875947)
              ·
                refine ⟨74529004909398859276313921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49686003272932572850875947 74529004909398859276313921)
                ·
                  refine ⟨55896753682049144457235441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74529004909398859276313921 55896753682049144457235441)
                  ·
                    refine ⟨41922565261536858342926581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55896753682049144457235441 41922565261536858342926581)
                    ·
                      refine ⟨3930240493269080469649367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41922565261536858342926581 3930240493269080469649367)
                      ·
                        rfl

theorem cell23_7654116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_7654116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654116 prefixEnd_7654116 := by exact prefixLift 7654116
  have htrace : WordTrace (prefixWord ++ tailWord_7654116) baseStart_7654116 baseEnd_7654116 := by
    simpa [prefixWord, tailWord_7654116, baseEnd_7654116] using wordTrace_append hprefix tailTrace_7654116
  have hstable : (prefixWord ++ tailWord_7654116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654116).length < 2 ^ (prefixWord ++ tailWord_7654116).sum := by decide
  have hdescent : baseEnd_7654116 < baseStart_7654116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654156 : List Nat := [2, 2, 1, 2, 2, 1, 1, 3, 1, 4, 4]
def baseStart_7654156 : Nat := 118140960795 + 7654156 * 2 ^ 59
def prefixEnd_7654156 : Nat := 4983230072969 + 3 ^ 40 * 7654156 * 2
def baseEnd_7654156 : Nat := 3930261032495260313149183

theorem tailTrace_7654156 : CollatzResearch.WordTrace tailWord_7654156 prefixEnd_7654156 3930261032495260313149183 := by
  unfold tailWord_7654156
  simp only [CollatzResearch.WordTrace]
  refine ⟨139585002029153756308175161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186113336038871675077566881 139585002029153756308175161)
  ·
    refine ⟨104688751521865317231131371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139585002029153756308175161 104688751521865317231131371)
    ·
      refine ⟨157033127282797975846697057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104688751521865317231131371 157033127282797975846697057)
      ·
        refine ⟨117774845462098481885022793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157033127282797975846697057 117774845462098481885022793)
        ·
          refine ⟨88331134096573861413767095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117774845462098481885022793 88331134096573861413767095)
          ·
            refine ⟨132496701144860792120650643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88331134096573861413767095 132496701144860792120650643)
            ·
              refine ⟨198745051717291188180975965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132496701144860792120650643 198745051717291188180975965)
              ·
                refine ⟨74529394393984195567865987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198745051717291188180975965 74529394393984195567865987)
                ·
                  refine ⟨111794091590976293351798981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74529394393984195567865987 111794091590976293351798981)
                  ·
                    refine ⟨20961392173308055003462309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 111794091590976293351798981 20961392173308055003462309)
                    ·
                      refine ⟨3930261032495260313149183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20961392173308055003462309 3930261032495260313149183)
                      ·
                        rfl

theorem cell23_7654156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_7654156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654156 prefixEnd_7654156 := by exact prefixLift 7654156
  have htrace : WordTrace (prefixWord ++ tailWord_7654156) baseStart_7654156 baseEnd_7654156 := by
    simpa [prefixWord, tailWord_7654156, baseEnd_7654156] using wordTrace_append hprefix tailTrace_7654156
  have hstable : (prefixWord ++ tailWord_7654156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654156).length < 2 ^ (prefixWord ++ tailWord_7654156).sum := by decide
  have hdescent : baseEnd_7654156 < baseStart_7654156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654193 : List Nat := [1, 2, 2, 3, 2, 1, 2, 2, 2, 3, 3]
def baseStart_7654193 : Nat := 118140960795 + 7654193 * 2 ^ 59
def prefixEnd_7654193 : Nat := 4983230072969 + 3 ^ 40 * 7654193 * 2
def baseEnd_7654193 : Nat := 3930280031279476668386513

theorem tailTrace_7654193 : CollatzResearch.WordTrace tailWord_7654193 prefixEnd_7654193 3930280031279476668386513 := by
  unfold tailWord_7654193
  simp only [CollatzResearch.WordTrace]
  refine ⟨279171353559173467935447233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186114235706115645290298155 279171353559173467935447233)
  ·
    refine ⟨209378515169380100951585425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279171353559173467935447233 209378515169380100951585425)
    ·
      refine ⟨157033886377035075713689069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209378515169380100951585425 157033886377035075713689069)
      ·
        refine ⟨58887707391388153392633401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157033886377035075713689069 58887707391388153392633401)
        ·
          refine ⟨44165780543541115044475051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58887707391388153392633401 44165780543541115044475051)
          ·
            refine ⟨66248670815311672566712577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44165780543541115044475051 66248670815311672566712577)
            ·
              refine ⟨49686503111483754425034433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66248670815311672566712577 49686503111483754425034433)
              ·
                refine ⟨37264877333612815818775825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49686503111483754425034433 37264877333612815818775825)
                ·
                  refine ⟨27948658000209611864081869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37264877333612815818775825 27948658000209611864081869)
                  ·
                    refine ⟨10480746750078604449030701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27948658000209611864081869 10480746750078604449030701)
                    ·
                      refine ⟨3930280031279476668386513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10480746750078604449030701 3930280031279476668386513)
                      ·
                        rfl

theorem cell23_7654193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_7654193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654193 prefixEnd_7654193 := by exact prefixLift 7654193
  have htrace : WordTrace (prefixWord ++ tailWord_7654193) baseStart_7654193 baseEnd_7654193 := by
    simpa [prefixWord, tailWord_7654193, baseEnd_7654193] using wordTrace_append hprefix tailTrace_7654193
  have hstable : (prefixWord ++ tailWord_7654193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654193).length < 2 ^ (prefixWord ++ tailWord_7654193).sum := by decide
  have hdescent : baseEnd_7654193 < baseStart_7654193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654233 : List Nat := [1, 2, 1, 2, 2, 5, 1, 1, 1, 3, 4]
def baseStart_7654233 : Nat := 118140960795 + 7654233 * 2 ^ 59
def prefixEnd_7654233 : Nat := 4983230072969 + 3 ^ 40 * 7654233 * 2
def baseEnd_7654233 : Nat := 3930300570505656511886329

theorem tailTrace_7654233 : CollatzResearch.WordTrace tailWord_7654233 prefixEnd_7654233 3930300570505656511886329 := by
  unfold tailWord_7654233
  simp only [CollatzResearch.WordTrace]
  refine ⟨279172812479028554766903353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186115208319352369844602235 279172812479028554766903353)
  ·
    refine ⟨209379609359271416075177515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279172812479028554766903353 209379609359271416075177515)
    ·
      refine ⟨314069414038907124112766273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209379609359271416075177515 314069414038907124112766273)
      ·
        refine ⟨235552060529180343084574705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314069414038907124112766273 235552060529180343084574705)
        ·
          refine ⟨176664045396885257313431029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235552060529180343084574705 176664045396885257313431029)
          ·
            refine ⟨16562254255957992873134159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 176664045396885257313431029 16562254255957992873134159)
            ·
              refine ⟨24843381383936989309701239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16562254255957992873134159 24843381383936989309701239)
              ·
                refine ⟨37265072075905483964551859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24843381383936989309701239 37265072075905483964551859)
                ·
                  refine ⟨55897608113858225946827789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37265072075905483964551859 55897608113858225946827789)
                  ·
                    refine ⟨20961603042696834730060421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55897608113858225946827789 20961603042696834730060421)
                    ·
                      refine ⟨3930300570505656511886329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20961603042696834730060421 3930300570505656511886329)
                      ·
                        rfl

theorem cell23_7654233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 3, 4].length) (baseStart_7654233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654233 prefixEnd_7654233 := by exact prefixLift 7654233
  have htrace : WordTrace (prefixWord ++ tailWord_7654233) baseStart_7654233 baseEnd_7654233 := by
    simpa [prefixWord, tailWord_7654233, baseEnd_7654233] using wordTrace_append hprefix tailTrace_7654233
  have hstable : (prefixWord ++ tailWord_7654233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654233).length < 2 ^ (prefixWord ++ tailWord_7654233).sum := by decide
  have hdescent : baseEnd_7654233 < baseStart_7654233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654311 : List Nat := [1, 1, 6, 1, 3, 1, 3, 2, 1, 4]
def baseStart_7654311 : Nat := 118140960795 + 7654311 * 2 ^ 59
def prefixEnd_7654311 : Nat := 4983230072969 + 3 ^ 40 * 7654311 * 2
def baseEnd_7654311 : Nat := 1310113540665569068903657

theorem tailTrace_7654311 : CollatzResearch.WordTrace tailWord_7654311 prefixEnd_7654311 1310113540665569068903657 := by
  unfold tailWord_7654311
  simp only [CollatzResearch.WordTrace]
  refine ⟨279175657372745974088242787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186117104915163982725495191 279175657372745974088242787)
  ·
    refine ⟨418763486059118961132364181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279175657372745974088242787 418763486059118961132364181)
    ·
      refine ⟨19629538409021201303079571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 418763486059118961132364181 19629538409021201303079571)
      ·
        refine ⟨29444307613531801954619357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19629538409021201303079571 29444307613531801954619357)
        ·
          refine ⟨11041615355074425732982259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29444307613531801954619357 11041615355074425732982259)
          ·
            refine ⟨16562423032611638599473389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11041615355074425732982259 16562423032611638599473389)
            ·
              refine ⟨6210908637229364474802521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16562423032611638599473389 6210908637229364474802521)
              ·
                refine ⟨4658181477922023356101891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6210908637229364474802521 4658181477922023356101891)
                ·
                  refine ⟨6987272216883035034152837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4658181477922023356101891 6987272216883035034152837)
                  ·
                    refine ⟨1310113540665569068903657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6987272216883035034152837 1310113540665569068903657)
                    ·
                      rfl

theorem cell23_7654311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_7654311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654311 prefixEnd_7654311 := by exact prefixLift 7654311
  have htrace : WordTrace (prefixWord ++ tailWord_7654311) baseStart_7654311 baseEnd_7654311 := by
    simpa [prefixWord, tailWord_7654311, baseEnd_7654311] using wordTrace_append hprefix tailTrace_7654311
  have hstable : (prefixWord ++ tailWord_7654311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654311).length < 2 ^ (prefixWord ++ tailWord_7654311).sum := by decide
  have hdescent : baseEnd_7654311 < baseStart_7654311 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654324 : List Nat := [2, 5, 2, 1, 1, 1, 4, 1, 6]
def baseStart_7654324 : Nat := 118140960795 + 7654324 * 2 ^ 59
def prefixEnd_7654324 : Nat := 4983230072969 + 3 ^ 40 * 7654324 * 2
def baseEnd_7654324 : Nat := 436705255249468406205379

theorem tailTrace_7654324 : CollatzResearch.WordTrace tailWord_7654324 prefixEnd_7654324 436705255249468406205379 := by
  unfold tailWord_7654324
  simp only [CollatzResearch.WordTrace]
  refine ⟨139588065760849438654233013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186117421014465918205644017 139588065760849438654233013)
  ·
    refine ⟨13086381165079634873834345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139588065760849438654233013 13086381165079634873834345)
    ·
      refine ⟨9814785873809726155375759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13086381165079634873834345 9814785873809726155375759)
      ·
        refine ⟨14722178810714589233063639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9814785873809726155375759 14722178810714589233063639)
        ·
          refine ⟨22083268216071883849595459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14722178810714589233063639 22083268216071883849595459)
          ·
            refine ⟨33124902324107825774393189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22083268216071883849595459 33124902324107825774393189)
            ·
              refine ⟨6210919185770217332698723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33124902324107825774393189 6210919185770217332698723)
              ·
                refine ⟨9316378778655325999048085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6210919185770217332698723 9316378778655325999048085)
                ·
                  refine ⟨436705255249468406205379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9316378778655325999048085 436705255249468406205379)
                  ·
                    rfl

theorem cell23_7654324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_7654324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654324 prefixEnd_7654324 := by exact prefixLift 7654324
  have htrace : WordTrace (prefixWord ++ tailWord_7654324) baseStart_7654324 baseEnd_7654324 := by
    simpa [prefixWord, tailWord_7654324, baseEnd_7654324] using wordTrace_append hprefix tailTrace_7654324
  have hstable : (prefixWord ++ tailWord_7654324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654324).length < 2 ^ (prefixWord ++ tailWord_7654324).sum := by decide
  have hdescent : baseEnd_7654324 < baseStart_7654324 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654343 : List Nat := [1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 5]
def baseStart_7654343 : Nat := 118140960795 + 7654343 * 2 ^ 59
def prefixEnd_7654343 : Nat := 4983230072969 + 3 ^ 40 * 7654343 * 2
def baseEnd_7654343 : Nat := 3930357053377651081510823

theorem tailTrace_7654343 : CollatzResearch.WordTrace tailWord_7654343 prefixEnd_7654343 3930357053377651081510823 := by
  unfold tailWord_7654343
  simp only [CollatzResearch.WordTrace]
  refine ⟨279176824508630043553407683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186117883005753362368938455 279176824508630043553407683)
  ·
    refine ⟨418765236762945065330111525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279176824508630043553407683 418765236762945065330111525)
    ·
      refine ⟨78518481893052199749395911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 418765236762945065330111525 78518481893052199749395911)
      ·
        refine ⟨117777722839578299624093867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78518481893052199749395911 117777722839578299624093867)
        ·
          refine ⟨176666584259367449436140801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117777722839578299624093867 176666584259367449436140801)
          ·
            refine ⟨132499938194525587077105601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176666584259367449436140801 132499938194525587077105601)
            ·
              refine ⟨99374953645894190307829201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132499938194525587077105601 99374953645894190307829201)
              ·
                refine ⟨74531215234420642730871901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99374953645894190307829201 74531215234420642730871901)
                ·
                  refine ⟨27949205712907741024076963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74531215234420642730871901 27949205712907741024076963)
                  ·
                    refine ⟨41923808569361611536115445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27949205712907741024076963 41923808569361611536115445)
                    ·
                      refine ⟨3930357053377651081510823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41923808569361611536115445 3930357053377651081510823)
                      ·
                        rfl

theorem cell23_7654343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_7654343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654343 prefixEnd_7654343 := by exact prefixLift 7654343
  have htrace : WordTrace (prefixWord ++ tailWord_7654343) baseStart_7654343 baseEnd_7654343 := by
    simpa [prefixWord, tailWord_7654343, baseEnd_7654343] using wordTrace_append hprefix tailTrace_7654343
  have hstable : (prefixWord ++ tailWord_7654343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654343).length < 2 ^ (prefixWord ++ tailWord_7654343).sum := by decide
  have hdescent : baseEnd_7654343 < baseStart_7654343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654344 : List Nat := [2, 1, 3, 1, 5, 1, 2, 1, 2, 3, 2]
def baseStart_7654344 : Nat := 118140960795 + 7654344 * 2 ^ 59
def prefixEnd_7654344 : Nat := 4983230072969 + 3 ^ 40 * 7654344 * 2
def baseEnd_7654344 : Nat := 3930357566858305577598319

theorem tailTrace_7654344 : CollatzResearch.WordTrace tailWord_7654344 prefixEnd_7654344 3930357566858305577598319 := by
  unfold tailWord_7654344
  simp only [CollatzResearch.WordTrace]
  refine ⟨139588430490813210362097043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186117907321084280482796057 139588430490813210362097043)
  ·
    refine ⟨209382645736219815543145565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139588430490813210362097043 209382645736219815543145565)
    ·
      refine ⟨78518492151082430828679587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209382645736219815543145565 78518492151082430828679587)
      ·
        refine ⟨117777738226623646243019381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78518492151082430828679587 117777738226623646243019381)
        ·
          refine ⟨11041662958745966835283067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117777738226623646243019381 11041662958745966835283067)
          ·
            refine ⟨16562494438118950252924601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11041662958745966835283067 16562494438118950252924601)
            ·
              refine ⟨12421870828589212689693451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16562494438118950252924601 12421870828589212689693451)
              ·
                refine ⟨18632806242883819034540177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12421870828589212689693451 18632806242883819034540177)
                ·
                  refine ⟨13974604682162864275905133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18632806242883819034540177 13974604682162864275905133)
                  ·
                    refine ⟨5240476755811074103464425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13974604682162864275905133 5240476755811074103464425)
                    ·
                      refine ⟨3930357566858305577598319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5240476755811074103464425 3930357566858305577598319)
                      ·
                        rfl

theorem cell23_7654344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 2, 3, 2].length) (baseStart_7654344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654344 prefixEnd_7654344 := by exact prefixLift 7654344
  have htrace : WordTrace (prefixWord ++ tailWord_7654344) baseStart_7654344 baseEnd_7654344 := by
    simpa [prefixWord, tailWord_7654344, baseEnd_7654344] using wordTrace_append hprefix tailTrace_7654344
  have hstable : (prefixWord ++ tailWord_7654344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654344).length < 2 ^ (prefixWord ++ tailWord_7654344).sum := by decide
  have hdescent : baseEnd_7654344 < baseStart_7654344 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654350 : List Nat := [4, 1, 1, 1, 2, 4, 1, 2, 1, 6]
def baseStart_7654350 : Nat := 118140960795 + 7654350 * 2 ^ 59
def prefixEnd_7654350 : Nat := 4983230072969 + 3 ^ 40 * 7654350 * 2
def baseEnd_7654350 : Nat := 1310120215914077518041097

theorem tailTrace_7654350 : CollatzResearch.WordTrace tailWord_7654350 prefixEnd_7654350 1310120215914077518041097 := by
  unfold tailWord_7654350
  simp only [CollatzResearch.WordTrace]
  refine ⟨34897134977450585468614063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186118053213069789165941669 34897134977450585468614063)
  ·
    refine ⟨52345702466175878202921095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34897134977450585468614063 52345702466175878202921095)
    ·
      refine ⟨78518553699263817304381643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52345702466175878202921095 78518553699263817304381643)
      ·
        refine ⟨117777830548895725956572465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78518553699263817304381643 117777830548895725956572465)
        ·
          refine ⟨88333372911671794467429349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117777830548895725956572465 88333372911671794467429349)
          ·
            refine ⟨16562507420938461462643003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88333372911671794467429349 16562507420938461462643003)
            ·
              refine ⟨24843761131407692193964505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16562507420938461462643003 24843761131407692193964505)
              ·
                refine ⟨18632820848555769145473379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24843761131407692193964505 18632820848555769145473379)
                ·
                  refine ⟨27949231272833653718210069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18632820848555769145473379 27949231272833653718210069)
                  ·
                    refine ⟨1310120215914077518041097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27949231272833653718210069 1310120215914077518041097)
                    ·
                      rfl

theorem cell23_7654350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_7654350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654350 prefixEnd_7654350 := by exact prefixLift 7654350
  have htrace : WordTrace (prefixWord ++ tailWord_7654350) baseStart_7654350 baseEnd_7654350 := by
    simpa [prefixWord, tailWord_7654350, baseEnd_7654350] using wordTrace_append hprefix tailTrace_7654350
  have hstable : (prefixWord ++ tailWord_7654350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654350).length < 2 ^ (prefixWord ++ tailWord_7654350).sum := by decide
  have hdescent : baseEnd_7654350 < baseStart_7654350 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654354 : List Nat := [3, 2, 2, 3, 1, 2, 3, 1, 1, 5]
def baseStart_7654354 : Nat := 118140960795 + 7654354 * 2 ^ 59
def prefixEnd_7654354 : Nat := 4983230072969 + 3 ^ 40 * 7654354 * 2
def baseEnd_7654354 : Nat := 1310120900554950179491091

theorem tailTrace_7654354 : CollatzResearch.WordTrace tailWord_7654354 prefixEnd_7654354 1310120900554950179491091 := by
  unfold tailWord_7654354
  simp only [CollatzResearch.WordTrace]
  refine ⟨69794306427897548108014529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186118150474393461621372077 69794306427897548108014529)
  ·
    refine ⟨52345729820923161081010897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69794306427897548108014529 52345729820923161081010897)
    ·
      refine ⟨39259297365692370810758173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52345729820923161081010897 39259297365692370810758173)
      ·
        refine ⟨14722236512134639054034315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39259297365692370810758173 14722236512134639054034315)
        ·
          refine ⟨22083354768201958581051473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14722236512134639054034315 22083354768201958581051473)
          ·
            refine ⟨16562516076151468935788605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22083354768201958581051473 16562516076151468935788605)
            ·
              refine ⟨6210943528556800850920727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16562516076151468935788605 6210943528556800850920727)
              ·
                refine ⟨9316415292835201276381091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6210943528556800850920727 9316415292835201276381091)
                ·
                  refine ⟨13974622939252801914571637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9316415292835201276381091 13974622939252801914571637)
                  ·
                    refine ⟨1310120900554950179491091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13974622939252801914571637 1310120900554950179491091)
                    ·
                      rfl

theorem cell23_7654354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_7654354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654354 prefixEnd_7654354 := by exact prefixLift 7654354
  have htrace : WordTrace (prefixWord ++ tailWord_7654354) baseStart_7654354 baseEnd_7654354 := by
    simpa [prefixWord, tailWord_7654354, baseEnd_7654354] using wordTrace_append hprefix tailTrace_7654354
  have hstable : (prefixWord ++ tailWord_7654354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654354).length < 2 ^ (prefixWord ++ tailWord_7654354).sum := by decide
  have hdescent : baseEnd_7654354 < baseStart_7654354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654360 : List Nat := [2, 1, 2, 2, 2, 3, 3, 1, 1, 1, 5]
def baseStart_7654360 : Nat := 118140960795 + 7654360 * 2 ^ 59
def prefixEnd_7654360 : Nat := 4983230072969 + 3 ^ 40 * 7654360 * 2
def baseEnd_7654360 : Nat := 3930365782548777514998245

theorem tailTrace_7654360 : CollatzResearch.WordTrace tailWord_7654360 prefixEnd_7654360 3930365782548777514998245 := by
  unfold tailWord_7654360
  simp only [CollatzResearch.WordTrace]
  refine ⟨139588722274784227728388267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186118296366378970304517689 139588722274784227728388267)
  ·
    refine ⟨209383083412176341592582401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139588722274784227728388267 209383083412176341592582401)
    ·
      refine ⟨157037312559132256194436801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209383083412176341592582401 157037312559132256194436801)
      ·
        refine ⟨117777984419349192145827601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157037312559132256194436801 117777984419349192145827601)
        ·
          refine ⟨88333488314511894109370701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117777984419349192145827601 88333488314511894109370701)
          ·
            refine ⟨33125058117941960291014013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88333488314511894109370701 33125058117941960291014013)
            ·
              refine ⟨12421896794228235109130255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33125058117941960291014013 12421896794228235109130255)
              ·
                refine ⟨18632845191342352663695383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12421896794228235109130255 18632845191342352663695383)
                ·
                  refine ⟨27949267787013528995543075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18632845191342352663695383 27949267787013528995543075)
                  ·
                    refine ⟨41923901680520293493314613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27949267787013528995543075 41923901680520293493314613)
                    ·
                      refine ⟨3930365782548777514998245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41923901680520293493314613 3930365782548777514998245)
                      ·
                        rfl

theorem cell23_7654360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 1, 1, 5].length) (baseStart_7654360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654360 prefixEnd_7654360 := by exact prefixLift 7654360
  have htrace : WordTrace (prefixWord ++ tailWord_7654360) baseStart_7654360 baseEnd_7654360 := by
    simpa [prefixWord, tailWord_7654360, baseEnd_7654360] using wordTrace_append hprefix tailTrace_7654360
  have hstable : (prefixWord ++ tailWord_7654360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654360).length < 2 ^ (prefixWord ++ tailWord_7654360).sum := by decide
  have hdescent : baseEnd_7654360 < baseStart_7654360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654393 : List Nat := [1, 2, 1, 3, 1, 3, 1, 2, 2, 7]
def baseStart_7654393 : Nat := 118140960795 + 7654393 * 2 ^ 59
def prefixEnd_7654393 : Nat := 4983230072969 + 3 ^ 40 * 7654393 * 2
def baseEnd_7654393 : Nat := 1310127575803458628628531

theorem tailTrace_7654393 : CollatzResearch.WordTrace tailWord_7654393 prefixEnd_7654393 1310127575803458628628531 := by
  unfold tailWord_7654393
  simp only [CollatzResearch.WordTrace]
  refine ⟨279178648158448902092727833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186119098772299268061818555 279178648158448902092727833)
  ·
    refine ⟨209383986118836676569545875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279178648158448902092727833 209383986118836676569545875)
    ·
      refine ⟨314075979178255014854318813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209383986118836676569545875 314075979178255014854318813)
      ·
        refine ⟨117778492191845630570369555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314075979178255014854318813 117778492191845630570369555)
        ·
          refine ⟨176667738287768445855554333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117778492191845630570369555 176667738287768445855554333)
          ·
            refine ⟨66250401857913167195832875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176667738287768445855554333 66250401857913167195832875)
            ·
              refine ⟨99375602786869750793749313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66250401857913167195832875 99375602786869750793749313)
              ·
                refine ⟨74531702090152313095311985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99375602786869750793749313 74531702090152313095311985)
                ·
                  refine ⟨55898776567614234821483989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74531702090152313095311985 55898776567614234821483989)
                  ·
                    refine ⟨1310127575803458628628531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55898776567614234821483989 1310127575803458628628531)
                    ·
                      rfl

theorem cell23_7654393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 7].length) (baseStart_7654393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654393 prefixEnd_7654393 := by exact prefixLift 7654393
  have htrace : WordTrace (prefixWord ++ tailWord_7654393) baseStart_7654393 baseEnd_7654393 := by
    simpa [prefixWord, tailWord_7654393, baseEnd_7654393] using wordTrace_append hprefix tailTrace_7654393
  have hstable : (prefixWord ++ tailWord_7654393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654393).length < 2 ^ (prefixWord ++ tailWord_7654393).sum := by decide
  have hdescent : baseEnd_7654393 < baseStart_7654393 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654407 : List Nat := [1, 1, 4, 3, 1, 1, 2, 2, 4, 1, 3]
def baseStart_7654407 : Nat := 118140960795 + 7654407 * 2 ^ 59
def prefixEnd_7654407 : Nat := 4983230072969 + 3 ^ 40 * 7654407 * 2
def baseEnd_7654407 : Nat := 3930389916139538831110529

theorem tailTrace_7654407 : CollatzResearch.WordTrace tailWord_7654407 prefixEnd_7654407 3930389916139538831110529 := by
  unfold tailWord_7654407
  simp only [CollatzResearch.WordTrace]
  refine ⟨279179158780398182483737475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186119439186932121655824983 279179158780398182483737475)
  ·
    refine ⟨418768738170597273725606213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279179158780398182483737475 418768738170597273725606213)
    ·
      refine ⟨78519138406986988823551165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 418768738170597273725606213 78519138406986988823551165)
      ·
        refine ⟨29444676902620120808831687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78519138406986988823551165 29444676902620120808831687)
        ·
          refine ⟨44167015353930181213247531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29444676902620120808831687 44167015353930181213247531)
          ·
            refine ⟨66250523030895271819871297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44167015353930181213247531 66250523030895271819871297)
            ·
              refine ⟨49687892273171453864903473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66250523030895271819871297 49687892273171453864903473)
              ·
                refine ⟨37265919204878590398677605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49687892273171453864903473 37265919204878590398677605)
                ·
                  refine ⟨6987359850914735699752051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37265919204878590398677605 6987359850914735699752051)
                  ·
                    refine ⟨10481039776372103549628077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6987359850914735699752051 10481039776372103549628077)
                    ·
                      refine ⟨3930389916139538831110529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10481039776372103549628077 3930389916139538831110529)
                      ·
                        rfl

theorem cell23_7654407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_7654407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654407 prefixEnd_7654407 := by exact prefixLift 7654407
  have htrace : WordTrace (prefixWord ++ tailWord_7654407) baseStart_7654407 baseEnd_7654407 := by
    simpa [prefixWord, tailWord_7654407, baseEnd_7654407] using wordTrace_append hprefix tailTrace_7654407
  have hstable : (prefixWord ++ tailWord_7654407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654407).length < 2 ^ (prefixWord ++ tailWord_7654407).sum := by decide
  have hdescent : baseEnd_7654407 < baseStart_7654407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654424 : List Nat := [2, 1, 2, 3, 2, 2, 3, 2, 2, 1, 3]
def baseStart_7654424 : Nat := 118140960795 + 7654424 * 2 ^ 59
def prefixEnd_7654424 : Nat := 4983230072969 + 3 ^ 40 * 7654424 * 2
def baseEnd_7654424 : Nat := 3930398645310665264597951

theorem tailTrace_7654424 : CollatzResearch.WordTrace tailWord_7654424 prefixEnd_7654424 3930398645310665264597951 := by
  unfold tailWord_7654424
  simp only [CollatzResearch.WordTrace]
  refine ⟨139589889410668297193553163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186119852547557729591404217 139589889410668297193553163)
  ·
    refine ⟨209384834116002445790329745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139589889410668297193553163 209384834116002445790329745)
    ·
      refine ⟨157038625587001834342747309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209384834116002445790329745 157038625587001834342747309)
      ·
        refine ⟨58889484595125687878530241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157038625587001834342747309 58889484595125687878530241)
        ·
          refine ⟨44167113446344265908897681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58889484595125687878530241 44167113446344265908897681)
          ·
            refine ⟨33125335084758199431673261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44167113446344265908897681 33125335084758199431673261)
            ·
              refine ⟨12422000656784324786877473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33125335084758199431673261 12422000656784324786877473)
              ·
                refine ⟨9316500492588243590158105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12422000656784324786877473 9316500492588243590158105)
                ·
                  refine ⟨6987375369441182692618579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9316500492588243590158105 6987375369441182692618579)
                  ·
                    refine ⟨10481063054161774038927869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6987375369441182692618579 10481063054161774038927869)
                    ·
                      refine ⟨3930398645310665264597951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10481063054161774038927869 3930398645310665264597951)
                      ·
                        rfl

theorem cell23_7654424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_7654424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654424 prefixEnd_7654424 := by exact prefixLift 7654424
  have htrace : WordTrace (prefixWord ++ tailWord_7654424) baseStart_7654424 baseEnd_7654424 := by
    simpa [prefixWord, tailWord_7654424, baseEnd_7654424] using wordTrace_append hprefix tailTrace_7654424
  have hstable : (prefixWord ++ tailWord_7654424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654424).length < 2 ^ (prefixWord ++ tailWord_7654424).sum := by decide
  have hdescent : baseEnd_7654424 < baseStart_7654424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654450 : List Nat := [3, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5]
def baseStart_7654450 : Nat := 118140960795 + 7654450 * 2 ^ 59
def prefixEnd_7654450 : Nat := 4983230072969 + 3 ^ 40 * 7654450 * 2
def baseEnd_7654450 : Nat := 3930411995807682162872831

theorem tailTrace_7654450 : CollatzResearch.WordTrace tailWord_7654450 prefixEnd_7654450 3930411995807682162872831 := by
  unfold tailWord_7654450
  simp only [CollatzResearch.WordTrace]
  refine ⟨69795181779810600206888201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186120484746161600551701869 69795181779810600206888201)
  ·
    refine ⟨52346386334857950155166151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69795181779810600206888201 52346386334857950155166151)
    ·
      refine ⟨78519579502286925232749227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52346386334857950155166151 78519579502286925232749227)
      ·
        refine ⟨117779369253430387849123841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78519579502286925232749227 117779369253430387849123841)
        ·
          refine ⟨88334526940072790886842881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117779369253430387849123841 88334526940072790886842881)
          ·
            refine ⟨66250895205054593165132161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88334526940072790886842881 66250895205054593165132161)
            ·
              refine ⟨49688171403790944873849121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66250895205054593165132161 49688171403790944873849121)
              ·
                refine ⟨37266128552843208655386841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49688171403790944873849121 37266128552843208655386841)
                ·
                  refine ⟨27949596414632406491540131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37266128552843208655386841 27949596414632406491540131)
                  ·
                    refine ⟨41924394621948609737310197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27949596414632406491540131 41924394621948609737310197)
                    ·
                      refine ⟨3930411995807682162872831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41924394621948609737310197 3930411995807682162872831)
                      ·
                        rfl

theorem cell23_7654450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_7654450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654450 prefixEnd_7654450 := by exact prefixLift 7654450
  have htrace : WordTrace (prefixWord ++ tailWord_7654450) baseStart_7654450 baseEnd_7654450 := by
    simpa [prefixWord, tailWord_7654450, baseEnd_7654450] using wordTrace_append hprefix tailTrace_7654450
  have hstable : (prefixWord ++ tailWord_7654450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654450).length < 2 ^ (prefixWord ++ tailWord_7654450).sum := by decide
  have hdescent : baseEnd_7654450 < baseStart_7654450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654480 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 3]
def baseStart_7654480 : Nat := 118140960795 + 7654480 * 2 ^ 59
def prefixEnd_7654480 : Nat := 4983230072969 + 3 ^ 40 * 7654480 * 2
def baseEnd_7654480 : Nat := 3930427400227317045497693

theorem tailTrace_7654480 : CollatzResearch.WordTrace tailWord_7654480 prefixEnd_7654480 3930427400227317045497693 := by
  unfold tailWord_7654480
  simp only [CollatzResearch.WordTrace]
  refine ⟨139590910654566857975572447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186121214206089143967429929 139590910654566857975572447)
  ·
    refine ⟨209386365981850286963358671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139590910654566857975572447 209386365981850286963358671)
    ·
      refine ⟨314079548972775430445038007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209386365981850286963358671 314079548972775430445038007)
      ·
        refine ⟨471119323459163145667557011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314079548972775430445038007 471119323459163145667557011)
        ·
          refine ⟨706678985188744718501335517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471119323459163145667557011 706678985188744718501335517)
          ·
            refine ⟨265004619445779269438000819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 706678985188744718501335517 265004619445779269438000819)
            ·
              refine ⟨397506929168668904157001229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265004619445779269438000819 397506929168668904157001229)
              ·
                refine ⟨149065098438250839058875461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 397506929168668904157001229 149065098438250839058875461)
                ·
                  refine ⟨27949705957172032323539149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149065098438250839058875461 27949705957172032323539149)
                  ·
                    refine ⟨10481139733939512121327181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27949705957172032323539149 10481139733939512121327181)
                    ·
                      refine ⟨3930427400227317045497693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10481139733939512121327181 3930427400227317045497693)
                      ·
                        rfl

theorem cell23_7654480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 3].length) (baseStart_7654480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654480 prefixEnd_7654480 := by exact prefixLift 7654480
  have htrace : WordTrace (prefixWord ++ tailWord_7654480) baseStart_7654480 baseEnd_7654480 := by
    simpa [prefixWord, tailWord_7654480, baseEnd_7654480] using wordTrace_append hprefix tailTrace_7654480
  have hstable : (prefixWord ++ tailWord_7654480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654480).length < 2 ^ (prefixWord ++ tailWord_7654480).sum := by decide
  have hdescent : baseEnd_7654480 < baseStart_7654480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654498 : List Nat := [3, 3, 2, 2, 1, 2, 1, 3, 2, 2, 2]
def baseStart_7654498 : Nat := 118140960795 + 7654498 * 2 ^ 59
def prefixEnd_7654498 : Nat := 4983230072969 + 3 ^ 40 * 7654498 * 2
def baseEnd_7654498 : Nat := 3930436642879097975072611

theorem tailTrace_7654498 : CollatzResearch.WordTrace tailWord_7654498 prefixEnd_7654498 3930436642879097975072611 := by
  unfold tailWord_7654498
  simp only [CollatzResearch.WordTrace]
  refine ⟨69795619455767126256325037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186121651882045670016866765 69795619455767126256325037)
  ·
    refine ⟨26173357295912672346121889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69795619455767126256325037 26173357295912672346121889)
    ·
      refine ⟨19630017971934504259591417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26173357295912672346121889 19630017971934504259591417)
      ·
        refine ⟨14722513478950878194693563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19630017971934504259591417 14722513478950878194693563)
        ·
          refine ⟨22083770218426317292040345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14722513478950878194693563 22083770218426317292040345)
          ·
            refine ⟨16562827663819737969030259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22083770218426317292040345 16562827663819737969030259)
            ·
              refine ⟨24844241495729606953545389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16562827663819737969030259 24844241495729606953545389)
              ·
                refine ⟨9316590560898602607579521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24844241495729606953545389 9316590560898602607579521)
                ·
                  refine ⟨6987442920673951955684641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9316590560898602607579521 6987442920673951955684641)
                  ·
                    refine ⟨5240582190505463966763481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6987442920673951955684641 5240582190505463966763481)
                    ·
                      refine ⟨3930436642879097975072611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5240582190505463966763481 3930436642879097975072611)
                      ·
                        rfl

theorem cell23_7654498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_7654498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654498 prefixEnd_7654498 := by exact prefixLift 7654498
  have htrace : WordTrace (prefixWord ++ tailWord_7654498) baseStart_7654498 baseEnd_7654498 := by
    simpa [prefixWord, tailWord_7654498, baseEnd_7654498] using wordTrace_append hprefix tailTrace_7654498
  have hstable : (prefixWord ++ tailWord_7654498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654498).length < 2 ^ (prefixWord ++ tailWord_7654498).sum := by decide
  have hdescent : baseEnd_7654498 < baseStart_7654498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654500 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 6, 5]
def baseStart_7654500 : Nat := 118140960795 + 7654500 * 2 ^ 59
def prefixEnd_7654500 : Nat := 4983230072969 + 3 ^ 40 * 7654500 * 2
def baseEnd_7654500 : Nat := 1310145889946802322415867

theorem tailTrace_7654500 : CollatzResearch.WordTrace tailWord_7654500 prefixEnd_7654500 1310145889946802322415867 := by
  unfold tailWord_7654500
  simp only [CollatzResearch.WordTrace]
  refine ⟨139591275384530629683436477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186121700512707506244581969 139591275384530629683436477)
  ·
    refine ⟨52346728269198986131288679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139591275384530629683436477 52346728269198986131288679)
    ·
      refine ⟨78520092403798479196933019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52346728269198986131288679 78520092403798479196933019)
      ·
        refine ⟨117780138605697718795399529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78520092403798479196933019 117780138605697718795399529)
        ·
          refine ⟨88335103954273289096549647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117780138605697718795399529 88335103954273289096549647)
          ·
            refine ⟨132502655931409933644824471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88335103954273289096549647 132502655931409933644824471)
            ·
              refine ⟨198753983897114900467236707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132502655931409933644824471 198753983897114900467236707)
              ·
                refine ⟨298130975845672350700855061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198753983897114900467236707 298130975845672350700855061)
                ·
                  refine ⟨13974889492765891439102581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 298130975845672350700855061 13974889492765891439102581)
                  ·
                    refine ⟨1310145889946802322415867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13974889492765891439102581 1310145889946802322415867)
                    ·
                      rfl

theorem cell23_7654500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_7654500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654500 prefixEnd_7654500 := by exact prefixLift 7654500
  have htrace : WordTrace (prefixWord ++ tailWord_7654500) baseStart_7654500 baseEnd_7654500 := by
    simpa [prefixWord, tailWord_7654500, baseEnd_7654500] using wordTrace_append hprefix tailTrace_7654500
  have hstable : (prefixWord ++ tailWord_7654500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654500).length < 2 ^ (prefixWord ++ tailWord_7654500).sum := by decide
  have hdescent : baseEnd_7654500 < baseStart_7654500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654520 : List Nat := [2, 1, 2, 1, 1, 1, 4, 3, 1, 3, 4]
def baseStart_7654520 : Nat := 118140960795 + 7654520 * 2 ^ 59
def prefixEnd_7654520 : Nat := 4983230072969 + 3 ^ 40 * 7654520 * 2
def baseEnd_7654520 : Nat := 3930447939453496888997509

theorem tailTrace_7654520 : CollatzResearch.WordTrace tailWord_7654520 prefixEnd_7654520 3930447939453496888997509 := by
  unfold tailWord_7654520
  simp only [CollatzResearch.WordTrace]
  refine ⟨139591640114494401391300507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186122186819325868521734009 139591640114494401391300507)
  ·
    refine ⟨209387460171741602086950761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139591640114494401391300507 209387460171741602086950761)
    ·
      refine ⟨157040595128806201565213071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209387460171741602086950761 157040595128806201565213071)
      ·
        refine ⟨235560892693209302347819607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157040595128806201565213071 235560892693209302347819607)
        ·
          refine ⟨353341339039813953521729411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235560892693209302347819607 353341339039813953521729411)
          ·
            refine ⟨530012008559720930282594117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353341339039813953521729411 530012008559720930282594117)
            ·
              refine ⟨99377251604947674427986397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 530012008559720930282594117 99377251604947674427986397)
              ·
                refine ⟨37266469351855377910494899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99377251604947674427986397 37266469351855377910494899)
                ·
                  refine ⟨55899704027783066865742349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37266469351855377910494899 55899704027783066865742349)
                  ·
                    refine ⟨20962389010418650074653381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55899704027783066865742349 20962389010418650074653381)
                    ·
                      refine ⟨3930447939453496888997509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20962389010418650074653381 3930447939453496888997509)
                      ·
                        rfl

theorem cell23_7654520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 1, 3, 4].length) (baseStart_7654520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654520 prefixEnd_7654520 := by exact prefixLift 7654520
  have htrace : WordTrace (prefixWord ++ tailWord_7654520) baseStart_7654520 baseEnd_7654520 := by
    simpa [prefixWord, tailWord_7654520, baseEnd_7654520] using wordTrace_append hprefix tailTrace_7654520
  have hstable : (prefixWord ++ tailWord_7654520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654520).length < 2 ^ (prefixWord ++ tailWord_7654520).sum := by decide
  have hdescent : baseEnd_7654520 < baseStart_7654520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654537 : List Nat := [1, 2, 1, 1, 4, 3, 2, 2, 2, 1, 4]
def baseStart_7654537 : Nat := 118140960795 + 7654537 * 2 ^ 59
def prefixEnd_7654537 : Nat := 4983230072969 + 3 ^ 40 * 7654537 * 2
def baseEnd_7654537 : Nat := 3930456668624623322484931

theorem tailTrace_7654537 : CollatzResearch.WordTrace tailWord_7654537 prefixEnd_7654537 3930456668624623322484931 := by
  unfold tailWord_7654537
  simp only [CollatzResearch.WordTrace]
  refine ⟨279183900269927214685969865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186122600179951476457313243 279183900269927214685969865)
  ·
    refine ⟨209387925202445411014477399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279183900269927214685969865 209387925202445411014477399)
    ·
      refine ⟨314081887803668116521716099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209387925202445411014477399 314081887803668116521716099)
      ·
        refine ⟨471122831705502174782574149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314081887803668116521716099 471122831705502174782574149)
        ·
          refine ⟨88335530944781657771732653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 471122831705502174782574149 88335530944781657771732653)
          ·
            refine ⟨33125824104293121664399745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88335530944781657771732653 33125824104293121664399745)
            ·
              refine ⟨24844368078219841248299809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33125824104293121664399745 24844368078219841248299809)
              ·
                refine ⟨18633276058664880936224857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24844368078219841248299809 18633276058664880936224857)
                ·
                  refine ⟨13974957043998660702168643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18633276058664880936224857 13974957043998660702168643)
                  ·
                    refine ⟨20962435565997991053252965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13974957043998660702168643 20962435565997991053252965)
                    ·
                      refine ⟨3930456668624623322484931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20962435565997991053252965 3930456668624623322484931)
                      ·
                        rfl

theorem cell23_7654537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 2, 1, 4].length) (baseStart_7654537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654537 prefixEnd_7654537 := by exact prefixLift 7654537
  have htrace : WordTrace (prefixWord ++ tailWord_7654537) baseStart_7654537 baseEnd_7654537 := by
    simpa [prefixWord, tailWord_7654537, baseEnd_7654537] using wordTrace_append hprefix tailTrace_7654537
  have hstable : (prefixWord ++ tailWord_7654537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654537).length < 2 ^ (prefixWord ++ tailWord_7654537).sum := by decide
  have hdescent : baseEnd_7654537 < baseStart_7654537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654554 : List Nat := [3, 1, 1, 5, 1, 1, 1, 1, 1, 6, 2]
def baseStart_7654554 : Nat := 118140960795 + 7654554 * 2 ^ 59
def prefixEnd_7654554 : Nat := 4983230072969 + 3 ^ 40 * 7654554 * 2
def baseEnd_7654554 : Nat := 3930465397795749755972353

theorem tailTrace_7654554 : CollatzResearch.WordTrace tailWord_7654554 prefixEnd_7654554 3930465397795749755972353 := by
  unfold tailWord_7654554
  simp only [CollatzResearch.WordTrace]
  refine ⟨69796130077716406647334679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186123013540577084392892477 69796130077716406647334679)
  ·
    refine ⟨104694195116574609971002019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69796130077716406647334679 104694195116574609971002019)
    ·
      refine ⟨157041292674861914956503029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104694195116574609971002019 157041292674861914956503029)
      ·
        refine ⟨14722621188268304527172159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 157041292674861914956503029 14722621188268304527172159)
        ·
          refine ⟨22083931782402456790758239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14722621188268304527172159 22083931782402456790758239)
          ·
            refine ⟨33125897673603685186137359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22083931782402456790758239 33125897673603685186137359)
            ·
              refine ⟨49688846510405527779206039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33125897673603685186137359 49688846510405527779206039)
              ·
                refine ⟨74533269765608291668809059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49688846510405527779206039 74533269765608291668809059)
                ·
                  refine ⟨111799904648412437503213589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74533269765608291668809059 111799904648412437503213589)
                  ·
                    refine ⟨5240620530394333007963137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 111799904648412437503213589 5240620530394333007963137)
                    ·
                      refine ⟨3930465397795749755972353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5240620530394333007963137 3930465397795749755972353)
                      ·
                        rfl

theorem cell23_7654554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_7654554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654554 prefixEnd_7654554 := by exact prefixLift 7654554
  have htrace : WordTrace (prefixWord ++ tailWord_7654554) baseStart_7654554 baseEnd_7654554 := by
    simpa [prefixWord, tailWord_7654554, baseEnd_7654554] using wordTrace_append hprefix tailTrace_7654554
  have hstable : (prefixWord ++ tailWord_7654554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654554).length < 2 ^ (prefixWord ++ tailWord_7654554).sum := by decide
  have hdescent : baseEnd_7654554 < baseStart_7654554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654557 : List Nat := [1, 4, 2, 1, 1, 2, 2, 2, 1, 4, 3]
def baseStart_7654557 : Nat := 118140960795 + 7654557 * 2 ^ 59
def prefixEnd_7654557 : Nat := 4983230072969 + 3 ^ 40 * 7654557 * 2
def baseEnd_7654557 : Nat := 3930466938237713244234839

theorem tailTrace_7654557 : CollatzResearch.WordTrace tailWord_7654557 prefixEnd_7654557 3930466938237713244234839 := by
  unfold tailWord_7654557
  simp only [CollatzResearch.WordTrace]
  refine ⟨279184629729854758101697925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186123086486569838734465283 279184629729854758101697925)
  ·
    refine ⟨52347118074347767144068361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 279184629729854758101697925 52347118074347767144068361)
    ·
      refine ⟨39260338555760825358051271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52347118074347767144068361 39260338555760825358051271)
      ·
        refine ⟨58890507833641238037076907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39260338555760825358051271 58890507833641238037076907)
        ·
          refine ⟨88335761750461857055615361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58890507833641238037076907 88335761750461857055615361)
          ·
            refine ⟨66251821312846392791711521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88335761750461857055615361 66251821312846392791711521)
            ·
              refine ⟨49688865984634794593783641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66251821312846392791711521 49688865984634794593783641)
              ·
                refine ⟨37266649488476095945337731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49688865984634794593783641 37266649488476095945337731)
                ·
                  refine ⟨55899974232714143918006597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37266649488476095945337731 55899974232714143918006597)
                  ·
                    refine ⟨10481245168633901984626237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55899974232714143918006597 10481245168633901984626237)
                    ·
                      refine ⟨3930466938237713244234839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10481245168633901984626237 3930466938237713244234839)
                      ·
                        rfl

theorem cell23_7654557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_7654557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654557 prefixEnd_7654557 := by exact prefixLift 7654557
  have htrace : WordTrace (prefixWord ++ tailWord_7654557) baseStart_7654557 baseEnd_7654557 := by
    simpa [prefixWord, tailWord_7654557, baseEnd_7654557] using wordTrace_append hprefix tailTrace_7654557
  have hstable : (prefixWord ++ tailWord_7654557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654557).length < 2 ^ (prefixWord ++ tailWord_7654557).sum := by decide
  have hdescent : baseEnd_7654557 < baseStart_7654557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654564 : List Nat := [2, 3, 1, 2, 3, 2, 1, 2, 3, 4]
def baseStart_7654564 : Nat := 118140960795 + 7654564 * 2 ^ 59
def prefixEnd_7654564 : Nat := 4983230072969 + 3 ^ 40 * 7654564 * 2
def baseEnd_7654564 : Nat := 1310156844200764905615769

theorem tailTrace_7654564 : CollatzResearch.WordTrace tailWord_7654564 prefixEnd_7654564 1310156844200764905615769 := by
  unfold tailWord_7654564
  simp only [CollatzResearch.WordTrace]
  refine ⟨139592442520414699148601373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186123256693886265531468497 139592442520414699148601373)
  ·
    refine ⟨52347165945155512180725515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139592442520414699148601373 52347165945155512180725515)
    ·
      refine ⟨78520748917733268271088273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52347165945155512180725515 78520748917733268271088273)
      ·
        refine ⟨58890561688299951203316205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78520748917733268271088273 58890561688299951203316205)
        ·
          refine ⟨22083960633112481701243577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58890561688299951203316205 22083960633112481701243577)
          ·
            refine ⟨16562970474834361275932683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22083960633112481701243577 16562970474834361275932683)
            ·
              refine ⟨24844455712251541913899025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16562970474834361275932683 24844455712251541913899025)
              ·
                refine ⟨18633341784188656435424269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24844455712251541913899025 18633341784188656435424269)
                ·
                  refine ⟨6987503169070746163284101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18633341784188656435424269 6987503169070746163284101)
                  ·
                    refine ⟨1310156844200764905615769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6987503169070746163284101 1310156844200764905615769)
                    ·
                      rfl

theorem cell23_7654564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 3, 4].length) (baseStart_7654564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654564 prefixEnd_7654564 := by exact prefixLift 7654564
  have htrace : WordTrace (prefixWord ++ tailWord_7654564) baseStart_7654564 baseEnd_7654564 := by
    simpa [prefixWord, tailWord_7654564, baseEnd_7654564] using wordTrace_append hprefix tailTrace_7654564
  have hstable : (prefixWord ++ tailWord_7654564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654564).length < 2 ^ (prefixWord ++ tailWord_7654564).sum := by decide
  have hdescent : baseEnd_7654564 < baseStart_7654564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654624 : List Nat := [2, 1, 1, 3, 1, 5, 2, 2, 1, 5]
def baseStart_7654624 : Nat := 118140960795 + 7654624 * 2 ^ 59
def prefixEnd_7654624 : Nat := 4983230072969 + 3 ^ 40 * 7654624 * 2
def baseEnd_7654624 : Nat := 1310167113813854827365677

theorem tailTrace_7654624 : CollatzResearch.WordTrace tailWord_7654624 prefixEnd_7654624 1310167113813854827365677 := by
  unfold tailWord_7654624
  simp only [CollatzResearch.WordTrace]
  refine ⟨139593536710306014272193463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186124715613741352362924617 139593536710306014272193463)
  ·
    refine ⟨209390305065459021408290195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139593536710306014272193463 209390305065459021408290195)
    ·
      refine ⟨314085457598188532112435293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209390305065459021408290195 314085457598188532112435293)
      ·
        refine ⟨117782046599320699542163235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314085457598188532112435293 117782046599320699542163235)
        ·
          refine ⟨176673069898981049313244853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117782046599320699542163235 176673069898981049313244853)
          ·
            refine ⟨16563100303029473373116705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 176673069898981049313244853 16563100303029473373116705)
            ·
              refine ⟨12422325227272105029837529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16563100303029473373116705 12422325227272105029837529)
              ·
                refine ⟨9316743920454078772378147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12422325227272105029837529 9316743920454078772378147)
                ·
                  refine ⟨13975115880681118158567221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9316743920454078772378147 13975115880681118158567221)
                  ·
                    refine ⟨1310167113813854827365677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13975115880681118158567221 1310167113813854827365677)
                    ·
                      rfl

theorem cell23_7654624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 2, 1, 5].length) (baseStart_7654624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654624 prefixEnd_7654624 := by exact prefixLift 7654624
  have htrace : WordTrace (prefixWord ++ tailWord_7654624) baseStart_7654624 baseEnd_7654624 := by
    simpa [prefixWord, tailWord_7654624, baseEnd_7654624] using wordTrace_append hprefix tailTrace_7654624
  have hstable : (prefixWord ++ tailWord_7654624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654624).length < 2 ^ (prefixWord ++ tailWord_7654624).sum := by decide
  have hdescent : baseEnd_7654624 < baseStart_7654624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654638 : List Nat := [4, 1, 2, 1, 1, 1, 5, 3, 1, 1, 3]
def baseStart_7654638 : Nat := 118140960795 + 7654638 * 2 ^ 59
def prefixEnd_7654638 : Nat := 4983230072969 + 3 ^ 40 * 7654638 * 2
def baseEnd_7654638 : Nat := 3930508530170727427321967

theorem tailTrace_7654638 : CollatzResearch.WordTrace tailWord_7654638 prefixEnd_7654638 3930508530170727427321967 := by
  unfold tailWord_7654638
  simp only [CollatzResearch.WordTrace]
  refine ⟨34898448005320163616924571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186125056028374205956931045 34898448005320163616924571)
  ·
    refine ⟨52347672007980245425386857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34898448005320163616924571 52347672007980245425386857)
    ·
      refine ⟨39260754005985184069040143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52347672007980245425386857 39260754005985184069040143)
      ·
        refine ⟨58891131008977776103560215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39260754005985184069040143 58891131008977776103560215)
        ·
          refine ⟨88336696513466664155340323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58891131008977776103560215 88336696513466664155340323)
          ·
            refine ⟨132505044770199996233010485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88336696513466664155340323 132505044770199996233010485)
            ·
              refine ⟨12422347947206249646844733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132505044770199996233010485 12422347947206249646844733)
              ·
                refine ⟨4658380480202343617566775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12422347947206249646844733 4658380480202343617566775)
                ·
                  refine ⟨6987570720303515426350163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4658380480202343617566775 6987570720303515426350163)
                  ·
                    refine ⟨10481356080455273139525245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6987570720303515426350163 10481356080455273139525245)
                    ·
                      refine ⟨3930508530170727427321967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10481356080455273139525245 3930508530170727427321967)
                      ·
                        rfl

theorem cell23_7654638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 3, 1, 1, 3].length) (baseStart_7654638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654638 prefixEnd_7654638 := by exact prefixLift 7654638
  have htrace : WordTrace (prefixWord ++ tailWord_7654638) baseStart_7654638 baseEnd_7654638 := by
    simpa [prefixWord, tailWord_7654638, baseEnd_7654638] using wordTrace_append hprefix tailTrace_7654638
  have hstable : (prefixWord ++ tailWord_7654638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654638).length < 2 ^ (prefixWord ++ tailWord_7654638).sum := by decide
  have hdescent : baseEnd_7654638 < baseStart_7654638 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654657 : List Nat := [1, 2, 4, 1, 1, 3, 1, 2, 1, 1, 6]
def baseStart_7654657 : Nat := 118140960795 + 7654657 * 2 ^ 59
def prefixEnd_7654657 : Nat := 4983230072969 + 3 ^ 40 * 7654657 * 2
def baseEnd_7654657 : Nat := 3930518286303162852984379

theorem tailTrace_7654657 : CollatzResearch.WordTrace tailWord_7654657 prefixEnd_7654657 3930518286303162852984379 := by
  unfold tailWord_7654657
  simp only [CollatzResearch.WordTrace]
  refine ⟨279188277029492475180338225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186125518019661650120225483 279188277029492475180338225)
  ·
    refine ⟨209391207772119356385253669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279188277029492475180338225 209391207772119356385253669)
    ·
      refine ⟨39260851457272379322235063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209391207772119356385253669 39260851457272379322235063)
      ·
        refine ⟨58891277185908568983352595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39260851457272379322235063 58891277185908568983352595)
        ·
          refine ⟨88336915778862853475028893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58891277185908568983352595 88336915778862853475028893)
          ·
            refine ⟨33126343417073570053135835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88336915778862853475028893 33126343417073570053135835)
            ·
              refine ⟨49689515125610355079703753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33126343417073570053135835 49689515125610355079703753)
              ·
                refine ⟨37267136344207766309777815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49689515125610355079703753 37267136344207766309777815)
                ·
                  refine ⟨55900704516311649464666723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37267136344207766309777815 55900704516311649464666723)
                  ·
                    refine ⟨83851056774467474197000085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55900704516311649464666723 83851056774467474197000085)
                    ·
                      refine ⟨3930518286303162852984379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83851056774467474197000085 3930518286303162852984379)
                      ·
                        rfl

theorem cell23_7654657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_7654657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654657 prefixEnd_7654657 := by exact prefixLift 7654657
  have htrace : WordTrace (prefixWord ++ tailWord_7654657) baseStart_7654657 baseEnd_7654657 := by
    simpa [prefixWord, tailWord_7654657, baseEnd_7654657] using wordTrace_append hprefix tailTrace_7654657
  have hstable : (prefixWord ++ tailWord_7654657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654657).length < 2 ^ (prefixWord ++ tailWord_7654657).sum := by decide
  have hdescent : baseEnd_7654657 < baseStart_7654657 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654667 : List Nat := [1, 1, 1, 1, 5, 4, 2, 8]
def baseStart_7654667 : Nat := 118140960795 + 7654667 * 2 ^ 59
def prefixEnd_7654667 : Nat := 4983230072969 + 3 ^ 40 * 7654667 * 2
def baseEnd_7654667 : Nat := 145574941522581770883679

theorem tailTrace_7654667 : CollatzResearch.WordTrace tailWord_7654667 prefixEnd_7654667 145574941522581770883679 := by
  unfold tailWord_7654667
  simp only [CollatzResearch.WordTrace]
  refine ⟨279188641759456246888202255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186125761172970831258801503 279188641759456246888202255)
  ·
    refine ⟨418782962639184370332303383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279188641759456246888202255 418782962639184370332303383)
    ·
      refine ⟨628174443958776555498455075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418782962639184370332303383 628174443958776555498455075)
      ·
        refine ⟨942261665938164833247682613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 628174443958776555498455075 942261665938164833247682613)
        ·
          refine ⟨88337031181702953116970245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 942261665938164833247682613 88337031181702953116970245)
          ·
            refine ⟨16563193346569303709431921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88337031181702953116970245 16563193346569303709431921)
            ·
              refine ⟨12422395009926977782073941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16563193346569303709431921 12422395009926977782073941)
              ·
                refine ⟨145574941522581770883679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12422395009926977782073941 145574941522581770883679)
                ·
                  rfl

theorem cell23_7654667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 8].length) (baseStart_7654667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654667 prefixEnd_7654667 := by exact prefixLift 7654667
  have htrace : WordTrace (prefixWord ++ tailWord_7654667) baseStart_7654667 baseEnd_7654667 := by
    simpa [prefixWord, tailWord_7654667, baseEnd_7654667] using wordTrace_append hprefix tailTrace_7654667
  have hstable : (prefixWord ++ tailWord_7654667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654667).length < 2 ^ (prefixWord ++ tailWord_7654667).sum := by decide
  have hdescent : baseEnd_7654667 < baseStart_7654667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654727 : List Nat := [1, 1, 4, 1, 2, 3, 1, 1, 1, 8]
def baseStart_7654727 : Nat := 118140960795 + 7654727 * 2 ^ 59
def prefixEnd_7654727 : Nat := 4983230072969 + 3 ^ 40 * 7654727 * 2
def baseEnd_7654727 : Nat := 1310184743316325859703019

theorem tailTrace_7654727 : CollatzResearch.WordTrace tailWord_7654727 prefixEnd_7654727 1310184743316325859703019 := by
  unfold tailWord_7654727
  simp only [CollatzResearch.WordTrace]
  refine ⟨279190830139238877135386435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186127220092825918090257623 279190830139238877135386435)
  ·
    refine ⟨418786245208858315703079653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279190830139238877135386435 418786245208858315703079653)
    ·
      refine ⟨78522420976660934194327435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 418786245208858315703079653 78522420976660934194327435)
      ·
        refine ⟨117783631464991401291491153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78522420976660934194327435 117783631464991401291491153)
        ·
          refine ⟨88337723598743550968618365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117783631464991401291491153 88337723598743550968618365)
          ·
            refine ⟨33126646349528831613231887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88337723598743550968618365 33126646349528831613231887)
            ·
              refine ⟨49689969524293247419847831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33126646349528831613231887 49689969524293247419847831)
              ·
                refine ⟨74534954286439871129771747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49689969524293247419847831 74534954286439871129771747)
                ·
                  refine ⟨111802431429659806694657621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74534954286439871129771747 111802431429659806694657621)
                  ·
                    refine ⟨1310184743316325859703019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 111802431429659806694657621 1310184743316325859703019)
                    ·
                      rfl

theorem cell23_7654727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_7654727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654727 prefixEnd_7654727 := by exact prefixLift 7654727
  have htrace : WordTrace (prefixWord ++ tailWord_7654727) baseStart_7654727 baseEnd_7654727 := by
    simpa [prefixWord, tailWord_7654727, baseEnd_7654727] using wordTrace_append hprefix tailTrace_7654727
  have hstable : (prefixWord ++ tailWord_7654727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654727).length < 2 ^ (prefixWord ++ tailWord_7654727).sum := by decide
  have hdescent : baseEnd_7654727 < baseStart_7654727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654749 : List Nat := [1, 4, 5, 1, 1, 2, 2, 1, 1, 2, 3]
def baseStart_7654749 : Nat := 118140960795 + 7654749 * 2 ^ 59
def prefixEnd_7654749 : Nat := 4983230072969 + 3 ^ 40 * 7654749 * 2
def baseEnd_7654749 : Nat := 3930565526523376493033957

theorem tailTrace_7654749 : CollatzResearch.WordTrace tailWord_7654749 prefixEnd_7654749 3930565526523376493033957 := by
  unfold tailWord_7654749
  simp only [CollatzResearch.WordTrace]
  refine ⟨279191632545159174892687301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186127755030106116595124867 279191632545159174892687301)
  ·
    refine ⟨52348431102217345292378869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 279191632545159174892687301 52348431102217345292378869)
    ·
      refine ⟨4907665415832876121160519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52348431102217345292378869 4907665415832876121160519)
      ·
        refine ⟨7361498123749314181740779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4907665415832876121160519 7361498123749314181740779)
        ·
          refine ⟨11042247185623971272611169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7361498123749314181740779 11042247185623971272611169)
          ·
            refine ⟨8281685389217978454458377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11042247185623971272611169 8281685389217978454458377)
            ·
              refine ⟨6211264041913483840843783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8281685389217978454458377 6211264041913483840843783)
              ·
                refine ⟨9316896062870225761265675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6211264041913483840843783 9316896062870225761265675)
                ·
                  refine ⟨13975344094305338641898513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9316896062870225761265675 13975344094305338641898513)
                  ·
                    refine ⟨10481508070729003981423885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13975344094305338641898513 10481508070729003981423885)
                    ·
                      refine ⟨3930565526523376493033957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10481508070729003981423885 3930565526523376493033957)
                      ·
                        rfl

theorem cell23_7654749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_7654749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654749 prefixEnd_7654749 := by exact prefixLift 7654749
  have htrace : WordTrace (prefixWord ++ tailWord_7654749) baseStart_7654749 baseEnd_7654749 := by
    simpa [prefixWord, tailWord_7654749, baseEnd_7654749] using wordTrace_append hprefix tailTrace_7654749
  have hstable : (prefixWord ++ tailWord_7654749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654749).length < 2 ^ (prefixWord ++ tailWord_7654749).sum := by decide
  have hdescent : baseEnd_7654749 < baseStart_7654749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654751 : List Nat := [1, 1, 2, 3, 1, 2, 1, 4, 4, 2, 2]
def baseStart_7654751 : Nat := 118140960795 + 7654751 * 2 ^ 59
def prefixEnd_7654751 : Nat := 4983230072969 + 3 ^ 40 * 7654751 * 2
def baseEnd_7654751 : Nat := 3930566553484685485208947

theorem tailTrace_7654751 : CollatzResearch.WordTrace tailWord_7654751 prefixEnd_7654751 3930566553484685485208947 := by
  unfold tailWord_7654751
  simp only [CollatzResearch.WordTrace]
  refine ⟨279191705491151929234260107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186127803660767952822840071 279191705491151929234260107)
  ·
    refine ⟨418787558236727893851390161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279191705491151929234260107 418787558236727893851390161)
    ·
      refine ⟨314090668677545920388542621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418787558236727893851390161 314090668677545920388542621)
      ·
        refine ⟨117784000754079720145703483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314090668677545920388542621 117784000754079720145703483)
        ·
          refine ⟨176676001131119580218555225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117784000754079720145703483 176676001131119580218555225)
          ·
            refine ⟨132507000848339685163916419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176676001131119580218555225 132507000848339685163916419)
            ·
              refine ⟨198760501272509527745874629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132507000848339685163916419 198760501272509527745874629)
              ·
                refine ⟨37267593988595536452351493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 198760501272509527745874629 37267593988595536452351493)
                ·
                  refine ⟨6987673872861663084815905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37267593988595536452351493 6987673872861663084815905)
                  ·
                    refine ⟨5240755404646247313611929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6987673872861663084815905 5240755404646247313611929)
                    ·
                      refine ⟨3930566553484685485208947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5240755404646247313611929 3930566553484685485208947)
                      ·
                        rfl

theorem cell23_7654751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 4, 2, 2].length) (baseStart_7654751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654751 prefixEnd_7654751 := by exact prefixLift 7654751
  have htrace : WordTrace (prefixWord ++ tailWord_7654751) baseStart_7654751 baseEnd_7654751 := by
    simpa [prefixWord, tailWord_7654751, baseEnd_7654751] using wordTrace_append hprefix tailTrace_7654751
  have hstable : (prefixWord ++ tailWord_7654751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654751).length < 2 ^ (prefixWord ++ tailWord_7654751).sum := by decide
  have hdescent : baseEnd_7654751 < baseStart_7654751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654754 : List Nat := [3, 3, 2, 1, 1, 1, 2, 1, 1, 3, 5]
def baseStart_7654754 : Nat := 118140960795 + 7654754 * 2 ^ 59
def prefixEnd_7654754 : Nat := 4983230072969 + 3 ^ 40 * 7654754 * 2
def baseEnd_7654754 : Nat := 3930568093926648973471433

theorem tailTrace_7654754 : CollatzResearch.WordTrace tailWord_7654754 prefixEnd_7654754 3930568093926648973471433 := by
  unfold tailWord_7654754
  simp only [CollatzResearch.WordTrace]
  refine ⟨69797953727535265186654829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186127876606760707164412877 69797953727535265186654829)
  ·
    refine ⟨26174232647825724444995561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69797953727535265186654829 26174232647825724444995561)
    ·
      refine ⟨19630674485869293333746671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26174232647825724444995561 19630674485869293333746671)
      ·
        refine ⟨29446011728803940000620007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19630674485869293333746671 29446011728803940000620007)
        ·
          refine ⟨44169017593205910000930011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29446011728803940000620007 44169017593205910000930011)
          ·
            refine ⟨66253526389808865001395017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44169017593205910000930011 66253526389808865001395017)
            ·
              refine ⟨49690144792356648751046263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66253526389808865001395017 49690144792356648751046263)
              ·
                refine ⟨74535217188534973126569395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49690144792356648751046263 74535217188534973126569395)
                ·
                  refine ⟨111802825782802459689854093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74535217188534973126569395 111802825782802459689854093)
                  ·
                    refine ⟨41926059668550922383695285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 111802825782802459689854093 41926059668550922383695285)
                    ·
                      refine ⟨3930568093926648973471433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41926059668550922383695285 3930568093926648973471433)
                      ·
                        rfl

theorem cell23_7654754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_7654754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654754 prefixEnd_7654754 := by exact prefixLift 7654754
  have htrace : WordTrace (prefixWord ++ tailWord_7654754) baseStart_7654754 baseEnd_7654754 := by
    simpa [prefixWord, tailWord_7654754, baseEnd_7654754] using wordTrace_append hprefix tailTrace_7654754
  have hstable : (prefixWord ++ tailWord_7654754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654754).length < 2 ^ (prefixWord ++ tailWord_7654754).sum := by decide
  have hdescent : baseEnd_7654754 < baseStart_7654754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654755 : List Nat := [1, 1, 1, 5, 2, 4, 2, 1, 1, 3, 2]
def baseStart_7654755 : Nat := 118140960795 + 7654755 * 2 ^ 59
def prefixEnd_7654755 : Nat := 4983230072969 + 3 ^ 40 * 7654755 * 2
def baseEnd_7654755 : Nat := 3930568607407303469558929

theorem tailTrace_7654755 : CollatzResearch.WordTrace tailWord_7654755 prefixEnd_7654755 3930568607407303469558929 := by
  unfold tailWord_7654755
  simp only [CollatzResearch.WordTrace]
  refine ⟨279191851383137437917405719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186127900922091625278270479 279191851383137437917405719)
  ·
    refine ⟨418787777074706156876108579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279191851383137437917405719 418787777074706156876108579)
    ·
      refine ⟨628181665612059235314162869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418787777074706156876108579 628181665612059235314162869)
      ·
        refine ⟨58892031151130553310702769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 628181665612059235314162869 58892031151130553310702769)
        ·
          refine ⟨44169023363347914983027077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58892031151130553310702769 44169023363347914983027077)
          ·
            refine ⟨8281691880627734059317577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44169023363347914983027077 8281691880627734059317577)
            ·
              refine ⟨6211268910470800544488183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8281691880627734059317577 6211268910470800544488183)
              ·
                refine ⟨9316903365706200816732275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6211268910470800544488183 9316903365706200816732275)
                ·
                  refine ⟨13975355048559301225098413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9316903365706200816732275 13975355048559301225098413)
                  ·
                    refine ⟨5240758143209737959411905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13975355048559301225098413 5240758143209737959411905)
                    ·
                      refine ⟨3930568607407303469558929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5240758143209737959411905 3930568607407303469558929)
                      ·
                        rfl

theorem cell23_7654755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 1, 1, 3, 2].length) (baseStart_7654755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654755 prefixEnd_7654755 := by exact prefixLift 7654755
  have htrace : WordTrace (prefixWord ++ tailWord_7654755) baseStart_7654755 baseEnd_7654755 := by
    simpa [prefixWord, tailWord_7654755, baseEnd_7654755] using wordTrace_append hprefix tailTrace_7654755
  have hstable : (prefixWord ++ tailWord_7654755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654755).length < 2 ^ (prefixWord ++ tailWord_7654755).sum := by decide
  have hdescent : baseEnd_7654755 < baseStart_7654755 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654757 : List Nat := [1, 3, 1, 3, 1, 2, 1, 2, 9]
def baseStart_7654757 : Nat := 118140960795 + 7654757 * 2 ^ 59
def prefixEnd_7654757 : Nat := 4983230072969 + 3 ^ 40 * 7654757 * 2
def baseEnd_7654757 : Nat := 436729959374290273525991

theorem tailTrace_7654757 : CollatzResearch.WordTrace tailWord_7654757 prefixEnd_7654757 436729959374290273525991 := by
  unfold tailWord_7654757
  simp only [CollatzResearch.WordTrace]
  refine ⟨279191924329130192258978525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186127949552753461505985683 279191924329130192258978525)
  ·
    refine ⟨104696971623423822097116947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279191924329130192258978525 104696971623423822097116947)
    ·
      refine ⟨157045457435135733145675421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104696971623423822097116947 157045457435135733145675421)
      ·
        refine ⟨58892046538175899929628283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157045457435135733145675421 58892046538175899929628283)
        ·
          refine ⟨88338069807263849894442425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58892046538175899929628283 88338069807263849894442425)
          ·
            refine ⟨66253552355447887420831819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88338069807263849894442425 66253552355447887420831819)
            ·
              refine ⟨99380328533171831131247729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66253552355447887420831819 99380328533171831131247729)
              ·
                refine ⟨74535246399878873348435797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99380328533171831131247729 74535246399878873348435797)
                ·
                  refine ⟨436729959374290273525991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 74535246399878873348435797 436729959374290273525991)
                  ·
                    rfl

theorem cell23_7654757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 9].length) (baseStart_7654757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654757 prefixEnd_7654757 := by exact prefixLift 7654757
  have htrace : WordTrace (prefixWord ++ tailWord_7654757) baseStart_7654757 baseEnd_7654757 := by
    simpa [prefixWord, tailWord_7654757, baseEnd_7654757] using wordTrace_append hprefix tailTrace_7654757
  have hstable : (prefixWord ++ tailWord_7654757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654757).length < 2 ^ (prefixWord ++ tailWord_7654757).sum := by decide
  have hdescent : baseEnd_7654757 < baseStart_7654757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654762 : List Nat := [3, 1, 3, 3, 3, 1, 1, 2, 2, 1, 3]
def baseStart_7654762 : Nat := 118140960795 + 7654762 * 2 ^ 59
def prefixEnd_7654762 : Nat := 4983230072969 + 3 ^ 40 * 7654762 * 2
def baseEnd_7654762 : Nat := 3930572201771884942171397

theorem tailTrace_7654762 : CollatzResearch.WordTrace tailWord_7654762 prefixEnd_7654762 3930572201771884942171397 := by
  unfold tailWord_7654762
  simp only [CollatzResearch.WordTrace]
  refine ⟨69798026673528019528227635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186128071129408052075273693 69798026673528019528227635)
  ·
    refine ⟨104697040010292029292341453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69798026673528019528227635 104697040010292029292341453)
    ·
      refine ⟨39261390003859510984628045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104697040010292029292341453 39261390003859510984628045)
      ·
        refine ⟨14723021251447316619235517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39261390003859510984628045 14723021251447316619235517)
        ·
          refine ⟨5521132969292743732213319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14723021251447316619235517 5521132969292743732213319)
          ·
            refine ⟨8281699453939115598319979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5521132969292743732213319 8281699453939115598319979)
            ·
              refine ⟨12422549180908673397479969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8281699453939115598319979 12422549180908673397479969)
              ·
                refine ⟨9316911885681505048109977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12422549180908673397479969 9316911885681505048109977)
                ·
                  refine ⟨6987683914261128786082483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9316911885681505048109977 6987683914261128786082483)
                  ·
                    refine ⟨10481525871391693179123725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6987683914261128786082483 10481525871391693179123725)
                    ·
                      refine ⟨3930572201771884942171397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10481525871391693179123725 3930572201771884942171397)
                      ·
                        rfl

theorem cell23_7654762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_7654762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654762 prefixEnd_7654762 := by exact prefixLift 7654762
  have htrace : WordTrace (prefixWord ++ tailWord_7654762) baseStart_7654762 baseEnd_7654762 := by
    simpa [prefixWord, tailWord_7654762, baseEnd_7654762] using wordTrace_append hprefix tailTrace_7654762
  have hstable : (prefixWord ++ tailWord_7654762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654762).length < 2 ^ (prefixWord ++ tailWord_7654762).sum := by decide
  have hdescent : baseEnd_7654762 < baseStart_7654762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654764 : List Nat := [2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 4]
def baseStart_7654764 : Nat := 118140960795 + 7654764 * 2 ^ 59
def prefixEnd_7654764 : Nat := 4983230072969 + 3 ^ 40 * 7654764 * 2
def baseEnd_7654764 : Nat := 3930573228733193934346387

theorem tailTrace_7654764 : CollatzResearch.WordTrace tailWord_7654764 prefixEnd_7654764 3930573228733193934346387 := by
  unfold tailWord_7654764
  simp only [CollatzResearch.WordTrace]
  refine ⟨139596089820052416227241673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186128119760069888302988897 139596089820052416227241673)
  ·
    refine ⟨104697067365039312170431255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139596089820052416227241673 104697067365039312170431255)
    ·
      refine ⟨157045601047558968255646883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104697067365039312170431255 157045601047558968255646883)
      ·
        refine ⟨235568401571338452383470325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157045601047558968255646883 235568401571338452383470325)
        ·
          refine ⟨22084537647312979910950343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 235568401571338452383470325 22084537647312979910950343)
          ·
            refine ⟨33126806470969469866425515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22084537647312979910950343 33126806470969469866425515)
            ·
              refine ⟨49690209706454204799638273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33126806470969469866425515 49690209706454204799638273)
              ·
                refine ⟨37267657279840653599728705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49690209706454204799638273 37267657279840653599728705)
                ·
                  refine ⟨27950742959880490199796529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37267657279840653599728705 27950742959880490199796529)
                  ·
                    refine ⟨20963057219910367649847397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27950742959880490199796529 20963057219910367649847397)
                    ·
                      refine ⟨3930573228733193934346387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20963057219910367649847397 3930573228733193934346387)
                      ·
                        rfl

theorem cell23_7654764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 4].length) (baseStart_7654764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654764 prefixEnd_7654764 := by exact prefixLift 7654764
  have htrace : WordTrace (prefixWord ++ tailWord_7654764) baseStart_7654764 baseEnd_7654764 := by
    simpa [prefixWord, tailWord_7654764, baseEnd_7654764] using wordTrace_append hprefix tailTrace_7654764
  have hstable : (prefixWord ++ tailWord_7654764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654764).length < 2 ^ (prefixWord ++ tailWord_7654764).sum := by decide
  have hdescent : baseEnd_7654764 < baseStart_7654764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654785 : List Nat := [1, 2, 4, 3, 2, 2, 1, 1, 1, 4, 2]
def baseStart_7654785 : Nat := 118140960795 + 7654785 * 2 ^ 59
def prefixEnd_7654785 : Nat := 4983230072969 + 3 ^ 40 * 7654785 * 2
def baseEnd_7654785 : Nat := 3930584011826938352183791

theorem tailTrace_7654785 : CollatzResearch.WordTrace tailWord_7654785 prefixEnd_7654785 3930584011826938352183791 := by
  unfold tailWord_7654785
  simp only [CollatzResearch.WordTrace]
  refine ⟨279192945573028753040997809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186128630382019168693998539 279192945573028753040997809)
  ·
    refine ⟨209394709179771564780748357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279192945573028753040997809 209394709179771564780748357)
    ·
      refine ⟨39261507971207168396390317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209394709179771564780748357 39261507971207168396390317)
      ·
        refine ⟨14723065489202688148646369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39261507971207168396390317 14723065489202688148646369)
        ·
          refine ⟨11042299116902016111484777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14723065489202688148646369 11042299116902016111484777)
          ·
            refine ⟨8281724337676512083613583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11042299116902016111484777 8281724337676512083613583)
            ·
              refine ⟨12422586506514768125420375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8281724337676512083613583 12422586506514768125420375)
              ·
                refine ⟨18633879759772152188130563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12422586506514768125420375 18633879759772152188130563)
                ·
                  refine ⟨27950819639658228282195845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18633879759772152188130563 27950819639658228282195845)
                  ·
                    refine ⟨5240778682435917802911721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27950819639658228282195845 5240778682435917802911721)
                    ·
                      refine ⟨3930584011826938352183791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5240778682435917802911721 3930584011826938352183791)
                      ·
                        rfl

theorem cell23_7654785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_7654785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654785 prefixEnd_7654785 := by exact prefixLift 7654785
  have htrace : WordTrace (prefixWord ++ tailWord_7654785) baseStart_7654785 baseEnd_7654785 := by
    simpa [prefixWord, tailWord_7654785, baseEnd_7654785] using wordTrace_append hprefix tailTrace_7654785
  have hstable : (prefixWord ++ tailWord_7654785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654785).length < 2 ^ (prefixWord ++ tailWord_7654785).sum := by decide
  have hdescent : baseEnd_7654785 < baseStart_7654785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654881 : List Nat := [1, 2, 3, 1, 2, 4, 2, 2, 6]
def baseStart_7654881 : Nat := 118140960795 + 7654881 * 2 ^ 59
def prefixEnd_7654881 : Nat := 4983230072969 + 3 ^ 40 * 7654881 * 2
def baseEnd_7654881 : Nat := 436737033996641108509261

theorem tailTrace_7654881 : CollatzResearch.WordTrace tailWord_7654881 prefixEnd_7654881 436737033996641108509261 := by
  unfold tailWord_7654881
  simp only [CollatzResearch.WordTrace]
  refine ⟨279196446980680961436492497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186130964653787307624328331 279196446980680961436492497)
  ·
    refine ⟨209397335235510721077369373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279196446980680961436492497 209397335235510721077369373)
    ·
      refine ⟨78524000713316520404013515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209397335235510721077369373 78524000713316520404013515)
      ·
        refine ⟨117786001069974780606020273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78524000713316520404013515 117786001069974780606020273)
        ·
          refine ⟨88339500802481085454515205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117786001069974780606020273 88339500802481085454515205)
          ·
            refine ⟨16563656400465203522721601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88339500802481085454515205 16563656400465203522721601)
            ·
              refine ⟨12422742300348902642041201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16563656400465203522721601 12422742300348902642041201)
              ·
                refine ⟨9317056725261676981530901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12422742300348902642041201 9317056725261676981530901)
                ·
                  refine ⟨436737033996641108509261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9317056725261676981530901 436737033996641108509261)
                  ·
                    rfl

theorem cell23_7654881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 2, 6].length) (baseStart_7654881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654881 prefixEnd_7654881 := by exact prefixLift 7654881
  have htrace : WordTrace (prefixWord ++ tailWord_7654881) baseStart_7654881 baseEnd_7654881 := by
    simpa [prefixWord, tailWord_7654881, baseEnd_7654881] using wordTrace_append hprefix tailTrace_7654881
  have hstable : (prefixWord ++ tailWord_7654881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654881).length < 2 ^ (prefixWord ++ tailWord_7654881).sum := by decide
  have hdescent : baseEnd_7654881 < baseStart_7654881 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654885 : List Nat := [1, 3, 1, 5, 1, 2, 1, 4, 1, 4]
def baseStart_7654885 : Nat := 118140960795 + 7654885 * 2 ^ 59
def prefixEnd_7654885 : Nat := 4983230072969 + 3 ^ 40 * 7654885 * 2
def baseEnd_7654885 : Nat := 1310211786630795986977777

theorem tailTrace_7654885 : CollatzResearch.WordTrace tailWord_7654885 prefixEnd_7654885 1310211786630795986977777 := by
  unfold tailWord_7654885
  simp only [CollatzResearch.WordTrace]
  refine ⟨279196592872666470119638109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186131061915110980079758739 279196592872666470119638109)
  ·
    refine ⟨104698722327249926294864291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279196592872666470119638109 104698722327249926294864291)
    ·
      refine ⟨157048083490874889442296437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104698722327249926294864291 157048083490874889442296437)
      ·
        refine ⟨14723257827269520885215291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 157048083490874889442296437 14723257827269520885215291)
        ·
          refine ⟨22084886740904281327822937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14723257827269520885215291 22084886740904281327822937)
          ·
            refine ⟨16563665055678210995867203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22084886740904281327822937 16563665055678210995867203)
            ·
              refine ⟨24845497583517316493800805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16563665055678210995867203 24845497583517316493800805)
              ·
                refine ⟨4658530796909496842587651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24845497583517316493800805 4658530796909496842587651)
                ·
                  refine ⟨6987796195364245263881477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4658530796909496842587651 6987796195364245263881477)
                  ·
                    refine ⟨1310211786630795986977777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6987796195364245263881477 1310211786630795986977777)
                    ·
                      rfl

theorem cell23_7654885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 4, 1, 4].length) (baseStart_7654885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654885 prefixEnd_7654885 := by exact prefixLift 7654885
  have htrace : WordTrace (prefixWord ++ tailWord_7654885) baseStart_7654885 baseEnd_7654885 := by
    simpa [prefixWord, tailWord_7654885, baseEnd_7654885] using wordTrace_append hprefix tailTrace_7654885
  have hstable : (prefixWord ++ tailWord_7654885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654885).length < 2 ^ (prefixWord ++ tailWord_7654885).sum := by decide
  have hdescent : baseEnd_7654885 < baseStart_7654885 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654932 : List Nat := [2, 4, 3, 1, 3, 1, 1, 2, 6]
def baseStart_7654932 : Nat := 118140960795 + 7654932 * 2 ^ 59
def prefixEnd_7654932 : Nat := 4983230072969 + 3 ^ 40 * 7654932 * 2
def baseEnd_7654932 : Nat := 436739943720349919671735

theorem tailTrace_7654932 : CollatzResearch.WordTrace tailWord_7654932 prefixEnd_7654932 436739943720349919671735 := by
  unfold tailWord_7654932
  simp only [CollatzResearch.WordTrace]
  refine ⟨139599153551748098573299525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186132204735664131431066033 139599153551748098573299525)
  ·
    refine ⟨26174841290952768482493661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139599153551748098573299525 26174841290952768482493661)
    ·
      refine ⟨9815565484107288180935123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26174841290952768482493661 9815565484107288180935123)
      ·
        refine ⟨14723348226160932271402685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9815565484107288180935123 14723348226160932271402685)
        ·
          refine ⟨5521255584810349601776007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14723348226160932271402685 5521255584810349601776007)
          ·
            refine ⟨8281883377215524402664011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5521255584810349601776007 8281883377215524402664011)
            ·
              refine ⟨12422825065823286603996017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8281883377215524402664011 12422825065823286603996017)
              ·
                refine ⟨9317118799367464952997013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12422825065823286603996017 9317118799367464952997013)
                ·
                  refine ⟨436739943720349919671735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9317118799367464952997013 436739943720349919671735)
                  ·
                    rfl

theorem cell23_7654932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_7654932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654932 prefixEnd_7654932 := by exact prefixLift 7654932
  have htrace : WordTrace (prefixWord ++ tailWord_7654932) baseStart_7654932 baseEnd_7654932 := by
    simpa [prefixWord, tailWord_7654932, baseEnd_7654932] using wordTrace_append hprefix tailTrace_7654932
  have hstable : (prefixWord ++ tailWord_7654932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654932).length < 2 ^ (prefixWord ++ tailWord_7654932).sum := by decide
  have hdescent : baseEnd_7654932 < baseStart_7654932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654958 : List Nat := [4, 1, 3, 1, 2, 1, 3, 1, 1, 6]
def baseStart_7654958 : Nat := 118140960795 + 7654958 * 2 ^ 59
def prefixEnd_7654958 : Nat := 4983230072969 + 3 ^ 40 * 7654958 * 2
def baseEnd_7654958 : Nat := 1310224281326722058440165

theorem tailTrace_7654958 : CollatzResearch.WordTrace tailWord_7654958 prefixEnd_7654958 1310224281326722058440165 := by
  unfold tailWord_7654958
  simp only [CollatzResearch.WordTrace]
  refine ⟨34899906925175250448380691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186132836934268002391363685 34899906925175250448380691)
  ·
    refine ⟨52349860387762875672571037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34899906925175250448380691 52349860387762875672571037)
    ·
      refine ⟨19631197645411078377214139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52349860387762875672571037 19631197645411078377214139)
      ·
        refine ⟨29446796468116617565821209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19631197645411078377214139 29446796468116617565821209)
        ·
          refine ⟨22085097351087463174365907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29446796468116617565821209 22085097351087463174365907)
          ·
            refine ⟨33127646026631194761548861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22085097351087463174365907 33127646026631194761548861)
            ·
              refine ⟨12422867259986698035580823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33127646026631194761548861 12422867259986698035580823)
              ·
                refine ⟨18634300889980047053371235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12422867259986698035580823 18634300889980047053371235)
                ·
                  refine ⟨27951451334970070580056853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18634300889980047053371235 27951451334970070580056853)
                  ·
                    refine ⟨1310224281326722058440165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27951451334970070580056853 1310224281326722058440165)
                    ·
                      rfl

theorem cell23_7654958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_7654958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654958 prefixEnd_7654958 := by exact prefixLift 7654958
  have htrace : WordTrace (prefixWord ++ tailWord_7654958) baseStart_7654958 baseEnd_7654958 := by
    simpa [prefixWord, tailWord_7654958, baseEnd_7654958] using wordTrace_append hprefix tailTrace_7654958
  have hstable : (prefixWord ++ tailWord_7654958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654958).length < 2 ^ (prefixWord ++ tailWord_7654958).sum := by decide
  have hdescent : baseEnd_7654958 < baseStart_7654958 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654965 : List Nat := [1, 3, 3, 1, 1, 3, 2, 2, 3, 2, 2]
def baseStart_7654965 : Nat := 118140960795 + 7654965 * 2 ^ 59
def prefixEnd_7654965 : Nat := 4983230072969 + 3 ^ 40 * 7654965 * 2
def baseEnd_7654965 : Nat := 3930676438344747647932963

theorem tailTrace_7654965 : CollatzResearch.WordTrace tailWord_7654965 prefixEnd_7654965 3930676438344747647932963 := by
  unfold tailWord_7654965
  simp only [CollatzResearch.WordTrace]
  refine ⟨279199510712376643782550349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186133007141584429188366899 279199510712376643782550349)
  ·
    refine ⟨104699816517141241418456381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279199510712376643782550349 104699816517141241418456381)
    ·
      refine ⟨39262431193927965531921143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104699816517141241418456381 39262431193927965531921143)
      ·
        refine ⟨58893646790891948297881715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39262431193927965531921143 58893646790891948297881715)
        ·
          refine ⟨88340470186337922446822573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58893646790891948297881715 88340470186337922446822573)
          ·
            refine ⟨33127676319876720917558465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88340470186337922446822573 33127676319876720917558465)
            ·
              refine ⟨24845757239907540688168849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33127676319876720917558465 24845757239907540688168849)
              ·
                refine ⟨18634317929930655516126637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24845757239907540688168849 18634317929930655516126637)
                ·
                  refine ⟨6987869223723995818547489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18634317929930655516126637 6987869223723995818547489)
                  ·
                    refine ⟨5240901917792996863910617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6987869223723995818547489 5240901917792996863910617)
                    ·
                      refine ⟨3930676438344747647932963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5240901917792996863910617 3930676438344747647932963)
                      ·
                        rfl

theorem cell23_7654965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 3, 2, 2].length) (baseStart_7654965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654965 prefixEnd_7654965 := by exact prefixLift 7654965
  have htrace : WordTrace (prefixWord ++ tailWord_7654965) baseStart_7654965 baseEnd_7654965 := by
    simpa [prefixWord, tailWord_7654965, baseEnd_7654965] using wordTrace_append hprefix tailTrace_7654965
  have hstable : (prefixWord ++ tailWord_7654965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654965).length < 2 ^ (prefixWord ++ tailWord_7654965).sum := by decide
  have hdescent : baseEnd_7654965 < baseStart_7654965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654968 : List Nat := [2, 1, 2, 1, 4, 2, 1, 4, 1, 2, 3]
def baseStart_7654968 : Nat := 118140960795 + 7654968 * 2 ^ 59
def prefixEnd_7654968 : Nat := 4983230072969 + 3 ^ 40 * 7654968 * 2
def baseEnd_7654968 : Nat := 3930677978786711136195449

theorem tailTrace_7654968 : CollatzResearch.WordTrace tailWord_7654968 prefixEnd_7654968 3930677978786711136195449 := by
  unfold tailWord_7654968
  simp only [CollatzResearch.WordTrace]
  refine ⟨139599810065682887647454779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186133080087577183529939705 139599810065682887647454779)
  ·
    refine ⟨209399715098524331471182169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139599810065682887647454779 209399715098524331471182169)
    ·
      refine ⟨157049786323893248603386627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209399715098524331471182169 157049786323893248603386627)
      ·
        refine ⟨235574679485839872905079941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157049786323893248603386627 235574679485839872905079941)
        ·
          refine ⟨44170252403594976169702489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 235574679485839872905079941 44170252403594976169702489)
          ·
            refine ⟨33127689302696232127276867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44170252403594976169702489 33127689302696232127276867)
            ·
              refine ⟨49691533954044348190915301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33127689302696232127276867 49691533954044348190915301)
              ·
                refine ⟨9317162616383315285796619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49691533954044348190915301 9317162616383315285796619)
                ·
                  refine ⟨13975743924574972928694929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9317162616383315285796619 13975743924574972928694929)
                  ·
                    refine ⟨10481807943431229696521197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13975743924574972928694929 10481807943431229696521197)
                    ·
                      refine ⟨3930677978786711136195449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10481807943431229696521197 3930677978786711136195449)
                      ·
                        rfl

theorem cell23_7654968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 4, 1, 2, 3].length) (baseStart_7654968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654968 prefixEnd_7654968 := by exact prefixLift 7654968
  have htrace : WordTrace (prefixWord ++ tailWord_7654968) baseStart_7654968 baseEnd_7654968 := by
    simpa [prefixWord, tailWord_7654968, baseEnd_7654968] using wordTrace_append hprefix tailTrace_7654968
  have hstable : (prefixWord ++ tailWord_7654968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654968).length < 2 ^ (prefixWord ++ tailWord_7654968).sum := by decide
  have hdescent : baseEnd_7654968 < baseStart_7654968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654981 : List Nat := [1, 3, 1, 1, 1, 4, 2, 1, 3, 3, 3]
def baseStart_7654981 : Nat := 118140960795 + 7654981 * 2 ^ 59
def prefixEnd_7654981 : Nat := 4983230072969 + 3 ^ 40 * 7654981 * 2
def baseEnd_7654981 : Nat := 3930684654035219585332889

theorem tailTrace_7654981 : CollatzResearch.WordTrace tailWord_7654981 prefixEnd_7654981 3930684654035219585332889 := by
  unfold tailWord_7654981
  simp only [CollatzResearch.WordTrace]
  refine ⟨279200094280318678515132797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186133396186879119010088531 279200094280318678515132797)
  ·
    refine ⟨104700035355119504443174799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279200094280318678515132797 104700035355119504443174799)
    ·
      refine ⟨157050053032679256664762199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104700035355119504443174799 157050053032679256664762199)
      ·
        refine ⟨235575079549018884997143299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157050053032679256664762199 235575079549018884997143299)
        ·
          refine ⟨353362619323528327495714949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235575079549018884997143299 353362619323528327495714949)
          ·
            refine ⟨66255491123161561405446553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 353362619323528327495714949 66255491123161561405446553)
            ·
              refine ⟨49691618342371171054084915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66255491123161561405446553 49691618342371171054084915)
              ·
                refine ⟨74537427513556756581127373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49691618342371171054084915 74537427513556756581127373)
                ·
                  refine ⟨27951535317583783717922765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74537427513556756581127373 27951535317583783717922765)
                  ·
                    refine ⟨10481825744093918894221037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27951535317583783717922765 10481825744093918894221037)
                    ·
                      refine ⟨3930684654035219585332889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10481825744093918894221037 3930684654035219585332889)
                      ·
                        rfl

theorem cell23_7654981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 3, 3].length) (baseStart_7654981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654981 prefixEnd_7654981 := by exact prefixLift 7654981
  have htrace : WordTrace (prefixWord ++ tailWord_7654981) baseStart_7654981 baseEnd_7654981 := by
    simpa [prefixWord, tailWord_7654981, baseEnd_7654981] using wordTrace_append hprefix tailTrace_7654981
  have hstable : (prefixWord ++ tailWord_7654981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654981).length < 2 ^ (prefixWord ++ tailWord_7654981).sum := by decide
  have hdescent : baseEnd_7654981 < baseStart_7654981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654984 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 3, 9]
def baseStart_7654984 : Nat := 118140960795 + 7654984 * 2 ^ 59
def prefixEnd_7654984 : Nat := 4983230072969 + 3 ^ 40 * 7654984 * 2
def baseEnd_7654984 : Nat := 1310228731492394357865125

theorem tailTrace_7654984 : CollatzResearch.WordTrace tailWord_7654984 prefixEnd_7654984 1310228731492394357865125 := by
  unfold tailWord_7654984
  simp only [CollatzResearch.WordTrace]
  refine ⟨139600101849653905013746003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186133469132871873351661337 139600101849653905013746003)
  ·
    refine ⟨209400152774480857520619005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139600101849653905013746003 209400152774480857520619005)
    ·
      refine ⟨78525057290430321570232127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209400152774480857520619005 78525057290430321570232127)
      ·
        refine ⟨117787585935645482355348191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78525057290430321570232127 117787585935645482355348191)
        ·
          refine ⟨176681378903468223533022287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117787585935645482355348191 176681378903468223533022287)
          ·
            refine ⟨265022068355202335299533431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176681378903468223533022287 265022068355202335299533431)
            ·
              refine ⟨397533102532803502949300147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265022068355202335299533431 397533102532803502949300147)
              ·
                refine ⟨596299653799205254423950221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 397533102532803502949300147 596299653799205254423950221)
                ·
                  refine ⟨223612370174701970408981333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 596299653799205254423950221 223612370174701970408981333)
                  ·
                    refine ⟨1310228731492394357865125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 223612370174701970408981333 1310228731492394357865125)
                    ·
                      rfl

theorem cell23_7654984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_7654984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654984 prefixEnd_7654984 := by exact prefixLift 7654984
  have htrace : WordTrace (prefixWord ++ tailWord_7654984) baseStart_7654984 baseEnd_7654984 := by
    simpa [prefixWord, tailWord_7654984, baseEnd_7654984] using wordTrace_append hprefix tailTrace_7654984
  have hstable : (prefixWord ++ tailWord_7654984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654984).length < 2 ^ (prefixWord ++ tailWord_7654984).sum := by decide
  have hdescent : baseEnd_7654984 < baseStart_7654984 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7654999 : List Nat := [1, 1, 3, 2, 2, 4, 3, 2, 1, 2, 2]
def baseStart_7654999 : Nat := 118140960795 + 7654999 * 2 ^ 59
def prefixEnd_7654999 : Nat := 4983230072969 + 3 ^ 40 * 7654999 * 2
def baseEnd_7654999 : Nat := 3930693896687000514907807

theorem tailTrace_7654999 : CollatzResearch.WordTrace tailWord_7654999 prefixEnd_7654999 3930693896687000514907807 := by
  unfold tailWord_7654999
  simp only [CollatzResearch.WordTrace]
  refine ⟨279200750794253467589288051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186133833862835645059525367 279200750794253467589288051)
  ·
    refine ⟨418801126191380201383932077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279200750794253467589288051 418801126191380201383932077)
    ·
      refine ⟨157050422321767575518974529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 418801126191380201383932077 157050422321767575518974529)
      ·
        refine ⟨117787816741325681639230897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157050422321767575518974529 117787816741325681639230897)
        ·
          refine ⟨88340862555994261229423173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117787816741325681639230897 88340862555994261229423173)
          ·
            refine ⟨16563911729248923980516845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88340862555994261229423173 16563911729248923980516845)
            ·
              refine ⟨6211466898468346492693817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16563911729248923980516845 6211466898468346492693817)
              ·
                refine ⟨4658600173851259869520363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6211466898468346492693817 4658600173851259869520363)
                ·
                  refine ⟨6987900260776889804280545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4658600173851259869520363 6987900260776889804280545)
                  ·
                    refine ⟨5240925195582667353210409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6987900260776889804280545 5240925195582667353210409)
                    ·
                      refine ⟨3930693896687000514907807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5240925195582667353210409 3930693896687000514907807)
                      ·
                        rfl

theorem cell23_7654999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 2, 1, 2, 2].length) (baseStart_7654999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7654999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7654999 prefixEnd_7654999 := by exact prefixLift 7654999
  have htrace : WordTrace (prefixWord ++ tailWord_7654999) baseStart_7654999 baseEnd_7654999 := by
    simpa [prefixWord, tailWord_7654999, baseEnd_7654999] using wordTrace_append hprefix tailTrace_7654999
  have hstable : (prefixWord ++ tailWord_7654999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7654999).length < 2 ^ (prefixWord ++ tailWord_7654999).sum := by decide
  have hdescent : baseEnd_7654999 < baseStart_7654999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7654999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655005 : List Nat := [1, 4, 4, 2, 1, 1, 2, 8]
def baseStart_7655005 : Nat := 118140960795 + 7655005 * 2 ^ 59
def prefixEnd_7655005 : Nat := 4983230072969 + 3 ^ 40 * 7655005 * 2
def baseEnd_7655005 : Nat := 145581369539663981164177

theorem tailTrace_7655005 : CollatzResearch.WordTrace tailWord_7655005 prefixEnd_7655005 145581369539663981164177 := by
  unfold tailWord_7655005
  simp only [CollatzResearch.WordTrace]
  refine ⟨279200969632231730614006469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186133979754821153742670979 279200969632231730614006469)
  ·
    refine ⟨52350181806043449490126213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 279200969632231730614006469 52350181806043449490126213)
    ·
      refine ⟨9815659088633146779398665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52350181806043449490126213 9815659088633146779398665)
      ·
        refine ⟨7361744316474860084548999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9815659088633146779398665 7361744316474860084548999)
        ·
          refine ⟨11042616474712290126823499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7361744316474860084548999 11042616474712290126823499)
          ·
            refine ⟨16563924712068435190235249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11042616474712290126823499 16563924712068435190235249)
            ·
              refine ⟨12422943534051326392676437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16563924712068435190235249 12422943534051326392676437)
              ·
                refine ⟨145581369539663981164177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12422943534051326392676437 145581369539663981164177)
                ·
                  rfl

theorem cell23_7655005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 8].length) (baseStart_7655005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655005 prefixEnd_7655005 := by exact prefixLift 7655005
  have htrace : WordTrace (prefixWord ++ tailWord_7655005) baseStart_7655005 baseEnd_7655005 := by
    simpa [prefixWord, tailWord_7655005, baseEnd_7655005] using wordTrace_append hprefix tailTrace_7655005
  have hstable : (prefixWord ++ tailWord_7655005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655005).length < 2 ^ (prefixWord ++ tailWord_7655005).sum := by decide
  have hdescent : baseEnd_7655005 < baseStart_7655005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655008 : List Nat := [2, 1, 1, 3, 2, 1, 1, 4, 3, 3, 2]
def baseStart_7655008 : Nat := 118140960795 + 7655008 * 2 ^ 59
def prefixEnd_7655008 : Nat := 4983230072969 + 3 ^ 40 * 7655008 * 2
def baseEnd_7655008 : Nat := 3930698518012890979695265

theorem tailTrace_7655008 : CollatzResearch.WordTrace tailWord_7655008 prefixEnd_7655008 3930698518012890979695265 := by
  unfold tailWord_7655008
  simp only [CollatzResearch.WordTrace]
  refine ⟨139600539525610431063182839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186134052700813908084243785 139600539525610431063182839)
  ·
    refine ⟨209400809288415646594774259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139600539525610431063182839 209400809288415646594774259)
    ·
      refine ⟨314101213932623469892161389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209400809288415646594774259 314101213932623469892161389)
      ·
        refine ⟨117787955224733801209560521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314101213932623469892161389 117787955224733801209560521)
        ·
          refine ⟨88340966418550350907170391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117787955224733801209560521 88340966418550350907170391)
          ·
            refine ⟨132511449627825526360755587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88340966418550350907170391 132511449627825526360755587)
            ·
              refine ⟨198767174441738289541133381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132511449627825526360755587 198767174441738289541133381)
              ·
                refine ⟨37268845207825929288962509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 198767174441738289541133381 37268845207825929288962509)
                ·
                  refine ⟨13975816952934723483360941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37268845207825929288962509 13975816952934723483360941)
                  ·
                    refine ⟨5240931357350521306260353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13975816952934723483360941 5240931357350521306260353)
                    ·
                      refine ⟨3930698518012890979695265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5240931357350521306260353 3930698518012890979695265)
                      ·
                        rfl

theorem cell23_7655008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 3, 3, 2].length) (baseStart_7655008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655008 prefixEnd_7655008 := by exact prefixLift 7655008
  have htrace : WordTrace (prefixWord ++ tailWord_7655008) baseStart_7655008 baseEnd_7655008 := by
    simpa [prefixWord, tailWord_7655008, baseEnd_7655008] using wordTrace_append hprefix tailTrace_7655008
  have hstable : (prefixWord ++ tailWord_7655008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655008).length < 2 ^ (prefixWord ++ tailWord_7655008).sum := by decide
  have hdescent : baseEnd_7655008 < baseStart_7655008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655051 : List Nat := [1, 1, 1, 1, 4, 1, 4, 2, 2, 2, 4]
def baseStart_7655051 : Nat := 118140960795 + 7655051 * 2 ^ 59
def prefixEnd_7655051 : Nat := 4983230072969 + 3 ^ 40 * 7655051 * 2
def baseEnd_7655051 : Nat := 3930720597681034311457567

theorem tailTrace_7655051 : CollatzResearch.WordTrace tailWord_7655051 prefixEnd_7655051 3930720597681034311457567 := by
  unfold tailWord_7655051
  simp only [CollatzResearch.WordTrace]
  refine ⟨279202647390065080470181007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186135098260043386980120671 279202647390065080470181007)
  ·
    refine ⟨418803971085097620705271511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279202647390065080470181007 418803971085097620705271511)
    ·
      refine ⟨628205956627646431057907267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418803971085097620705271511 628205956627646431057907267)
      ·
        refine ⟨942308934941469646586860901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 628205956627646431057907267 942308934941469646586860901)
        ·
          refine ⟨176682925301525558735036419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 942308934941469646586860901 176682925301525558735036419)
          ·
            refine ⟨265024387952288338102554629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176682925301525558735036419 265024387952288338102554629)
            ·
              refine ⟨49692072741054063394228993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 265024387952288338102554629 49692072741054063394228993)
              ·
                refine ⟨37269054555790547545671745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49692072741054063394228993 37269054555790547545671745)
                ·
                  refine ⟨27951790916842910659253809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37269054555790547545671745 27951790916842910659253809)
                  ·
                    refine ⟨20963843187632182994440357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27951790916842910659253809 20963843187632182994440357)
                    ·
                      refine ⟨3930720597681034311457567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20963843187632182994440357 3930720597681034311457567)
                      ·
                        rfl

theorem cell23_7655051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 2, 4].length) (baseStart_7655051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655051 prefixEnd_7655051 := by exact prefixLift 7655051
  have htrace : WordTrace (prefixWord ++ tailWord_7655051) baseStart_7655051 baseEnd_7655051 := by
    simpa [prefixWord, tailWord_7655051, baseEnd_7655051] using wordTrace_append hprefix tailTrace_7655051
  have hstable : (prefixWord ++ tailWord_7655051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655051).length < 2 ^ (prefixWord ++ tailWord_7655051).sum := by decide
  have hdescent : baseEnd_7655051 < baseStart_7655051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655072 : List Nat := [2, 1, 1, 4, 3, 1, 2, 3, 2, 2, 2]
def baseStart_7655072 : Nat := 118140960795 + 7655072 * 2 ^ 59
def prefixEnd_7655072 : Nat := 4983230072969 + 3 ^ 40 * 7655072 * 2
def baseEnd_7655072 : Nat := 3930731380774778729294971

theorem tailTrace_7655072 : CollatzResearch.WordTrace tailWord_7655072 prefixEnd_7655072 3930731380774778729294971 := by
  unfold tailWord_7655072
  simp only [CollatzResearch.WordTrace]
  refine ⟨139601706661494500528347735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186135608881992667371130313 139601706661494500528347735)
  ·
    refine ⟨209402559992241750792521603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139601706661494500528347735 209402559992241750792521603)
    ·
      refine ⟨314103839988362626188782405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209402559992241750792521603 314103839988362626188782405)
      ·
        refine ⟨58894469997817992410396701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 314103839988362626188782405 58894469997817992410396701)
        ·
          refine ⟨22085426249181747153898763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58894469997817992410396701 22085426249181747153898763)
          ·
            refine ⟨33128139373772620730848145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22085426249181747153898763 33128139373772620730848145)
            ·
              refine ⟨24846104530329465548136109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33128139373772620730848145 24846104530329465548136109)
              ·
                refine ⟨9317289198873549580551041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24846104530329465548136109 9317289198873549580551041)
                ·
                  refine ⟨6987966899155162185413281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9317289198873549580551041 6987966899155162185413281)
                  ·
                    refine ⟨5240975174366371639059961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6987966899155162185413281 5240975174366371639059961)
                    ·
                      refine ⟨3930731380774778729294971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5240975174366371639059961 3930731380774778729294971)
                      ·
                        rfl

theorem cell23_7655072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3, 2, 2, 2].length) (baseStart_7655072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655072 prefixEnd_7655072 := by exact prefixLift 7655072
  have htrace : WordTrace (prefixWord ++ tailWord_7655072) baseStart_7655072 baseEnd_7655072 := by
    simpa [prefixWord, tailWord_7655072, baseEnd_7655072] using wordTrace_append hprefix tailTrace_7655072
  have hstable : (prefixWord ++ tailWord_7655072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655072).length < 2 ^ (prefixWord ++ tailWord_7655072).sum := by decide
  have hdescent : baseEnd_7655072 < baseStart_7655072 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655091 : List Nat := [1, 1, 1, 2, 3, 3, 3, 1, 1, 7]
def baseStart_7655091 : Nat := 118140960795 + 7655091 * 2 ^ 59
def prefixEnd_7655091 : Nat := 4983230072969 + 3 ^ 40 * 7655091 * 2
def baseEnd_7655091 : Nat := 1310247045635738051652461

theorem tailTrace_7655091 : CollatzResearch.WordTrace tailWord_7655091 prefixEnd_7655091 1310247045635738051652461 := by
  unfold tailWord_7655091
  simp only [CollatzResearch.WordTrace]
  refine ⟨279204106309920167301637127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186136070873280111534424751 279204106309920167301637127)
  ·
    refine ⟨418806159464880250952455691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279204106309920167301637127 418806159464880250952455691)
    ·
      refine ⟨628209239197320376428683537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418806159464880250952455691 628209239197320376428683537)
      ·
        refine ⟨471156929397990282321512653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 628209239197320376428683537 471156929397990282321512653)
        ·
          refine ⟨176683848524246355870567245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 471156929397990282321512653 176683848524246355870567245)
          ·
            refine ⟨66256443196592383451462717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176683848524246355870567245 66256443196592383451462717)
            ·
              refine ⟨24846166198722143794298519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66256443196592383451462717 24846166198722143794298519)
              ·
                refine ⟨37269249298083215691447779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24846166198722143794298519 37269249298083215691447779)
                ·
                  refine ⟨55903873947124823537171669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37269249298083215691447779 55903873947124823537171669)
                  ·
                    refine ⟨1310247045635738051652461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55903873947124823537171669 1310247045635738051652461)
                    ·
                      rfl

theorem cell23_7655091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 7].length) (baseStart_7655091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655091 prefixEnd_7655091 := by exact prefixLift 7655091
  have htrace : WordTrace (prefixWord ++ tailWord_7655091) baseStart_7655091 baseEnd_7655091 := by
    simpa [prefixWord, tailWord_7655091, baseEnd_7655091] using wordTrace_append hprefix tailTrace_7655091
  have hstable : (prefixWord ++ tailWord_7655091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655091).length < 2 ^ (prefixWord ++ tailWord_7655091).sum := by decide
  have hdescent : baseEnd_7655091 < baseStart_7655091 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655095 : List Nat := [1, 1, 3, 1, 5, 2, 2, 3, 5]
def baseStart_7655095 : Nat := 118140960795 + 7655095 * 2 ^ 59
def prefixEnd_7655095 : Nat := 4983230072969 + 3 ^ 40 * 7655095 * 2
def baseEnd_7655095 : Nat := 436749243425536904367485

theorem tailTrace_7655095 : CollatzResearch.WordTrace tailWord_7655095 prefixEnd_7655095 436749243425536904367485 := by
  unfold tailWord_7655095
  simp only [CollatzResearch.WordTrace]
  refine ⟨279204252201905675984782739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186136168134603783989855159 279204252201905675984782739)
  ·
    refine ⟨418806378302858513977174109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279204252201905675984782739 418806378302858513977174109)
    ·
      refine ⟨157052391863571942741440291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 418806378302858513977174109 157052391863571942741440291)
      ·
        refine ⟨235578587795357914112160437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157052391863571942741440291 235578587795357914112160437)
        ·
          refine ⟨22085492605814804448015041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 235578587795357914112160437 22085492605814804448015041)
          ·
            refine ⟨16564119454361103336011281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22085492605814804448015041 16564119454361103336011281)
            ·
              refine ⟨12423089590770827502008461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16564119454361103336011281 12423089590770827502008461)
              ·
                refine ⟨4658658596539060313253173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12423089590770827502008461 4658658596539060313253173)
                ·
                  refine ⟨436749243425536904367485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4658658596539060313253173 436749243425536904367485)
                  ·
                    rfl

theorem cell23_7655095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 3, 5].length) (baseStart_7655095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655095 prefixEnd_7655095 := by exact prefixLift 7655095
  have htrace : WordTrace (prefixWord ++ tailWord_7655095) baseStart_7655095 baseEnd_7655095 := by
    simpa [prefixWord, tailWord_7655095, baseEnd_7655095] using wordTrace_append hprefix tailTrace_7655095
  have hstable : (prefixWord ++ tailWord_7655095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655095).length < 2 ^ (prefixWord ++ tailWord_7655095).sum := by decide
  have hdescent : baseEnd_7655095 < baseStart_7655095 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655108 : List Nat := [2, 3, 3, 1, 1, 1, 2, 1, 4, 5]
def baseStart_7655108 : Nat := 118140960795 + 7655108 * 2 ^ 59
def prefixEnd_7655108 : Nat := 4983230072969 + 3 ^ 40 * 7655108 * 2
def baseEnd_7655108 : Nat := 1310249955359446862814935

theorem tailTrace_7655108 : CollatzResearch.WordTrace tailWord_7655108 prefixEnd_7655108 1310249955359446862814935 := by
  unfold tailWord_7655108
  simp only [CollatzResearch.WordTrace]
  refine ⟨139602363175429289602502989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186136484233905719470003985 139602363175429289602502989)
  ·
    refine ⟨52350886190785983600938621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139602363175429289602502989 52350886190785983600938621)
    ·
      refine ⟨19631582321544743850351983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52350886190785983600938621 19631582321544743850351983)
      ·
        refine ⟨29447373482317115775527975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19631582321544743850351983 29447373482317115775527975)
        ·
          refine ⟨44171060223475673663291963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29447373482317115775527975 44171060223475673663291963)
          ·
            refine ⟨66256590335213510494937945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44171060223475673663291963 66256590335213510494937945)
            ·
              refine ⟨49692442751410132871203459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66256590335213510494937945 49692442751410132871203459)
              ·
                refine ⟨74538664127115199306805189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49692442751410132871203459 74538664127115199306805189)
                ·
                  refine ⟨13975999523834099870025973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74538664127115199306805189 13975999523834099870025973)
                  ·
                    refine ⟨1310249955359446862814935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13975999523834099870025973 1310249955359446862814935)
                    ·
                      rfl

theorem cell23_7655108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_7655108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655108 prefixEnd_7655108 := by exact prefixLift 7655108
  have htrace : WordTrace (prefixWord ++ tailWord_7655108) baseStart_7655108 baseEnd_7655108 := by
    simpa [prefixWord, tailWord_7655108, baseEnd_7655108] using wordTrace_append hprefix tailTrace_7655108
  have hstable : (prefixWord ++ tailWord_7655108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655108).length < 2 ^ (prefixWord ++ tailWord_7655108).sum := by decide
  have hdescent : baseEnd_7655108 < baseStart_7655108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655148 : List Nat := [2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 3]
def baseStart_7655148 : Nat := 118140960795 + 7655148 * 2 ^ 59
def prefixEnd_7655148 : Nat := 4983230072969 + 3 ^ 40 * 7655148 * 2
def baseEnd_7655148 : Nat := 3930770405304520431944621

theorem tailTrace_7655148 : CollatzResearch.WordTrace tailWord_7655148 prefixEnd_7655148 3930770405304520431944621 := by
  unfold tailWord_7655148
  simp only [CollatzResearch.WordTrace]
  refine ⟨139603092635356833018231049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186137456847142444024308065 139603092635356833018231049)
  ·
    refine ⟨104702319476517624763673287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139603092635356833018231049 104702319476517624763673287)
    ·
      refine ⟨157053479214776437145509931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104702319476517624763673287 157053479214776437145509931)
      ·
        refine ⟨235580218822164655718264897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157053479214776437145509931 235580218822164655718264897)
        ·
          refine ⟨176685164116623491788698673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235580218822164655718264897 176685164116623491788698673)
          ·
            refine ⟨132513873087467618841524005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176685164116623491788698673 132513873087467618841524005)
            ·
              refine ⟨24846351203900178532785751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132513873087467618841524005 24846351203900178532785751)
              ·
                refine ⟨37269526805850267799178627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24846351203900178532785751 37269526805850267799178627)
                ·
                  refine ⟨55904290208775401698767941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37269526805850267799178627 55904290208775401698767941)
                  ·
                    refine ⟨10482054414145387818518989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55904290208775401698767941 10482054414145387818518989)
                    ·
                      refine ⟨3930770405304520431944621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10482054414145387818518989 3930770405304520431944621)
                      ·
                        rfl

theorem cell23_7655148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 3].length) (baseStart_7655148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655148 prefixEnd_7655148 := by exact prefixLift 7655148
  have htrace : WordTrace (prefixWord ++ tailWord_7655148) baseStart_7655148 baseEnd_7655148 := by
    simpa [prefixWord, tailWord_7655148, baseEnd_7655148] using wordTrace_append hprefix tailTrace_7655148
  have hstable : (prefixWord ++ tailWord_7655148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655148).length < 2 ^ (prefixWord ++ tailWord_7655148).sum := by decide
  have hdescent : baseEnd_7655148 < baseStart_7655148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655151 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 10]
def baseStart_7655151 : Nat := 118140960795 + 7655151 * 2 ^ 59
def prefixEnd_7655151 : Nat := 4983230072969 + 3 ^ 40 * 7655151 * 2
def baseEnd_7655151 : Nat := 436752438416275991134123

theorem tailTrace_7655151 : CollatzResearch.WordTrace tailWord_7655151 prefixEnd_7655151 436752438416275991134123 := by
  unfold tailWord_7655151
  simp only [CollatzResearch.WordTrace]
  refine ⟨279206294689702797548821307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186137529793135198365880871 279206294689702797548821307)
  ·
    refine ⟨418809442034554196323231961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279206294689702797548821307 418809442034554196323231961)
    ·
      refine ⟨314107081525915647242423971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418809442034554196323231961 314107081525915647242423971)
      ·
        refine ⟨471160622288873470863635957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314107081525915647242423971 471160622288873470863635957)
        ·
          refine ⟨44171308339581887893465871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 471160622288873470863635957 44171308339581887893465871)
          ·
            refine ⟨66256962509372831840198807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44171308339581887893465871 66256962509372831840198807)
            ·
              refine ⟨99385443764059247760298211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66256962509372831840198807 99385443764059247760298211)
              ·
                refine ⟨149078165646088871640447317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99385443764059247760298211 149078165646088871640447317)
                ·
                  refine ⟨436752438416275991134123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 149078165646088871640447317 436752438416275991134123)
                  ·
                    rfl

theorem cell23_7655151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 10].length) (baseStart_7655151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655151 prefixEnd_7655151 := by exact prefixLift 7655151
  have htrace : WordTrace (prefixWord ++ tailWord_7655151) baseStart_7655151 baseEnd_7655151 := by
    simpa [prefixWord, tailWord_7655151, baseEnd_7655151] using wordTrace_append hprefix tailTrace_7655151
  have hstable : (prefixWord ++ tailWord_7655151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655151).length < 2 ^ (prefixWord ++ tailWord_7655151).sum := by decide
  have hdescent : baseEnd_7655151 < baseStart_7655151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655171 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 8]
def baseStart_7655171 : Nat := 118140960795 + 7655171 * 2 ^ 59
def prefixEnd_7655171 : Nat := 4983230072969 + 3 ^ 40 * 7655171 * 2
def baseEnd_7655171 : Nat := 3930782215359573841957015

theorem tailTrace_7655171 : CollatzResearch.WordTrace tailWord_7655171 prefixEnd_7655171 3930782215359573841957015 := by
  unfold tailWord_7655171
  simp only [CollatzResearch.WordTrace]
  refine ⟨279207024149630340964549367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186138016099753560643032911 279207024149630340964549367)
  ·
    refine ⟨418810536224445511446824051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279207024149630340964549367 418810536224445511446824051)
    ·
      refine ⟨628215804336668267170236077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418810536224445511446824051 628215804336668267170236077)
      ·
        refine ⟨235580926626250600188838529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 628215804336668267170236077 235580926626250600188838529)
        ·
          refine ⟨176685694969687950141628897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235580926626250600188838529 176685694969687950141628897)
          ·
            refine ⟨132514271227265962606221673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176685694969687950141628897 132514271227265962606221673)
            ·
              refine ⟨99385703420449471954666255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132514271227265962606221673 99385703420449471954666255)
              ·
                refine ⟨149078555130674207931999383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99385703420449471954666255 149078555130674207931999383)
                ·
                  refine ⟨223617832696011311897999075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149078555130674207931999383 223617832696011311897999075)
                  ·
                    refine ⟨335426749044016967846998613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 223617832696011311897999075 335426749044016967846998613)
                    ·
                      refine ⟨3930782215359573841957015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 335426749044016967846998613 3930782215359573841957015)
                      ·
                        rfl

theorem cell23_7655171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_7655171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655171 prefixEnd_7655171 := by exact prefixLift 7655171
  have htrace : WordTrace (prefixWord ++ tailWord_7655171) baseStart_7655171 baseEnd_7655171 := by
    simpa [prefixWord, tailWord_7655171, baseEnd_7655171] using wordTrace_append hprefix tailTrace_7655171
  have hstable : (prefixWord ++ tailWord_7655171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655171).length < 2 ^ (prefixWord ++ tailWord_7655171).sum := by decide
  have hdescent : baseEnd_7655171 < baseStart_7655171 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655172 : List Nat := [2, 3, 2, 2, 1, 4, 1, 1, 3, 4]
def baseStart_7655172 : Nat := 118140960795 + 7655172 * 2 ^ 59
def prefixEnd_7655172 : Nat := 4983230072969 + 3 ^ 40 * 7655172 * 2
def baseEnd_7655172 : Nat := 1310260909613409446014837

theorem tailTrace_7655172 : CollatzResearch.WordTrace tailWord_7655172 prefixEnd_7655172 1310260909613409446014837 := by
  unfold tailWord_7655172
  simp only [CollatzResearch.WordTrace]
  refine ⟨139603530311313359067667885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186138040415084478756890513 139603530311313359067667885)
  ·
    refine ⟨52351323866742509650375457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139603530311313359067667885 52351323866742509650375457)
    ·
      refine ⟨39263492900056882237781593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52351323866742509650375457 39263492900056882237781593)
      ·
        refine ⟨29447619675042661678336195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39263492900056882237781593 29447619675042661678336195)
        ·
          refine ⟨44171429512563992517504293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29447619675042661678336195 44171429512563992517504293)
          ·
            refine ⟨8282143033605748597032055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44171429512563992517504293 8282143033605748597032055)
            ·
              refine ⟨12423214550408622895548083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8282143033605748597032055 12423214550408622895548083)
              ·
                refine ⟨18634821825612934343322125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12423214550408622895548083 18634821825612934343322125)
                ·
                  refine ⟨6988058184604850378745797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18634821825612934343322125 6988058184604850378745797)
                  ·
                    refine ⟨1310260909613409446014837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6988058184604850378745797 1310260909613409446014837)
                    ·
                      rfl

theorem cell23_7655172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_7655172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655172 prefixEnd_7655172 := by exact prefixLift 7655172
  have htrace : WordTrace (prefixWord ++ tailWord_7655172) baseStart_7655172 baseEnd_7655172 := by
    simpa [prefixWord, tailWord_7655172, baseEnd_7655172] using wordTrace_append hprefix tailTrace_7655172
  have hstable : (prefixWord ++ tailWord_7655172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655172).length < 2 ^ (prefixWord ++ tailWord_7655172).sum := by decide
  have hdescent : baseEnd_7655172 < baseStart_7655172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655174 : List Nat := [6, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2]
def baseStart_7655174 : Nat := 118140960795 + 7655174 * 2 ^ 59
def prefixEnd_7655174 : Nat := 4983230072969 + 3 ^ 40 * 7655174 * 2
def baseEnd_7655174 : Nat := 3930783755801537330219503

theorem tailTrace_7655174 : CollatzResearch.WordTrace tailWord_7655174 prefixEnd_7655174 3930783755801537330219503 := by
  unfold tailWord_7655174
  simp only [CollatzResearch.WordTrace]
  refine ⟨8725222924019358514903393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 186138089045746314984605717 8725222924019358514903393)
  ·
    refine ⟨6543917193014518886177545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8725222924019358514903393 6543917193014518886177545)
    ·
      refine ⟨4907937894760889164633159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6543917193014518886177545 4907937894760889164633159)
      ·
        refine ⟨7361906842141333746949739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4907937894760889164633159 7361906842141333746949739)
        ·
          refine ⟨11042860263212000620424609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7361906842141333746949739 11042860263212000620424609)
          ·
            refine ⟨8282145197409000465318457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11042860263212000620424609 8282145197409000465318457)
            ·
              refine ⟨6211608898056750348988843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8282145197409000465318457 6211608898056750348988843)
              ·
                refine ⟨9317413347085125523483265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6211608898056750348988843 9317413347085125523483265)
                ·
                  refine ⟨6988060010313844142612449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9317413347085125523483265 6988060010313844142612449)
                  ·
                    refine ⟨5241045007735383106959337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6988060010313844142612449 5241045007735383106959337)
                    ·
                      refine ⟨3930783755801537330219503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5241045007735383106959337 3930783755801537330219503)
                      ·
                        rfl

theorem cell23_7655174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_7655174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655174 prefixEnd_7655174 := by exact prefixLift 7655174
  have htrace : WordTrace (prefixWord ++ tailWord_7655174) baseStart_7655174 baseEnd_7655174 := by
    simpa [prefixWord, tailWord_7655174, baseEnd_7655174] using wordTrace_append hprefix tailTrace_7655174
  have hstable : (prefixWord ++ tailWord_7655174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655174).length < 2 ^ (prefixWord ++ tailWord_7655174).sum := by decide
  have hdescent : baseEnd_7655174 < baseStart_7655174 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655211 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 2, 10]
def baseStart_7655211 : Nat := 118140960795 + 7655211 * 2 ^ 59
def prefixEnd_7655211 : Nat := 4983230072969 + 3 ^ 40 * 7655211 * 2
def baseEnd_7655211 : Nat := 1310267584861917895152277

theorem tailTrace_7655211 : CollatzResearch.WordTrace tailWord_7655211 prefixEnd_7655211 1310267584861917895152277 := by
  unfold tailWord_7655211
  simp only [CollatzResearch.WordTrace]
  refine ⟨279208483069485427796005487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186138988712990285197336991 279208483069485427796005487)
  ·
    refine ⟨418812724604228141694008231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279208483069485427796005487 418812724604228141694008231)
    ·
      refine ⟨628219086906342212541012347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418812724604228141694008231 628219086906342212541012347)
      ·
        refine ⟨942328630359513318811518521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 628219086906342212541012347 942328630359513318811518521)
        ·
          refine ⟨706746472769634989108638891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 942328630359513318811518521 706746472769634989108638891)
          ·
            refine ⟨1060119709154452483662958337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706746472769634989108638891 1060119709154452483662958337)
            ·
              refine ⟨795089781865839362747218753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1060119709154452483662958337 795089781865839362747218753)
              ·
                refine ⟨596317336399379522060414065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 795089781865839362747218753 596317336399379522060414065)
                ·
                  refine ⟨447238002299534641545310549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 596317336399379522060414065 447238002299534641545310549)
                  ·
                    refine ⟨1310267584861917895152277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 447238002299534641545310549 1310267584861917895152277)
                    ·
                      rfl

theorem cell23_7655211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 10].length) (baseStart_7655211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655211 prefixEnd_7655211 := by exact prefixLift 7655211
  have htrace : WordTrace (prefixWord ++ tailWord_7655211) baseStart_7655211 baseEnd_7655211 := by
    simpa [prefixWord, tailWord_7655211, baseEnd_7655211] using wordTrace_append hprefix tailTrace_7655211
  have hstable : (prefixWord ++ tailWord_7655211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655211).length < 2 ^ (prefixWord ++ tailWord_7655211).sum := by decide
  have hdescent : baseEnd_7655211 < baseStart_7655211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655272 : List Nat := [2, 1, 4, 2, 1, 1, 3, 3, 1, 2, 3]
def baseStart_7655272 : Nat := 118140960795 + 7655272 * 2 ^ 59
def prefixEnd_7655272 : Nat := 4983230072969 + 3 ^ 40 * 7655272 * 2
def baseEnd_7655272 : Nat := 3930834076905677946794051

theorem tailTrace_7655272 : CollatzResearch.WordTrace tailWord_7655272 prefixEnd_7655272 3930834076905677946794051 := by
  unfold tailWord_7655272
  simp only [CollatzResearch.WordTrace]
  refine ⟨139605353961132217606988035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186140471948176290142650713 139605353961132217606988035)
  ·
    refine ⟨209408030941698326410482053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139605353961132217606988035 209408030941698326410482053)
    ·
      refine ⟨39264005801568436201965385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209408030941698326410482053 39264005801568436201965385)
      ·
        refine ⟨29448004351176327151474039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39264005801568436201965385 29448004351176327151474039)
        ·
          refine ⟨44172006526764490727211059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29448004351176327151474039 44172006526764490727211059)
          ·
            refine ⟨66258009790146736090816589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44172006526764490727211059 66258009790146736090816589)
            ·
              refine ⟨24846753671305026034056221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66258009790146736090816589 24846753671305026034056221)
              ·
                refine ⟨9317532626739384762771083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24846753671305026034056221 9317532626739384762771083)
                ·
                  refine ⟨13976298940109077144156625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9317532626739384762771083 13976298940109077144156625)
                  ·
                    refine ⟨10482224205081807858117469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13976298940109077144156625 10482224205081807858117469)
                    ·
                      refine ⟨3930834076905677946794051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10482224205081807858117469 3930834076905677946794051)
                      ·
                        rfl

theorem cell23_7655272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_7655272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655272 prefixEnd_7655272 := by exact prefixLift 7655272
  have htrace : WordTrace (prefixWord ++ tailWord_7655272) baseStart_7655272 baseEnd_7655272 := by
    simpa [prefixWord, tailWord_7655272, baseEnd_7655272] using wordTrace_append hprefix tailTrace_7655272
  have hstable : (prefixWord ++ tailWord_7655272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655272).length < 2 ^ (prefixWord ++ tailWord_7655272).sum := by decide
  have hdescent : baseEnd_7655272 < baseStart_7655272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655312 : List Nat := [2, 1, 1, 1, 1, 1, 2, 8, 1, 3, 2]
def baseStart_7655312 : Nat := 118140960795 + 7655312 * 2 ^ 59
def prefixEnd_7655312 : Nat := 4983230072969 + 3 ^ 40 * 7655312 * 2
def baseEnd_7655312 : Nat := 3930854616131857790293867

theorem tailTrace_7655312 : CollatzResearch.WordTrace tailWord_7655312 prefixEnd_7655312 3930854616131857790293867 := by
  unfold tailWord_7655312
  simp only [CollatzResearch.WordTrace]
  refine ⟨139606083421059761022716095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186141444561413014696954793 139606083421059761022716095)
  ·
    refine ⟨209409125131589641534074143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139606083421059761022716095 209409125131589641534074143)
    ·
      refine ⟨314113687697384462301111215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209409125131589641534074143 314113687697384462301111215)
      ·
        refine ⟨471170531546076693451666823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314113687697384462301111215 471170531546076693451666823)
        ·
          refine ⟨706755797319115040177500235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471170531546076693451666823 706755797319115040177500235)
          ·
            refine ⟨1060133695978672560266250353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706755797319115040177500235 1060133695978672560266250353)
            ·
              refine ⟨795100271984004420199687765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1060133695978672560266250353 795100271984004420199687765)
              ·
                refine ⟨9317581312312551799215091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 795100271984004420199687765 9317581312312551799215091)
                ·
                  refine ⟨13976371968468827698822637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9317581312312551799215091 13976371968468827698822637)
                  ·
                    refine ⟨5241139488175810387058489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13976371968468827698822637 5241139488175810387058489)
                    ·
                      refine ⟨3930854616131857790293867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5241139488175810387058489 3930854616131857790293867)
                      ·
                        rfl

theorem cell23_7655312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 8, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 8, 1, 3, 2].length) (baseStart_7655312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655312 prefixEnd_7655312 := by exact prefixLift 7655312
  have htrace : WordTrace (prefixWord ++ tailWord_7655312) baseStart_7655312 baseEnd_7655312 := by
    simpa [prefixWord, tailWord_7655312, baseEnd_7655312] using wordTrace_append hprefix tailTrace_7655312
  have hstable : (prefixWord ++ tailWord_7655312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655312).length < 2 ^ (prefixWord ++ tailWord_7655312).sum := by decide
  have hdescent : baseEnd_7655312 < baseStart_7655312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655320 : List Nat := [2, 1, 2, 6, 1, 2, 1, 3, 1, 2, 2]
def baseStart_7655320 : Nat := 118140960795 + 7655320 * 2 ^ 59
def prefixEnd_7655320 : Nat := 4983230072969 + 3 ^ 40 * 7655320 * 2
def baseEnd_7655320 : Nat := 3930858723977093758993831

theorem tailTrace_7655320 : CollatzResearch.WordTrace tailWord_7655320 prefixEnd_7655320 3930858723977093758993831 := by
  unfold tailWord_7655320
  simp only [CollatzResearch.WordTrace]
  refine ⟨139606229313045269705861707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186141639084060359607815609 139606229313045269705861707)
  ·
    refine ⟨209409343969567904558792561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139606229313045269705861707 209409343969567904558792561)
    ·
      refine ⟨157057007977175928419094421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209409343969567904558792561 157057007977175928419094421)
      ·
        refine ⟨7362047248930121644645051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 157057007977175928419094421 7362047248930121644645051)
        ·
          refine ⟨11043070873395182466967577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7362047248930121644645051 11043070873395182466967577)
          ·
            refine ⟨8282303155046386850225683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11043070873395182466967577 8282303155046386850225683)
            ·
              refine ⟨12423454732569580275338525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8282303155046386850225683 12423454732569580275338525)
              ·
                refine ⟨4658795524713592603251947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12423454732569580275338525 4658795524713592603251947)
                ·
                  refine ⟨6988193287070388904877921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4658795524713592603251947 6988193287070388904877921)
                  ·
                    refine ⟨5241144965302791678658441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6988193287070388904877921 5241144965302791678658441)
                    ·
                      refine ⟨3930858723977093758993831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5241144965302791678658441 3930858723977093758993831)
                      ·
                        rfl

theorem cell23_7655320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_7655320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655320 prefixEnd_7655320 := by exact prefixLift 7655320
  have htrace : WordTrace (prefixWord ++ tailWord_7655320) baseStart_7655320 baseEnd_7655320 := by
    simpa [prefixWord, tailWord_7655320, baseEnd_7655320] using wordTrace_append hprefix tailTrace_7655320
  have hstable : (prefixWord ++ tailWord_7655320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655320).length < 2 ^ (prefixWord ++ tailWord_7655320).sum := by decide
  have hdescent : baseEnd_7655320 < baseStart_7655320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655359 : List Nat := [1, 1, 2, 2, 2, 1, 5, 3, 2, 2, 2]
def baseStart_7655359 : Nat := 118140960795 + 7655359 * 2 ^ 59
def prefixEnd_7655359 : Nat := 4983230072969 + 3 ^ 40 * 7655359 * 2
def baseEnd_7655359 : Nat := 3930878749722619106406151

theorem tailTrace_7655359 : CollatzResearch.WordTrace tailWord_7655359 prefixEnd_7655359 3930878749722619106406151 := by
  unfold tailWord_7655359
  simp only [CollatzResearch.WordTrace]
  refine ⟨279213881072949249072393131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186142587381966166048262087 279213881072949249072393131)
  ·
    refine ⟨418820821609423873608589697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279213881072949249072393131 418820821609423873608589697)
    ·
      refine ⟨314115616207067905206442273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418820821609423873608589697 314115616207067905206442273)
      ·
        refine ⟨235586712155300928904831705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314115616207067905206442273 235586712155300928904831705)
        ·
          refine ⟨176690034116475696678623779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235586712155300928904831705 176690034116475696678623779)
          ·
            refine ⟨265035051174713545017935669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176690034116475696678623779 265035051174713545017935669)
            ·
              refine ⟨24847036047629394845431469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 265035051174713545017935669 24847036047629394845431469)
              ·
                refine ⟨9317638517861023067036801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24847036047629394845431469 9317638517861023067036801)
                ·
                  refine ⟨6988228888395767300277601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9317638517861023067036801 6988228888395767300277601)
                  ·
                    refine ⟨5241171666296825475208201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6988228888395767300277601 5241171666296825475208201)
                    ·
                      refine ⟨3930878749722619106406151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5241171666296825475208201 3930878749722619106406151)
                      ·
                        rfl

theorem cell23_7655359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 3, 2, 2, 2].length) (baseStart_7655359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655359 prefixEnd_7655359 := by exact prefixLift 7655359
  have htrace : WordTrace (prefixWord ++ tailWord_7655359) baseStart_7655359 baseEnd_7655359 := by
    simpa [prefixWord, tailWord_7655359, baseEnd_7655359] using wordTrace_append hprefix tailTrace_7655359
  have hstable : (prefixWord ++ tailWord_7655359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655359).length < 2 ^ (prefixWord ++ tailWord_7655359).sum := by decide
  have hdescent : baseEnd_7655359 < baseStart_7655359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655399 : List Nat := [1, 1, 5, 2, 3, 1, 1, 4, 5]
def baseStart_7655399 : Nat := 118140960795 + 7655399 * 2 ^ 59
def prefixEnd_7655399 : Nat := 4983230072969 + 3 ^ 40 * 7655399 * 2
def baseEnd_7655399 : Nat := 436766587660977661100663

theorem tailTrace_7655399 : CollatzResearch.WordTrace tailWord_7655399 prefixEnd_7655399 436766587660977661100663 := by
  unfold tailWord_7655399
  simp only [CollatzResearch.WordTrace]
  refine ⟨279215339992804335903849251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186143559995202890602566167 279215339992804335903849251)
  ·
    refine ⟨418823009989206503855773877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279215339992804335903849251 418823009989206503855773877)
    ·
      refine ⟨39264657186488109736478801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 418823009989206503855773877 39264657186488109736478801)
      ·
        refine ⟨29448492889866082302359101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39264657186488109736478801 29448492889866082302359101)
        ·
          refine ⟨11043184833699780863384663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29448492889866082302359101 11043184833699780863384663)
          ·
            refine ⟨16564777250549671295076995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11043184833699780863384663 16564777250549671295076995)
            ·
              refine ⟨24847165875824506942615493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16564777250549671295076995 24847165875824506942615493)
              ·
                refine ⟨4658843601717095051740405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24847165875824506942615493 4658843601717095051740405)
                ·
                  refine ⟨436766587660977661100663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4658843601717095051740405 436766587660977661100663)
                  ·
                    rfl

theorem cell23_7655399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 4, 5].length) (baseStart_7655399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655399 prefixEnd_7655399 := by exact prefixLift 7655399
  have htrace : WordTrace (prefixWord ++ tailWord_7655399) baseStart_7655399 baseEnd_7655399 := by
    simpa [prefixWord, tailWord_7655399, baseEnd_7655399] using wordTrace_append hprefix tailTrace_7655399
  have hstable : (prefixWord ++ tailWord_7655399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655399).length < 2 ^ (prefixWord ++ tailWord_7655399).sum := by decide
  have hdescent : baseEnd_7655399 < baseStart_7655399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655402 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 1, 7, 2]
def baseStart_7655402 : Nat := 118140960795 + 7655402 * 2 ^ 59
def prefixEnd_7655402 : Nat := 4983230072969 + 3 ^ 40 * 7655402 * 2
def baseEnd_7655402 : Nat := 3930900829390762438168453

theorem tailTrace_7655402 : CollatzResearch.WordTrace tailWord_7655402 prefixEnd_7655402 3930900829390762438168453 := by
  unfold tailWord_7655402
  simp only [CollatzResearch.WordTrace]
  refine ⟨69803862352948366854052115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186143632941195644944138973 69803862352948366854052115)
  ·
    refine ⟨104705793529422550281078173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69803862352948366854052115 104705793529422550281078173)
    ·
      refine ⟨39264672573533456355404315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104705793529422550281078173 39264672573533456355404315)
      ·
        refine ⟨58897008860300184533106473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39264672573533456355404315 58897008860300184533106473)
        ·
          refine ⟨44172756645225138399829855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58897008860300184533106473 44172756645225138399829855)
          ·
            refine ⟨66259134967837707599744783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44172756645225138399829855 66259134967837707599744783)
            ·
              refine ⟨99388702451756561399617175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66259134967837707599744783 99388702451756561399617175)
              ·
                refine ⟨149083053677634842099425763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99388702451756561399617175 149083053677634842099425763)
                ·
                  refine ⟨223624580516452263149138645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149083053677634842099425763 223624580516452263149138645)
                  ·
                    refine ⟨5241201105854349917557937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 223624580516452263149138645 5241201105854349917557937)
                    ·
                      refine ⟨3930900829390762438168453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5241201105854349917557937 3930900829390762438168453)
                      ·
                        rfl

theorem cell23_7655402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 1, 7, 2].length) (baseStart_7655402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655402 prefixEnd_7655402 := by exact prefixLift 7655402
  have htrace : WordTrace (prefixWord ++ tailWord_7655402) baseStart_7655402 baseEnd_7655402 := by
    simpa [prefixWord, tailWord_7655402, baseEnd_7655402] using wordTrace_append hprefix tailTrace_7655402
  have hstable : (prefixWord ++ tailWord_7655402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655402).length < 2 ^ (prefixWord ++ tailWord_7655402).sum := by decide
  have hdescent : baseEnd_7655402 < baseStart_7655402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655432 : List Nat := [2, 1, 3, 2, 1, 2, 1, 2, 1, 6, 2]
def baseStart_7655432 : Nat := 118140960795 + 7655432 * 2 ^ 59
def prefixEnd_7655432 : Nat := 4983230072969 + 3 ^ 40 * 7655432 * 2
def baseEnd_7655432 : Nat := 3930916233810397320793315

theorem tailTrace_7655432 : CollatzResearch.WordTrace tailWord_7655432 prefixEnd_7655432 3930916233810397320793315 := by
  unfold tailWord_7655432
  simp only [CollatzResearch.WordTrace]
  refine ⟨139608271800842391269900275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186144362401123188359867033 139608271800842391269900275)
  ·
    refine ⟨209412407701263586904850413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139608271800842391269900275 209412407701263586904850413)
    ·
      refine ⟨78529652887973845089318905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209412407701263586904850413 78529652887973845089318905)
      ·
        refine ⟨58897239665980383816989179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78529652887973845089318905 58897239665980383816989179)
        ·
          refine ⟨88345859498970575725483769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58897239665980383816989179 88345859498970575725483769)
          ·
            refine ⟨66259394624227931794112827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88345859498970575725483769 66259394624227931794112827)
            ·
              refine ⟨99389091936341897691169241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66259394624227931794112827 99389091936341897691169241)
              ·
                refine ⟨74541818952256423268376931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99389091936341897691169241 74541818952256423268376931)
                ·
                  refine ⟨111812728428384634902565397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74541818952256423268376931 111812728428384634902565397)
                  ·
                    refine ⟨5241221645080529761057753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 111812728428384634902565397 5241221645080529761057753)
                    ·
                      refine ⟨3930916233810397320793315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5241221645080529761057753 3930916233810397320793315)
                      ·
                        rfl

theorem cell23_7655432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 1, 6, 2].length) (baseStart_7655432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655432 prefixEnd_7655432 := by exact prefixLift 7655432
  have htrace : WordTrace (prefixWord ++ tailWord_7655432) baseStart_7655432 baseEnd_7655432 := by
    simpa [prefixWord, tailWord_7655432, baseEnd_7655432] using wordTrace_append hprefix tailTrace_7655432
  have hstable : (prefixWord ++ tailWord_7655432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655432).length < 2 ^ (prefixWord ++ tailWord_7655432).sum := by decide
  have hdescent : baseEnd_7655432 < baseStart_7655432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655455 : List Nat := [1, 1, 2, 4, 1, 2, 3, 1, 8]
def baseStart_7655455 : Nat := 118140960795 + 7655455 * 2 ^ 59
def prefixEnd_7655455 : Nat := 4983230072969 + 3 ^ 40 * 7655455 * 2
def baseEnd_7655455 : Nat := 436769782651716747867301

theorem tailTrace_7655455 : CollatzResearch.WordTrace tailWord_7655455 prefixEnd_7655455 436769782651716747867301 := by
  unfold tailWord_7655455
  simp only [CollatzResearch.WordTrace]
  refine ⟨279217382480601457467887819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186144921653734304978591879 279217382480601457467887819)
  ·
    refine ⟨418826073720902186201831729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279217382480601457467887819 418826073720902186201831729)
    ·
      refine ⟨314119555290676639651373797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418826073720902186201831729 314119555290676639651373797)
      ·
        refine ⟨58897416617001869934632587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 314119555290676639651373797 58897416617001869934632587)
        ·
          refine ⟨88346124925502804901948881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58897416617001869934632587 88346124925502804901948881)
          ·
            refine ⟨66259593694127103676461661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88346124925502804901948881 66259593694127103676461661)
            ·
              refine ⟨24847347635297663878673123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66259593694127103676461661 24847347635297663878673123)
              ·
                refine ⟨37271021452946495818009685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24847347635297663878673123 37271021452946495818009685)
                ·
                  refine ⟨436769782651716747867301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37271021452946495818009685 436769782651716747867301)
                  ·
                    rfl

theorem cell23_7655455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 8].length) (baseStart_7655455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655455 prefixEnd_7655455 := by exact prefixLift 7655455
  have htrace : WordTrace (prefixWord ++ tailWord_7655455) baseStart_7655455 baseEnd_7655455 := by
    simpa [prefixWord, tailWord_7655455, baseEnd_7655455] using wordTrace_append hprefix tailTrace_7655455
  have hstable : (prefixWord ++ tailWord_7655455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655455).length < 2 ^ (prefixWord ++ tailWord_7655455).sum := by decide
  have hdescent : baseEnd_7655455 < baseStart_7655455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655459 : List Nat := [1, 1, 1, 4, 3, 1, 1, 6, 1, 4]
def baseStart_7655459 : Nat := 118140960795 + 7655459 * 2 ^ 59
def prefixEnd_7655459 : Nat := 4983230072969 + 3 ^ 40 * 7655459 * 2
def baseEnd_7655459 : Nat := 1310310032596022905051897

theorem tailTrace_7655459 : CollatzResearch.WordTrace tailWord_7655459 prefixEnd_7655459 1310310032596022905051897 := by
  unfold tailWord_7655459
  simp only [CollatzResearch.WordTrace]
  refine ⟨279217528372586966151033431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186145018915057977434022287 279217528372586966151033431)
  ·
    refine ⟨418826292558880449226550147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279217528372586966151033431 418826292558880449226550147)
    ·
      refine ⟨628239438838320673839825221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418826292558880449226550147 628239438838320673839825221)
      ·
        refine ⟨117794894782185126344967229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 628239438838320673839825221 117794894782185126344967229)
        ·
          refine ⟨44173085543319422379362711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117794894782185126344967229 44173085543319422379362711)
          ·
            refine ⟨66259628314979133569044067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44173085543319422379362711 66259628314979133569044067)
            ·
              refine ⟨99389442472468700353566101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66259628314979133569044067 99389442472468700353566101)
              ·
                refine ⟨4658880115896970329073411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99389442472468700353566101 4658880115896970329073411)
                ·
                  refine ⟨6988320173845455493610117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4658880115896970329073411 6988320173845455493610117)
                  ·
                    refine ⟨1310310032596022905051897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6988320173845455493610117 1310310032596022905051897)
                    ·
                      rfl

theorem cell23_7655459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 6, 1, 4].length) (baseStart_7655459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655459 prefixEnd_7655459 := by exact prefixLift 7655459
  have htrace : WordTrace (prefixWord ++ tailWord_7655459) baseStart_7655459 baseEnd_7655459 := by
    simpa [prefixWord, tailWord_7655459, baseEnd_7655459] using wordTrace_append hprefix tailTrace_7655459
  have hstable : (prefixWord ++ tailWord_7655459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655459).length < 2 ^ (prefixWord ++ tailWord_7655459).sum := by decide
  have hdescent : baseEnd_7655459 < baseStart_7655459 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655509 : List Nat := [1, 3, 2, 2, 1, 3, 1, 1, 4, 3, 2]
def baseStart_7655509 : Nat := 118140960795 + 7655509 * 2 ^ 59
def prefixEnd_7655509 : Nat := 4983230072969 + 3 ^ 40 * 7655509 * 2
def baseEnd_7655509 : Nat := 3930955771820793519530461

theorem tailTrace_7655509 : CollatzResearch.WordTrace tailWord_7655509 prefixEnd_7655509 3930955771820793519530461 := by
  unfold tailWord_7655509
  simp only [CollatzResearch.WordTrace]
  refine ⟨279219352022405824690353581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186146234681603883126902387 279219352022405824690353581)
  ·
    refine ⟨104707257008402184258882593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279219352022405824690353581 104707257008402184258882593)
    ·
      refine ⟨78530442756301638194161945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104707257008402184258882593 78530442756301638194161945)
      ·
        refine ⟨58897832067226228645621459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78530442756301638194161945 58897832067226228645621459)
        ·
          refine ⟨88346748100839342968432189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58897832067226228645621459 88346748100839342968432189)
          ·
            refine ⟨33130030537814753613162071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88346748100839342968432189 33130030537814753613162071)
            ·
              refine ⟨49695045806722130419743107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33130030537814753613162071 49695045806722130419743107)
              ·
                refine ⟨74542568710083195629614661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49695045806722130419743107 74542568710083195629614661)
                ·
                  refine ⟨13976731633140599180552749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74542568710083195629614661 13976731633140599180552749)
                  ·
                    refine ⟨5241274362427724692707281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13976731633140599180552749 5241274362427724692707281)
                    ·
                      refine ⟨3930955771820793519530461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5241274362427724692707281 3930955771820793519530461)
                      ·
                        rfl

theorem cell23_7655509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4, 3, 2].length) (baseStart_7655509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655509 prefixEnd_7655509 := by exact prefixLift 7655509
  have htrace : WordTrace (prefixWord ++ tailWord_7655509) baseStart_7655509 baseEnd_7655509 := by
    simpa [prefixWord, tailWord_7655509, baseEnd_7655509] using wordTrace_append hprefix tailTrace_7655509
  have hstable : (prefixWord ++ tailWord_7655509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655509).length < 2 ^ (prefixWord ++ tailWord_7655509).sum := by decide
  have hdescent : baseEnd_7655509 < baseStart_7655509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655516 : List Nat := [2, 2, 4, 1, 1, 2, 3, 1, 3, 1, 3]
def baseStart_7655516 : Nat := 118140960795 + 7655516 * 2 ^ 59
def prefixEnd_7655516 : Nat := 4983230072969 + 3 ^ 40 * 7655516 * 2
def baseEnd_7655516 : Nat := 3930959366185374992142929

theorem tailTrace_7655516 : CollatzResearch.WordTrace tailWord_7655516 prefixEnd_7655516 3930959366185374992142929 := by
  unfold tailWord_7655516
  simp only [CollatzResearch.WordTrace]
  refine ⟨139609803666690232442929201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186146404888920309923905601 139609803666690232442929201)
  ·
    refine ⟨104707352750017674332196901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139609803666690232442929201 104707352750017674332196901)
    ·
      refine ⟨19632628640628313937286919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104707352750017674332196901 19632628640628313937286919)
      ·
        refine ⟨29448942960942470905930379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19632628640628313937286919 29448942960942470905930379)
        ·
          refine ⟨44173414441413706358895569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29448942960942470905930379 44173414441413706358895569)
          ·
            refine ⟨33130060831060279769171677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44173414441413706358895569 33130060831060279769171677)
            ·
              refine ⟨12423772811647604913439379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33130060831060279769171677 12423772811647604913439379)
              ·
                refine ⟨18635659217471407370159069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12423772811647604913439379 18635659217471407370159069)
                ·
                  refine ⟨6988372206551777763809651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18635659217471407370159069 6988372206551777763809651)
                  ·
                    refine ⟨10482558309827666645714477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6988372206551777763809651 10482558309827666645714477)
                    ·
                      refine ⟨3930959366185374992142929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10482558309827666645714477 3930959366185374992142929)
                      ·
                        rfl

theorem cell23_7655516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_7655516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655516 prefixEnd_7655516 := by exact prefixLift 7655516
  have htrace : WordTrace (prefixWord ++ tailWord_7655516) baseStart_7655516 baseEnd_7655516 := by
    simpa [prefixWord, tailWord_7655516, baseEnd_7655516] using wordTrace_append hprefix tailTrace_7655516
  have hstable : (prefixWord ++ tailWord_7655516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655516).length < 2 ^ (prefixWord ++ tailWord_7655516).sum := by decide
  have hdescent : baseEnd_7655516 < baseStart_7655516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655556 : List Nat := [2, 3, 2, 1, 2, 1, 5, 1, 1, 1, 4]
def baseStart_7655556 : Nat := 118140960795 + 7655556 * 2 ^ 59
def prefixEnd_7655556 : Nat := 4983230072969 + 3 ^ 40 * 7655556 * 2
def baseEnd_7655556 : Nat := 3930979905411554835642745

theorem tailTrace_7655556 : CollatzResearch.WordTrace tailWord_7655556 prefixEnd_7655556 3930979905411554835642745 := by
  unfold tailWord_7655556
  simp only [CollatzResearch.WordTrace]
  refine ⟨139610533126617775858657261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186147377502157034478209681 139610533126617775858657261)
  ·
    refine ⟨52353949922481665946996473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139610533126617775858657261 52353949922481665946996473)
    ·
      refine ⟨39265462441861249460247355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52353949922481665946996473 39265462441861249460247355)
      ·
        refine ⟨58898193662791874190371033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39265462441861249460247355 58898193662791874190371033)
        ·
          refine ⟨44173645247093905642778275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58898193662791874190371033 44173645247093905642778275)
          ·
            refine ⟨66260467870640858464167413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44173645247093905642778275 66260467870640858464167413)
            ·
              refine ⟨6211918862872580481015695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66260467870640858464167413 6211918862872580481015695)
              ·
                refine ⟨9317878294308870721523543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6211918862872580481015695 9317878294308870721523543)
                ·
                  refine ⟨13976817441463306082285315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9317878294308870721523543 13976817441463306082285315)
                  ·
                    refine ⟨20965226162194959123427973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13976817441463306082285315 20965226162194959123427973)
                    ·
                      refine ⟨3930979905411554835642745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20965226162194959123427973 3930979905411554835642745)
                      ·
                        rfl

theorem cell23_7655556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 1, 1, 1, 4].length) (baseStart_7655556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655556 prefixEnd_7655556 := by exact prefixLift 7655556
  have htrace : WordTrace (prefixWord ++ tailWord_7655556) baseStart_7655556 baseEnd_7655556 := by
    simpa [prefixWord, tailWord_7655556, baseEnd_7655556] using wordTrace_append hprefix tailTrace_7655556
  have hstable : (prefixWord ++ tailWord_7655556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655556).length < 2 ^ (prefixWord ++ tailWord_7655556).sum := by decide
  have hdescent : baseEnd_7655556 < baseStart_7655556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655559 : List Nat := [1, 1, 4, 2, 1, 1, 2, 5, 1, 2, 3]
def baseStart_7655559 : Nat := 118140960795 + 7655559 * 2 ^ 59
def prefixEnd_7655559 : Nat := 4983230072969 + 3 ^ 40 * 7655559 * 2
def baseEnd_7655559 : Nat := 3930981445853518323905231

theorem tailTrace_7655559 : CollatzResearch.WordTrace tailWord_7655559 prefixEnd_7655559 3930981445853518323905231 := by
  unfold tailWord_7655559
  simp only [CollatzResearch.WordTrace]
  refine ⟨279221175672224683229673731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186147450448149788819782487 279221175672224683229673731)
  ·
    refine ⟨418831763508337024844510597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279221175672224683229673731 418831763508337024844510597)
    ·
      refine ⟨78530955657813192158345737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 418831763508337024844510597 78530955657813192158345737)
      ·
        refine ⟨58898216743359894118759303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78530955657813192158345737 58898216743359894118759303)
        ·
          refine ⟨88347325115039841178138955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58898216743359894118759303 88347325115039841178138955)
          ·
            refine ⟨132520987672559761767208433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88347325115039841178138955 132520987672559761767208433)
            ·
              refine ⟨99390740754419821325406325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132520987672559761767208433 99390740754419821325406325)
              ·
                refine ⟨9317881945726858249256843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99390740754419821325406325 9317881945726858249256843)
                ·
                  refine ⟨13976822918590287373885265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9317881945726858249256843 13976822918590287373885265)
                  ·
                    refine ⟨10482617188942715530413949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13976822918590287373885265 10482617188942715530413949)
                    ·
                      refine ⟨3930981445853518323905231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10482617188942715530413949 3930981445853518323905231)
                      ·
                        rfl

theorem cell23_7655559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_7655559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655559 prefixEnd_7655559 := by exact prefixLift 7655559
  have htrace : WordTrace (prefixWord ++ tailWord_7655559) baseStart_7655559 baseEnd_7655559 := by
    simpa [prefixWord, tailWord_7655559, baseEnd_7655559] using wordTrace_append hprefix tailTrace_7655559
  have hstable : (prefixWord ++ tailWord_7655559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655559).length < 2 ^ (prefixWord ++ tailWord_7655559).sum := by decide
  have hdescent : baseEnd_7655559 < baseStart_7655559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655573 : List Nat := [1, 3, 2, 1, 1, 1, 5, 4, 1, 2, 2]
def baseStart_7655573 : Nat := 118140960795 + 7655573 * 2 ^ 59
def prefixEnd_7655573 : Nat := 4983230072969 + 3 ^ 40 * 7655573 * 2
def baseEnd_7655573 : Nat := 3930988634582681269130167

theorem tailTrace_7655573 : CollatzResearch.WordTrace tailWord_7655573 prefixEnd_7655573 3930988634582681269130167 := by
  unfold tailWord_7655573
  simp only [CollatzResearch.WordTrace]
  refine ⟨279221686294173963620683373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186147790862782642413788915 279221686294173963620683373)
  ·
    refine ⟨104708132360315236357756265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279221686294173963620683373 104708132360315236357756265)
    ·
      refine ⟨78531099270236427268317199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104708132360315236357756265 78531099270236427268317199)
      ·
        refine ⟨117796648905354640902475799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78531099270236427268317199 117796648905354640902475799)
        ·
          refine ⟨176694973358031961353713699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117796648905354640902475799 176694973358031961353713699)
          ·
            refine ⟨265042460037047942030570549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176694973358031961353713699 265042460037047942030570549)
            ·
              refine ⟨24847730628473244565365989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 265042460037047942030570549 24847730628473244565365989)
              ·
                refine ⟨4658949492838733356006123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24847730628473244565365989 4658949492838733356006123)
                ·
                  refine ⟨6988424239258100034009185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4658949492838733356006123 6988424239258100034009185)
                  ·
                    refine ⟨5241318179443575025506889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6988424239258100034009185 5241318179443575025506889)
                    ·
                      refine ⟨3930988634582681269130167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5241318179443575025506889 3930988634582681269130167)
                      ·
                        rfl

theorem cell23_7655573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 4, 1, 2, 2].length) (baseStart_7655573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655573 prefixEnd_7655573 := by exact prefixLift 7655573
  have htrace : WordTrace (prefixWord ++ tailWord_7655573) baseStart_7655573 baseEnd_7655573 := by
    simpa [prefixWord, tailWord_7655573, baseEnd_7655573] using wordTrace_append hprefix tailTrace_7655573
  have hstable : (prefixWord ++ tailWord_7655573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655573).length < 2 ^ (prefixWord ++ tailWord_7655573).sum := by decide
  have hdescent : baseEnd_7655573 < baseStart_7655573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655586 : List Nat := [3, 3, 1, 3, 1, 2, 2, 1, 1, 2, 4]
def baseStart_7655586 : Nat := 118140960795 + 7655586 * 2 ^ 59
def prefixEnd_7655586 : Nat := 4983230072969 + 3 ^ 40 * 7655586 * 2
def baseEnd_7655586 : Nat := 3930995309831189718267607

theorem tailTrace_7655586 : CollatzResearch.WordTrace tailWord_7655586 prefixEnd_7655586 3930995309831189718267607 := by
  unfold tailWord_7655586
  simp only [CollatzResearch.WordTrace]
  refine ⟨69805540110781716710226653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186148106962084577893937741 69805540110781716710226653)
  ·
    refine ⟨26177077541543143766334995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69805540110781716710226653 26177077541543143766334995)
    ·
      refine ⟨39265616312314715649502493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26177077541543143766334995 39265616312314715649502493)
      ·
        refine ⟨14724606117118018368563435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39265616312314715649502493 14724606117118018368563435)
        ·
          refine ⟨22086909175677027552845153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14724606117118018368563435 22086909175677027552845153)
          ·
            refine ⟨16565181881757770664633865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22086909175677027552845153 16565181881757770664633865)
            ·
              refine ⟨12423886411318327998475399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16565181881757770664633865 12423886411318327998475399)
              ·
                refine ⟨18635829616977491997713099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12423886411318327998475399 18635829616977491997713099)
                ·
                  refine ⟨27953744425466237996569649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18635829616977491997713099 27953744425466237996569649)
                  ·
                    refine ⟨20965308319099678497427237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27953744425466237996569649 20965308319099678497427237)
                    ·
                      refine ⟨3930995309831189718267607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20965308319099678497427237 3930995309831189718267607)
                      ·
                        rfl

theorem cell23_7655586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_7655586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655586 prefixEnd_7655586 := by exact prefixLift 7655586
  have htrace : WordTrace (prefixWord ++ tailWord_7655586) baseStart_7655586 baseEnd_7655586 := by
    simpa [prefixWord, tailWord_7655586, baseEnd_7655586] using wordTrace_append hprefix tailTrace_7655586
  have hstable : (prefixWord ++ tailWord_7655586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655586).length < 2 ^ (prefixWord ++ tailWord_7655586).sum := by decide
  have hdescent : baseEnd_7655586 < baseStart_7655586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655589 : List Nat := [1, 3, 1, 2, 1, 3, 4, 1, 1, 3, 3]
def baseStart_7655589 : Nat := 118140960795 + 7655589 * 2 ^ 59
def prefixEnd_7655589 : Nat := 4983230072969 + 3 ^ 40 * 7655589 * 2
def baseEnd_7655589 : Nat := 3930996850273153206530093

theorem tailTrace_7655589 : CollatzResearch.WordTrace tailWord_7655589 prefixEnd_7655589 3930996850273153206530093 := by
  unfold tailWord_7655589
  simp only [CollatzResearch.WordTrace]
  refine ⟨279222269862115998353265821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186148179908077332235510547 279222269862115998353265821)
  ·
    refine ⟨104708351198293499382474683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279222269862115998353265821 104708351198293499382474683)
    ·
      refine ⟨157062526797440249073712025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104708351198293499382474683 157062526797440249073712025)
      ·
        refine ⟨117796895098080186805284019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157062526797440249073712025 117796895098080186805284019)
        ·
          refine ⟨176695342647120280207926029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117796895098080186805284019 176695342647120280207926029)
          ·
            refine ⟨66260753492670105077972261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176695342647120280207926029 66260753492670105077972261)
            ·
              refine ⟨12423891279875644702119799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66260753492670105077972261 12423891279875644702119799)
              ·
                refine ⟨18635836919813467053179699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12423891279875644702119799 18635836919813467053179699)
                ·
                  refine ⟨27953755379720200579769549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18635836919813467053179699 27953755379720200579769549)
                  ·
                    refine ⟨10482658267395075217413581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27953755379720200579769549 10482658267395075217413581)
                    ·
                      refine ⟨3930996850273153206530093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10482658267395075217413581 3930996850273153206530093)
                      ·
                        rfl

theorem cell23_7655589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 3, 3].length) (baseStart_7655589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655589 prefixEnd_7655589 := by exact prefixLift 7655589
  have htrace : WordTrace (prefixWord ++ tailWord_7655589) baseStart_7655589 baseEnd_7655589 := by
    simpa [prefixWord, tailWord_7655589, baseEnd_7655589] using wordTrace_append hprefix tailTrace_7655589
  have hstable : (prefixWord ++ tailWord_7655589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655589).length < 2 ^ (prefixWord ++ tailWord_7655589).sum := by decide
  have hdescent : baseEnd_7655589 < baseStart_7655589 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655602 : List Nat := [3, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5]
def baseStart_7655602 : Nat := 118140960795 + 7655602 * 2 ^ 59
def prefixEnd_7655602 : Nat := 4983230072969 + 3 ^ 40 * 7655602 * 2
def baseEnd_7655602 : Nat := 3931003525521661655667533

theorem tailTrace_7655602 : CollatzResearch.WordTrace tailWord_7655602 prefixEnd_7655602 3931003525521661655667533 := by
  unfold tailWord_7655602
  simp only [CollatzResearch.WordTrace]
  refine ⟨69805686002767225393372265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186148496007379267715659373 69805686002767225393372265)
  ·
    refine ⟨52354264502075419045029199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69805686002767225393372265 52354264502075419045029199)
    ·
      refine ⟨78531396753113128567543799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52354264502075419045029199 78531396753113128567543799)
      ·
        refine ⟨117797095129669692851315699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78531396753113128567543799 117797095129669692851315699)
        ·
          refine ⟨176695642694504539276973549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117797095129669692851315699 176695642694504539276973549)
          ·
            refine ⟨66260866010439202228865081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176695642694504539276973549 66260866010439202228865081)
            ·
              refine ⟨49695649507829401671648811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66260866010439202228865081 49695649507829401671648811)
              ·
                refine ⟨74543474261744102507473217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49695649507829401671648811 74543474261744102507473217)
                ·
                  refine ⟨55907605696308076880604913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74543474261744102507473217 55907605696308076880604913)
                  ·
                    refine ⟨41930704272231057660453685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55907605696308076880604913 41930704272231057660453685)
                    ·
                      refine ⟨3931003525521661655667533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41930704272231057660453685 3931003525521661655667533)
                      ·
                        rfl

theorem cell23_7655602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_7655602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655602 prefixEnd_7655602 := by exact prefixLift 7655602
  have htrace : WordTrace (prefixWord ++ tailWord_7655602) baseStart_7655602 baseEnd_7655602 := by
    simpa [prefixWord, tailWord_7655602, baseEnd_7655602] using wordTrace_append hprefix tailTrace_7655602
  have hstable : (prefixWord ++ tailWord_7655602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655602).length < 2 ^ (prefixWord ++ tailWord_7655602).sum := by decide
  have hdescent : baseEnd_7655602 < baseStart_7655602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655604 : List Nat := [2, 5, 3, 1, 2, 1, 2, 1, 1, 5]
def baseStart_7655604 : Nat := 118140960795 + 7655604 * 2 ^ 59
def prefixEnd_7655604 : Nat := 4983230072969 + 3 ^ 40 * 7655604 * 2
def baseEnd_7655604 : Nat := 1310334850827656882614175

theorem tailTrace_7655604 : CollatzResearch.WordTrace tailWord_7655604 prefixEnd_7655604 1310334850827656882614175 := by
  unfold tailWord_7655604
  simp only [CollatzResearch.WordTrace]
  refine ⟨139611408478530827957530933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186148544638041103943374577 139611408478530827957530933)
  ·
    refine ⟨13088569544862265121018525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139611408478530827957530933 13088569544862265121018525)
    ·
      refine ⟨4908213579323349420381947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13088569544862265121018525 4908213579323349420381947)
      ·
        refine ⟨7362320368985024130572921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4908213579323349420381947 7362320368985024130572921)
        ·
          refine ⟨5521740276738768097929691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7362320368985024130572921 5521740276738768097929691)
          ·
            refine ⟨8282610415108152146894537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5521740276738768097929691 8282610415108152146894537)
            ·
              refine ⟨6211957811331114110170903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8282610415108152146894537 6211957811331114110170903)
              ·
                refine ⟨9317936716996671165256355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6211957811331114110170903 9317936716996671165256355)
                ·
                  refine ⟨13976905075495006747884533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9317936716996671165256355 13976905075495006747884533)
                  ·
                    refine ⟨1310334850827656882614175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13976905075495006747884533 1310334850827656882614175)
                    ·
                      rfl

theorem cell23_7655604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_7655604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655604 prefixEnd_7655604 := by exact prefixLift 7655604
  have htrace : WordTrace (prefixWord ++ tailWord_7655604) baseStart_7655604 baseEnd_7655604 := by
    simpa [prefixWord, tailWord_7655604, baseEnd_7655604] using wordTrace_append hprefix tailTrace_7655604
  have hstable : (prefixWord ++ tailWord_7655604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655604).length < 2 ^ (prefixWord ++ tailWord_7655604).sum := by decide
  have hdescent : baseEnd_7655604 < baseStart_7655604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655716 : List Nat := [2, 3, 1, 3, 1, 3, 2, 1, 2, 5]
def baseStart_7655716 : Nat := 118140960795 + 7655716 * 2 ^ 59
def prefixEnd_7655716 : Nat := 4983230072969 + 3 ^ 40 * 7655716 * 2
def baseEnd_7655716 : Nat := 1310354020772091403214003

theorem tailTrace_7655716 : CollatzResearch.WordTrace tailWord_7655716 prefixEnd_7655716 1310354020772091403214003 := by
  unfold tailWord_7655716
  simp only [CollatzResearch.WordTrace]
  refine ⟨139613450966327949521569501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186151267955103932695426001 139613450966327949521569501)
  ·
    refine ⟨52355044112372981070588563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139613450966327949521569501 52355044112372981070588563)
    ·
      refine ⟨78532566168559471605882845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52355044112372981070588563 78532566168559471605882845)
      ·
        refine ⟨29449712313209801852206067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78532566168559471605882845 29449712313209801852206067)
        ·
          refine ⟨44174568469814702778309101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29449712313209801852206067 44174568469814702778309101)
          ·
            refine ⟨16565463176180513541865913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44174568469814702778309101 16565463176180513541865913)
            ·
              refine ⟨12424097382135385156399435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16565463176180513541865913 12424097382135385156399435)
              ·
                refine ⟨18636146073203077734599153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12424097382135385156399435 18636146073203077734599153)
                ·
                  refine ⟨13977109554902308300949365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18636146073203077734599153 13977109554902308300949365)
                  ·
                    refine ⟨1310354020772091403214003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13977109554902308300949365 1310354020772091403214003)
                    ·
                      rfl

theorem cell23_7655716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 2, 5].length) (baseStart_7655716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655716 prefixEnd_7655716 := by exact prefixLift 7655716
  have htrace : WordTrace (prefixWord ++ tailWord_7655716) baseStart_7655716 baseEnd_7655716 := by
    simpa [prefixWord, tailWord_7655716, baseEnd_7655716] using wordTrace_append hprefix tailTrace_7655716
  have hstable : (prefixWord ++ tailWord_7655716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655716).length < 2 ^ (prefixWord ++ tailWord_7655716).sum := by decide
  have hdescent : baseEnd_7655716 < baseStart_7655716 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655803 : List Nat := [1, 1, 1, 1, 1, 8, 2, 1, 3, 1, 3]
def baseStart_7655803 : Nat := 118140960795 + 7655803 * 2 ^ 59
def prefixEnd_7655803 : Nat := 4983230072969 + 3 ^ 40 * 7655803 * 2
def baseEnd_7655803 : Nat := 3931106735133215369254109

theorem tailTrace_7655803 : CollatzResearch.WordTrace tailWord_7655803 prefixEnd_7655803 3931106735133215369254109 := by
  unfold tailWord_7655803
  simp only [CollatzResearch.WordTrace]
  refine ⟨279230075083340712901556063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186153383388893808601037375 279230075083340712901556063)
  ·
    refine ⟨418845112625011069352334095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279230075083340712901556063 418845112625011069352334095)
    ·
      refine ⟨628267668937516604028501143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418845112625011069352334095 628267668937516604028501143)
      ·
        refine ⟨942401503406274906042751715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 628267668937516604028501143 942401503406274906042751715)
        ·
          refine ⟨1413602255109412359064127573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 942401503406274906042751715 1413602255109412359064127573)
          ·
            refine ⟨16565651427063426082782745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1413602255109412359064127573 16565651427063426082782745)
            ·
              refine ⟨12424238570297569562087059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16565651427063426082782745 12424238570297569562087059)
              ·
                refine ⟨18636357855446354343130589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12424238570297569562087059 18636357855446354343130589)
                ·
                  refine ⟨6988634195792382878673971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18636357855446354343130589 6988634195792382878673971)
                  ·
                    refine ⟨10482951293688574318010957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6988634195792382878673971 10482951293688574318010957)
                    ·
                      refine ⟨3931106735133215369254109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10482951293688574318010957 3931106735133215369254109)
                      ·
                        rfl

theorem cell23_7655803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 3, 1, 3].length) (baseStart_7655803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655803 prefixEnd_7655803 := by exact prefixLift 7655803
  have htrace : WordTrace (prefixWord ++ tailWord_7655803) baseStart_7655803 baseEnd_7655803 := by
    simpa [prefixWord, tailWord_7655803, baseEnd_7655803] using wordTrace_append hprefix tailTrace_7655803
  have hstable : (prefixWord ++ tailWord_7655803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655803).length < 2 ^ (prefixWord ++ tailWord_7655803).sum := by decide
  have hdescent : baseEnd_7655803 < baseStart_7655803 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655829 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 5, 1, 5]
def baseStart_7655829 : Nat := 118140960795 + 7655829 * 2 ^ 59
def prefixEnd_7655829 : Nat := 4983230072969 + 3 ^ 40 * 7655829 * 2
def baseEnd_7655829 : Nat := 3931120085630232267528989

theorem tailTrace_7655829 : CollatzResearch.WordTrace tailWord_7655829 prefixEnd_7655829 3931120085630232267528989 := by
  unfold tailWord_7655829
  simp only [CollatzResearch.WordTrace]
  refine ⟨279231023381246519342002541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186154015587497679561335027 279231023381246519342002541)
  ·
    refine ⟨104711633767967444753250953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279231023381246519342002541 104711633767967444753250953)
    ·
      refine ⟨78533725325975583564938215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104711633767967444753250953 78533725325975583564938215)
      ·
        refine ⟨117800587988963375347407323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78533725325975583564938215 117800587988963375347407323)
        ·
          refine ⟨176700881983445063021110985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117800587988963375347407323 176700881983445063021110985)
          ·
            refine ⟨132525661487583797265833239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176700881983445063021110985 132525661487583797265833239)
            ·
              refine ⟨198788492231375695898749859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132525661487583797265833239 198788492231375695898749859)
              ·
                refine ⟨298182738347063543848124789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198788492231375695898749859 298182738347063543848124789)
                ·
                  refine ⟨27954631720037207235761699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 298182738347063543848124789 27954631720037207235761699)
                  ·
                    refine ⟨41931947580055810853642549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27954631720037207235761699 41931947580055810853642549)
                    ·
                      refine ⟨3931120085630232267528989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41931947580055810853642549 3931120085630232267528989)
                      ·
                        rfl

theorem cell23_7655829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_7655829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655829 prefixEnd_7655829 := by exact prefixLift 7655829
  have htrace : WordTrace (prefixWord ++ tailWord_7655829) baseStart_7655829 baseEnd_7655829 := by
    simpa [prefixWord, tailWord_7655829, baseEnd_7655829] using wordTrace_append hprefix tailTrace_7655829
  have hstable : (prefixWord ++ tailWord_7655829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655829).length < 2 ^ (prefixWord ++ tailWord_7655829).sum := by decide
  have hdescent : baseEnd_7655829 < baseStart_7655829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655870 : List Nat := [4, 2, 1, 1, 1, 1, 6, 1, 2, 4]
def baseStart_7655870 : Nat := 118140960795 + 7655870 * 2 ^ 59
def prefixEnd_7655870 : Nat := 4983230072969 + 3 ^ 40 * 7655870 * 2
def baseEnd_7655870 : Nat := 1310380379445688869038767

theorem tailTrace_7655870 : CollatzResearch.WordTrace tailWord_7655870 prefixEnd_7655870 1310380379445688869038767 := by
  unfold tailWord_7655870
  simp only [CollatzResearch.WordTrace]
  refine ⟨34904064846762247918030633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186155012516065322229496709 34904064846762247918030633)
  ·
    refine ⟨26178048635071685938522975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34904064846762247918030633 26178048635071685938522975)
    ·
      refine ⟨39267072952607528907784463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26178048635071685938522975 39267072952607528907784463)
      ·
        refine ⟨58900609428911293361676695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39267072952607528907784463 58900609428911293361676695)
        ·
          refine ⟨88350914143366940042515043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58900609428911293361676695 88350914143366940042515043)
          ·
            refine ⟨132526371215050410063772565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88350914143366940042515043 132526371215050410063772565)
            ·
              refine ⟨6212173650705487971739339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 132526371215050410063772565 6212173650705487971739339)
              ·
                refine ⟨9318260476058231957609009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6212173650705487971739339 9318260476058231957609009)
                ·
                  refine ⟨6988695357043673968206757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9318260476058231957609009 6988695357043673968206757)
                  ·
                    refine ⟨1310380379445688869038767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6988695357043673968206757 1310380379445688869038767)
                    ·
                      rfl

theorem cell23_7655870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_7655870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655870 prefixEnd_7655870 := by exact prefixLift 7655870
  have htrace : WordTrace (prefixWord ++ tailWord_7655870) baseStart_7655870 baseEnd_7655870 := by
    simpa [prefixWord, tailWord_7655870, baseEnd_7655870] using wordTrace_append hprefix tailTrace_7655870
  have hstable : (prefixWord ++ tailWord_7655870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655870).length < 2 ^ (prefixWord ++ tailWord_7655870).sum := by decide
  have hdescent : baseEnd_7655870 < baseStart_7655870 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655880 : List Nat := [2, 1, 3, 1, 3, 4, 1, 2, 1, 2, 3]
def baseStart_7655880 : Nat := 118140960795 + 7655880 * 2 ^ 59
def prefixEnd_7655880 : Nat := 4983230072969 + 3 ^ 40 * 7655880 * 2
def baseEnd_7655880 : Nat := 3931146273143611567991255

theorem tailTrace_7655880 : CollatzResearch.WordTrace tailWord_7655880 prefixEnd_7655880 3931146273143611567991255 := by
  unfold tailWord_7655880
  simp only [CollatzResearch.WordTrace]
  refine ⟨139616441752030877526054547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186155255669374503368072729 139616441752030877526054547)
  ·
    refine ⟨209424662628046316289081821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139616441752030877526054547 209424662628046316289081821)
    ·
      refine ⟨78534248485517368608405683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209424662628046316289081821 78534248485517368608405683)
      ·
        refine ⟨117801372728276052912608525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78534248485517368608405683 117801372728276052912608525)
        ·
          refine ⟨44175514773103519842228197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117801372728276052912608525 44175514773103519842228197)
          ·
            refine ⟨8282909019956909970417787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44175514773103519842228197 8282909019956909970417787)
            ·
              refine ⟨12424363529935364955626681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8282909019956909970417787 12424363529935364955626681)
              ·
                refine ⟨9318272647451523716720011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12424363529935364955626681 9318272647451523716720011)
                ·
                  refine ⟨13977408971177285575080017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9318272647451523716720011 13977408971177285575080017)
                  ·
                    refine ⟨10483056728382964181310013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13977408971177285575080017 10483056728382964181310013)
                    ·
                      refine ⟨3931146273143611567991255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10483056728382964181310013 3931146273143611567991255)
                      ·
                        rfl

theorem cell23_7655880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 2, 1, 2, 3].length) (baseStart_7655880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655880 prefixEnd_7655880 := by exact prefixLift 7655880
  have htrace : WordTrace (prefixWord ++ tailWord_7655880) baseStart_7655880 baseEnd_7655880 := by
    simpa [prefixWord, tailWord_7655880, baseEnd_7655880] using wordTrace_append hprefix tailTrace_7655880
  have hstable : (prefixWord ++ tailWord_7655880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655880).length < 2 ^ (prefixWord ++ tailWord_7655880).sum := by decide
  have hdescent : baseEnd_7655880 < baseStart_7655880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655889 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 1, 4, 5]
def baseStart_7655889 : Nat := 118140960795 + 7655889 * 2 ^ 59
def prefixEnd_7655889 : Nat := 4983230072969 + 3 ^ 40 * 7655889 * 2
def baseEnd_7655889 : Nat := 3931150894469502032778713

theorem tailTrace_7655889 : CollatzResearch.WordTrace tailWord_7655889 prefixEnd_7655889 3931150894469502032778713 := by
  unfold tailWord_7655889
  simp only [CollatzResearch.WordTrace]
  refine ⟨279233211761029149589186721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186155474507352766392791147 279233211761029149589186721)
  ·
    refine ⟨209424908820771862191890041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279233211761029149589186721 209424908820771862191890041)
    ·
      refine ⟨157068681615578896643917531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209424908820771862191890041 157068681615578896643917531)
      ·
        refine ⟨235603022423368344965876297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157068681615578896643917531 235603022423368344965876297)
        ·
          refine ⟨176702266817526258724407223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235603022423368344965876297 176702266817526258724407223)
          ·
            refine ⟨265053400226289388086610835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176702266817526258724407223 265053400226289388086610835)
            ·
              refine ⟨397580100339434082129916253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265053400226289388086610835 397580100339434082129916253)
              ·
                refine ⟨149092537627287780798718595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 397580100339434082129916253 149092537627287780798718595)
                ·
                  refine ⟨223638806440931671198077893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149092537627287780798718595 223638806440931671198077893)
                  ·
                    refine ⟨41932276207674688349639605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 223638806440931671198077893 41932276207674688349639605)
                    ·
                      refine ⟨3931150894469502032778713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41932276207674688349639605 3931150894469502032778713)
                      ·
                        rfl

theorem cell23_7655889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_7655889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655889 prefixEnd_7655889 := by exact prefixLift 7655889
  have htrace : WordTrace (prefixWord ++ tailWord_7655889) baseStart_7655889 baseEnd_7655889 := by
    simpa [prefixWord, tailWord_7655889, baseEnd_7655889] using wordTrace_append hprefix tailTrace_7655889
  have hstable : (prefixWord ++ tailWord_7655889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655889).length < 2 ^ (prefixWord ++ tailWord_7655889).sum := by decide
  have hdescent : baseEnd_7655889 < baseStart_7655889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655890 : List Nat := [3, 2, 2, 4, 1, 1, 1, 2, 1, 2, 4]
def baseStart_7655890 : Nat := 118140960795 + 7655890 * 2 ^ 59
def prefixEnd_7655890 : Nat := 4983230072969 + 3 ^ 40 * 7655890 * 2
def baseEnd_7655890 : Nat := 3931151407950156528866209

theorem tailTrace_7655890 : CollatzResearch.WordTrace tailWord_7655890 prefixEnd_7655890 3931151407950156528866209 := by
  unfold tailWord_7655890
  simp only [CollatzResearch.WordTrace]
  refine ⟨69808312058506381689993281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186155498822683684506648749 69808312058506381689993281)
  ·
    refine ⟨52356234043879786267494961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69808312058506381689993281 52356234043879786267494961)
    ·
      refine ⟨39267175532909839700621221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52356234043879786267494961 39267175532909839700621221)
      ·
        refine ⟨7362595412420594943866479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39267175532909839700621221 7362595412420594943866479)
        ·
          refine ⟨11043893118630892415799719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7362595412420594943866479 11043893118630892415799719)
          ·
            refine ⟨16565839677946338623699579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11043893118630892415799719 16565839677946338623699579)
            ·
              refine ⟨24848759516919507935549369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16565839677946338623699579 24848759516919507935549369)
              ·
                refine ⟨18636569637689630951662027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24848759516919507935549369 18636569637689630951662027)
                ·
                  refine ⟨27954854456534446427493041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18636569637689630951662027 27954854456534446427493041)
                  ·
                    refine ⟨20966140842400834820619781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27954854456534446427493041 20966140842400834820619781)
                    ·
                      refine ⟨3931151407950156528866209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20966140842400834820619781 3931151407950156528866209)
                      ·
                        rfl

theorem cell23_7655890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_7655890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655890 prefixEnd_7655890 := by exact prefixLift 7655890
  have htrace : WordTrace (prefixWord ++ tailWord_7655890) baseStart_7655890 baseEnd_7655890 := by
    simpa [prefixWord, tailWord_7655890, baseEnd_7655890] using wordTrace_append hprefix tailTrace_7655890
  have hstable : (prefixWord ++ tailWord_7655890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655890).length < 2 ^ (prefixWord ++ tailWord_7655890).sum := by decide
  have hdescent : baseEnd_7655890 < baseStart_7655890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655893 : List Nat := [1, 3, 2, 3, 1, 3, 1, 2, 1, 3, 3]
def baseStart_7655893 : Nat := 118140960795 + 7655893 * 2 ^ 59
def prefixEnd_7655893 : Nat := 4983230072969 + 3 ^ 40 * 7655893 * 2
def baseEnd_7655893 : Nat := 3931152948392120017128695

theorem tailTrace_7655893 : CollatzResearch.WordTrace tailWord_7655893 prefixEnd_7655893 3931152948392120017128695 := by
  unfold tailWord_7655893
  simp only [CollatzResearch.WordTrace]
  refine ⟨279233357653014658272332333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186155571768676438848221555 279233357653014658272332333)
  ·
    refine ⟨104712509119880496852124625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279233357653014658272332333 104712509119880496852124625)
    ·
      refine ⟨78534381839910372639093469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104712509119880496852124625 78534381839910372639093469)
      ·
        refine ⟨29450393189966389739660051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78534381839910372639093469 29450393189966389739660051)
        ·
          refine ⟨44175589784949584609490077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29450393189966389739660051 44175589784949584609490077)
          ·
            refine ⟨16565846169356094228558779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44175589784949584609490077 16565846169356094228558779)
            ·
              refine ⟨24848769254034141342838169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16565846169356094228558779 24848769254034141342838169)
              ·
                refine ⟨18636576940525606007128627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24848769254034141342838169 18636576940525606007128627)
                ·
                  refine ⟨27954865410788409010692941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18636576940525606007128627 27954865410788409010692941)
                  ·
                    refine ⟨10483074529045653379009853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27954865410788409010692941 10483074529045653379009853)
                    ·
                      refine ⟨3931152948392120017128695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10483074529045653379009853 3931152948392120017128695)
                      ·
                        rfl

theorem cell23_7655893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_7655893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655893 prefixEnd_7655893 := by exact prefixLift 7655893
  have htrace : WordTrace (prefixWord ++ tailWord_7655893) baseStart_7655893 baseEnd_7655893 := by
    simpa [prefixWord, tailWord_7655893, baseEnd_7655893] using wordTrace_append hprefix tailTrace_7655893
  have hstable : (prefixWord ++ tailWord_7655893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655893).length < 2 ^ (prefixWord ++ tailWord_7655893).sum := by decide
  have hdescent : baseEnd_7655893 < baseStart_7655893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655894 : List Nat := [5, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2]
def baseStart_7655894 : Nat := 118140960795 + 7655894 * 2 ^ 59
def prefixEnd_7655894 : Nat := 4983230072969 + 3 ^ 40 * 7655894 * 2
def baseEnd_7655894 : Nat := 3931153461872774513216191

theorem tailTrace_7655894 : CollatzResearch.WordTrace tailWord_7655894 prefixEnd_7655894 3931153461872774513216191 := by
  unfold tailWord_7655894
  simp only [CollatzResearch.WordTrace]
  refine ⟨17452087132875689715194921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186155596084007356962079157 17452087132875689715194921)
  ·
    refine ⟨13089065349656767286396191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17452087132875689715194921 13089065349656767286396191)
    ·
      refine ⟨19633598024485150929594287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13089065349656767286396191 19633598024485150929594287)
      ·
        refine ⟨29450397036727726394391431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19633598024485150929594287 29450397036727726394391431)
        ·
          refine ⟨44175595555091589591587147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29450397036727726394391431 44175595555091589591587147)
          ·
            refine ⟨66263393332637384387380721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44175595555091589591587147 66263393332637384387380721)
            ·
              refine ⟨49697544999478038290535541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66263393332637384387380721 49697544999478038290535541)
              ·
                refine ⟨4659144843701066089737707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49697544999478038290535541 4659144843701066089737707)
                ·
                  refine ⟨6988717265551599134606561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4659144843701066089737707 6988717265551599134606561)
                  ·
                    refine ⟨5241537949163699350954921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6988717265551599134606561 5241537949163699350954921)
                    ·
                      refine ⟨3931153461872774513216191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5241537949163699350954921 3931153461872774513216191)
                      ·
                        rfl

theorem cell23_7655894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_7655894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655894 prefixEnd_7655894 := by exact prefixLift 7655894
  have htrace : WordTrace (prefixWord ++ tailWord_7655894) baseStart_7655894 baseEnd_7655894 := by
    simpa [prefixWord, tailWord_7655894, baseEnd_7655894] using wordTrace_append hprefix tailTrace_7655894
  have hstable : (prefixWord ++ tailWord_7655894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655894).length < 2 ^ (prefixWord ++ tailWord_7655894).sum := by decide
  have hdescent : baseEnd_7655894 < baseStart_7655894 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655946 : List Nat := [3, 1, 2, 2, 2, 1, 1, 2, 1, 4, 4]
def baseStart_7655946 : Nat := 118140960795 + 7655946 * 2 ^ 59
def prefixEnd_7655946 : Nat := 4983230072969 + 3 ^ 40 * 7655946 * 2
def baseEnd_7655946 : Nat := 3931180162866808309765951

theorem tailTrace_7655946 : CollatzResearch.WordTrace tailWord_7655946 prefixEnd_7655946 3931180162866808309765951 := by
  unfold tailWord_7655946
  simp only [CollatzResearch.WordTrace]
  refine ⟨69808822680455662081002923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186156860481215098882674461 69808822680455662081002923)
  ·
    refine ⟨104713234020683493121504385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69808822680455662081002923 104713234020683493121504385)
    ·
      refine ⟨78534925515512619841128289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104713234020683493121504385 78534925515512619841128289)
      ·
        refine ⟨58901194136634464880846217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78534925515512619841128289 58901194136634464880846217)
        ·
          refine ⟨44175895602475848660634663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58901194136634464880846217 44175895602475848660634663)
          ·
            refine ⟨66263843403713772990951995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44175895602475848660634663 66263843403713772990951995)
            ·
              refine ⟨99395765105570659486427993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66263843403713772990951995 99395765105570659486427993)
              ·
                refine ⟨74546823829177994614820995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99395765105570659486427993 74546823829177994614820995)
                ·
                  refine ⟨111820235743766991922231493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74546823829177994614820995 111820235743766991922231493)
                  ·
                    refine ⟨20966294201956310985418405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 111820235743766991922231493 20966294201956310985418405)
                    ·
                      refine ⟨3931180162866808309765951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20966294201956310985418405 3931180162866808309765951)
                      ·
                        rfl

theorem cell23_7655946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_7655946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655946 prefixEnd_7655946 := by exact prefixLift 7655946
  have htrace : WordTrace (prefixWord ++ tailWord_7655946) baseStart_7655946 baseEnd_7655946 := by
    simpa [prefixWord, tailWord_7655946, baseEnd_7655946] using wordTrace_append hprefix tailTrace_7655946
  have hstable : (prefixWord ++ tailWord_7655946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655946).length < 2 ^ (prefixWord ++ tailWord_7655946).sum := by decide
  have hdescent : baseEnd_7655946 < baseStart_7655946 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655950 : List Nat := [4, 1, 1, 2, 3, 1, 2, 2, 1, 4, 2]
def baseStart_7655950 : Nat := 118140960795 + 7655950 * 2 ^ 59
def prefixEnd_7655950 : Nat := 4983230072969 + 3 ^ 40 * 7655950 * 2
def baseEnd_7655950 : Nat := 3931182216789426294115933

theorem tailTrace_7655950 : CollatzResearch.WordTrace tailWord_7655950 prefixEnd_7655950 3931182216789426294115933 := by
  unfold tailWord_7655950
  simp only [CollatzResearch.WordTrace]
  refine ⟨34904429576726019625894663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186156957742538771338104869 34904429576726019625894663)
  ·
    refine ⟨52356644365089029438841995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34904429576726019625894663 52356644365089029438841995)
    ·
      refine ⟨78534966547633544158262993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52356644365089029438841995 78534966547633544158262993)
      ·
        refine ⟨58901224910725158118697245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78534966547633544158262993 58901224910725158118697245)
        ·
          refine ⟨22087959341521934294511467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58901224910725158118697245 22087959341521934294511467)
          ·
            refine ⟨33131939012282901441767201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22087959341521934294511467 33131939012282901441767201)
            ·
              refine ⟨24848954259212176081325401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33131939012282901441767201 24848954259212176081325401)
              ·
                refine ⟨18636715694409132060994051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24848954259212176081325401 18636715694409132060994051)
                ·
                  refine ⟨27955073541613698091491077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18636715694409132060994051 27955073541613698091491077)
                  ·
                    refine ⟨5241576289052568392154577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27955073541613698091491077 5241576289052568392154577)
                    ·
                      refine ⟨3931182216789426294115933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5241576289052568392154577 3931182216789426294115933)
                      ·
                        rfl

theorem cell23_7655950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 1, 4, 2].length) (baseStart_7655950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655950 prefixEnd_7655950 := by exact prefixLift 7655950
  have htrace : WordTrace (prefixWord ++ tailWord_7655950) baseStart_7655950 baseEnd_7655950 := by
    simpa [prefixWord, tailWord_7655950, baseEnd_7655950] using wordTrace_append hprefix tailTrace_7655950
  have hstable : (prefixWord ++ tailWord_7655950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655950).length < 2 ^ (prefixWord ++ tailWord_7655950).sum := by decide
  have hdescent : baseEnd_7655950 < baseStart_7655950 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655973 : List Nat := [1, 3, 1, 2, 2, 1, 4, 4, 5]
def baseStart_7655973 : Nat := 118140960795 + 7655973 * 2 ^ 59
def prefixEnd_7655973 : Nat := 4983230072969 + 3 ^ 40 * 7655973 * 2
def baseEnd_7655973 : Nat := 436799336316053300458703

theorem tailTrace_7655973 : CollatzResearch.WordTrace tailWord_7655973 prefixEnd_7655973 436799336316053300458703 := by
  unfold tailWord_7655973
  simp only [CollatzResearch.WordTrace]
  refine ⟨279236275492724831935244573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186157516995149887956829715 279236275492724831935244573)
  ·
    refine ⟨104713603309771811975716715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279236275492724831935244573 104713603309771811975716715)
    ·
      refine ⟨157070404964657717963575073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104713603309771811975716715 157070404964657717963575073)
      ·
        refine ⟨117802803723493288472681305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157070404964657717963575073 117802803723493288472681305)
        ·
          refine ⟨88352102792619966354510979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117802803723493288472681305 88352102792619966354510979)
          ·
            refine ⟨132528154188929949531766469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88352102792619966354510979 132528154188929949531766469)
            ·
              refine ⟨24849028910424365537206213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132528154188929949531766469 24849028910424365537206213)
              ·
                refine ⟨4659192920704568538226165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24849028910424365537206213 4659192920704568538226165)
                ·
                  refine ⟨436799336316053300458703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4659192920704568538226165 436799336316053300458703)
                  ·
                    rfl

theorem cell23_7655973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 4, 5].length) (baseStart_7655973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655973 prefixEnd_7655973 := by exact prefixLift 7655973
  have htrace : WordTrace (prefixWord ++ tailWord_7655973) baseStart_7655973 baseEnd_7655973 := by
    simpa [prefixWord, tailWord_7655973, baseEnd_7655973] using wordTrace_append hprefix tailTrace_7655973
  have hstable : (prefixWord ++ tailWord_7655973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655973).length < 2 ^ (prefixWord ++ tailWord_7655973).sum := by decide
  have hdescent : baseEnd_7655973 < baseStart_7655973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7655986 : List Nat := [3, 2, 1, 1, 2, 1, 3, 2, 1, 7]
def baseStart_7655986 : Nat := 118140960795 + 7655986 * 2 ^ 59
def prefixEnd_7655986 : Nat := 4983230072969 + 3 ^ 40 * 7655986 * 2
def baseEnd_7655986 : Nat := 1310400234030996051088589

theorem tailTrace_7655986 : CollatzResearch.WordTrace tailWord_7655986 prefixEnd_7655986 1310400234030996051088589 := by
  unfold tailWord_7655986
  simp only [CollatzResearch.WordTrace]
  refine ⟨69809187410419433788866953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186157833094451823436978541 69809187410419433788866953)
  ·
    refine ⟨52356890557814575341650215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69809187410419433788866953 52356890557814575341650215)
    ·
      refine ⟨78535335836721863012475323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52356890557814575341650215 78535335836721863012475323)
      ·
        refine ⟨117803003755082794518712985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78535335836721863012475323 117803003755082794518712985)
        ·
          refine ⟨88352252816312095889034739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117803003755082794518712985 88352252816312095889034739)
          ·
            refine ⟨132528379224468143833552109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88352252816312095889034739 132528379224468143833552109)
            ·
              refine ⟨49698142209175553937582041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132528379224468143833552109 49698142209175553937582041)
              ·
                refine ⟨37273606656881665453186531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49698142209175553937582041 37273606656881665453186531)
                ·
                  refine ⟨55910409985322498179779797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37273606656881665453186531 55910409985322498179779797)
                  ·
                    refine ⟨1310400234030996051088589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55910409985322498179779797 1310400234030996051088589)
                    ·
                      rfl

theorem cell23_7655986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_7655986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7655986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7655986 prefixEnd_7655986 := by exact prefixLift 7655986
  have htrace : WordTrace (prefixWord ++ tailWord_7655986) baseStart_7655986 baseEnd_7655986 := by
    simpa [prefixWord, tailWord_7655986, baseEnd_7655986] using wordTrace_append hprefix tailTrace_7655986
  have hstable : (prefixWord ++ tailWord_7655986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7655986).length < 2 ^ (prefixWord ++ tailWord_7655986).sum := by decide
  have hdescent : baseEnd_7655986 < baseStart_7655986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7655986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7656023 : List Nat := [1, 1, 3, 2, 2, 2, 3, 2, 2, 1, 4]
def baseStart_7656023 : Nat := 118140960795 + 7656023 * 2 ^ 59
def prefixEnd_7656023 : Nat := 4983230072969 + 3 ^ 40 * 7656023 * 2
def baseEnd_7656023 : Nat := 3931219700877204508503097

theorem tailTrace_7656023 : CollatzResearch.WordTrace tailWord_7656023 prefixEnd_7656023 3931219700877204508503097 := by
  unfold tailWord_7656023
  simp only [CollatzResearch.WordTrace]
  refine ⟨279238099142543690474564723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186158732761695793649709815 279238099142543690474564723)
  ·
    refine ⟨418857148713815535711847085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279238099142543690474564723 418857148713815535711847085)
    ·
      refine ⟨157071430767680825891942657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 418857148713815535711847085 157071430767680825891942657)
      ·
        refine ⟨117803573075760619418956993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157071430767680825891942657 117803573075760619418956993)
        ·
          refine ⟨88352679806820464564217745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117803573075760619418956993 88352679806820464564217745)
          ·
            refine ⟨66264509855115348423163309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88352679806820464564217745 66264509855115348423163309)
            ·
              refine ⟨24849191195668255658686241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66264509855115348423163309 24849191195668255658686241)
              ·
                refine ⟨18636893396751191744014681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24849191195668255658686241 18636893396751191744014681)
                ·
                  refine ⟨13977670047563393808011011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18636893396751191744014681 13977670047563393808011011)
                  ·
                    refine ⟨20966505071345090712016517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13977670047563393808011011 20966505071345090712016517)
                    ·
                      refine ⟨3931219700877204508503097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20966505071345090712016517 3931219700877204508503097)
                      ·
                        rfl

theorem cell23_7656023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_7656023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7656023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7656023 prefixEnd_7656023 := by exact prefixLift 7656023
  have htrace : WordTrace (prefixWord ++ tailWord_7656023) baseStart_7656023 baseEnd_7656023 := by
    simpa [prefixWord, tailWord_7656023, baseEnd_7656023] using wordTrace_append hprefix tailTrace_7656023
  have hstable : (prefixWord ++ tailWord_7656023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7656023).length < 2 ^ (prefixWord ++ tailWord_7656023).sum := by decide
  have hdescent : baseEnd_7656023 < baseStart_7656023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7656023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7656084 : List Nat := [2, 4, 2, 2, 1, 2, 1, 4, 1, 4]
def baseStart_7656084 : Nat := 118140960795 + 7656084 * 2 ^ 59
def prefixEnd_7656084 : Nat := 4983230072969 + 3 ^ 40 * 7656084 * 2
def baseEnd_7656084 : Nat := 1310417007732376256613439

theorem tailTrace_7656084 : CollatzResearch.WordTrace tailWord_7656084 prefixEnd_7656084 1310417007732376256613439 := by
  unfold tailWord_7656084
  simp only [CollatzResearch.WordTrace]
  refine ⟨139620161997661348946267653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186160215996881798595023537 139620161997661348946267653)
  ·
    refine ⟨26178780374561502927425185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139620161997661348946267653 26178780374561502927425185)
    ·
      refine ⟨19634085280921127195568889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26178780374561502927425185 19634085280921127195568889)
      ·
        refine ⟨14725563960690845396676667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19634085280921127195568889 14725563960690845396676667)
        ·
          refine ⟨22088345941036268095015001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14725563960690845396676667 22088345941036268095015001)
          ·
            refine ⟨16566259455777201071261251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22088345941036268095015001 16566259455777201071261251)
            ·
              refine ⟨24849389183665801606891877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16566259455777201071261251 24849389183665801606891877)
              ·
                refine ⟨4659260471937337801292227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24849389183665801606891877 4659260471937337801292227)
                ·
                  refine ⟨6988890707906006701938341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4659260471937337801292227 6988890707906006701938341)
                  ·
                    refine ⟨1310417007732376256613439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6988890707906006701938341 1310417007732376256613439)
                    ·
                      rfl

theorem cell23_7656084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_7656084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7656084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7656084 prefixEnd_7656084 := by exact prefixLift 7656084
  have htrace : WordTrace (prefixWord ++ tailWord_7656084) baseStart_7656084 baseEnd_7656084 := by
    simpa [prefixWord, tailWord_7656084, baseEnd_7656084] using wordTrace_append hprefix tailTrace_7656084
  have hstable : (prefixWord ++ tailWord_7656084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7656084).length < 2 ^ (prefixWord ++ tailWord_7656084).sum := by decide
  have hdescent : baseEnd_7656084 < baseStart_7656084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7656084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7656093 : List Nat := [1, 4, 2, 1, 1, 1, 3, 2, 3, 5]
def baseStart_7656093 : Nat := 118140960795 + 7656093 * 2 ^ 59
def prefixEnd_7656093 : Nat := 4983230072969 + 3 ^ 40 * 7656093 * 2
def baseEnd_7656093 : Nat := 1310418548174339744875925

theorem tailTrace_7656093 : CollatzResearch.WordTrace tailWord_7656093 prefixEnd_7656093 1310418548174339744875925 := by
  unfold tailWord_7656093
  simp only [CollatzResearch.WordTrace]
  refine ⟨279240652252290092429612933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186160434834860061619741955 279240652252290092429612933)
  ·
    refine ⟨52357622297304392330552425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 279240652252290092429612933 52357622297304392330552425)
    ·
      refine ⟨39268216722978294247914319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52357622297304392330552425 39268216722978294247914319)
      ·
        refine ⟨58902325084467441371871479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39268216722978294247914319 58902325084467441371871479)
        ·
          refine ⟨88353487626701162057807219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58902325084467441371871479 88353487626701162057807219)
          ·
            refine ⟨132530231440051743086710829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88353487626701162057807219 132530231440051743086710829)
            ·
              refine ⟨49698836790019403657516561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132530231440051743086710829 49698836790019403657516561)
              ·
                refine ⟨37274127592514552743137421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49698836790019403657516561 37274127592514552743137421)
                ·
                  refine ⟨13977797847192957278676533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37274127592514552743137421 13977797847192957278676533)
                  ·
                    refine ⟨1310418548174339744875925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13977797847192957278676533 1310418548174339744875925)
                    ·
                      rfl

theorem cell23_7656093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_7656093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7656093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7656093 prefixEnd_7656093 := by exact prefixLift 7656093
  have htrace : WordTrace (prefixWord ++ tailWord_7656093) baseStart_7656093 baseEnd_7656093 := by
    simpa [prefixWord, tailWord_7656093, baseEnd_7656093] using wordTrace_append hprefix tailTrace_7656093
  have hstable : (prefixWord ++ tailWord_7656093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7656093).length < 2 ^ (prefixWord ++ tailWord_7656093).sum := by decide
  have hdescent : baseEnd_7656093 < baseStart_7656093 := by decide
  rcases family_descends (prefixWord ++ tailWord_7656093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7656100 : List Nat := [2, 3, 1, 2, 2, 1, 2, 2, 1, 5, 2]
def baseStart_7656100 : Nat := 118140960795 + 7656100 * 2 ^ 59
def prefixEnd_7656100 : Nat := 4983230072969 + 3 ^ 40 * 7656100 * 2
def baseEnd_7656100 : Nat := 3931259238887600707240243

theorem tailTrace_7656100 : CollatzResearch.WordTrace tailWord_7656100 prefixEnd_7656100 3931259238887600707240243 := by
  unfold tailWord_7656100
  simp only [CollatzResearch.WordTrace]
  refine ⟨139620453781632366312558877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186160605042176488416745169 139620453781632366312558877)
  ·
    refine ⟨52357670168112137367209579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139620453781632366312558877 52357670168112137367209579)
    ·
      refine ⟨78536505252168206050814369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52357670168112137367209579 78536505252168206050814369)
      ·
        refine ⟨58902378939126154538110777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78536505252168206050814369 58902378939126154538110777)
        ·
          refine ⟨44176784204344615903583083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58902378939126154538110777 44176784204344615903583083)
          ·
            refine ⟨66265176306516923855374625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44176784204344615903583083 66265176306516923855374625)
            ·
              refine ⟨49698882229887692891530969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66265176306516923855374625 49698882229887692891530969)
              ·
                refine ⟨37274161672415769668648227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49698882229887692891530969 37274161672415769668648227)
                ·
                  refine ⟨55911242508623654502972341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37274161672415769668648227 55911242508623654502972341)
                  ·
                    refine ⟨5241678985183467609653657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55911242508623654502972341 5241678985183467609653657)
                    ·
                      refine ⟨3931259238887600707240243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5241678985183467609653657 3931259238887600707240243)
                      ·
                        rfl

theorem cell23_7656100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 1, 5, 2].length) (baseStart_7656100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7656100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7656100 prefixEnd_7656100 := by exact prefixLift 7656100
  have htrace : WordTrace (prefixWord ++ tailWord_7656100) baseStart_7656100 baseEnd_7656100 := by
    simpa [prefixWord, tailWord_7656100, baseEnd_7656100] using wordTrace_append hprefix tailTrace_7656100
  have hstable : (prefixWord ++ tailWord_7656100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7656100).length < 2 ^ (prefixWord ++ tailWord_7656100).sum := by decide
  have hdescent : baseEnd_7656100 < baseStart_7656100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7656100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7656117 : List Nat := [1, 3, 3, 3, 1, 2, 1, 1, 1, 5, 2]
def baseStart_7656117 : Nat := 118140960795 + 7656117 * 2 ^ 59
def prefixEnd_7656117 : Nat := 4983230072969 + 3 ^ 40 * 7656117 * 2
def baseEnd_7656117 : Nat := 3931267968058727140727665

theorem tailTrace_7656117 : CollatzResearch.WordTrace tailWord_7656117 prefixEnd_7656117 3931267968058727140727665 := by
  unfold tailWord_7656117
  simp only [CollatzResearch.WordTrace]
  refine ⟨279241527604203144528486605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186161018402802096352324403 279241527604203144528486605)
  ·
    refine ⟨104715572851576179198182477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279241527604203144528486605 104715572851576179198182477)
    ·
      refine ⟨39268339819341067199318429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104715572851576179198182477 39268339819341067199318429)
      ·
        refine ⟨14725627432252900199744411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39268339819341067199318429 14725627432252900199744411)
        ·
          refine ⟨22088441148379350299616617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14725627432252900199744411 22088441148379350299616617)
          ·
            refine ⟨16566330861284512724712463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22088441148379350299616617 16566330861284512724712463)
            ·
              refine ⟨24849496291926769087068695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16566330861284512724712463 24849496291926769087068695)
              ·
                refine ⟨37274244437890153630603043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24849496291926769087068695 37274244437890153630603043)
                ·
                  refine ⟨55911366656835230445904565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37274244437890153630603043 55911366656835230445904565)
                  ·
                    refine ⟨5241690624078302854303553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55911366656835230445904565 5241690624078302854303553)
                    ·
                      refine ⟨3931267968058727140727665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5241690624078302854303553 3931267968058727140727665)
                      ·
                        rfl

theorem cell23_7656117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_7656117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7656117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7656117 prefixEnd_7656117 := by exact prefixLift 7656117
  have htrace : WordTrace (prefixWord ++ tailWord_7656117) baseStart_7656117 baseEnd_7656117 := by
    simpa [prefixWord, tailWord_7656117, baseEnd_7656117] using wordTrace_append hprefix tailTrace_7656117
  have hstable : (prefixWord ++ tailWord_7656117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7656117).length < 2 ^ (prefixWord ++ tailWord_7656117).sum := by decide
  have hdescent : baseEnd_7656117 < baseStart_7656117 := by decide
  rcases family_descends (prefixWord ++ tailWord_7656117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7656124 : List Nat := [2, 2, 2, 3, 1, 1, 4, 3, 1, 1, 3]
def baseStart_7656124 : Nat := 118140960795 + 7656124 * 2 ^ 59
def prefixEnd_7656124 : Nat := 4983230072969 + 3 ^ 40 * 7656124 * 2
def baseEnd_7656124 : Nat := 3931271562423308613340133

theorem tailTrace_7656124 : CollatzResearch.WordTrace tailWord_7656124 prefixEnd_7656124 3931271562423308613340133 := by
  unfold tailWord_7656124
  simp only [CollatzResearch.WordTrace]
  refine ⟨139620891457588892361995713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186161188610118523149327617 139620891457588892361995713)
  ·
    refine ⟨104715668593191669271496785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139620891457588892361995713 104715668593191669271496785)
    ·
      refine ⟨78536751444893751953622589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104715668593191669271496785 78536751444893751953622589)
      ·
        refine ⟨29451281791835156982608471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78536751444893751953622589 29451281791835156982608471)
        ·
          refine ⟨44176922687752735473912707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29451281791835156982608471 44176922687752735473912707)
          ·
            refine ⟨66265384031629103210869061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44176922687752735473912707 66265384031629103210869061)
            ·
              refine ⟨12424759505930456852037949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66265384031629103210869061 12424759505930456852037949)
              ·
                refine ⟨4659284814723921319514231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12424759505930456852037949 4659284814723921319514231)
                ·
                  refine ⟨6988927222085881979271347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4659284814723921319514231 6988927222085881979271347)
                  ·
                    refine ⟨10483390833128822968907021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6988927222085881979271347 10483390833128822968907021)
                    ·
                      refine ⟨3931271562423308613340133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10483390833128822968907021 3931271562423308613340133)
                      ·
                        rfl

theorem cell23_7656124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_7656124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7656124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7656124 prefixEnd_7656124 := by exact prefixLift 7656124
  have htrace : WordTrace (prefixWord ++ tailWord_7656124) baseStart_7656124 baseEnd_7656124 := by
    simpa [prefixWord, tailWord_7656124, baseEnd_7656124] using wordTrace_append hprefix tailTrace_7656124
  have hstable : (prefixWord ++ tailWord_7656124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7656124).length < 2 ^ (prefixWord ++ tailWord_7656124).sum := by decide
  have hdescent : baseEnd_7656124 < baseStart_7656124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7656124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7656127 : List Nat := [1, 1, 2, 2, 2, 6, 2, 1, 1, 5]
def baseStart_7656127 : Nat := 118140960795 + 7656127 * 2 ^ 59
def prefixEnd_7656127 : Nat := 4983230072969 + 3 ^ 40 * 7656127 * 2
def baseEnd_7656127 : Nat := 1310424367621757367200873

theorem tailTrace_7656127 : CollatzResearch.WordTrace tailWord_7656127 prefixEnd_7656127 1310424367621757367200873 := by
  unfold tailWord_7656127
  simp only [CollatzResearch.WordTrace]
  refine ⟨279241892334166916236350635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186161261556111277490900423 279241892334166916236350635)
  ·
    refine ⟨418862838501250374354525953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279241892334166916236350635 418862838501250374354525953)
    ·
      refine ⟨314147128875937780765894465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418862838501250374354525953 314147128875937780765894465)
      ·
        refine ⟨235610346656953335574420849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314147128875937780765894465 235610346656953335574420849)
        ·
          refine ⟨176707759992715001680815637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235610346656953335574420849 176707759992715001680815637)
          ·
            refine ⟨8283176249658515703788233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 176707759992715001680815637 8283176249658515703788233)
            ·
              refine ⟨6212382187243886777841175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8283176249658515703788233 6212382187243886777841175)
              ·
                refine ⟨9318573280865830166761763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6212382187243886777841175 9318573280865830166761763)
                ·
                  refine ⟨13977859921298745250142645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9318573280865830166761763 13977859921298745250142645)
                  ·
                    refine ⟨1310424367621757367200873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13977859921298745250142645 1310424367621757367200873)
                    ·
                      rfl

theorem cell23_7656127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 1, 1, 5].length) (baseStart_7656127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7656127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7656127 prefixEnd_7656127 := by exact prefixLift 7656127
  have htrace : WordTrace (prefixWord ++ tailWord_7656127) baseStart_7656127 baseEnd_7656127 := by
    simpa [prefixWord, tailWord_7656127, baseEnd_7656127] using wordTrace_append hprefix tailTrace_7656127
  have hstable : (prefixWord ++ tailWord_7656127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7656127).length < 2 ^ (prefixWord ++ tailWord_7656127).sum := by decide
  have hdescent : baseEnd_7656127 < baseStart_7656127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7656127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7656141 : List Nat := [1, 6, 2, 1, 2, 1, 2, 1, 3, 1, 3]
def baseStart_7656141 : Nat := 118140960795 + 7656141 * 2 ^ 59
def prefixEnd_7656141 : Nat := 4983230072969 + 3 ^ 40 * 7656141 * 2
def baseEnd_7656141 : Nat := 3931280291594435046827555

theorem tailTrace_7656141 : CollatzResearch.WordTrace tailWord_7656141 prefixEnd_7656141 3931280291594435046827555 := by
  unfold tailWord_7656141
  simp only [CollatzResearch.WordTrace]
  refine ⟨279242402956116196627360277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186161601970744131084906851 279242402956116196627360277)
  ·
    refine ⟨13089487638567946716907513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 279242402956116196627360277 13089487638567946716907513)
    ·
      refine ⟨9817115728925960037680635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13089487638567946716907513 9817115728925960037680635)
      ·
        refine ⟨14725673593388940056520953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9817115728925960037680635 14725673593388940056520953)
        ·
          refine ⟨11044255195041705042390715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14725673593388940056520953 11044255195041705042390715)
          ·
            refine ⟨16566382792562557563586073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11044255195041705042390715 16566382792562557563586073)
            ·
              refine ⟨12424787094421918172689555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16566382792562557563586073 12424787094421918172689555)
              ·
                refine ⟨18637180641632877259034333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12424787094421918172689555 18637180641632877259034333)
                ·
                  refine ⟨6988942740612328972137875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18637180641632877259034333 6988942740612328972137875)
                  ·
                    refine ⟨10483414110918493458206813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6988942740612328972137875 10483414110918493458206813)
                    ·
                      refine ⟨3931280291594435046827555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10483414110918493458206813 3931280291594435046827555)
                      ·
                        rfl

theorem cell23_7656141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_7656141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7656141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7656141 prefixEnd_7656141 := by exact prefixLift 7656141
  have htrace : WordTrace (prefixWord ++ tailWord_7656141) baseStart_7656141 baseEnd_7656141 := by
    simpa [prefixWord, tailWord_7656141, baseEnd_7656141] using wordTrace_append hprefix tailTrace_7656141
  have hstable : (prefixWord ++ tailWord_7656141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7656141).length < 2 ^ (prefixWord ++ tailWord_7656141).sum := by decide
  have hdescent : baseEnd_7656141 < baseStart_7656141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7656141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7656193 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 4, 2, 5]
def baseStart_7656193 : Nat := 118140960795 + 7656193 * 2 ^ 59
def prefixEnd_7656193 : Nat := 4983230072969 + 3 ^ 40 * 7656193 * 2
def baseEnd_7656193 : Nat := 3931306992588468843377315

theorem tailTrace_7656193 : CollatzResearch.WordTrace tailWord_7656193 prefixEnd_7656193 3931306992588468843377315 := by
  unfold tailWord_7656193
  simp only [CollatzResearch.WordTrace]
  refine ⟨279244299551927809508253233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186162866367951873005502155 279244299551927809508253233)
  ·
    refine ⟨209433224663945857131189925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279244299551927809508253233 209433224663945857131189925)
    ·
      refine ⟨39268729624489848212098111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209433224663945857131189925 39268729624489848212098111)
      ·
        refine ⟨58903094436734772318147167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39268729624489848212098111 58903094436734772318147167)
        ·
          refine ⟨88354641655102158477220751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58903094436734772318147167 88354641655102158477220751)
          ·
            refine ⟨132531962482653237715831127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88354641655102158477220751 132531962482653237715831127)
            ·
              refine ⟨198797943723979856573746691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132531962482653237715831127 198797943723979856573746691)
              ·
                refine ⟨298196915585969784860620037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198797943723979856573746691 298196915585969784860620037)
                ·
                  refine ⟨55911921672369334661366257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 298196915585969784860620037 55911921672369334661366257)
                  ·
                    refine ⟨41933941254277000996024693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55911921672369334661366257 41933941254277000996024693)
                    ·
                      refine ⟨3931306992588468843377315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41933941254277000996024693 3931306992588468843377315)
                      ·
                        rfl

theorem cell23_7656193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_7656193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7656193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7656193 prefixEnd_7656193 := by exact prefixLift 7656193
  have htrace : WordTrace (prefixWord ++ tailWord_7656193) baseStart_7656193 baseEnd_7656193 := by
    simpa [prefixWord, tailWord_7656193, baseEnd_7656193] using wordTrace_append hprefix tailTrace_7656193
  have hstable : (prefixWord ++ tailWord_7656193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7656193).length < 2 ^ (prefixWord ++ tailWord_7656193).sum := by decide
  have hdescent : baseEnd_7656193 < baseStart_7656193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7656193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7656203 : List Nat := [1, 1, 1, 1, 5, 1, 1, 3, 2, 3, 4]
def baseStart_7656203 : Nat := 118140960795 + 7656203 * 2 ^ 59
def prefixEnd_7656203 : Nat := 4983230072969 + 3 ^ 40 * 7656203 * 2
def baseEnd_7656203 : Nat := 3931312127395013804252269

theorem tailTrace_7656203 : CollatzResearch.WordTrace tailWord_7656203 prefixEnd_7656203 3931312127395013804252269 := by
  unfold tailWord_7656203
  simp only [CollatzResearch.WordTrace]
  refine ⟨279244664281891581216117263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186163109521261054144078175 279244664281891581216117263)
  ·
    refine ⟨418866996422837371824175895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279244664281891581216117263 418866996422837371824175895)
    ·
      refine ⟨628300494634256057736263843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418866996422837371824175895 628300494634256057736263843)
      ·
        refine ⟨942450741951384086604395765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 628300494634256057736263843 942450741951384086604395765)
        ·
          refine ⟨88354757057942258119162103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 942450741951384086604395765 88354757057942258119162103)
          ·
            refine ⟨132532135586913387178743155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88354757057942258119162103 132532135586913387178743155)
            ·
              refine ⟨198798203380370080768114733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132532135586913387178743155 198798203380370080768114733)
              ·
                refine ⟨74549326267638780288043025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198798203380370080768114733 74549326267638780288043025)
                ·
                  refine ⟨55911994700729085216032269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74549326267638780288043025 55911994700729085216032269)
                  ·
                    refine ⟨20966998012773406956012101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55911994700729085216032269 20966998012773406956012101)
                    ·
                      refine ⟨3931312127395013804252269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20966998012773406956012101 3931312127395013804252269)
                      ·
                        rfl

theorem cell23_7656203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 3, 4].length) (baseStart_7656203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7656203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7656203 prefixEnd_7656203 := by exact prefixLift 7656203
  have htrace : WordTrace (prefixWord ++ tailWord_7656203) baseStart_7656203 baseEnd_7656203 := by
    simpa [prefixWord, tailWord_7656203, baseEnd_7656203] using wordTrace_append hprefix tailTrace_7656203
  have hstable : (prefixWord ++ tailWord_7656203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7656203).length < 2 ^ (prefixWord ++ tailWord_7656203).sum := by decide
  have hdescent : baseEnd_7656203 < baseStart_7656203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7656203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7656213 : List Nat := [1, 3, 2, 1, 2, 2, 2, 1, 1, 8]
def baseStart_7656213 : Nat := 118140960795 + 7656213 * 2 ^ 59
def prefixEnd_7656213 : Nat := 4983230072969 + 3 ^ 40 * 7656213 * 2
def baseEnd_7656213 : Nat := 1310439087400519588375741

theorem tailTrace_7656213 : CollatzResearch.WordTrace tailWord_7656213 prefixEnd_7656213 1310439087400519588375741 := by
  unfold tailWord_7656213
  simp only [CollatzResearch.WordTrace]
  refine ⟨279245029011855352923981293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186163352674570235282654195 279245029011855352923981293)
  ·
    refine ⟨104716885879445757346492985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279245029011855352923981293 104716885879445757346492985)
    ·
      refine ⟨78537664409584318009869739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104716885879445757346492985 78537664409584318009869739)
      ·
        refine ⟨117806496614376477014804609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78537664409584318009869739 117806496614376477014804609)
        ·
          refine ⟨88354872460782357761103457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117806496614376477014804609 88354872460782357761103457)
          ·
            refine ⟨66266154345586768320827593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88354872460782357761103457 66266154345586768320827593)
            ·
              refine ⟨49699615759190076240620695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66266154345586768320827593 49699615759190076240620695)
              ·
                refine ⟨74549423638785114360931043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49699615759190076240620695 74549423638785114360931043)
                ·
                  refine ⟨111824135458177671541396565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74549423638785114360931043 111824135458177671541396565)
                  ·
                    refine ⟨1310439087400519588375741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 111824135458177671541396565 1310439087400519588375741)
                    ·
                      rfl

theorem cell23_7656213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_7656213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7656213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7656213 prefixEnd_7656213 := by exact prefixLift 7656213
  have htrace : WordTrace (prefixWord ++ tailWord_7656213) baseStart_7656213 baseEnd_7656213 := by
    simpa [prefixWord, tailWord_7656213, baseEnd_7656213] using wordTrace_append hprefix tailTrace_7656213
  have hstable : (prefixWord ++ tailWord_7656213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7656213).length < 2 ^ (prefixWord ++ tailWord_7656213).sum := by decide
  have hdescent : baseEnd_7656213 < baseStart_7656213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7656213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7656224 : List Nat := [2, 1, 1, 5, 1, 2, 3, 2, 1, 3, 2]
def baseStart_7656224 : Nat := 118140960795 + 7656224 * 2 ^ 59
def prefixEnd_7656224 : Nat := 4983230072969 + 3 ^ 40 * 7656224 * 2
def baseEnd_7656224 : Nat := 3931322910488758222089673

theorem tailTrace_7656224 : CollatzResearch.WordTrace tailWord_7656224 prefixEnd_7656224 3931322910488758222089673 := by
  unfold tailWord_7656224
  simp only [CollatzResearch.WordTrace]
  refine ⟨139622715107407750901315863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186163620143210334535087817 139622715107407750901315863)
  ·
    refine ⟨209434072661111626351973795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139622715107407750901315863 209434072661111626351973795)
    ·
      refine ⟨314151108991667439527960693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209434072661111626351973795 314151108991667439527960693)
      ·
        refine ⟨29451666467968822455746315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 314151108991667439527960693 29451666467968822455746315)
        ·
          refine ⟨44177499701953233683619473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29451666467968822455746315 44177499701953233683619473)
          ·
            refine ⟨33133124776464925262714605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44177499701953233683619473 33133124776464925262714605)
            ·
              refine ⟨12424921791174346973517977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33133124776464925262714605 12424921791174346973517977)
              ·
                refine ⟨9318691343380760230138483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12424921791174346973517977 9318691343380760230138483)
                ·
                  refine ⟨13978037015071140345207725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9318691343380760230138483 13978037015071140345207725)
                  ·
                    refine ⟨5241763880651677629452897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13978037015071140345207725 5241763880651677629452897)
                    ·
                      refine ⟨3931322910488758222089673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5241763880651677629452897 3931322910488758222089673)
                      ·
                        rfl

theorem cell23_7656224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_7656224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7656224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7656224 prefixEnd_7656224 := by exact prefixLift 7656224
  have htrace : WordTrace (prefixWord ++ tailWord_7656224) baseStart_7656224 baseEnd_7656224 := by
    simpa [prefixWord, tailWord_7656224, baseEnd_7656224] using wordTrace_append hprefix tailTrace_7656224
  have hstable : (prefixWord ++ tailWord_7656224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7656224).length < 2 ^ (prefixWord ++ tailWord_7656224).sum := by decide
  have hdescent : baseEnd_7656224 < baseStart_7656224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7656224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7656233 : List Nat := [1, 2, 1, 1, 1, 1, 1, 6, 1, 4, 4]
def baseStart_7656233 : Nat := 118140960795 + 7656233 * 2 ^ 59
def prefixEnd_7656233 : Nat := 4983230072969 + 3 ^ 40 * 7656233 * 2
def baseEnd_7656233 : Nat := 3931327531814648686877131

theorem tailTrace_7656233 : CollatzResearch.WordTrace tailWord_7656233 prefixEnd_7656233 3931327531814648686877131 := by
  unfold tailWord_7656233
  simp only [CollatzResearch.WordTrace]
  refine ⟨279245758471782896339709353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186163838981188597559806235 279245758471782896339709353)
  ·
    refine ⟨209434318853837172254782015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279245758471782896339709353 209434318853837172254782015)
    ·
      refine ⟨314151478280755758382173023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209434318853837172254782015 314151478280755758382173023)
      ·
        refine ⟨471227217421133637573259535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314151478280755758382173023 471227217421133637573259535)
        ·
          refine ⟨706840826131700456359889303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471227217421133637573259535 706840826131700456359889303)
          ·
            refine ⟨1060261239197550684539833955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706840826131700456359889303 1060261239197550684539833955)
            ·
              refine ⟨1590391858796326026809750933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1060261239197550684539833955 1590391858796326026809750933)
              ·
                refine ⟨74549618381077782506707075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1590391858796326026809750933 74549618381077782506707075)
                ·
                  refine ⟨111824427571616673760060613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74549618381077782506707075 111824427571616673760060613)
                  ·
                    refine ⟨20967080169678126330011365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 111824427571616673760060613 20967080169678126330011365)
                    ·
                      refine ⟨3931327531814648686877131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20967080169678126330011365 3931327531814648686877131)
                      ·
                        rfl

theorem cell23_7656233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 4, 4].length) (baseStart_7656233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7656233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7656233 prefixEnd_7656233 := by exact prefixLift 7656233
  have htrace : WordTrace (prefixWord ++ tailWord_7656233) baseStart_7656233 baseEnd_7656233 := by
    simpa [prefixWord, tailWord_7656233, baseEnd_7656233] using wordTrace_append hprefix tailTrace_7656233
  have hstable : (prefixWord ++ tailWord_7656233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7656233).length < 2 ^ (prefixWord ++ tailWord_7656233).sum := by decide
  have hdescent : baseEnd_7656233 < baseStart_7656233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7656233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7656263 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 8]
def baseStart_7656263 : Nat := 118140960795 + 7656263 * 2 ^ 59
def prefixEnd_7656263 : Nat := 4983230072969 + 3 ^ 40 * 7656263 * 2
def baseEnd_7656263 : Nat := 3931342936234283569501993

theorem tailTrace_7656263 : CollatzResearch.WordTrace tailWord_7656263 prefixEnd_7656263 3931342936234283569501993 := by
  unfold tailWord_7656263
  simp only [CollatzResearch.WordTrace]
  refine ⟨279246852661674211463301443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186164568441116140975534295 279246852661674211463301443)
  ·
    refine ⟨418870278992511317194952165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279246852661674211463301443 418870278992511317194952165)
    ·
      refine ⟨78538177311095871974053531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 418870278992511317194952165 78538177311095871974053531)
      ·
        refine ⟨117807265966643807961080297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78538177311095871974053531 117807265966643807961080297)
        ·
          refine ⟨88355449474982855970810223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117807265966643807961080297 88355449474982855970810223)
          ·
            refine ⟨132533174212474283956215335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88355449474982855970810223 132533174212474283956215335)
            ·
              refine ⟨198799761318711425934323003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132533174212474283956215335 198799761318711425934323003)
              ·
                refine ⟨298199641978067138901484505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198799761318711425934323003 298199641978067138901484505)
                ·
                  refine ⟨223649731483550354176113379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 298199641978067138901484505 223649731483550354176113379)
                  ·
                    refine ⟨335474597225325531264170069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 223649731483550354176113379 335474597225325531264170069)
                    ·
                      refine ⟨3931342936234283569501993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 335474597225325531264170069 3931342936234283569501993)
                      ·
                        rfl

theorem cell23_7656263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_7656263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7656263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7656263 prefixEnd_7656263 := by exact prefixLift 7656263
  have htrace : WordTrace (prefixWord ++ tailWord_7656263) baseStart_7656263 baseEnd_7656263 := by
    simpa [prefixWord, tailWord_7656263, baseEnd_7656263] using wordTrace_append hprefix tailTrace_7656263
  have hstable : (prefixWord ++ tailWord_7656263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7656263).length < 2 ^ (prefixWord ++ tailWord_7656263).sum := by decide
  have hdescent : baseEnd_7656263 < baseStart_7656263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7656263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7656303 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 1, 10]
def baseStart_7656303 : Nat := 118140960795 + 7656303 * 2 ^ 59
def prefixEnd_7656303 : Nat := 4983230072969 + 3 ^ 40 * 7656303 * 2
def baseEnd_7656303 : Nat := 1310454491820154471000603

theorem tailTrace_7656303 : CollatzResearch.WordTrace tailWord_7656303 prefixEnd_7656303 1310454491820154471000603 := by
  unfold tailWord_7656303
  simp only [CollatzResearch.WordTrace]
  refine ⟨279248311581529298294757563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186165541054352865529838375 279248311581529298294757563)
  ·
    refine ⟨418872467372293947442136345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279248311581529298294757563 418872467372293947442136345)
    ·
      refine ⟨314154350529220460581602259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418872467372293947442136345 314154350529220460581602259)
      ·
        refine ⟨471231525793830690872403389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314154350529220460581602259 471231525793830690872403389)
        ·
          refine ⟨176711822172686509077151271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 471231525793830690872403389 176711822172686509077151271)
          ·
            refine ⟨265067733259029763615726907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176711822172686509077151271 265067733259029763615726907)
            ·
              refine ⟨397601599888544645423590361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265067733259029763615726907 397601599888544645423590361)
              ·
                refine ⟨298201199916408484067692771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 397601599888544645423590361 298201199916408484067692771)
                ·
                  refine ⟨447301799874612726101539157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 298201199916408484067692771 447301799874612726101539157)
                  ·
                    refine ⟨1310454491820154471000603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 447301799874612726101539157 1310454491820154471000603)
                    ·
                      rfl

theorem cell23_7656303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 10].length) (baseStart_7656303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7656303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7656303 prefixEnd_7656303 := by exact prefixLift 7656303
  have htrace : WordTrace (prefixWord ++ tailWord_7656303) baseStart_7656303 baseEnd_7656303 := by
    simpa [prefixWord, tailWord_7656303, baseEnd_7656303] using wordTrace_append hprefix tailTrace_7656303
  have hstable : (prefixWord ++ tailWord_7656303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7656303).length < 2 ^ (prefixWord ++ tailWord_7656303).sum := by decide
  have hdescent : baseEnd_7656303 < baseStart_7656303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7656303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7656322 : List Nat := [3, 4, 2, 2, 1, 1, 3, 1, 2, 2, 2]
def baseStart_7656322 : Nat := 118140960795 + 7656322 * 2 ^ 59
def prefixEnd_7656322 : Nat := 4983230072969 + 3 ^ 40 * 7656322 * 2
def baseEnd_7656322 : Nat := 3931373231592898838664223

theorem tailTrace_7656322 : CollatzResearch.WordTrace tailWord_7656322 prefixEnd_7656322 3931373231592898838664223 := by
  unfold tailWord_7656322
  simp only [CollatzResearch.WordTrace]
  refine ⟨69812251142115116134924805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186166003045640309693132813 69812251142115116134924805)
  ·
    refine ⟨13089797089146584275298401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69812251142115116134924805 13089797089146584275298401)
    ·
      refine ⟨9817347816859938206473801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13089797089146584275298401 9817347816859938206473801)
      ·
        refine ⟨7363010862644953654855351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9817347816859938206473801 7363010862644953654855351)
        ·
          refine ⟨11044516293967430482283027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7363010862644953654855351 11044516293967430482283027)
          ·
            refine ⟨16566774440951145723424541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11044516293967430482283027 16566774440951145723424541)
            ·
              refine ⟨6212540415356679646284203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16566774440951145723424541 6212540415356679646284203)
              ·
                refine ⟨9318810623035019469426305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6212540415356679646284203 9318810623035019469426305)
                ·
                  refine ⟨6989107967276264602069729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9318810623035019469426305 6989107967276264602069729)
                  ·
                    refine ⟨5241830975457198451552297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6989107967276264602069729 5241830975457198451552297)
                    ·
                      refine ⟨3931373231592898838664223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5241830975457198451552297 3931373231592898838664223)
                      ·
                        rfl

theorem cell23_7656322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_7656322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7656322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7656322 prefixEnd_7656322 := by exact prefixLift 7656322
  have htrace : WordTrace (prefixWord ++ tailWord_7656322) baseStart_7656322 baseEnd_7656322 := by
    simpa [prefixWord, tailWord_7656322, baseEnd_7656322] using wordTrace_append hprefix tailTrace_7656322
  have hstable : (prefixWord ++ tailWord_7656322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7656322).length < 2 ^ (prefixWord ++ tailWord_7656322).sum := by decide
  have hdescent : baseEnd_7656322 < baseStart_7656322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7656322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7656384 : List Nat := [2, 1, 1, 2, 3, 5, 2, 1, 6]
def baseStart_7656384 : Nat := 118140960795 + 7656384 * 2 ^ 59
def prefixEnd_7656384 : Nat := 4983230072969 + 3 ^ 40 * 7656384 * 2
def baseEnd_7656384 : Nat := 436822785265941955120993

theorem tailTrace_7656384 : CollatzResearch.WordTrace tailWord_7656384 prefixEnd_7656384 436822785265941955120993 := by
  unfold tailWord_7656384
  simp only [CollatzResearch.WordTrace]
  refine ⟨139625632947117924564228103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186167510596157232752304137 139625632947117924564228103)
  ·
    refine ⟨209438449420676886846342155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139625632947117924564228103 209438449420676886846342155)
    ·
      refine ⟨314157674131015330269513233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209438449420676886846342155 314157674131015330269513233)
      ·
        refine ⟨235618255598261497702134925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314157674131015330269513233 235618255598261497702134925)
        ·
          refine ⟨88356845849348061638300597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235618255598261497702134925 88356845849348061638300597)
          ·
            refine ⟨8283454298376380778590681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88356845849348061638300597 8283454298376380778590681)
            ·
              refine ⟨6212590723782285583943011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8283454298376380778590681 6212590723782285583943011)
              ·
                refine ⟨9318886085673428375914517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6212590723782285583943011 9318886085673428375914517)
                ·
                  refine ⟨436822785265941955120993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9318886085673428375914517 436822785265941955120993)
                  ·
                    rfl

theorem cell23_7656384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 1, 6].length) (baseStart_7656384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7656384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7656384 prefixEnd_7656384 := by exact prefixLift 7656384
  have htrace : WordTrace (prefixWord ++ tailWord_7656384) baseStart_7656384 baseEnd_7656384 := by
    simpa [prefixWord, tailWord_7656384, baseEnd_7656384] using wordTrace_append hprefix tailTrace_7656384
  have hstable : (prefixWord ++ tailWord_7656384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7656384).length < 2 ^ (prefixWord ++ tailWord_7656384).sum := by decide
  have hdescent : baseEnd_7656384 < baseStart_7656384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7656384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7656444 : List Nat := [2, 2, 2, 1, 2, 3, 2, 3, 2, 4]
def baseStart_7656444 : Nat := 118140960795 + 7656444 * 2 ^ 59
def prefixEnd_7656444 : Nat := 4983230072969 + 3 ^ 40 * 7656444 * 2
def baseEnd_7656444 : Nat := 1310478625410915787112887

theorem tailTrace_7656444 : CollatzResearch.WordTrace tailWord_7656444 prefixEnd_7656444 1310478625410915787112887 := by
  unfold tailWord_7656444
  simp only [CollatzResearch.WordTrace]
  refine ⟨139626727137009239687820193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186168969516012319583760257 139626727137009239687820193)
  ·
    refine ⟨104720045352756929765865145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139626727137009239687820193 104720045352756929765865145)
    ·
      refine ⟨78540034014567697324398859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104720045352756929765865145 78540034014567697324398859)
      ·
        refine ⟨117810051021851545986598289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78540034014567697324398859 117810051021851545986598289)
        ·
          refine ⟨88357538266388659489948717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117810051021851545986598289 88357538266388659489948717)
          ·
            refine ⟨33134076849895747308730769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88357538266388659489948717 33134076849895747308730769)
            ·
              refine ⟨24850557637421810481548077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33134076849895747308730769 24850557637421810481548077)
              ·
                refine ⟨9318959114033178930580529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24850557637421810481548077 9318959114033178930580529)
                ·
                  refine ⟨6989219335524884197935397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9318959114033178930580529 6989219335524884197935397)
                  ·
                    refine ⟨1310478625410915787112887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6989219335524884197935397 1310478625410915787112887)
                    ·
                      rfl

theorem cell23_7656444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 3, 2, 4].length) (baseStart_7656444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7656444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7656444 prefixEnd_7656444 := by exact prefixLift 7656444
  have htrace : WordTrace (prefixWord ++ tailWord_7656444) baseStart_7656444 baseEnd_7656444 := by
    simpa [prefixWord, tailWord_7656444, baseEnd_7656444] using wordTrace_append hprefix tailTrace_7656444
  have hstable : (prefixWord ++ tailWord_7656444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7656444).length < 2 ^ (prefixWord ++ tailWord_7656444).sum := by decide
  have hdescent : baseEnd_7656444 < baseStart_7656444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7656444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7656471 : List Nat := [1, 1, 3, 5, 1, 2, 1, 3, 1, 2, 3]
def baseStart_7656471 : Nat := 118140960795 + 7656471 * 2 ^ 59
def prefixEnd_7656471 : Nat := 4983230072969 + 3 ^ 40 * 7656471 * 2
def baseEnd_7656471 : Nat := 3931449740210418755701037

theorem tailTrace_7656471 : CollatzResearch.WordTrace tailWord_7656471 prefixEnd_7656471 3931449740210418755701037 := by
  unfold tailWord_7656471
  simp only [CollatzResearch.WordTrace]
  refine ⟨279254439044920662986873267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186169626029947108657915511 279254439044920662986873267)
  ·
    refine ⟨418881658567380994480309901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279254439044920662986873267 418881658567380994480309901)
    ·
      refine ⟨157080621962767872930116213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 418881658567380994480309901 157080621962767872930116213)
      ·
        refine ⟨14726308309009488087198395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 157080621962767872930116213 14726308309009488087198395)
        ·
          refine ⟨22089462463514232130797593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14726308309009488087198395 22089462463514232130797593)
          ·
            refine ⟨16567096847635674098098195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22089462463514232130797593 16567096847635674098098195)
            ·
              refine ⟨24850645271453511147147293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16567096847635674098098195 24850645271453511147147293)
              ·
                refine ⟨9318991976795066680180235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24850645271453511147147293 9318991976795066680180235)
                ·
                  refine ⟨13978487965192600020270353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9318991976795066680180235 13978487965192600020270353)
                  ·
                    refine ⟨10483865973894450015202765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13978487965192600020270353 10483865973894450015202765)
                    ·
                      refine ⟨3931449740210418755701037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10483865973894450015202765 3931449740210418755701037)
                      ·
                        rfl

theorem cell23_7656471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_7656471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7656471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7656471 prefixEnd_7656471 := by exact prefixLift 7656471
  have htrace : WordTrace (prefixWord ++ tailWord_7656471) baseStart_7656471 baseEnd_7656471 := by
    simpa [prefixWord, tailWord_7656471, baseEnd_7656471] using wordTrace_append hprefix tailTrace_7656471
  have hstable : (prefixWord ++ tailWord_7656471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7656471).length < 2 ^ (prefixWord ++ tailWord_7656471).sum := by decide
  have hdescent : baseEnd_7656471 < baseStart_7656471 := by decide
  rcases family_descends (prefixWord ++ tailWord_7656471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7656518 : List Nat := [6, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3]
def baseStart_7656518 : Nat := 118140960795 + 7656518 * 2 ^ 59
def prefixEnd_7656518 : Nat := 4983230072969 + 3 ^ 40 * 7656518 * 2
def baseEnd_7656518 : Nat := 3931473873801180071813321

theorem tailTrace_7656518 : CollatzResearch.WordTrace tailWord_7656518 prefixEnd_7656518 3931473873801180071813321 := by
  unfold tailWord_7656518
  simp only [CollatzResearch.WordTrace]
  refine ⟨8726754789867199687932319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 186170768850500260009222805 8726754789867199687932319)
  ·
    refine ⟨13090132184800799531898479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8726754789867199687932319 13090132184800799531898479)
    ·
      refine ⟨19635198277201199297847719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13090132184800799531898479 19635198277201199297847719)
      ·
        refine ⟨29452797415801798946771579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19635198277201199297847719 29452797415801798946771579)
        ·
          refine ⟨44179196123702698420157369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29452797415801798946771579 44179196123702698420157369)
          ·
            refine ⟨33134397092777023815118027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44179196123702698420157369 33134397092777023815118027)
            ·
              refine ⟨49701595639165535722677041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33134397092777023815118027 49701595639165535722677041)
              ·
                refine ⟨37276196729374151792007781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49701595639165535722677041 37276196729374151792007781)
                ·
                  refine ⟨6989286886757653461001459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37276196729374151792007781 6989286886757653461001459)
                  ·
                    refine ⟨10483930330136480191502189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6989286886757653461001459 10483930330136480191502189)
                    ·
                      refine ⟨3931473873801180071813321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10483930330136480191502189 3931473873801180071813321)
                      ·
                        rfl

theorem cell23_7656518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_7656518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7656518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7656518 prefixEnd_7656518 := by exact prefixLift 7656518
  have htrace : WordTrace (prefixWord ++ tailWord_7656518) baseStart_7656518 baseEnd_7656518 := by
    simpa [prefixWord, tailWord_7656518, baseEnd_7656518] using wordTrace_append hprefix tailTrace_7656518
  have hstable : (prefixWord ++ tailWord_7656518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7656518).length < 2 ^ (prefixWord ++ tailWord_7656518).sum := by decide
  have hdescent : baseEnd_7656518 < baseStart_7656518 := by decide
  rcases family_descends (prefixWord ++ tailWord_7656518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7656524 : List Nat := [2, 2, 1, 3, 1, 1, 1, 3, 3, 4, 2]
def baseStart_7656524 : Nat := 118140960795 + 7656524 * 2 ^ 59
def prefixEnd_7656524 : Nat := 4983230072969 + 3 ^ 40 * 7656524 * 2
def baseEnd_7656524 : Nat := 3931476954685107048338293

theorem tailTrace_7656524 : CollatzResearch.WordTrace tailWord_7656524 prefixEnd_7656524 3931476954685107048338293 := by
  unfold tailWord_7656524
  simp only [CollatzResearch.WordTrace]
  refine ⟨139628186056864326519276313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186170914742485768692368417 139628186056864326519276313)
  ·
    refine ⟨104721139542648244889457235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139628186056864326519276313 104721139542648244889457235)
    ·
      refine ⟨157081709313972367334185853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104721139542648244889457235 157081709313972367334185853)
      ·
        refine ⟨58905640992739637750319695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157081709313972367334185853 58905640992739637750319695)
        ·
          refine ⟨88358461489109456625479543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58905640992739637750319695 88358461489109456625479543)
          ·
            refine ⟨132537692233664184938219315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88358461489109456625479543 132537692233664184938219315)
            ·
              refine ⟨198806538350496277407328973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132537692233664184938219315 198806538350496277407328973)
              ·
                refine ⟨74552451881436104027748365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198806538350496277407328973 74552451881436104027748365)
                ·
                  refine ⟨27957169455538539010405637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74552451881436104027748365 27957169455538539010405637)
                  ·
                    refine ⟨5241969272913476064451057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27957169455538539010405637 5241969272913476064451057)
                    ·
                      refine ⟨3931476954685107048338293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5241969272913476064451057 3931476954685107048338293)
                      ·
                        rfl

theorem cell23_7656524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 3, 4, 2].length) (baseStart_7656524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7656524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7656524 prefixEnd_7656524 := by exact prefixLift 7656524
  have htrace : WordTrace (prefixWord ++ tailWord_7656524) baseStart_7656524 baseEnd_7656524 := by
    simpa [prefixWord, tailWord_7656524, baseEnd_7656524] using wordTrace_append hprefix tailTrace_7656524
  have hstable : (prefixWord ++ tailWord_7656524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7656524).length < 2 ^ (prefixWord ++ tailWord_7656524).sum := by decide
  have hdescent : baseEnd_7656524 < baseStart_7656524 := by decide
  rcases family_descends (prefixWord ++ tailWord_7656524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7656537 : List Nat := [1, 2, 1, 2, 2, 1, 2, 4, 2, 2, 4]
def baseStart_7656537 : Nat := 118140960795 + 7656537 * 2 ^ 59
def prefixEnd_7656537 : Nat := 4983230072969 + 3 ^ 40 * 7656537 * 2
def baseEnd_7656537 : Nat := 3931483629933615497475733

theorem tailTrace_7656537 : CollatzResearch.WordTrace tailWord_7656537 prefixEnd_7656537 3931483629933615497475733 := by
  unfold tailWord_7656537
  simp only [CollatzResearch.WordTrace]
  refine ⟨279256846262681556258775865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186171230841787704172517243 279256846262681556258775865)
  ·
    refine ⟨209442634697011167194081899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279256846262681556258775865 209442634697011167194081899)
    ·
      refine ⟨314163952045516750791122849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209442634697011167194081899 314163952045516750791122849)
      ·
        refine ⟨235622964034137563093342137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314163952045516750791122849 235622964034137563093342137)
        ·
          refine ⟨176717223025603172320006603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235622964034137563093342137 176717223025603172320006603)
          ·
            refine ⟨265075834538404758480009905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176717223025603172320006603 265075834538404758480009905)
            ·
              refine ⟨198806875903803568860007429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265075834538404758480009905 198806875903803568860007429)
              ·
                refine ⟨37276289231963169161251393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 198806875903803568860007429 37276289231963169161251393)
                ·
                  refine ⟨27957216923972376870938545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37276289231963169161251393 27957216923972376870938545)
                  ·
                    refine ⟨20967912692979282653203909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27957216923972376870938545 20967912692979282653203909)
                    ·
                      refine ⟨3931483629933615497475733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20967912692979282653203909 3931483629933615497475733)
                      ·
                        rfl

theorem cell23_7656537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 2, 4].length) (baseStart_7656537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7656537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7656537 prefixEnd_7656537 := by exact prefixLift 7656537
  have htrace : WordTrace (prefixWord ++ tailWord_7656537) baseStart_7656537 baseEnd_7656537 := by
    simpa [prefixWord, tailWord_7656537, baseEnd_7656537] using wordTrace_append hprefix tailTrace_7656537
  have hstable : (prefixWord ++ tailWord_7656537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7656537).length < 2 ^ (prefixWord ++ tailWord_7656537).sum := by decide
  have hdescent : baseEnd_7656537 < baseStart_7656537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7656537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7656552 : List Nat := [2, 1, 4, 4, 1, 2, 2, 1, 2, 1, 3]
def baseStart_7656552 : Nat := 118140960795 + 7656552 * 2 ^ 59
def prefixEnd_7656552 : Nat := 4983230072969 + 3 ^ 40 * 7656552 * 2
def baseEnd_7656552 : Nat := 3931491332143432938788165

theorem tailTrace_7656552 : CollatzResearch.WordTrace tailWord_7656552 prefixEnd_7656552 3931491332143432938788165 := by
  unfold tailWord_7656552
  simp only [CollatzResearch.WordTrace]
  refine ⟨139628696678813606910285955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186171595571751475880381273 139628696678813606910285955)
  ·
    refine ⟨209443045018220410365428933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139628696678813606910285955 209443045018220410365428933)
    ·
      refine ⟨39270570940916326943517925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209443045018220410365428933 39270570940916326943517925)
      ·
        refine ⟨7363232051421811301909611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39270570940916326943517925 7363232051421811301909611)
        ·
          refine ⟨11044848077132716952864417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7363232051421811301909611 11044848077132716952864417)
          ·
            refine ⟨8283636057849537714648313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11044848077132716952864417 8283636057849537714648313)
            ·
              refine ⟨6212727043387153285986235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8283636057849537714648313 6212727043387153285986235)
              ·
                refine ⟨9319090565080729928979353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6212727043387153285986235 9319090565080729928979353)
                ·
                  refine ⟨6989317923810547446734515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9319090565080729928979353 6989317923810547446734515)
                  ·
                    refine ⟨10483976885715821170101773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6989317923810547446734515 10483976885715821170101773)
                    ·
                      refine ⟨3931491332143432938788165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10483976885715821170101773 3931491332143432938788165)
                      ·
                        rfl

theorem cell23_7656552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_7656552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7656552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7656552 prefixEnd_7656552 := by exact prefixLift 7656552
  have htrace : WordTrace (prefixWord ++ tailWord_7656552) baseStart_7656552 baseEnd_7656552 := by
    simpa [prefixWord, tailWord_7656552, baseEnd_7656552] using wordTrace_append hprefix tailTrace_7656552
  have hstable : (prefixWord ++ tailWord_7656552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7656552).length < 2 ^ (prefixWord ++ tailWord_7656552).sum := by decide
  have hdescent : baseEnd_7656552 < baseStart_7656552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7656552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7656604 : List Nat := [2, 2, 3, 2, 1, 2, 2, 1, 1, 2, 5]
def baseStart_7656604 : Nat := 118140960795 + 7656604 * 2 ^ 59
def prefixEnd_7656604 : Nat := 4983230072969 + 3 ^ 40 * 7656604 * 2
def baseEnd_7656604 : Nat := 3931518033137466735337925

theorem tailTrace_7656604 : CollatzResearch.WordTrace tailWord_7656604 prefixEnd_7656604 3931518033137466735337925 := by
  unfold tailWord_7656604
  simp only [CollatzResearch.WordTrace]
  refine ⟨139629644976719413350732433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186172859968959217800976577 139629644976719413350732433)
  ·
    refine ⟨104722233732539560013049325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139629644976719413350732433 104722233732539560013049325)
    ·
      refine ⟨39270837649702335004893497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104722233732539560013049325 39270837649702335004893497)
      ·
        refine ⟨29453128237276751253670123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39270837649702335004893497 29453128237276751253670123)
        ·
          refine ⟨44179692355915126880505185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29453128237276751253670123 44179692355915126880505185)
          ·
            refine ⟨33134769266936345160378889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44179692355915126880505185 33134769266936345160378889)
            ·
              refine ⟨24851076950202258870284167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33134769266936345160378889 24851076950202258870284167)
              ·
                refine ⟨37276615425303388305426251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24851076950202258870284167 37276615425303388305426251)
                ·
                  refine ⟨55914923137955082458139377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37276615425303388305426251 55914923137955082458139377)
                  ·
                    refine ⟨41936192353466311843604533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55914923137955082458139377 41936192353466311843604533)
                    ·
                      refine ⟨3931518033137466735337925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41936192353466311843604533 3931518033137466735337925)
                      ·
                        rfl

theorem cell23_7656604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_7656604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7656604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7656604 prefixEnd_7656604 := by exact prefixLift 7656604
  have htrace : WordTrace (prefixWord ++ tailWord_7656604) baseStart_7656604 baseEnd_7656604 := by
    simpa [prefixWord, tailWord_7656604, baseEnd_7656604] using wordTrace_append hprefix tailTrace_7656604
  have hstable : (prefixWord ++ tailWord_7656604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7656604).length < 2 ^ (prefixWord ++ tailWord_7656604).sum := by decide
  have hdescent : baseEnd_7656604 < baseStart_7656604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7656604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7656624 : List Nat := [2, 1, 1, 1, 2, 1, 2, 6, 3, 4]
def baseStart_7656624 : Nat := 118140960795 + 7656624 * 2 ^ 59
def prefixEnd_7656624 : Nat := 4983230072969 + 3 ^ 40 * 7656624 * 2
def baseEnd_7656624 : Nat := 1310509434250185552362611

theorem tailTrace_7656624 : CollatzResearch.WordTrace tailWord_7656624 prefixEnd_7656624 1310509434250185552362611 := by
  unfold tailWord_7656624
  simp only [CollatzResearch.WordTrace]
  refine ⟨139630009706683185058596463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186173346275577580078128617 139630009706683185058596463)
  ·
    refine ⟨209445014560024777587894695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139630009706683185058596463 209445014560024777587894695)
    ·
      refine ⟨314167521840037166381842043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209445014560024777587894695 314167521840037166381842043)
      ·
        refine ⟨471251282760055749572763065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314167521840037166381842043 471251282760055749572763065)
        ·
          refine ⟨353438462070041812179572299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 471251282760055749572763065 353438462070041812179572299)
          ·
            refine ⟨530157693105062718269358449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353438462070041812179572299 530157693105062718269358449)
            ·
              refine ⟨397618269828797038702018837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 530157693105062718269358449 397618269828797038702018837)
              ·
                refine ⟨18638356398224861189157133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 397618269828797038702018837 18638356398224861189157133)
                ·
                  refine ⟨6989383649334322945933925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18638356398224861189157133 6989383649334322945933925)
                  ·
                    refine ⟨1310509434250185552362611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6989383649334322945933925 1310509434250185552362611)
                    ·
                      rfl

theorem cell23_7656624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 3, 4].length) (baseStart_7656624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7656624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7656624 prefixEnd_7656624 := by exact prefixLift 7656624
  have htrace : WordTrace (prefixWord ++ tailWord_7656624) baseStart_7656624 baseEnd_7656624 := by
    simpa [prefixWord, tailWord_7656624, baseEnd_7656624] using wordTrace_append hprefix tailTrace_7656624
  have hstable : (prefixWord ++ tailWord_7656624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7656624).length < 2 ^ (prefixWord ++ tailWord_7656624).sum := by decide
  have hdescent : baseEnd_7656624 < baseStart_7656624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7656624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7656658 : List Nat := [3, 2, 2, 2, 1, 1, 1, 6, 1, 4]
def baseStart_7656658 : Nat := 118140960795 + 7656658 * 2 ^ 59
def prefixEnd_7656658 : Nat := 4983230072969 + 3 ^ 40 * 7656658 * 2
def baseEnd_7656658 : Nat := 1310515253697603174687559

theorem tailTrace_7656658 : CollatzResearch.WordTrace tailWord_7656658 prefixEnd_7656658 1310515253697603174687559 := by
  unfold tailWord_7656658
  simp only [CollatzResearch.WordTrace]
  refine ⟨69815314873810798480982657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186174172996828795949287085 69815314873810798480982657)
  ·
    refine ⟨52361486155358098860736993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69815314873810798480982657 52361486155358098860736993)
    ·
      refine ⟨39271114616518574145552745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52361486155358098860736993 39271114616518574145552745)
      ·
        refine ⟨29453335962388930609164559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39271114616518574145552745 29453335962388930609164559)
        ·
          refine ⟨44180003943583395913746839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29453335962388930609164559 44180003943583395913746839)
          ·
            refine ⟨66270005915375093870620259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44180003943583395913746839 66270005915375093870620259)
            ·
              refine ⟨99405008873062640805930389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66270005915375093870620259 99405008873062640805930389)
              ·
                refine ⟨4659609790924811287777987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99405008873062640805930389 4659609790924811287777987)
                ·
                  refine ⟨6989414686387216931666981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4659609790924811287777987 6989414686387216931666981)
                  ·
                    refine ⟨1310515253697603174687559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6989414686387216931666981 1310515253697603174687559)
                    ·
                      rfl

theorem cell23_7656658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_7656658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7656658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7656658 prefixEnd_7656658 := by exact prefixLift 7656658
  have htrace : WordTrace (prefixWord ++ tailWord_7656658) baseStart_7656658 baseEnd_7656658 := by
    simpa [prefixWord, tailWord_7656658, baseEnd_7656658] using wordTrace_append hprefix tailTrace_7656658
  have hstable : (prefixWord ++ tailWord_7656658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7656658).length < 2 ^ (prefixWord ++ tailWord_7656658).sum := by decide
  have hdescent : baseEnd_7656658 < baseStart_7656658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7656658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7656691 : List Nat := [1, 1, 1, 2, 2, 5, 2, 1, 1, 5, 2]
def baseStart_7656691 : Nat := 118140960795 + 7656691 * 2 ^ 59
def prefixEnd_7656691 : Nat := 4983230072969 + 3 ^ 40 * 7656691 * 2
def baseEnd_7656691 : Nat := 3931562705954407894950025

theorem tailTrace_7656691 : CollatzResearch.WordTrace tailWord_7656691 prefixEnd_7656691 3931562705954407894950025 := by
  unfold tailWord_7656691
  simp only [CollatzResearch.WordTrace]
  refine ⟨279262463104123640559881927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186174975402749093706587951 279262463104123640559881927)
  ·
    refine ⟨418893694656185460839822891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279262463104123640559881927 418893694656185460839822891)
    ·
      refine ⟨628340541984278191259734337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418893694656185460839822891 628340541984278191259734337)
      ·
        refine ⟨471255406488208643444800753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 628340541984278191259734337 471255406488208643444800753)
        ·
          refine ⟨353441554866156482583600565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 471255406488208643444800753 353441554866156482583600565)
          ·
            refine ⟨33135145768702170242212553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 353441554866156482583600565 33135145768702170242212553)
            ·
              refine ⟨24851359326526627681659415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33135145768702170242212553 24851359326526627681659415)
              ·
                refine ⟨37277038989789941522489123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24851359326526627681659415 37277038989789941522489123)
                ·
                  refine ⟨55915558484684912283733685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37277038989789941522489123 55915558484684912283733685)
                  ·
                    refine ⟨5242083607939210526600033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55915558484684912283733685 5242083607939210526600033)
                    ·
                      refine ⟨3931562705954407894950025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5242083607939210526600033 3931562705954407894950025)
                      ·
                        rfl

theorem cell23_7656691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 5, 2].length) (baseStart_7656691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7656691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7656691 prefixEnd_7656691 := by exact prefixLift 7656691
  have htrace : WordTrace (prefixWord ++ tailWord_7656691) baseStart_7656691 baseEnd_7656691 := by
    simpa [prefixWord, tailWord_7656691, baseEnd_7656691] using wordTrace_append hprefix tailTrace_7656691
  have hstable : (prefixWord ++ tailWord_7656691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7656691).length < 2 ^ (prefixWord ++ tailWord_7656691).sum := by decide
  have hdescent : baseEnd_7656691 < baseStart_7656691 := by decide
  rcases family_descends (prefixWord ++ tailWord_7656691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7656704 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 4]
def baseStart_7656704 : Nat := 118140960795 + 7656704 * 2 ^ 59
def prefixEnd_7656704 : Nat := 4983230072969 + 3 ^ 40 * 7656704 * 2
def baseEnd_7656704 : Nat := 3931569381202916344087465

theorem tailTrace_7656704 : CollatzResearch.WordTrace tailWord_7656704 prefixEnd_7656704 3931569381202916344087465 := by
  unfold tailWord_7656704
  simp only [CollatzResearch.WordTrace]
  refine ⟨139631468626538271890052583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186175291502051029186736777 139631468626538271890052583)
  ·
    refine ⟨209447202939807407835078875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139631468626538271890052583 209447202939807407835078875)
    ·
      refine ⟨314170804409711111752618313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209447202939807407835078875 314170804409711111752618313)
      ·
        refine ⟨235628103307283333814463735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314170804409711111752618313 235628103307283333814463735)
        ·
          refine ⟨353442154960925000721695603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235628103307283333814463735 353442154960925000721695603)
          ·
            refine ⟨530163232441387501082543405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353442154960925000721695603 530163232441387501082543405)
            ·
              refine ⟨198811212165520312905953777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 530163232441387501082543405 198811212165520312905953777)
              ·
                refine ⟨149108409124140234679465333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198811212165520312905953777 149108409124140234679465333)
                ·
                  refine ⟨13978913355388147001199875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 149108409124140234679465333 13978913355388147001199875)
                  ·
                    refine ⟨20968370033082220501799813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13978913355388147001199875 20968370033082220501799813)
                    ·
                      refine ⟨3931569381202916344087465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20968370033082220501799813 3931569381202916344087465)
                      ·
                        rfl

theorem cell23_7656704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 4].length) (baseStart_7656704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7656704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7656704 prefixEnd_7656704 := by exact prefixLift 7656704
  have htrace : WordTrace (prefixWord ++ tailWord_7656704) baseStart_7656704 baseEnd_7656704 := by
    simpa [prefixWord, tailWord_7656704, baseEnd_7656704] using wordTrace_append hprefix tailTrace_7656704
  have hstable : (prefixWord ++ tailWord_7656704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7656704).length < 2 ^ (prefixWord ++ tailWord_7656704).sum := by decide
  have hdescent : baseEnd_7656704 < baseStart_7656704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7656704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7656708 : List Nat := [2, 3, 2, 2, 2, 1, 1, 1, 4, 3, 2]
def baseStart_7656708 : Nat := 118140960795 + 7656708 * 2 ^ 59
def prefixEnd_7656708 : Nat := 4983230072969 + 3 ^ 40 * 7656708 * 2
def baseEnd_7656708 : Nat := 3931571435125534328437447

theorem tailTrace_7656708 : CollatzResearch.WordTrace tailWord_7656708 prefixEnd_7656708 3931571435125534328437447 := by
  unfold tailWord_7656708
  simp only [CollatzResearch.WordTrace]
  refine ⟨139631541572531026231625389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186175388763374701642167185 139631541572531026231625389)
  ·
    refine ⟨52361828089699134836859521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139631541572531026231625389 52361828089699134836859521)
    ·
      refine ⟨39271371067274351127644641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52361828089699134836859521 39271371067274351127644641)
      ·
        refine ⟨29453528300455763345733481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39271371067274351127644641 29453528300455763345733481)
        ·
          refine ⟨22090146225341822509300111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29453528300455763345733481 22090146225341822509300111)
          ·
            refine ⟨33135219338012733763950167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22090146225341822509300111 33135219338012733763950167)
            ·
              refine ⟨49702829007019100645925251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33135219338012733763950167 49702829007019100645925251)
              ·
                refine ⟨74554243510528650968887877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49702829007019100645925251 74554243510528650968887877)
                ·
                  refine ⟨13978920658224122056666477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74554243510528650968887877 13978920658224122056666477)
                  ·
                    refine ⟨5242095246834045771249929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13978920658224122056666477 5242095246834045771249929)
                    ·
                      refine ⟨3931571435125534328437447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5242095246834045771249929 3931571435125534328437447)
                      ·
                        rfl

theorem cell23_7656708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_7656708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7656708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7656708 prefixEnd_7656708 := by exact prefixLift 7656708
  have htrace : WordTrace (prefixWord ++ tailWord_7656708) baseStart_7656708 baseEnd_7656708 := by
    simpa [prefixWord, tailWord_7656708, baseEnd_7656708] using wordTrace_append hprefix tailTrace_7656708
  have hstable : (prefixWord ++ tailWord_7656708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7656708).length < 2 ^ (prefixWord ++ tailWord_7656708).sum := by decide
  have hdescent : baseEnd_7656708 < baseStart_7656708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7656708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7656722 : List Nat := [3, 2, 4, 2, 1, 2, 2, 1, 6]
def baseStart_7656722 : Nat := 118140960795 + 7656722 * 2 ^ 59
def prefixEnd_7656722 : Nat := 4983230072969 + 3 ^ 40 * 7656722 * 2
def baseEnd_7656722 : Nat := 436842069317188585962487

theorem tailTrace_7656722 : CollatzResearch.WordTrace tailWord_7656722 prefixEnd_7656722 436842069317188585962487 := by
  unfold tailWord_7656722
  simp only [CollatzResearch.WordTrace]
  refine ⟨69815898441752833213565105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186175729178007555236173613 69815898441752833213565105)
  ·
    refine ⟨52361923831314624910173829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69815898441752833213565105 52361923831314624910173829)
    ·
      refine ⟨9817860718371492170657593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52361923831314624910173829 9817860718371492170657593)
      ·
        refine ⟨7363395538778619127993195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9817860718371492170657593 7363395538778619127993195)
        ·
          refine ⟨11045093308167928691989793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7363395538778619127993195 11045093308167928691989793)
          ·
            refine ⟨8283819981125946518992345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11045093308167928691989793 8283819981125946518992345)
            ·
              refine ⟨6212864985844459889244259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8283819981125946518992345 6212864985844459889244259)
              ·
                refine ⟨9319297478766689833866389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6212864985844459889244259 9319297478766689833866389)
                ·
                  refine ⟨436842069317188585962487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9319297478766689833866389 436842069317188585962487)
                  ·
                    rfl

theorem cell23_7656722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 1, 6].length) (baseStart_7656722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7656722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7656722 prefixEnd_7656722 := by exact prefixLift 7656722
  have htrace : WordTrace (prefixWord ++ tailWord_7656722) baseStart_7656722 baseEnd_7656722 := by
    simpa [prefixWord, tailWord_7656722, baseEnd_7656722] using wordTrace_append hprefix tailTrace_7656722
  have hstable : (prefixWord ++ tailWord_7656722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7656722).length < 2 ^ (prefixWord ++ tailWord_7656722).sum := by decide
  have hdescent : baseEnd_7656722 < baseStart_7656722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7656722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7656735 : List Nat := [1, 1, 2, 4, 5, 1, 1, 2, 1, 5]
def baseStart_7656735 : Nat := 118140960795 + 7656735 * 2 ^ 59
def prefixEnd_7656735 : Nat := 4983230072969 + 3 ^ 40 * 7656735 * 2
def baseEnd_7656735 : Nat := 1310528433034401907599941

theorem tailTrace_7656735 : CollatzResearch.WordTrace tailWord_7656735 prefixEnd_7656735 1310528433034401907599941 := by
  unfold tailWord_7656735
  simp only [CollatzResearch.WordTrace]
  refine ⟨279264067915964236074483659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186176045277309490716322439 279264067915964236074483659)
  ·
    refine ⟨418896101873946354111725489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279264067915964236074483659 418896101873946354111725489)
    ·
      refine ⟨314172076405459765583794117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418896101873946354111725489 314172076405459765583794117)
      ·
        refine ⟨58907264326023706046961397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 314172076405459765583794117 58907264326023706046961397)
        ·
          refine ⟨5522556030564722441902631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58907264326023706046961397 5522556030564722441902631)
          ·
            refine ⟨8283834045847083662853947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5522556030564722441902631 8283834045847083662853947)
            ·
              refine ⟨12425751068770625494280921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8283834045847083662853947 12425751068770625494280921)
              ·
                refine ⟨9319313301577969120710691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12425751068770625494280921 9319313301577969120710691)
                ·
                  refine ⟨13978969952366953681066037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9319313301577969120710691 13978969952366953681066037)
                  ·
                    refine ⟨1310528433034401907599941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13978969952366953681066037 1310528433034401907599941)
                    ·
                      rfl

theorem cell23_7656735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 2, 1, 5].length) (baseStart_7656735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7656735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7656735 prefixEnd_7656735 := by exact prefixLift 7656735
  have htrace : WordTrace (prefixWord ++ tailWord_7656735) baseStart_7656735 baseEnd_7656735 := by
    simpa [prefixWord, tailWord_7656735, baseEnd_7656735] using wordTrace_append hprefix tailTrace_7656735
  have hstable : (prefixWord ++ tailWord_7656735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7656735).length < 2 ^ (prefixWord ++ tailWord_7656735).sum := by decide
  have hdescent : baseEnd_7656735 < baseStart_7656735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7656735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7656738 : List Nat := [3, 3, 1, 1, 4, 1, 1, 1, 3, 1, 4]
def baseStart_7656738 : Nat := 118140960795 + 7656738 * 2 ^ 59
def prefixEnd_7656738 : Nat := 4983230072969 + 3 ^ 40 * 7656738 * 2
def baseEnd_7656738 : Nat := 3931586839545169211062309

theorem tailTrace_7656738 : CollatzResearch.WordTrace tailWord_7656738 prefixEnd_7656738 3931586839545169211062309 := by
  unfold tailWord_7656738
  simp only [CollatzResearch.WordTrace]
  refine ⟨69816044333738341896710717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186176118223302245057895245 69816044333738341896710717)
  ·
    refine ⟨26181016625151878211266519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69816044333738341896710717 26181016625151878211266519)
    ·
      refine ⟨39271524937727817316899779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26181016625151878211266519 39271524937727817316899779)
      ·
        refine ⟨58907287406591725975349669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39271524937727817316899779 58907287406591725975349669)
        ·
          refine ⟨11045116388735948620378063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58907287406591725975349669 11045116388735948620378063)
          ·
            refine ⟨16567674583103922930567095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11045116388735948620378063 16567674583103922930567095)
            ·
              refine ⟨24851511874655884395850643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16567674583103922930567095 24851511874655884395850643)
              ·
                refine ⟨37277267811983826593775965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24851511874655884395850643 37277267811983826593775965)
                ·
                  refine ⟨13978975429493934972665987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37277267811983826593775965 13978975429493934972665987)
                  ·
                    refine ⟨20968463144240902458998981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13978975429493934972665987 20968463144240902458998981)
                    ·
                      refine ⟨3931586839545169211062309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20968463144240902458998981 3931586839545169211062309)
                      ·
                        rfl

theorem cell23_7656738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_7656738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7656738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7656738 prefixEnd_7656738 := by exact prefixLift 7656738
  have htrace : WordTrace (prefixWord ++ tailWord_7656738) baseStart_7656738 baseEnd_7656738 := by
    simpa [prefixWord, tailWord_7656738, baseEnd_7656738] using wordTrace_append hprefix tailTrace_7656738
  have hstable : (prefixWord ++ tailWord_7656738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7656738).length < 2 ^ (prefixWord ++ tailWord_7656738).sum := by decide
  have hdescent : baseEnd_7656738 < baseStart_7656738 := by decide
  rcases family_descends (prefixWord ++ tailWord_7656738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7656761 : List Nat := [1, 2, 1, 6, 3, 10]
def baseStart_7656761 : Nat := 118140960795 + 7656761 * 2 ^ 59
def prefixEnd_7656761 : Nat := 4983230072969 + 3 ^ 40 * 7656761 * 2
def baseEnd_7656761 : Nat := 16179418311112027247221

theorem tailTrace_7656761 : CollatzResearch.WordTrace tailWord_7656761 prefixEnd_7656761 16179418311112027247221 := by
  unfold tailWord_7656761
  simp only [CollatzResearch.WordTrace]
  refine ⟨279265016213870042514930137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186176677475913361676620091 279265016213870042514930137)
  ·
    refine ⟨209448762160402531886197603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279265016213870042514930137 209448762160402531886197603)
    ·
      refine ⟨314173143240603797829296405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209448762160402531886197603 314173143240603797829296405)
      ·
        refine ⟨14726866089403303023248269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 314173143240603797829296405 14726866089403303023248269)
        ·
          refine ⟨5522574783526238633718101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14726866089403303023248269 5522574783526238633718101)
          ·
            refine ⟨16179418311112027247221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5522574783526238633718101 16179418311112027247221)
            ·
              rfl

theorem cell23_7656761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 10].length) (baseStart_7656761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7656761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7656761 prefixEnd_7656761 := by exact prefixLift 7656761
  have htrace : WordTrace (prefixWord ++ tailWord_7656761) baseStart_7656761 baseEnd_7656761 := by
    simpa [prefixWord, tailWord_7656761, baseEnd_7656761] using wordTrace_append hprefix tailTrace_7656761
  have hstable : (prefixWord ++ tailWord_7656761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7656761).length < 2 ^ (prefixWord ++ tailWord_7656761).sum := by decide
  have hdescent : baseEnd_7656761 < baseStart_7656761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7656761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7656788 : List Nat := [2, 4, 1, 1, 2, 1, 4, 1, 1, 3, 3]
def baseStart_7656788 : Nat := 118140960795 + 7656788 * 2 ^ 59
def prefixEnd_7656788 : Nat := 4983230072969 + 3 ^ 40 * 7656788 * 2
def baseEnd_7656788 : Nat := 3931612513577894015437079

theorem tailTrace_7656788 : CollatzResearch.WordTrace tailWord_7656788 prefixEnd_7656788 3931612513577894015437079 := by
  unfold tailWord_7656788
  simp only [CollatzResearch.WordTrace]
  refine ⟨139633000492386113063081509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186177333989848150750775345 139633000492386113063081509)
  ·
    refine ⟨26181187592322396199327783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139633000492386113063081509 26181187592322396199327783)
    ·
      refine ⟨39271781388483594298991675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26181187592322396199327783 39271781388483594298991675)
      ·
        refine ⟨58907672082725391448487513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39271781388483594298991675 58907672082725391448487513)
        ·
          refine ⟨44180754062044043586365635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58907672082725391448487513 44180754062044043586365635)
          ·
            refine ⟨66271131093066065379548453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44180754062044043586365635 66271131093066065379548453)
            ·
              refine ⟨12425837079949887258665335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66271131093066065379548453 12425837079949887258665335)
              ·
                refine ⟨18638755619924830887998003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12425837079949887258665335 18638755619924830887998003)
                ·
                  refine ⟨27958133429887246331997005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18638755619924830887998003 27958133429887246331997005)
                  ·
                    refine ⟨10484300036207717374498877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27958133429887246331997005 10484300036207717374498877)
                    ·
                      refine ⟨3931612513577894015437079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10484300036207717374498877 3931612513577894015437079)
                      ·
                        rfl

theorem cell23_7656788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_7656788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7656788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7656788 prefixEnd_7656788 := by exact prefixLift 7656788
  have htrace : WordTrace (prefixWord ++ tailWord_7656788) baseStart_7656788 baseEnd_7656788 := by
    simpa [prefixWord, tailWord_7656788, baseEnd_7656788] using wordTrace_append hprefix tailTrace_7656788
  have hstable : (prefixWord ++ tailWord_7656788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7656788).length < 2 ^ (prefixWord ++ tailWord_7656788).sum := by decide
  have hdescent : baseEnd_7656788 < baseStart_7656788 := by decide
  rcases family_descends (prefixWord ++ tailWord_7656788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7656962 : List Nat := [3, 4, 1, 2, 1, 2, 1, 2, 3, 4]
def baseStart_7656962 : Nat := 118140960795 + 7656962 * 2 ^ 59
def prefixEnd_7656962 : Nat := 4983230072969 + 3 ^ 40 * 7656962 * 2
def baseEnd_7656962 : Nat := 1310567286403925444887093

theorem tailTrace_7656962 : CollatzResearch.WordTrace tailWord_7656962 prefixEnd_7656962 1310567286403925444887093 := by
  unfold tailWord_7656962
  simp only [CollatzResearch.WordTrace]
  refine ⟨69818086821535463460749285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186181564857427902561998093 69818086821535463460749285)
  ·
    refine ⟨13090891279037899398890491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69818086821535463460749285 13090891279037899398890491)
    ·
      refine ⟨19636336918556849098335737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13090891279037899398890491 19636336918556849098335737)
      ·
        refine ⟨14727252688917636823751803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19636336918556849098335737 14727252688917636823751803)
        ·
          refine ⟨22090879033376455235627705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14727252688917636823751803 22090879033376455235627705)
          ·
            refine ⟨16568159275032341426720779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22090879033376455235627705 16568159275032341426720779)
            ·
              refine ⟨24852238912548512140081169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16568159275032341426720779 24852238912548512140081169)
              ·
                refine ⟨18639179184411384105060877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24852238912548512140081169 18639179184411384105060877)
                ·
                  refine ⟨6989692194154269039397829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18639179184411384105060877 6989692194154269039397829)
                  ·
                    refine ⟨1310567286403925444887093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6989692194154269039397829 1310567286403925444887093)
                    ·
                      rfl

theorem cell23_7656962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_7656962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7656962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7656962 prefixEnd_7656962 := by exact prefixLift 7656962
  have htrace : WordTrace (prefixWord ++ tailWord_7656962) baseStart_7656962 baseEnd_7656962 := by
    simpa [prefixWord, tailWord_7656962, baseEnd_7656962] using wordTrace_append hprefix tailTrace_7656962
  have hstable : (prefixWord ++ tailWord_7656962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7656962).length < 2 ^ (prefixWord ++ tailWord_7656962).sum := by decide
  have hdescent : baseEnd_7656962 < baseStart_7656962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7656962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7656966 : List Nat := [6, 2, 1, 1, 2, 2, 1, 1, 2, 5]
def baseStart_7656966 : Nat := 118140960795 + 7656966 * 2 ^ 59
def prefixEnd_7656966 : Nat := 4983230072969 + 3 ^ 40 * 7656966 * 2
def baseEnd_7656966 : Nat := 1310567971044798106337087

theorem tailTrace_7656966 : CollatzResearch.WordTrace tailWord_7656966 prefixEnd_7656966 1310567971044798106337087 := by
  unfold tailWord_7656966
  simp only [CollatzResearch.WordTrace]
  refine ⟨8727265411816480078941961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 186181662118751575017428501 8727265411816480078941961)
  ·
    refine ⟨6545449058862360059206471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8727265411816480078941961 6545449058862360059206471)
    ·
      refine ⟨9818173588293540088809707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6545449058862360059206471 9818173588293540088809707)
      ·
        refine ⟨14727260382440310133214561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9818173588293540088809707 14727260382440310133214561)
        ·
          refine ⟨11045445286830232599910921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14727260382440310133214561 11045445286830232599910921)
          ·
            refine ⟨8284083965122674449933191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11045445286830232599910921 8284083965122674449933191)
            ·
              refine ⟨12426125947684011674899787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8284083965122674449933191 12426125947684011674899787)
              ·
                refine ⟨18639188921526017512349681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12426125947684011674899787 18639188921526017512349681)
                ·
                  refine ⟨13979391691144513134262261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18639188921526017512349681 13979391691144513134262261)
                  ·
                    refine ⟨1310567971044798106337087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13979391691144513134262261 1310567971044798106337087)
                    ·
                      rfl

theorem cell23_7656966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_7656966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7656966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7656966 prefixEnd_7656966 := by exact prefixLift 7656966
  have htrace : WordTrace (prefixWord ++ tailWord_7656966) baseStart_7656966 baseEnd_7656966 := by
    simpa [prefixWord, tailWord_7656966, baseEnd_7656966] using wordTrace_append hprefix tailTrace_7656966
  have hstable : (prefixWord ++ tailWord_7656966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7656966).length < 2 ^ (prefixWord ++ tailWord_7656966).sum := by decide
  have hdescent : baseEnd_7656966 < baseStart_7656966 := by decide
  rcases family_descends (prefixWord ++ tailWord_7656966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7656972 : List Nat := [2, 2, 1, 2, 5, 2, 1, 1, 2, 2, 3]
def baseStart_7656972 : Nat := 118140960795 + 7656972 * 2 ^ 59
def prefixEnd_7656972 : Nat := 4983230072969 + 3 ^ 40 * 7656972 * 2
def baseEnd_7656972 : Nat := 3931706994018321295536233

theorem tailTrace_7656972 : CollatzResearch.WordTrace tailWord_7656972 prefixEnd_7656972 3931706994018321295536233 := by
  unfold tailWord_7656972
  simp only [CollatzResearch.WordTrace]
  refine ⟨139636356008052812775430585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186181808010737083700574113 139636356008052812775430585)
  ·
    refine ⟨104727267006039609581572939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139636356008052812775430585 104727267006039609581572939)
    ·
      refine ⟨157090900509059414372359409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104727267006039609581572939 157090900509059414372359409)
      ·
        refine ⟨117818175381794560779269557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157090900509059414372359409 117818175381794560779269557)
        ·
          refine ⟨11045453942043240073056521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117818175381794560779269557 11045453942043240073056521)
          ·
            refine ⟨8284090456532430054792391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11045453942043240073056521 8284090456532430054792391)
            ·
              refine ⟨12426135684798645082188587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8284090456532430054792391 12426135684798645082188587)
              ·
                refine ⟨18639203527197967623282881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12426135684798645082188587 18639203527197967623282881)
                ·
                  refine ⟨13979402645398475717462161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18639203527197967623282881 13979402645398475717462161)
                  ·
                    refine ⟨10484551984048856788096621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13979402645398475717462161 10484551984048856788096621)
                    ·
                      refine ⟨3931706994018321295536233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10484551984048856788096621 3931706994018321295536233)
                      ·
                        rfl

theorem cell23_7656972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 2, 2, 3].length) (baseStart_7656972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7656972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7656972 prefixEnd_7656972 := by exact prefixLift 7656972
  have htrace : WordTrace (prefixWord ++ tailWord_7656972) baseStart_7656972 baseEnd_7656972 := by
    simpa [prefixWord, tailWord_7656972, baseEnd_7656972] using wordTrace_append hprefix tailTrace_7656972
  have hstable : (prefixWord ++ tailWord_7656972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7656972).length < 2 ^ (prefixWord ++ tailWord_7656972).sum := by decide
  have hdescent : baseEnd_7656972 < baseStart_7656972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7656972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7657002 : List Nat := [3, 1, 4, 1, 1, 1, 4, 1, 3, 1, 3]
def baseStart_7657002 : Nat := 118140960795 + 7657002 * 2 ^ 59
def prefixEnd_7657002 : Nat := 4983230072969 + 3 ^ 40 * 7657002 * 2
def baseEnd_7657002 : Nat := 3931722398437956178161095

theorem tailTrace_7657002 : CollatzResearch.WordTrace tailWord_7657002 prefixEnd_7657002 3931722398437956178161095 := by
  unfold tailWord_7657002
  simp only [CollatzResearch.WordTrace]
  refine ⟨69818451551499235168613315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186182537470664627116302173 69818451551499235168613315)
  ·
    refine ⟨104727677327248852752919973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69818451551499235168613315 104727677327248852752919973)
    ·
      refine ⟨19636439498859159891172495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104727677327248852752919973 19636439498859159891172495)
      ·
        refine ⟨29454659248288739836758743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19636439498859159891172495 29454659248288739836758743)
        ·
          refine ⟨44181988872433109755138115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29454659248288739836758743 44181988872433109755138115)
          ·
            refine ⟨66272983308649664632707173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44181988872433109755138115 66272983308649664632707173)
            ·
              refine ⟨12426184370371812118632595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66272983308649664632707173 12426184370371812118632595)
              ·
                refine ⟨18639276555557718177948893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12426184370371812118632595 18639276555557718177948893)
                ·
                  refine ⟨6989728708334144316730835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18639276555557718177948893 6989728708334144316730835)
                  ·
                    refine ⟨10484593062501216475096253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6989728708334144316730835 10484593062501216475096253)
                    ·
                      refine ⟨3931722398437956178161095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10484593062501216475096253 3931722398437956178161095)
                      ·
                        rfl

theorem cell23_7657002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_7657002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7657002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7657002 prefixEnd_7657002 := by exact prefixLift 7657002
  have htrace : WordTrace (prefixWord ++ tailWord_7657002) baseStart_7657002 baseEnd_7657002 := by
    simpa [prefixWord, tailWord_7657002, baseEnd_7657002] using wordTrace_append hprefix tailTrace_7657002
  have hstable : (prefixWord ++ tailWord_7657002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7657002).length < 2 ^ (prefixWord ++ tailWord_7657002).sum := by decide
  have hdescent : baseEnd_7657002 < baseStart_7657002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7657002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7657025 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 2, 6, 2]
def baseStart_7657025 : Nat := 118140960795 + 7657025 * 2 ^ 59
def prefixEnd_7657025 : Nat := 4983230072969 + 3 ^ 40 * 7657025 * 2
def baseEnd_7657025 : Nat := 3931734208493009588173489

theorem tailTrace_7657025 : CollatzResearch.WordTrace tailWord_7657025 prefixEnd_7657025 3931734208493009588173489 := by
  unfold tailWord_7657025
  simp only [CollatzResearch.WordTrace]
  refine ⟨279274645084913615602540529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186183096723275743735027019 279274645084913615602540529)
  ·
    refine ⟨209455983813685211701905397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279274645084913615602540529 209455983813685211701905397)
    ·
      refine ⟨19636498482532988597053631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 209455983813685211701905397 19636498482532988597053631)
      ·
        refine ⟨29454747723799482895580447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19636498482532988597053631 29454747723799482895580447)
        ·
          refine ⟨44182121585699224343370671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29454747723799482895580447 44182121585699224343370671)
          ·
            refine ⟨66273182378548836515056007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44182121585699224343370671 66273182378548836515056007)
            ·
              refine ⟨99409773567823254772584011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66273182378548836515056007 99409773567823254772584011)
              ·
                refine ⟨149114660351734882158876017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99409773567823254772584011 149114660351734882158876017)
                ·
                  refine ⟨111835995263801161619157013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149114660351734882158876017 111835995263801161619157013)
                  ·
                    refine ⟨5242312277990679450897985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 111835995263801161619157013 5242312277990679450897985)
                    ·
                      refine ⟨3931734208493009588173489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5242312277990679450897985 3931734208493009588173489)
                      ·
                        rfl

theorem cell23_7657025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_7657025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7657025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7657025 prefixEnd_7657025 := by exact prefixLift 7657025
  have htrace : WordTrace (prefixWord ++ tailWord_7657025) baseStart_7657025 baseEnd_7657025 := by
    simpa [prefixWord, tailWord_7657025, baseEnd_7657025] using wordTrace_append hprefix tailTrace_7657025
  have hstable : (prefixWord ++ tailWord_7657025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7657025).length < 2 ^ (prefixWord ++ tailWord_7657025).sum := by decide
  have hdescent : baseEnd_7657025 < baseStart_7657025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7657025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7657038 : List Nat := [4, 1, 1, 1, 1, 2, 1, 3, 3, 2, 4]
def baseStart_7657038 : Nat := 118140960795 + 7657038 * 2 ^ 59
def prefixEnd_7657038 : Nat := 4983230072969 + 3 ^ 40 * 7657038 * 2
def baseEnd_7657038 : Nat := 3931740883741518037310929

theorem tailTrace_7657038 : CollatzResearch.WordTrace tailWord_7657038 prefixEnd_7657038 3931740883741518037310929 := by
  unfold tailWord_7657038
  simp only [CollatzResearch.WordTrace]
  refine ⟨34909389904233314852845471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186183412822577679215175845 34909389904233314852845471)
  ·
    refine ⟨52364084856349972279268207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34909389904233314852845471 52364084856349972279268207)
    ·
      refine ⟨78546127284524958418902311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52364084856349972279268207 78546127284524958418902311)
      ·
        refine ⟨117819190926787437628353467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78546127284524958418902311 117819190926787437628353467)
        ·
          refine ⟨176728786390181156442530201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117819190926787437628353467 176728786390181156442530201)
          ·
            refine ⟨132546589792635867331897651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176728786390181156442530201 132546589792635867331897651)
            ·
              refine ⟨198819884688953800997846477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132546589792635867331897651 198819884688953800997846477)
              ·
                refine ⟨74557456758357675374192429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198819884688953800997846477 74557456758357675374192429)
                ·
                  refine ⟨27959046284384128265322161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74557456758357675374192429 27959046284384128265322161)
                  ·
                    refine ⟨20969284713288096198991621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27959046284384128265322161 20969284713288096198991621)
                    ·
                      refine ⟨3931740883741518037310929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20969284713288096198991621 3931740883741518037310929)
                      ·
                        rfl

theorem cell23_7657038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_7657038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7657038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7657038 prefixEnd_7657038 := by exact prefixLift 7657038
  have htrace : WordTrace (prefixWord ++ tailWord_7657038) baseStart_7657038 baseEnd_7657038 := by
    simpa [prefixWord, tailWord_7657038, baseEnd_7657038] using wordTrace_append hprefix tailTrace_7657038
  have hstable : (prefixWord ++ tailWord_7657038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7657038).length < 2 ^ (prefixWord ++ tailWord_7657038).sum := by decide
  have hdescent : baseEnd_7657038 < baseStart_7657038 := by decide
  rcases family_descends (prefixWord ++ tailWord_7657038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7657053 : List Nat := [1, 4, 4, 2, 2, 1, 1, 1, 3, 1, 3]
def baseStart_7657053 : Nat := 118140960795 + 7657053 * 2 ^ 59
def prefixEnd_7657053 : Nat := 4983230072969 + 3 ^ 40 * 7657053 * 2
def baseEnd_7657053 : Nat := 3931748585951335478623361

theorem tailTrace_7657053 : CollatzResearch.WordTrace tailWord_7657053 prefixEnd_7657053 3931748585951335478623361 := by
  unfold tailWord_7657053
  simp only [CollatzResearch.WordTrace]
  refine ⟨279275666328812176384559813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186183777552541450923039875 279275666328812176384559813)
  ·
    refine ⟨52364187436652283072104965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 279275666328812176384559813 52364187436652283072104965)
    ·
      refine ⟨9818285144372303076019681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52364187436652283072104965 9818285144372303076019681)
      ·
        refine ⟨7363713858279227307014761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9818285144372303076019681 7363713858279227307014761)
        ·
          refine ⟨5522785393709420480261071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7363713858279227307014761 5522785393709420480261071)
          ·
            refine ⟨8284178090564130720391607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5522785393709420480261071 8284178090564130720391607)
            ·
              refine ⟨12426267135846196080587411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8284178090564130720391607 12426267135846196080587411)
              ·
                refine ⟨18639400703769294120881117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12426267135846196080587411 18639400703769294120881117)
                ·
                  refine ⟨6989775263913485295330419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18639400703769294120881117 6989775263913485295330419)
                  ·
                    refine ⟨10484662895870227942995629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6989775263913485295330419 10484662895870227942995629)
                    ·
                      refine ⟨3931748585951335478623361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10484662895870227942995629 3931748585951335478623361)
                      ·
                        rfl

theorem cell23_7657053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_7657053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7657053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7657053 prefixEnd_7657053 := by exact prefixLift 7657053
  have htrace : WordTrace (prefixWord ++ tailWord_7657053) baseStart_7657053 baseEnd_7657053 := by
    simpa [prefixWord, tailWord_7657053, baseEnd_7657053] using wordTrace_append hprefix tailTrace_7657053
  have hstable : (prefixWord ++ tailWord_7657053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7657053).length < 2 ^ (prefixWord ++ tailWord_7657053).sum := by decide
  have hdescent : baseEnd_7657053 < baseStart_7657053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7657053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7657059 : List Nat := [1, 1, 1, 5, 1, 5, 1, 1, 3, 2, 2]
def baseStart_7657059 : Nat := 118140960795 + 7657059 * 2 ^ 59
def prefixEnd_7657059 : Nat := 4983230072969 + 3 ^ 40 * 7657059 * 2
def baseEnd_7657059 : Nat := 3931751666835262455148333

theorem tailTrace_7657059 : CollatzResearch.WordTrace tailWord_7657059 prefixEnd_7657059 3931751666835262455148333 := by
  unfold tailWord_7657059
  simp only [CollatzResearch.WordTrace]
  refine ⟨279275885166790439409278231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186183923444526959606185487 279275885166790439409278231)
  ·
    refine ⟨418913827750185659113917347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279275885166790439409278231 418913827750185659113917347)
    ·
      refine ⟨628370741625278488670876021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418913827750185659113917347 628370741625278488670876021)
      ·
        refine ⟨58909757027369858312894627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 628370741625278488670876021 58909757027369858312894627)
        ·
          refine ⟨88364635541054787469341941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58909757027369858312894627 88364635541054787469341941)
          ·
            refine ⟨8284184581973886325250807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88364635541054787469341941 8284184581973886325250807)
            ·
              refine ⟨12426276872960829487876211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8284184581973886325250807 12426276872960829487876211)
              ·
                refine ⟨18639415309441244231814317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12426276872960829487876211 18639415309441244231814317)
                ·
                  refine ⟨6989780741040466586930369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18639415309441244231814317 6989780741040466586930369)
                  ·
                    refine ⟨5242335555780349940197777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6989780741040466586930369 5242335555780349940197777)
                    ·
                      refine ⟨3931751666835262455148333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5242335555780349940197777 3931751666835262455148333)
                      ·
                        rfl

theorem cell23_7657059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 3, 2, 2].length) (baseStart_7657059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7657059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7657059 prefixEnd_7657059 := by exact prefixLift 7657059
  have htrace : WordTrace (prefixWord ++ tailWord_7657059) baseStart_7657059 baseEnd_7657059 := by
    simpa [prefixWord, tailWord_7657059, baseEnd_7657059] using wordTrace_append hprefix tailTrace_7657059
  have hstable : (prefixWord ++ tailWord_7657059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7657059).length < 2 ^ (prefixWord ++ tailWord_7657059).sum := by decide
  have hdescent : baseEnd_7657059 < baseStart_7657059 := by decide
  rcases family_descends (prefixWord ++ tailWord_7657059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7657092 : List Nat := [2, 3, 2, 1, 4, 1, 1, 2, 1, 3, 3]
def baseStart_7657092 : Nat := 118140960795 + 7657092 * 2 ^ 59
def prefixEnd_7657092 : Nat := 4983230072969 + 3 ^ 40 * 7657092 * 2
def baseEnd_7657092 : Nat := 3931768611696860826035681

theorem tailTrace_7657092 : CollatzResearch.WordTrace tailWord_7657092 prefixEnd_7657092 3931768611696860826035681 := by
  unfold tailWord_7657092
  simp only [CollatzResearch.WordTrace]
  refine ⟨139638544387835443022614765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186184725850447257363486353 139638544387835443022614765)
  ·
    refine ⟨52364454145438291133480537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139638544387835443022614765 52364454145438291133480537)
    ·
      refine ⟨39273340609078718350110403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52364454145438291133480537 39273340609078718350110403)
      ·
        refine ⟨58910010913618077525165605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39273340609078718350110403 58910010913618077525165605)
        ·
          refine ⟨11045627046303389535968551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58910010913618077525165605 11045627046303389535968551)
          ·
            refine ⟨16568440569455084303952827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11045627046303389535968551 16568440569455084303952827)
            ·
              refine ⟨24852660854182626455929241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16568440569455084303952827 24852660854182626455929241)
              ·
                refine ⟨18639495640636969841946931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24852660854182626455929241 18639495640636969841946931)
                ·
                  refine ⟨27959243460955454762920397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18639495640636969841946931 27959243460955454762920397)
                  ·
                    refine ⟨10484716297858295536095149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27959243460955454762920397 10484716297858295536095149)
                    ·
                      refine ⟨3931768611696860826035681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10484716297858295536095149 3931768611696860826035681)
                      ·
                        rfl

theorem cell23_7657092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_7657092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7657092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7657092 prefixEnd_7657092 := by exact prefixLift 7657092
  have htrace : WordTrace (prefixWord ++ tailWord_7657092) baseStart_7657092 baseEnd_7657092 := by
    simpa [prefixWord, tailWord_7657092, baseEnd_7657092] using wordTrace_append hprefix tailTrace_7657092
  have hstable : (prefixWord ++ tailWord_7657092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7657092).length < 2 ^ (prefixWord ++ tailWord_7657092).sum := by decide
  have hdescent : baseEnd_7657092 < baseStart_7657092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7657092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7657096 : List Nat := [2, 1, 3, 5, 1, 1, 3, 1, 1, 2, 3]
def baseStart_7657096 : Nat := 118140960795 + 7657096 * 2 ^ 59
def prefixEnd_7657096 : Nat := 4983230072969 + 3 ^ 40 * 7657096 * 2
def baseEnd_7657096 : Nat := 3931770665619478810385663

theorem tailTrace_7657096 : CollatzResearch.WordTrace tailWord_7657096 prefixEnd_7657096 3931770665619478810385663 := by
  unfold tailWord_7657096
  simp only [CollatzResearch.WordTrace]
  refine ⟨139638617333828197364187571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186184823111770929818916761 139638617333828197364187571)
  ·
    refine ⟨209457926000742296046281357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139638617333828197364187571 209457926000742296046281357)
    ·
      refine ⟨78546722250278361017355509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209457926000742296046281357 78546722250278361017355509)
      ·
        refine ⟨7363755210963596345377079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78546722250278361017355509 7363755210963596345377079)
        ·
          refine ⟨11045632816445394518065619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7363755210963596345377079 11045632816445394518065619)
          ·
            refine ⟨16568449224668091777098429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11045632816445394518065619 16568449224668091777098429)
            ·
              refine ⟨6213168459250534416411911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16568449224668091777098429 6213168459250534416411911)
              ·
                refine ⟨9319752688875801624617867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6213168459250534416411911 9319752688875801624617867)
                ·
                  refine ⟨13979629033313702436926801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9319752688875801624617867 13979629033313702436926801)
                  ·
                    refine ⟨10484721774985276827695101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13979629033313702436926801 10484721774985276827695101)
                    ·
                      refine ⟨3931770665619478810385663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10484721774985276827695101 3931770665619478810385663)
                      ·
                        rfl

theorem cell23_7657096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_7657096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7657096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7657096 prefixEnd_7657096 := by exact prefixLift 7657096
  have htrace : WordTrace (prefixWord ++ tailWord_7657096) baseStart_7657096 baseEnd_7657096 := by
    simpa [prefixWord, tailWord_7657096, baseEnd_7657096] using wordTrace_append hprefix tailTrace_7657096
  have hstable : (prefixWord ++ tailWord_7657096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7657096).length < 2 ^ (prefixWord ++ tailWord_7657096).sum := by decide
  have hdescent : baseEnd_7657096 < baseStart_7657096 := by decide
  rcases family_descends (prefixWord ++ tailWord_7657096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7657138 : List Nat := [3, 2, 1, 1, 1, 2, 3, 1, 9]
def baseStart_7657138 : Nat := 118140960795 + 7657138 * 2 ^ 59
def prefixEnd_7657138 : Nat := 4983230072969 + 3 ^ 40 * 7657138 * 2
def baseEnd_7657138 : Nat := 436865803534107516228941

theorem tailTrace_7657138 : CollatzResearch.WordTrace tailWord_7657138 prefixEnd_7657138 436865803534107516228941 := by
  unfold tailWord_7657138
  simp only [CollatzResearch.WordTrace]
  refine ⟨69819691633376058975351017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186185844355669490600936045 69819691633376058975351017)
  ·
    refine ⟨52364768725032044231513263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69819691633376058975351017 52364768725032044231513263)
    ·
      refine ⟨78547153087548066347269895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52364768725032044231513263 78547153087548066347269895)
      ·
        refine ⟨117820729631322099520904843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78547153087548066347269895 117820729631322099520904843)
        ·
          refine ⟨176731094446983149281357265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117820729631322099520904843 176731094446983149281357265)
          ·
            refine ⟨132548320835237361961017949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176731094446983149281357265 132548320835237361961017949)
            ·
              refine ⟨49705620313214010735381731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132548320835237361961017949 49705620313214010735381731)
              ·
                refine ⟨74558430469821016103072597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49705620313214010735381731 74558430469821016103072597)
                ·
                  refine ⟨436865803534107516228941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 74558430469821016103072597 436865803534107516228941)
                  ·
                    rfl

theorem cell23_7657138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 9].length) (baseStart_7657138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7657138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7657138 prefixEnd_7657138 := by exact prefixLift 7657138
  have htrace : WordTrace (prefixWord ++ tailWord_7657138) baseStart_7657138 baseEnd_7657138 := by
    simpa [prefixWord, tailWord_7657138, baseEnd_7657138] using wordTrace_append hprefix tailTrace_7657138
  have hstable : (prefixWord ++ tailWord_7657138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7657138).length < 2 ^ (prefixWord ++ tailWord_7657138).sum := by decide
  have hdescent : baseEnd_7657138 < baseStart_7657138 := by decide
  rcases family_descends (prefixWord ++ tailWord_7657138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7657172 : List Nat := [2, 4, 1, 3, 1, 2, 2, 1, 7]
def baseStart_7657172 : Nat := 118140960795 + 7657172 * 2 ^ 59
def prefixEnd_7657172 : Nat := 4983230072969 + 3 ^ 40 * 7657172 * 2
def baseEnd_7657172 : Nat := 436867743349913390337257

theorem tailTrace_7657172 : CollatzResearch.WordTrace tailWord_7657172 prefixEnd_7657172 436867743349913390337257 := by
  unfold tailWord_7657172
  simp only [CollatzResearch.WordTrace]
  refine ⟨139640003307690529854070885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186186671076920706472094513 139640003307690529854070885)
  ·
    refine ⟨26182500620191974347638291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139640003307690529854070885 26182500620191974347638291)
    ·
      refine ⟨39273750930287961521457437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26182500620191974347638291 39273750930287961521457437)
      ·
        refine ⟨14727656598857985570546539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39273750930287961521457437 14727656598857985570546539)
        ·
          refine ⟨22091484898286978355819809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14727656598857985570546539 22091484898286978355819809)
          ·
            refine ⟨16568613673715233766864857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22091484898286978355819809 16568613673715233766864857)
            ·
              refine ⟨12426460255286425325148643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16568613673715233766864857 12426460255286425325148643)
              ·
                refine ⟨18639690382929637987722965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12426460255286425325148643 18639690382929637987722965)
                ·
                  refine ⟨436867743349913390337257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18639690382929637987722965 436867743349913390337257)
                  ·
                    rfl

theorem cell23_7657172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_7657172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7657172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7657172 prefixEnd_7657172 := by exact prefixLift 7657172
  have htrace : WordTrace (prefixWord ++ tailWord_7657172) baseStart_7657172 baseEnd_7657172 := by
    simpa [prefixWord, tailWord_7657172, baseEnd_7657172] using wordTrace_append hprefix tailTrace_7657172
  have hstable : (prefixWord ++ tailWord_7657172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7657172).length < 2 ^ (prefixWord ++ tailWord_7657172).sum := by decide
  have hdescent : baseEnd_7657172 < baseStart_7657172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7657172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7657215 : List Nat := [1, 1, 2, 2, 1, 3, 2, 2, 5, 4]
def baseStart_7657215 : Nat := 118140960795 + 7657215 * 2 ^ 59
def prefixEnd_7657215 : Nat := 4983230072969 + 3 ^ 40 * 7657215 * 2
def baseEnd_7657215 : Nat := 1310610589939121281599205

theorem tailTrace_7657215 : CollatzResearch.WordTrace tailWord_7657215 prefixEnd_7657215 1310610589939121281599205 := by
  unfold tailWord_7657215
  simp only [CollatzResearch.WordTrace]
  refine ⟨279281574954225278051957099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186187716636150185367971399 279281574954225278051957099)
  ·
    refine ⟨418922362431337917077935649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279281574954225278051957099 418922362431337917077935649)
    ·
      refine ⟨314191771823503437808451737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418922362431337917077935649 314191771823503437808451737)
      ·
        refine ⟨235643828867627578356338803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314191771823503437808451737 235643828867627578356338803)
        ·
          refine ⟨353465743301441367534508205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235643828867627578356338803 353465743301441367534508205)
          ·
            refine ⟨132549653738040512825440577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 353465743301441367534508205 132549653738040512825440577)
            ·
              refine ⟨99412240303530384619080433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132549653738040512825440577 99412240303530384619080433)
              ·
                refine ⟨74559180227647788464310325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99412240303530384619080433 74559180227647788464310325)
                ·
                  refine ⟨6989923146341980168529093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74559180227647788464310325 6989923146341980168529093)
                  ·
                    refine ⟨1310610589939121281599205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6989923146341980168529093 1310610589939121281599205)
                    ·
                      rfl

theorem cell23_7657215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 5, 4].length) (baseStart_7657215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7657215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7657215 prefixEnd_7657215 := by exact prefixLift 7657215
  have htrace : WordTrace (prefixWord ++ tailWord_7657215) baseStart_7657215 baseEnd_7657215 := by
    simpa [prefixWord, tailWord_7657215, baseEnd_7657215] using wordTrace_append hprefix tailTrace_7657215
  have hstable : (prefixWord ++ tailWord_7657215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7657215).length < 2 ^ (prefixWord ++ tailWord_7657215).sum := by decide
  have hdescent : baseEnd_7657215 < baseStart_7657215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7657215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7657312 : List Nat := [2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 4]
def baseStart_7657312 : Nat := 118140960795 + 7657312 * 2 ^ 59
def prefixEnd_7657312 : Nat := 4983230072969 + 3 ^ 40 * 7657312 * 2
def baseEnd_7657312 : Nat := 3931881577440849965284669

theorem tailTrace_7657312 : CollatzResearch.WordTrace tailWord_7657312 prefixEnd_7657312 3931881577440849965284669 := by
  unfold tailWord_7657312
  simp only [CollatzResearch.WordTrace]
  refine ⟨139642556417436931809119095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186190075223249242412158793 139642556417436931809119095)
  ·
    refine ⟨209463834626155397713678643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139642556417436931809119095 209463834626155397713678643)
    ·
      refine ⟨314195751939233096570517965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209463834626155397713678643 314195751939233096570517965)
      ·
        refine ⟨117823406977212411213944237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314195751939233096570517965 117823406977212411213944237)
        ·
          refine ⟨44183777616454654205229089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117823406977212411213944237 44183777616454654205229089)
          ·
            refine ⟨33137833212340990653921817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44183777616454654205229089 33137833212340990653921817)
            ·
              refine ⟨24853374909255742990441363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33137833212340990653921817 24853374909255742990441363)
              ·
                refine ⟨37280062363883614485662045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24853374909255742990441363 37280062363883614485662045)
                ·
                  refine ⟨13980023386456355432123267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37280062363883614485662045 13980023386456355432123267)
                  ·
                    refine ⟨20970035079684533148184901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13980023386456355432123267 20970035079684533148184901)
                    ·
                      refine ⟨3931881577440849965284669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20970035079684533148184901 3931881577440849965284669)
                      ·
                        rfl

theorem cell23_7657312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_7657312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7657312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7657312 prefixEnd_7657312 := by exact prefixLift 7657312
  have htrace : WordTrace (prefixWord ++ tailWord_7657312) baseStart_7657312 baseEnd_7657312 := by
    simpa [prefixWord, tailWord_7657312, baseEnd_7657312] using wordTrace_append hprefix tailTrace_7657312
  have hstable : (prefixWord ++ tailWord_7657312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7657312).length < 2 ^ (prefixWord ++ tailWord_7657312).sum := by decide
  have hdescent : baseEnd_7657312 < baseStart_7657312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7657312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7657326 : List Nat := [4, 1, 2, 3, 1, 1, 4, 1, 1, 5]
def baseStart_7657326 : Nat := 118140960795 + 7657326 * 2 ^ 59
def prefixEnd_7657326 : Nat := 4983230072969 + 3 ^ 40 * 7657326 * 2
def baseEnd_7657326 : Nat := 1310629588723337636836535

theorem tailTrace_7657326 : CollatzResearch.WordTrace tailWord_7657326 prefixEnd_7657326 1310629588723337636836535 := by
  unfold tailWord_7657326
  simp only [CollatzResearch.WordTrace]
  refine ⟨34910702932102893001155979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186190415637882096006165221 34910702932102893001155979)
  ·
    refine ⟨52366054398154339501733969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34910702932102893001155979 52366054398154339501733969)
    ·
      refine ⟨39274540798615754626300477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52366054398154339501733969 39274540798615754626300477)
      ·
        refine ⟨14727952799480907984862679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39274540798615754626300477 14727952799480907984862679)
        ·
          refine ⟨22091929199221361977294019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14727952799480907984862679 22091929199221361977294019)
          ·
            refine ⟨33137893798832042965941029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22091929199221361977294019 33137893798832042965941029)
            ·
              refine ⟨6213355087281008056113943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33137893798832042965941029 6213355087281008056113943)
              ·
                refine ⟨9320032630921512084170915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6213355087281008056113943 9320032630921512084170915)
                ·
                  refine ⟨13980048946382268126256373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9320032630921512084170915 13980048946382268126256373)
                  ·
                    refine ⟨1310629588723337636836535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13980048946382268126256373 1310629588723337636836535)
                    ·
                      rfl

theorem cell23_7657326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_7657326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7657326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7657326 prefixEnd_7657326 := by exact prefixLift 7657326
  have htrace : WordTrace (prefixWord ++ tailWord_7657326) baseStart_7657326 baseEnd_7657326 := by
    simpa [prefixWord, tailWord_7657326, baseEnd_7657326] using wordTrace_append hprefix tailTrace_7657326
  have hstable : (prefixWord ++ tailWord_7657326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7657326).length < 2 ^ (prefixWord ++ tailWord_7657326).sum := by decide
  have hdescent : baseEnd_7657326 < baseStart_7657326 := by decide
  rcases family_descends (prefixWord ++ tailWord_7657326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7657329 : List Nat := [1, 2, 2, 2, 1, 3, 1, 2, 5, 2, 2]
def baseStart_7657329 : Nat := 118140960795 + 7657329 * 2 ^ 59
def prefixEnd_7657329 : Nat := 4983230072969 + 3 ^ 40 * 7657329 * 2
def baseEnd_7657329 : Nat := 3931890306611976398772091

theorem tailTrace_7657329 : CollatzResearch.WordTrace tailWord_7657329 prefixEnd_7657329 3931890306611976398772091 := by
  unfold tailWord_7657329
  simp only [CollatzResearch.WordTrace]
  refine ⟨279285732875812275521607041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186190488583874850347738027 279285732875812275521607041)
  ·
    refine ⟨209464299656859206641205281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279285732875812275521607041 209464299656859206641205281)
    ·
      refine ⟨157098224742644404980903961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209464299656859206641205281 157098224742644404980903961)
      ·
        refine ⟨117823668556983303735677971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157098224742644404980903961 117823668556983303735677971)
        ·
          refine ⟨176735502835474955603516957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117823668556983303735677971 176735502835474955603516957)
          ·
            refine ⟨66275813563303108351318859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176735502835474955603516957 66275813563303108351318859)
            ·
              refine ⟨99413720344954662526978289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66275813563303108351318859 99413720344954662526978289)
              ·
                refine ⟨74560290258715996895233717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99413720344954662526978289 74560290258715996895233717)
                ·
                  refine ⟨6990027211754624708928161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74560290258715996895233717 6990027211754624708928161)
                  ·
                    refine ⟨5242520408815968531696121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6990027211754624708928161 5242520408815968531696121)
                    ·
                      refine ⟨3931890306611976398772091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5242520408815968531696121 3931890306611976398772091)
                      ·
                        rfl

theorem cell23_7657329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 5, 2, 2].length) (baseStart_7657329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7657329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7657329 prefixEnd_7657329 := by exact prefixLift 7657329
  have htrace : WordTrace (prefixWord ++ tailWord_7657329) baseStart_7657329 baseEnd_7657329 := by
    simpa [prefixWord, tailWord_7657329, baseEnd_7657329] using wordTrace_append hprefix tailTrace_7657329
  have hstable : (prefixWord ++ tailWord_7657329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7657329).length < 2 ^ (prefixWord ++ tailWord_7657329).sum := by decide
  have hdescent : baseEnd_7657329 < baseStart_7657329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7657329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7657374 : List Nat := [4, 3, 1, 3, 2, 1, 1, 3, 1, 1, 3]
def baseStart_7657374 : Nat := 118140960795 + 7657374 * 2 ^ 59
def prefixEnd_7657374 : Nat := 4983230072969 + 3 ^ 40 * 7657374 * 2
def baseEnd_7657374 : Nat := 3931913413241428722709385

theorem tailTrace_7657374 : CollatzResearch.WordTrace tailWord_7657374 prefixEnd_7657374 3931913413241428722709385 := by
  unfold tailWord_7657374
  simp only [CollatzResearch.WordTrace]
  refine ⟨34910921770081156025874397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186191582773766165471330117 34910921770081156025874397)
  ·
    refine ⟨13091595663780433509702899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34910921770081156025874397 13091595663780433509702899)
    ·
      refine ⟨19637393495670650264554349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13091595663780433509702899 19637393495670650264554349)
      ·
        refine ⟨7364022560876493849207881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19637393495670650264554349 7364022560876493849207881)
        ·
          refine ⟨5523016920657370386905911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7364022560876493849207881 5523016920657370386905911)
          ·
            refine ⟨8284525380986055580358867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5523016920657370386905911 8284525380986055580358867)
            ·
              refine ⟨12426788071479083370538301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8284525380986055580358867 12426788071479083370538301)
              ·
                refine ⟨4660045526804656263951863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12426788071479083370538301 4660045526804656263951863)
                ·
                  refine ⟨6990068290206984395927795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4660045526804656263951863 6990068290206984395927795)
                  ·
                    refine ⟨10485102435310476593891693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6990068290206984395927795 10485102435310476593891693)
                    ·
                      refine ⟨3931913413241428722709385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10485102435310476593891693 3931913413241428722709385)
                      ·
                        rfl

theorem cell23_7657374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_7657374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7657374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7657374 prefixEnd_7657374 := by exact prefixLift 7657374
  have htrace : WordTrace (prefixWord ++ tailWord_7657374) baseStart_7657374 baseEnd_7657374 := by
    simpa [prefixWord, tailWord_7657374, baseEnd_7657374] using wordTrace_append hprefix tailTrace_7657374
  have hstable : (prefixWord ++ tailWord_7657374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7657374).length < 2 ^ (prefixWord ++ tailWord_7657374).sum := by decide
  have hdescent : baseEnd_7657374 < baseStart_7657374 := by decide
  rcases family_descends (prefixWord ++ tailWord_7657374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7657380 : List Nat := [2, 3, 1, 2, 1, 5, 1, 3, 1, 2, 2]
def baseStart_7657380 : Nat := 118140960795 + 7657380 * 2 ^ 59
def prefixEnd_7657380 : Nat := 4983230072969 + 3 ^ 40 * 7657380 * 2
def baseEnd_7657380 : Nat := 3931916494125355699234357

theorem tailTrace_7657380 : CollatzResearch.WordTrace tailWord_7657380 prefixEnd_7657380 3931916494125355699234357 := by
  unfold tailWord_7657380
  simp only [CollatzResearch.WordTrace]
  refine ⟨139643796499313755615856797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186191728665751674154475729 139643796499313755615856797)
  ·
    refine ⟨52366423687242658355946299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139643796499313755615856797 52366423687242658355946299)
    ·
      refine ⟨78549635530863987533919449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52366423687242658355946299 78549635530863987533919449)
      ·
        refine ⟨58912226648147990650439587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78549635530863987533919449 58912226648147990650439587)
        ·
          refine ⟨88368339972221985975659381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58912226648147990650439587 88368339972221985975659381)
          ·
            refine ⟨8284531872395811185218067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88368339972221985975659381 8284531872395811185218067)
            ·
              refine ⟨12426797808593716777827101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8284531872395811185218067 12426797808593716777827101)
              ·
                refine ⟨4660049178222643791685163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12426797808593716777827101 4660049178222643791685163)
                ·
                  refine ⟨6990073767333965687527745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4660049178222643791685163 6990073767333965687527745)
                  ·
                    refine ⟨5242555325500474265645809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6990073767333965687527745 5242555325500474265645809)
                    ·
                      refine ⟨3931916494125355699234357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5242555325500474265645809 3931916494125355699234357)
                      ·
                        rfl

theorem cell23_7657380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 3, 1, 2, 2].length) (baseStart_7657380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7657380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7657380 prefixEnd_7657380 := by exact prefixLift 7657380
  have htrace : WordTrace (prefixWord ++ tailWord_7657380) baseStart_7657380 baseEnd_7657380 := by
    simpa [prefixWord, tailWord_7657380, baseEnd_7657380] using wordTrace_append hprefix tailTrace_7657380
  have hstable : (prefixWord ++ tailWord_7657380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7657380).length < 2 ^ (prefixWord ++ tailWord_7657380).sum := by decide
  have hdescent : baseEnd_7657380 < baseStart_7657380 := by decide
  rcases family_descends (prefixWord ++ tailWord_7657380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7657419 : List Nat := [1, 1, 1, 1, 3, 4, 2, 3, 1, 4, 2]
def baseStart_7657419 : Nat := 118140960795 + 7657419 * 2 ^ 59
def prefixEnd_7657419 : Nat := 4983230072969 + 3 ^ 40 * 7657419 * 2
def baseEnd_7657419 : Nat := 3931936519870881046646677

theorem tailTrace_7657419 : CollatzResearch.WordTrace tailWord_7657419 prefixEnd_7657419 3931936519870881046646677 := by
  unfold tailWord_7657419
  simp only [CollatzResearch.WordTrace]
  refine ⟨279289015445486220892383311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186192676963657480594922207 279289015445486220892383311)
  ·
    refine ⟨418933523168229331338574967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279289015445486220892383311 418933523168229331338574967)
    ·
      refine ⟨628400284752343997007862451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418933523168229331338574967 628400284752343997007862451)
      ·
        refine ⟨942600427128515995511793677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 628400284752343997007862451 942600427128515995511793677)
        ·
          refine ⟨353475160173193498316922629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 942600427128515995511793677 353475160173193498316922629)
          ·
            refine ⟨66276592532473780934422993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 353475160173193498316922629 66276592532473780934422993)
            ·
              refine ⟨49707444399355335700817245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66276592532473780934422993 49707444399355335700817245)
              ·
                refine ⟨18640291649758250887806467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49707444399355335700817245 18640291649758250887806467)
                ·
                  refine ⟨27960437474637376331709701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18640291649758250887806467 27960437474637376331709701)
                  ·
                    refine ⟨5242582026494508062195569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27960437474637376331709701 5242582026494508062195569)
                    ·
                      refine ⟨3931936519870881046646677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5242582026494508062195569 3931936519870881046646677)
                      ·
                        rfl

theorem cell23_7657419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 4, 2].length) (baseStart_7657419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7657419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7657419 prefixEnd_7657419 := by exact prefixLift 7657419
  have htrace : WordTrace (prefixWord ++ tailWord_7657419) baseStart_7657419 baseEnd_7657419 := by
    simpa [prefixWord, tailWord_7657419, baseEnd_7657419] using wordTrace_append hprefix tailTrace_7657419
  have hstable : (prefixWord ++ tailWord_7657419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7657419).length < 2 ^ (prefixWord ++ tailWord_7657419).sum := by decide
  have hdescent : baseEnd_7657419 < baseStart_7657419 := by decide
  rcases family_descends (prefixWord ++ tailWord_7657419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7657422 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 4, 1, 5]
def baseStart_7657422 : Nat := 118140960795 + 7657422 * 2 ^ 59
def prefixEnd_7657422 : Nat := 4983230072969 + 3 ^ 40 * 7657422 * 2
def baseEnd_7657422 : Nat := 3931938060312844534909163

theorem tailTrace_7657422 : CollatzResearch.WordTrace tailWord_7657422 prefixEnd_7657422 3931938060312844534909163 := by
  unfold tailWord_7657422
  simp only [CollatzResearch.WordTrace]
  refine ⟨34911140608059419050592815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186192749909650234936495013 34911140608059419050592815)
  ·
    refine ⟨52366710912089128575889223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34911140608059419050592815 52366710912089128575889223)
    ·
      refine ⟨78550066368133692863833835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52366710912089128575889223 78550066368133692863833835)
      ·
        refine ⟨117825099552200539295750753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78550066368133692863833835 117825099552200539295750753)
        ·
          refine ⟨88368824664150404471813065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117825099552200539295750753 88368824664150404471813065)
          ·
            refine ⟨66276618498112803353859799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88368824664150404471813065 66276618498112803353859799)
            ·
              refine ⟨99414927747169205030789699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66276618498112803353859799 99414927747169205030789699)
              ·
                refine ⟨149122391620753807546184549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99414927747169205030789699 149122391620753807546184549)
                ·
                  refine ⟨27960448428891338914909603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149122391620753807546184549 27960448428891338914909603)
                  ·
                    refine ⟨41940672643337008372364405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27960448428891338914909603 41940672643337008372364405)
                    ·
                      refine ⟨3931938060312844534909163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41940672643337008372364405 3931938060312844534909163)
                      ·
                        rfl

theorem cell23_7657422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_7657422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7657422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7657422 prefixEnd_7657422 := by exact prefixLift 7657422
  have htrace : WordTrace (prefixWord ++ tailWord_7657422) baseStart_7657422 baseEnd_7657422 := by
    simpa [prefixWord, tailWord_7657422, baseEnd_7657422] using wordTrace_append hprefix tailTrace_7657422
  have hstable : (prefixWord ++ tailWord_7657422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7657422).length < 2 ^ (prefixWord ++ tailWord_7657422).sum := by decide
  have hdescent : baseEnd_7657422 < baseStart_7657422 := by decide
  rcases family_descends (prefixWord ++ tailWord_7657422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7657452 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 3]
def baseStart_7657452 : Nat := 118140960795 + 7657452 * 2 ^ 59
def prefixEnd_7657452 : Nat := 4983230072969 + 3 ^ 40 * 7657452 * 2
def baseEnd_7657452 : Nat := 3931953464732479417534025

theorem tailTrace_7657452 : CollatzResearch.WordTrace tailWord_7657452 prefixEnd_7657452 3931953464732479417534025 := by
  unfold tailWord_7657452
  simp only [CollatzResearch.WordTrace]
  refine ⟨139645109527183333764167305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186193479369577778352223073 139645109527183333764167305)
  ·
    refine ⟨104733832145387500323125479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139645109527183333764167305 104733832145387500323125479)
    ·
      refine ⟨157100748218081250484688219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104733832145387500323125479 157100748218081250484688219)
      ·
        refine ⟨235651122327121875727032329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157100748218081250484688219 235651122327121875727032329)
        ·
          refine ⟨176738341745341406795274247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235651122327121875727032329 176738341745341406795274247)
          ·
            refine ⟨265107512618012110192911371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176738341745341406795274247 265107512618012110192911371)
            ·
              refine ⟨397661268927018165289367057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265107512618012110192911371 397661268927018165289367057)
              ·
                refine ⟨298245951695263623967025293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 397661268927018165289367057 298245951695263623967025293)
                ·
                  refine ⟨111842231885723858987634485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 298245951695263623967025293 111842231885723858987634485)
                  ·
                    refine ⟨10485209239286611780090733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 111842231885723858987634485 10485209239286611780090733)
                    ·
                      refine ⟨3931953464732479417534025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10485209239286611780090733 3931953464732479417534025)
                      ·
                        rfl

theorem cell23_7657452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 3].length) (baseStart_7657452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7657452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7657452 prefixEnd_7657452 := by exact prefixLift 7657452
  have htrace : WordTrace (prefixWord ++ tailWord_7657452) baseStart_7657452 baseEnd_7657452 := by
    simpa [prefixWord, tailWord_7657452, baseEnd_7657452] using wordTrace_append hprefix tailTrace_7657452
  have hstable : (prefixWord ++ tailWord_7657452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7657452).length < 2 ^ (prefixWord ++ tailWord_7657452).sum := by decide
  have hdescent : baseEnd_7657452 < baseStart_7657452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7657452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7657470 : List Nat := [4, 2, 2, 2, 1, 1, 2, 3, 2, 2, 2]
def baseStart_7657470 : Nat := 118140960795 + 7657470 * 2 ^ 59
def prefixEnd_7657470 : Nat := 4983230072969 + 3 ^ 40 * 7657470 * 2
def baseEnd_7657470 : Nat := 3931962707384260347108943

theorem tailTrace_7657470 : CollatzResearch.WordTrace tailWord_7657470 prefixEnd_7657470 3931962707384260347108943 := by
  unfold tailWord_7657470
  simp only [CollatzResearch.WordTrace]
  refine ⟨34911359446037682075311233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186193917045534304401659909 34911359446037682075311233)
  ·
    refine ⟨26183519584528261556483425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34911359446037682075311233 26183519584528261556483425)
    ·
      refine ⟨19637639688396196167362569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26183519584528261556483425 19637639688396196167362569)
      ·
        refine ⟨14728229766297147125521927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19637639688396196167362569 14728229766297147125521927)
        ·
          refine ⟨22092344649445720688282891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14728229766297147125521927 22092344649445720688282891)
          ·
            refine ⟨33138516974168581032424337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22092344649445720688282891 33138516974168581032424337)
            ·
              refine ⟨24853887730626435774318253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33138516974168581032424337 24853887730626435774318253)
              ·
                refine ⟨9320207898984913415369345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24853887730626435774318253 9320207898984913415369345)
                ·
                  refine ⟨6990155924238685061527009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9320207898984913415369345 6990155924238685061527009)
                  ·
                    refine ⟨5242616943179013796145257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6990155924238685061527009 5242616943179013796145257)
                    ·
                      refine ⟨3931962707384260347108943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5242616943179013796145257 3931962707384260347108943)
                      ·
                        rfl

theorem cell23_7657470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_7657470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7657470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7657470 prefixEnd_7657470 := by exact prefixLift 7657470
  have htrace : WordTrace (prefixWord ++ tailWord_7657470) baseStart_7657470 baseEnd_7657470 := by
    simpa [prefixWord, tailWord_7657470, baseEnd_7657470] using wordTrace_append hprefix tailTrace_7657470
  have hstable : (prefixWord ++ tailWord_7657470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7657470).length < 2 ^ (prefixWord ++ tailWord_7657470).sum := by decide
  have hdescent : baseEnd_7657470 < baseStart_7657470 := by decide
  rcases family_descends (prefixWord ++ tailWord_7657470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7657476 : List Nat := [2, 3, 2, 4, 1, 1, 1, 2, 7]
def baseStart_7657476 : Nat := 118140960795 + 7657476 * 2 ^ 59
def prefixEnd_7657476 : Nat := 4983230072969 + 3 ^ 40 * 7657476 * 2
def baseEnd_7657476 : Nat := 436885087585354147070435

theorem tailTrace_7657476 : CollatzResearch.WordTrace tailWord_7657476 prefixEnd_7657476 436885087585354147070435 := by
  unfold tailWord_7657476
  simp only [CollatzResearch.WordTrace]
  refine ⟨139645547203139859813604141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186194062937519813084805521 139645547203139859813604141)
  ·
    refine ⟨52367080201177447430101553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139645547203139859813604141 52367080201177447430101553)
    ·
      refine ⟨39275310150883085572576165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52367080201177447430101553 39275310150883085572576165)
      ·
        refine ⟨7364120653290578544858031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39275310150883085572576165 7364120653290578544858031)
        ·
          refine ⟨11046180979935867817287047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7364120653290578544858031 11046180979935867817287047)
          ·
            refine ⟨16569271469903801725930571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11046180979935867817287047 16569271469903801725930571)
            ·
              refine ⟨24853907204855702588895857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16569271469903801725930571 24853907204855702588895857)
              ·
                refine ⟨18640430403641776941671893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24853907204855702588895857 18640430403641776941671893)
                ·
                  refine ⟨436885087585354147070435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18640430403641776941671893 436885087585354147070435)
                  ·
                    rfl

theorem cell23_7657476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 7].length) (baseStart_7657476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7657476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7657476 prefixEnd_7657476 := by exact prefixLift 7657476
  have htrace : WordTrace (prefixWord ++ tailWord_7657476) baseStart_7657476 baseEnd_7657476 := by
    simpa [prefixWord, tailWord_7657476, baseEnd_7657476] using wordTrace_append hprefix tailTrace_7657476
  have hstable : (prefixWord ++ tailWord_7657476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7657476).length < 2 ^ (prefixWord ++ tailWord_7657476).sum := by decide
  have hdescent : baseEnd_7657476 < baseStart_7657476 := by decide
  rcases family_descends (prefixWord ++ tailWord_7657476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7657549 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 10]
def baseStart_7657549 : Nat := 118140960795 + 7657549 * 2 ^ 59
def prefixEnd_7657549 : Nat := 4983230072969 + 3 ^ 40 * 7657549 * 2
def baseEnd_7657549 : Nat := 436889252483996170891231

theorem tailTrace_7657549 : CollatzResearch.WordTrace tailWord_7657549 prefixEnd_7657549 436889252483996170891231 := by
  unfold tailWord_7657549
  simp only [CollatzResearch.WordTrace]
  refine ⟨279293756935015253094615701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186195837956676835396410467 279293756935015253094615701)
  ·
    refine ⟨13091894856328839988810111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 279293756935015253094615701 13091894856328839988810111)
    ·
      refine ⟨19637842284493259983215167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13091894856328839988810111 19637842284493259983215167)
      ·
        refine ⟨29456763426739889974822751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19637842284493259983215167 29456763426739889974822751)
        ·
          refine ⟨44185145140109834962234127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29456763426739889974822751 44185145140109834962234127)
          ·
            refine ⟨66277717710164752443351191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44185145140109834962234127 66277717710164752443351191)
            ·
              refine ⟨99416576565247128665026787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66277717710164752443351191 99416576565247128665026787)
              ·
                refine ⟨149124864847870692997540181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99416576565247128665026787 149124864847870692997540181)
                ·
                  refine ⟨436889252483996170891231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 149124864847870692997540181 436889252483996170891231)
                  ·
                    rfl

theorem cell23_7657549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_7657549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7657549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7657549 prefixEnd_7657549 := by exact prefixLift 7657549
  have htrace : WordTrace (prefixWord ++ tailWord_7657549) baseStart_7657549 baseEnd_7657549 := by
    simpa [prefixWord, tailWord_7657549, baseEnd_7657549] using wordTrace_append hprefix tailTrace_7657549
  have hstable : (prefixWord ++ tailWord_7657549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7657549).length < 2 ^ (prefixWord ++ tailWord_7657549).sum := by decide
  have hdescent : baseEnd_7657549 < baseStart_7657549 := by decide
  rcases family_descends (prefixWord ++ tailWord_7657549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7657570 : List Nat := [3, 3, 2, 2, 2, 2, 1, 1, 3, 4]
def baseStart_7657570 : Nat := 118140960795 + 7657570 * 2 ^ 59
def prefixEnd_7657570 : Nat := 4983230072969 + 3 ^ 40 * 7657570 * 2
def baseEnd_7657570 : Nat := 1310671351816569985286161

theorem tailTrace_7657570 : CollatzResearch.WordTrace tailWord_7657570 prefixEnd_7657570 1310671351816569985286161 := by
  unfold tailWord_7657570
  simp only [CollatzResearch.WordTrace]
  refine ⟨69823630716984793420282541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186196348578626115787420109 69823630716984793420282541)
  ·
    refine ⟨26183861518869297532605953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69823630716984793420282541 26183861518869297532605953)
    ·
      refine ⟨19637896139151973149454465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26183861518869297532605953 19637896139151973149454465)
      ·
        refine ⟨14728422104363979862090849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19637896139151973149454465 14728422104363979862090849)
        ·
          refine ⟨11046316578272984896568137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14728422104363979862090849 11046316578272984896568137)
          ·
            refine ⟨8284737433704738672426103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11046316578272984896568137 8284737433704738672426103)
            ·
              refine ⟨12427106150557108008639155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8284737433704738672426103 12427106150557108008639155)
              ·
                refine ⟨18640659225835662012958733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12427106150557108008639155 18640659225835662012958733)
                ·
                  refine ⟨6990247209688373254859525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18640659225835662012958733 6990247209688373254859525)
                  ·
                    refine ⟨1310671351816569985286161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6990247209688373254859525 1310671351816569985286161)
                    ·
                      rfl

theorem cell23_7657570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_7657570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7657570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7657570 prefixEnd_7657570 := by exact prefixLift 7657570
  have htrace : WordTrace (prefixWord ++ tailWord_7657570) baseStart_7657570 baseEnd_7657570 := by
    simpa [prefixWord, tailWord_7657570, baseEnd_7657570] using wordTrace_append hprefix tailTrace_7657570
  have hstable : (prefixWord ++ tailWord_7657570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7657570).length < 2 ^ (prefixWord ++ tailWord_7657570).sum := by decide
  have hdescent : baseEnd_7657570 < baseStart_7657570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7657570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7657596 : List Nat := [2, 2, 2, 1, 1, 4, 3, 2, 1, 5]
def baseStart_7657596 : Nat := 118140960795 + 7657596 * 2 ^ 59
def prefixEnd_7657596 : Nat := 4983230072969 + 3 ^ 40 * 7657596 * 2
def baseEnd_7657596 : Nat := 1310675801982242284711121

theorem tailTrace_7657596 : CollatzResearch.WordTrace tailWord_7657596 prefixEnd_7657596 1310675801982242284711121 := by
  unfold tailWord_7657596
  simp only [CollatzResearch.WordTrace]
  refine ⟨139647735582922490060788321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186196980777229986747717761 139647735582922490060788321)
  ·
    refine ⟨104735801687191867545591241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139647735582922490060788321 104735801687191867545591241)
    ·
      refine ⟨78551851265393900659193431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104735801687191867545591241 78551851265393900659193431)
      ·
        refine ⟨117827776898090850988790147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78551851265393900659193431 117827776898090850988790147)
        ·
          refine ⟨176741665347136276483185221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117827776898090850988790147 176741665347136276483185221)
          ·
            refine ⟨33139062252588051840597229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176741665347136276483185221 33139062252588051840597229)
            ·
              refine ⟨12427148344720519440223961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33139062252588051840597229 12427148344720519440223961)
              ·
                refine ⟨9320361258540389580167971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12427148344720519440223961 9320361258540389580167971)
                ·
                  refine ⟨13980541887810584370251957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9320361258540389580167971 13980541887810584370251957)
                  ·
                    refine ⟨1310675801982242284711121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13980541887810584370251957 1310675801982242284711121)
                    ·
                      rfl

theorem cell23_7657596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 2, 1, 5].length) (baseStart_7657596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7657596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7657596 prefixEnd_7657596 := by exact prefixLift 7657596
  have htrace : WordTrace (prefixWord ++ tailWord_7657596) baseStart_7657596 baseEnd_7657596 := by
    simpa [prefixWord, tailWord_7657596, baseEnd_7657596] using wordTrace_append hprefix tailTrace_7657596
  have hstable : (prefixWord ++ tailWord_7657596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7657596).length < 2 ^ (prefixWord ++ tailWord_7657596).sum := by decide
  have hdescent : baseEnd_7657596 < baseStart_7657596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7657596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7657603 : List Nat := [1, 1, 1, 3, 3, 4, 2, 1, 2, 3, 2]
def baseStart_7657603 : Nat := 118140960795 + 7657603 * 2 ^ 59
def prefixEnd_7657603 : Nat := 4983230072969 + 3 ^ 40 * 7657603 * 2
def baseEnd_7657603 : Nat := 3932031000311308326745831

theorem tailTrace_7657603 : CollatzResearch.WordTrace tailWord_7657603 prefixEnd_7657603 3932031000311308326745831 := by
  unfold tailWord_7657603
  simp only [CollatzResearch.WordTrace]
  refine ⟨279295726476819620317081463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186197150984546413544720975 279295726476819620317081463)
  ·
    refine ⟨418943589715229430475622195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279295726476819620317081463 418943589715229430475622195)
    ·
      refine ⟨628415384572844145713433293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418943589715229430475622195 628415384572844145713433293)
      ·
        refine ⟨235655769214816554642537485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 628415384572844145713433293 235655769214816554642537485)
        ·
          refine ⟨88370913455556207990951557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235655769214816554642537485 88370913455556207990951557)
          ·
            refine ⟨16569546272916788998303417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88370913455556207990951557 16569546272916788998303417)
            ·
              refine ⟨12427159704687591748727563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16569546272916788998303417 12427159704687591748727563)
              ·
                refine ⟨18640739557031387623091345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12427159704687591748727563 18640739557031387623091345)
                ·
                  refine ⟨13980554667773540717318509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18640739557031387623091345 13980554667773540717318509)
                  ·
                    refine ⟨5242708000415077768994441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13980554667773540717318509 5242708000415077768994441)
                    ·
                      refine ⟨3932031000311308326745831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5242708000415077768994441 3932031000311308326745831)
                      ·
                        rfl

theorem cell23_7657603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 2, 3, 2].length) (baseStart_7657603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7657603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7657603 prefixEnd_7657603 := by exact prefixLift 7657603
  have htrace : WordTrace (prefixWord ++ tailWord_7657603) baseStart_7657603 baseEnd_7657603 := by
    simpa [prefixWord, tailWord_7657603, baseEnd_7657603] using wordTrace_append hprefix tailTrace_7657603
  have hstable : (prefixWord ++ tailWord_7657603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7657603).length < 2 ^ (prefixWord ++ tailWord_7657603).sum := by decide
  have hdescent : baseEnd_7657603 < baseStart_7657603 := by decide
  rcases family_descends (prefixWord ++ tailWord_7657603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7657609 : List Nat := [1, 2, 1, 1, 4, 2, 3, 2, 1, 6]
def baseStart_7657609 : Nat := 118140960795 + 7657609 * 2 ^ 59
def prefixEnd_7657609 : Nat := 4983230072969 + 3 ^ 40 * 7657609 * 2
def baseEnd_7657609 : Nat := 1310678027065078434423601

theorem tailTrace_7657609 : CollatzResearch.WordTrace tailWord_7657609 prefixEnd_7657609 1310678027065078434423601 := by
  unfold tailWord_7657609
  simp only [CollatzResearch.WordTrace]
  refine ⟨279295945314797883341799881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186197296876531922227866587 279295945314797883341799881)
  ·
    refine ⟨209471958986098412506349911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279295945314797883341799881 209471958986098412506349911)
    ·
      refine ⟨314207938479147618759524867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209471958986098412506349911 314207938479147618759524867)
      ·
        refine ⟨471311907718721428139287301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314207938479147618759524867 471311907718721428139287301)
        ·
          refine ⟨88370982697260267776116369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 471311907718721428139287301 88370982697260267776116369)
          ·
            refine ⟨66278237022945200832087277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88370982697260267776116369 66278237022945200832087277)
            ·
              refine ⟨24854338883604450312032729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66278237022945200832087277 24854338883604450312032729)
              ·
                refine ⟨18640754162703337734024547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24854338883604450312032729 18640754162703337734024547)
                ·
                  refine ⟨27961131244055006601036821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18640754162703337734024547 27961131244055006601036821)
                  ·
                    refine ⟨1310678027065078434423601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27961131244055006601036821 1310678027065078434423601)
                    ·
                      rfl

theorem cell23_7657609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 6].length) (baseStart_7657609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7657609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7657609 prefixEnd_7657609 := by exact prefixLift 7657609
  have htrace : WordTrace (prefixWord ++ tailWord_7657609) baseStart_7657609 baseEnd_7657609 := by
    simpa [prefixWord, tailWord_7657609, baseEnd_7657609] using wordTrace_append hprefix tailTrace_7657609
  have hstable : (prefixWord ++ tailWord_7657609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7657609).length < 2 ^ (prefixWord ++ tailWord_7657609).sum := by decide
  have hdescent : baseEnd_7657609 < baseStart_7657609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7657609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7657689 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 1, 5, 4]
def baseStart_7657689 : Nat := 118140960795 + 7657689 * 2 ^ 59
def prefixEnd_7657689 : Nat := 4983230072969 + 3 ^ 40 * 7657689 * 2
def baseEnd_7657689 : Nat := 3932075159647594990270435

theorem tailTrace_7657689 : CollatzResearch.WordTrace tailWord_7657689 prefixEnd_7657689 3932075159647594990270435 := by
  unfold tailWord_7657689
  simp only [CollatzResearch.WordTrace]
  refine ⟨279298863154508057004712121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186199242103005371336474747 279298863154508057004712121)
  ·
    refine ⟨209474147365881042753534091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279298863154508057004712121 209474147365881042753534091)
    ·
      refine ⟨314211221048821564130301137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209474147365881042753534091 314211221048821564130301137)
      ·
        refine ⟨235658415786616173097725853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314211221048821564130301137 235658415786616173097725853)
        ·
          refine ⟨88371905919981064911647195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235658415786616173097725853 88371905919981064911647195)
          ·
            refine ⟨132557858879971597367470793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88371905919981064911647195 132557858879971597367470793)
            ·
              refine ⟨99418394159978698025603095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132557858879971597367470793 99418394159978698025603095)
              ·
                refine ⟨149127591239968047038404643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99418394159978698025603095 149127591239968047038404643)
                ·
                  refine ⟨223691386859952070557606965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149127591239968047038404643 223691386859952070557606965)
                  ·
                    refine ⟨20971067518120506614775653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 223691386859952070557606965 20971067518120506614775653)
                    ·
                      refine ⟨3932075159647594990270435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20971067518120506614775653 3932075159647594990270435)
                      ·
                        rfl

theorem cell23_7657689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 5, 4].length) (baseStart_7657689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7657689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7657689 prefixEnd_7657689 := by exact prefixLift 7657689
  have htrace : WordTrace (prefixWord ++ tailWord_7657689) baseStart_7657689 baseEnd_7657689 := by
    simpa [prefixWord, tailWord_7657689, baseEnd_7657689] using wordTrace_append hprefix tailTrace_7657689
  have hstable : (prefixWord ++ tailWord_7657689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7657689).length < 2 ^ (prefixWord ++ tailWord_7657689).sum := by decide
  have hdescent : baseEnd_7657689 < baseStart_7657689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7657689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7657739 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 7]
def baseStart_7657739 : Nat := 118140960795 + 7657739 * 2 ^ 59
def prefixEnd_7657739 : Nat := 4983230072969 + 3 ^ 40 * 7657739 * 2
def baseEnd_7657739 : Nat := 3932100833680319794645205

theorem tailTrace_7657739 : CollatzResearch.WordTrace tailWord_7657739 prefixEnd_7657739 3932100833680319794645205 := by
  unfold tailWord_7657739
  simp only [CollatzResearch.WordTrace]
  refine ⟨279300686804326915544032271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186200457869551277029354847 279300686804326915544032271)
  ·
    refine ⟨418951030206490373316048407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279300686804326915544032271 418951030206490373316048407)
    ·
      refine ⟨628426545309735559974072611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418951030206490373316048407 628426545309735559974072611)
      ·
        refine ⟨942639817964603339961108917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 628426545309735559974072611 942639817964603339961108917)
        ·
          refine ⟨88372482934181563121353961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 942639817964603339961108917 88372482934181563121353961)
          ·
            refine ⟨66279362200636172341015471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88372482934181563121353961 66279362200636172341015471)
            ·
              refine ⟨99419043300954258511523207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66279362200636172341015471 99419043300954258511523207)
              ·
                refine ⟨149128564951431387767284811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99419043300954258511523207 149128564951431387767284811)
                ·
                  refine ⟨223692847427147081650927217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149128564951431387767284811 223692847427147081650927217)
                  ·
                    refine ⟨167769635570360311238195413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 223692847427147081650927217 167769635570360311238195413)
                    ·
                      refine ⟨3932100833680319794645205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 167769635570360311238195413 3932100833680319794645205)
                      ·
                        rfl

theorem cell23_7657739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 7].length) (baseStart_7657739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7657739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7657739 prefixEnd_7657739 := by exact prefixLift 7657739
  have htrace : WordTrace (prefixWord ++ tailWord_7657739) baseStart_7657739 baseEnd_7657739 := by
    simpa [prefixWord, tailWord_7657739, baseEnd_7657739] using wordTrace_append hprefix tailTrace_7657739
  have hstable : (prefixWord ++ tailWord_7657739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7657739).length < 2 ^ (prefixWord ++ tailWord_7657739).sum := by decide
  have hdescent : baseEnd_7657739 < baseStart_7657739 := by decide
  rcases family_descends (prefixWord ++ tailWord_7657739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7657740 : List Nat := [2, 2, 1, 2, 2, 2, 2, 4, 2, 2, 2]
def baseStart_7657740 : Nat := 118140960795 + 7657740 * 2 ^ 59
def prefixEnd_7657740 : Nat := 4983230072969 + 3 ^ 40 * 7657740 * 2
def baseEnd_7657740 : Nat := 3932101347160974290732701

theorem tailTrace_7657740 : CollatzResearch.WordTrace tailWord_7657740 prefixEnd_7657740 3932101347160974290732701 := by
  unfold tailWord_7657740
  simp only [CollatzResearch.WordTrace]
  refine ⟨139650361638661646357409337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186200482184882195143212449 139650361638661646357409337)
  ·
    refine ⟨104737771228996234768057003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139650361638661646357409337 104737771228996234768057003)
    ·
      refine ⟨157106656843494352152085505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104737771228996234768057003 157106656843494352152085505)
      ·
        refine ⟨117829992632620764114064129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157106656843494352152085505 117829992632620764114064129)
        ·
          refine ⟨88372494474465573085548097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117829992632620764114064129 88372494474465573085548097)
          ·
            refine ⟨66279370855849179814161073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88372494474465573085548097 66279370855849179814161073)
            ·
              refine ⟨49709528141886884860620805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66279370855849179814161073 49709528141886884860620805)
              ·
                refine ⟨9320536526603790911366401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49709528141886884860620805 9320536526603790911366401)
                ·
                  refine ⟨6990402394952843183524801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9320536526603790911366401 6990402394952843183524801)
                  ·
                    refine ⟨5242801796214632387643601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6990402394952843183524801 5242801796214632387643601)
                    ·
                      refine ⟨3932101347160974290732701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5242801796214632387643601 3932101347160974290732701)
                      ·
                        rfl

theorem cell23_7657740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 4, 2, 2, 2].length) (baseStart_7657740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7657740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7657740 prefixEnd_7657740 := by exact prefixLift 7657740
  have htrace : WordTrace (prefixWord ++ tailWord_7657740) baseStart_7657740 baseEnd_7657740 := by
    simpa [prefixWord, tailWord_7657740, baseEnd_7657740] using wordTrace_append hprefix tailTrace_7657740
  have hstable : (prefixWord ++ tailWord_7657740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7657740).length < 2 ^ (prefixWord ++ tailWord_7657740).sum := by decide
  have hdescent : baseEnd_7657740 < baseStart_7657740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7657740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7657756 : List Nat := [2, 2, 3, 1, 1, 1, 1, 3, 1, 5, 3]
def baseStart_7657756 : Nat := 118140960795 + 7657756 * 2 ^ 59
def prefixEnd_7657756 : Nat := 4983230072969 + 3 ^ 40 * 7657756 * 2
def baseEnd_7657756 : Nat := 3932109562851446228132627

theorem tailTrace_7657756 : CollatzResearch.WordTrace tailWord_7657756 prefixEnd_7657756 3932109562851446228132627 := by
  unfold tailWord_7657756
  simp only [CollatzResearch.WordTrace]
  refine ⟨139650653422632663723700561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186200871230176884964934081 139650653422632663723700561)
  ·
    refine ⟨104737990066974497792775421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139650653422632663723700561 104737990066974497792775421)
    ·
      refine ⟨39276746275115436672290783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104737990066974497792775421 39276746275115436672290783)
      ·
        refine ⟨58915119412673155008436175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39276746275115436672290783 58915119412673155008436175)
        ·
          refine ⟨88372679119009732512654263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58915119412673155008436175 88372679119009732512654263)
          ·
            refine ⟨132559018678514598768981395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88372679119009732512654263 132559018678514598768981395)
            ·
              refine ⟨198838528017771898153472093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132559018678514598768981395 198838528017771898153472093)
              ·
                refine ⟨74564448006664461807552035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198838528017771898153472093 74564448006664461807552035)
                ·
                  refine ⟨111846672009996692711328053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74564448006664461807552035 111846672009996692711328053)
                  ·
                    refine ⟨10485625500937189941687005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 111846672009996692711328053 10485625500937189941687005)
                    ·
                      refine ⟨3932109562851446228132627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10485625500937189941687005 3932109562851446228132627)
                      ·
                        rfl

theorem cell23_7657756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_7657756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7657756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7657756 prefixEnd_7657756 := by exact prefixLift 7657756
  have htrace : WordTrace (prefixWord ++ tailWord_7657756) baseStart_7657756 baseEnd_7657756 := by
    simpa [prefixWord, tailWord_7657756, baseEnd_7657756] using wordTrace_append hprefix tailTrace_7657756
  have hstable : (prefixWord ++ tailWord_7657756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7657756).length < 2 ^ (prefixWord ++ tailWord_7657756).sum := by decide
  have hdescent : baseEnd_7657756 < baseStart_7657756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7657756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7657786 : List Nat := [3, 1, 1, 1, 4, 2, 1, 2, 1, 2, 5]
def baseStart_7657786 : Nat := 118140960795 + 7657786 * 2 ^ 59
def prefixEnd_7657786 : Nat := 4983230072969 + 3 ^ 40 * 7657786 * 2
def baseEnd_7657786 : Nat := 3932124967271081110757489

theorem tailTrace_7657786 : CollatzResearch.WordTrace tailWord_7657786 prefixEnd_7657786 3932124967271081110757489 := by
  unfold tailWord_7657786
  simp only [CollatzResearch.WordTrace]
  refine ⟨69825600258789160642748303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186201600690104428380662141 69825600258789160642748303)
  ·
    refine ⟨104738400388183740964122455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69825600258789160642748303 104738400388183740964122455)
    ·
      refine ⟨157107600582275611446183683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104738400388183740964122455 157107600582275611446183683)
      ·
        refine ⟨235661400873413417169275525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157107600582275611446183683 235661400873413417169275525)
        ·
          refine ⟨44186512663765015719239161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 235661400873413417169275525 44186512663765015719239161)
          ·
            refine ⟨33139884497823761789429371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44186512663765015719239161 33139884497823761789429371)
            ·
              refine ⟨49709826746735642684144057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33139884497823761789429371 49709826746735642684144057)
              ·
                refine ⟨37282370060051732013108043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49709826746735642684144057 37282370060051732013108043)
                ·
                  refine ⟨55923555090077598019662065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37282370060051732013108043 55923555090077598019662065)
                  ·
                    refine ⟨41942666317558198514746549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55923555090077598019662065 41942666317558198514746549)
                    ·
                      refine ⟨3932124967271081110757489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41942666317558198514746549 3932124967271081110757489)
                      ·
                        rfl

theorem cell23_7657786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 1, 2, 5].length) (baseStart_7657786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7657786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7657786 prefixEnd_7657786 := by exact prefixLift 7657786
  have htrace : WordTrace (prefixWord ++ tailWord_7657786) baseStart_7657786 baseEnd_7657786 := by
    simpa [prefixWord, tailWord_7657786, baseEnd_7657786] using wordTrace_append hprefix tailTrace_7657786
  have hstable : (prefixWord ++ tailWord_7657786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7657786).length < 2 ^ (prefixWord ++ tailWord_7657786).sum := by decide
  have hdescent : baseEnd_7657786 < baseStart_7657786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7657786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7657840 : List Nat := [2, 1, 1, 1, 4, 3, 1, 5, 1, 4]
def baseStart_7657840 : Nat := 118140960795 + 7657840 * 2 ^ 59
def prefixEnd_7657840 : Nat := 4983230072969 + 3 ^ 40 * 7657840 * 2
def baseEnd_7657840 : Nat := 1310717565075474633160747

theorem tailTrace_7657840 : CollatzResearch.WordTrace tailWord_7657840 prefixEnd_7657840 1310717565075474633160747 := by
  unfold tailWord_7657840
  simp only [CollatzResearch.WordTrace]
  refine ⟨139652185288480504896729487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186202913717974006528972649 139652185288480504896729487)
  ·
    refine ⟨209478277932720757345094231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139652185288480504896729487 209478277932720757345094231)
    ·
      refine ⟨314217416899081136017641347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209478277932720757345094231 314217416899081136017641347)
      ·
        refine ⟨471326125348621704026462021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314217416899081136017641347 471326125348621704026462021)
        ·
          refine ⟨88373648502866569504961629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 471326125348621704026462021 88373648502866569504961629)
          ·
            refine ⟨33140118188574963564360611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88373648502866569504961629 33140118188574963564360611)
            ·
              refine ⟨49710177282862445346540917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33140118188574963564360611 49710177282862445346540917)
              ·
                refine ⟨4660329120268354251238211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49710177282862445346540917 4660329120268354251238211)
                ·
                  refine ⟨6990493680402531376857317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4660329120268354251238211 6990493680402531376857317)
                  ·
                    refine ⟨1310717565075474633160747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6990493680402531376857317 1310717565075474633160747)
                    ·
                      rfl

theorem cell23_7657840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 5, 1, 4].length) (baseStart_7657840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7657840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7657840 prefixEnd_7657840 := by exact prefixLift 7657840
  have htrace : WordTrace (prefixWord ++ tailWord_7657840) baseStart_7657840 baseEnd_7657840 := by
    simpa [prefixWord, tailWord_7657840, baseEnd_7657840] using wordTrace_append hprefix tailTrace_7657840
  have hstable : (prefixWord ++ tailWord_7657840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7657840).length < 2 ^ (prefixWord ++ tailWord_7657840).sum := by decide
  have hdescent : baseEnd_7657840 < baseStart_7657840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7657840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7657853 : List Nat := [1, 4, 1, 1, 2, 3, 3, 2, 6]
def baseStart_7657853 : Nat := 118140960795 + 7657853 * 2 ^ 59
def prefixEnd_7657853 : Nat := 4983230072969 + 3 ^ 40 * 7657853 * 2
def baseEnd_7657853 : Nat := 436906596719436927624409

theorem tailTrace_7657853 : CollatzResearch.WordTrace tailWord_7657853 prefixEnd_7657853 436906596719436927624409 := by
  unfold tailWord_7657853
  simp only [CollatzResearch.WordTrace]
  refine ⟨279304844725913913013682213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186203229817275942009121475 279304844725913913013682213)
  ·
    refine ⟨52369658386108858690065415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 279304844725913913013682213 52369658386108858690065415)
    ·
      refine ⟨78554487579163288035098123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52369658386108858690065415 78554487579163288035098123)
      ·
        refine ⟨117831731368744932052647185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78554487579163288035098123 117831731368744932052647185)
        ·
          refine ⟨88373798526558699039485389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117831731368744932052647185 88373798526558699039485389)
          ·
            refine ⟨33140174447459512139807021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88373798526558699039485389 33140174447459512139807021)
            ·
              refine ⟨12427565417797317052427633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33140174447459512139807021 12427565417797317052427633)
              ·
                refine ⟨9320674063347987789320725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12427565417797317052427633 9320674063347987789320725)
                ·
                  refine ⟨436906596719436927624409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9320674063347987789320725 436906596719436927624409)
                  ·
                    rfl

theorem cell23_7657853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 2, 6].length) (baseStart_7657853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7657853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7657853 prefixEnd_7657853 := by exact prefixLift 7657853
  have htrace : WordTrace (prefixWord ++ tailWord_7657853) baseStart_7657853 baseEnd_7657853 := by
    simpa [prefixWord, tailWord_7657853, baseEnd_7657853] using wordTrace_append hprefix tailTrace_7657853
  have hstable : (prefixWord ++ tailWord_7657853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7657853).length < 2 ^ (prefixWord ++ tailWord_7657853).sum := by decide
  have hdescent : baseEnd_7657853 < baseStart_7657853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7657853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7657857 : List Nat := [1, 2, 4, 3, 1, 1, 2, 4, 1, 4]
def baseStart_7657857 : Nat := 118140960795 + 7657857 * 2 ^ 59
def prefixEnd_7657857 : Nat := 4983230072969 + 3 ^ 40 * 7657857 * 2
def baseEnd_7657857 : Nat := 1310720474799183444323221

theorem tailTrace_7657857 : CollatzResearch.WordTrace tailWord_7657857 prefixEnd_7657857 1310720474799183444323221 := by
  unfold tailWord_7657857
  simp only [CollatzResearch.WordTrace]
  refine ⟨279304990617899421696827825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186203327078599614464551883 279304990617899421696827825)
  ·
    refine ⟨209478742963424566272620869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279304990617899421696827825 209478742963424566272620869)
    ·
      refine ⟨39277264305642106176116413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209478742963424566272620869 39277264305642106176116413)
      ·
        refine ⟨14728974114615789816043655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39277264305642106176116413 14728974114615789816043655)
        ·
          refine ⟨22093461171923684724065483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14728974114615789816043655 22093461171923684724065483)
          ·
            refine ⟨33140191757885527086098225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22093461171923684724065483 33140191757885527086098225)
            ·
              refine ⟨24855143818414145314573669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33140191757885527086098225 24855143818414145314573669)
              ·
                refine ⟨4660339465952652246482563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24855143818414145314573669 4660339465952652246482563)
                ·
                  refine ⟨6990509198928978369723845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4660339465952652246482563 6990509198928978369723845)
                  ·
                    refine ⟨1310720474799183444323221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6990509198928978369723845 1310720474799183444323221)
                    ·
                      rfl

theorem cell23_7657857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_7657857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7657857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7657857 prefixEnd_7657857 := by exact prefixLift 7657857
  have htrace : WordTrace (prefixWord ++ tailWord_7657857) baseStart_7657857 baseEnd_7657857 := by
    simpa [prefixWord, tailWord_7657857, baseEnd_7657857] using wordTrace_append hprefix tailTrace_7657857
  have hstable : (prefixWord ++ tailWord_7657857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7657857).length < 2 ^ (prefixWord ++ tailWord_7657857).sum := by decide
  have hdescent : baseEnd_7657857 < baseStart_7657857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7657857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7657890 : List Nat := [3, 3, 1, 2, 1, 1, 1, 3, 1, 5, 2]
def baseStart_7657890 : Nat := 118140960795 + 7657890 * 2 ^ 59
def prefixEnd_7657890 : Nat := 4983230072969 + 3 ^ 40 * 7657890 * 2
def baseEnd_7657890 : Nat := 3932178369259148703857011

theorem tailTrace_7657890 : CollatzResearch.WordTrace tailWord_7657890 prefixEnd_7657890 3932178369259148703857011 := by
  unfold tailWord_7657890
  simp only [CollatzResearch.WordTrace]
  refine ⟨69826548556694967083194781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186204129484519912221852749 69826548556694967083194781)
  ·
    refine ⟨26184955708760612656198043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69826548556694967083194781 26184955708760612656198043)
    ·
      refine ⟨39277433563140918984297065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26184955708760612656198043 39277433563140918984297065)
      ·
        refine ⟨29458075172355689238222799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39277433563140918984297065 29458075172355689238222799)
        ·
          refine ⟨44187112758533533857334199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29458075172355689238222799 44187112758533533857334199)
          ·
            refine ⟨66280669137800300786001299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44187112758533533857334199 66280669137800300786001299)
            ·
              refine ⟨99421003706700451179001949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66280669137800300786001299 99421003706700451179001949)
              ·
                refine ⟨37282876390012669192125731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99421003706700451179001949 37282876390012669192125731)
                ·
                  refine ⟨55924314585019003788188597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37282876390012669192125731 55924314585019003788188597)
                  ·
                    refine ⟨5242904492345531605142681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55924314585019003788188597 5242904492345531605142681)
                    ·
                      refine ⟨3932178369259148703857011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5242904492345531605142681 3932178369259148703857011)
                      ·
                        rfl

theorem cell23_7657890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_7657890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7657890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7657890 prefixEnd_7657890 := by exact prefixLift 7657890
  have htrace : WordTrace (prefixWord ++ tailWord_7657890) baseStart_7657890 baseEnd_7657890 := by
    simpa [prefixWord, tailWord_7657890, baseEnd_7657890] using wordTrace_append hprefix tailTrace_7657890
  have hstable : (prefixWord ++ tailWord_7657890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7657890).length < 2 ^ (prefixWord ++ tailWord_7657890).sum := by decide
  have hdescent : baseEnd_7657890 < baseStart_7657890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7657890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7657908 : List Nat := [2, 5, 2, 2, 1, 1, 3, 2, 1, 4]
def baseStart_7657908 : Nat := 118140960795 + 7657908 * 2 ^ 59
def prefixEnd_7657908 : Nat := 4983230072969 + 3 ^ 40 * 7657908 * 2
def baseEnd_7657908 : Nat := 1310729203970309877810643

theorem tailTrace_7657908 : CollatzResearch.WordTrace tailWord_7657908 prefixEnd_7657908 1310729203970309877810643 := by
  unfold tailWord_7657908
  simp only [CollatzResearch.WordTrace]
  refine ⟨139653425370357328703467189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186204567160476438271289585 139653425370357328703467189)
  ·
    refine ⟨13092508628470999565950049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139653425370357328703467189 13092508628470999565950049)
    ·
      refine ⟨9819381471353249674462537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13092508628470999565950049 9819381471353249674462537)
      ·
        refine ⟨7364536103514937255846903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9819381471353249674462537 7364536103514937255846903)
        ·
          refine ⟨11046804155272405883770355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7364536103514937255846903 11046804155272405883770355)
          ·
            refine ⟨16570206232908608825655533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11046804155272405883770355 16570206232908608825655533)
            ·
              refine ⟨6213827337340728309620825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16570206232908608825655533 6213827337340728309620825)
              ·
                refine ⟨4660370503005546232215619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6213827337340728309620825 4660370503005546232215619)
                ·
                  refine ⟨6990555754508319348323429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4660370503005546232215619 6990555754508319348323429)
                  ·
                    refine ⟨1310729203970309877810643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6990555754508319348323429 1310729203970309877810643)
                    ·
                      rfl

theorem cell23_7657908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_7657908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7657908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7657908 prefixEnd_7657908 := by exact prefixLift 7657908
  have htrace : WordTrace (prefixWord ++ tailWord_7657908) baseStart_7657908 baseEnd_7657908 := by
    simpa [prefixWord, tailWord_7657908, baseEnd_7657908] using wordTrace_append hprefix tailTrace_7657908
  have hstable : (prefixWord ++ tailWord_7657908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7657908).length < 2 ^ (prefixWord ++ tailWord_7657908).sum := by decide
  have hdescent : baseEnd_7657908 < baseStart_7657908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7657908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7657921 : List Nat := [1, 2, 7, 1, 1, 2, 2, 1, 6]
def baseStart_7657921 : Nat := 118140960795 + 7657921 * 2 ^ 59
def prefixEnd_7657921 : Nat := 4983230072969 + 3 ^ 40 * 7657921 * 2
def baseEnd_7657921 : Nat := 436910476351048675841041

theorem tailTrace_7657921 : CollatzResearch.WordTrace tailWord_7657921 prefixEnd_7657921 436910476351048675841041 := by
  unfold tailWord_7657921
  simp only [CollatzResearch.WordTrace]
  refine ⟨279307324889667560627157617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186204883259778373751438411 279307324889667560627157617)
  ·
    refine ⟨209480493667250670470368213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279307324889667560627157617 209480493667250670470368213)
    ·
      refine ⟨4909699070326187589149255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 209480493667250670470368213 4909699070326187589149255)
      ·
        refine ⟨7364548605489281383723883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4909699070326187589149255 7364548605489281383723883)
        ·
          refine ⟨11046822908233922075585825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7364548605489281383723883 11046822908233922075585825)
          ·
            refine ⟨8285117181175441556689369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11046822908233922075585825 8285117181175441556689369)
            ·
              refine ⟨6213837885881581167517027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8285117181175441556689369 6213837885881581167517027)
              ·
                refine ⟨9320756828822371751275541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6213837885881581167517027 9320756828822371751275541)
                ·
                  refine ⟨436910476351048675841041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9320756828822371751275541 436910476351048675841041)
                  ·
                    rfl

theorem cell23_7657921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 1, 6].length) (baseStart_7657921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7657921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7657921 prefixEnd_7657921 := by exact prefixLift 7657921
  have htrace : WordTrace (prefixWord ++ tailWord_7657921) baseStart_7657921 baseEnd_7657921 := by
    simpa [prefixWord, tailWord_7657921, baseEnd_7657921] using wordTrace_append hprefix tailTrace_7657921
  have hstable : (prefixWord ++ tailWord_7657921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7657921).length < 2 ^ (prefixWord ++ tailWord_7657921).sum := by decide
  have hdescent : baseEnd_7657921 < baseStart_7657921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7657921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7657923 : List Nat := [1, 1, 1, 3, 1, 1, 3, 4, 3, 2, 3]
def baseStart_7657923 : Nat := 118140960795 + 7657923 * 2 ^ 59
def prefixEnd_7657923 : Nat := 4983230072969 + 3 ^ 40 * 7657923 * 2
def baseEnd_7657923 : Nat := 3932195314120747074744359

theorem tailTrace_7657923 : CollatzResearch.WordTrace tailWord_7657923 prefixEnd_7657923 3932195314120747074744359 := by
  unfold tailWord_7657923
  simp only [CollatzResearch.WordTrace]
  refine ⟨279307397835660314968730423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186204931890440209979153615 279307397835660314968730423)
  ·
    refine ⟨418961096753490472453095635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279307397835660314968730423 418961096753490472453095635)
    ·
      refine ⟨628441645130235708679643453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418961096753490472453095635 628441645130235708679643453)
      ·
        refine ⟨235665616923838390754866295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 628441645130235708679643453 235665616923838390754866295)
        ·
          refine ⟨353498425385757586132299443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235665616923838390754866295 353498425385757586132299443)
          ·
            refine ⟨530247638078636379198449165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353498425385757586132299443 530247638078636379198449165)
            ·
              refine ⟨198842864279488642199418437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 530247638078636379198449165 198842864279488642199418437)
              ·
                refine ⟨37283037052404120412390957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 198842864279488642199418437 37283037052404120412390957)
                ·
                  refine ⟨13981138894651545154646609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37283037052404120412390957 13981138894651545154646609)
                  ·
                    refine ⟨10485854170988658865984957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13981138894651545154646609 10485854170988658865984957)
                    ·
                      refine ⟨3932195314120747074744359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10485854170988658865984957 3932195314120747074744359)
                      ·
                        rfl

theorem cell23_7657923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 2, 3].length) (baseStart_7657923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7657923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7657923 prefixEnd_7657923 := by exact prefixLift 7657923
  have htrace : WordTrace (prefixWord ++ tailWord_7657923) baseStart_7657923 baseEnd_7657923 := by
    simpa [prefixWord, tailWord_7657923, baseEnd_7657923] using wordTrace_append hprefix tailTrace_7657923
  have hstable : (prefixWord ++ tailWord_7657923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7657923).length < 2 ^ (prefixWord ++ tailWord_7657923).sum := by decide
  have hdescent : baseEnd_7657923 < baseStart_7657923 := by decide
  rcases family_descends (prefixWord ++ tailWord_7657923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7657930 : List Nat := [3, 1, 2, 1, 2, 2, 3, 3, 2, 4]
def baseStart_7657930 : Nat := 118140960795 + 7657930 * 2 ^ 59
def prefixEnd_7657930 : Nat := 4983230072969 + 3 ^ 40 * 7657930 * 2
def baseEnd_7657930 : Nat := 1310732969495109515785609

theorem tailTrace_7657930 : CollatzResearch.WordTrace tailWord_7657930 prefixEnd_7657930 1310732969495109515785609 := by
  unfold tailWord_7657930
  simp only [CollatzResearch.WordTrace]
  refine ⟨69826913286658738791058811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186205102097756636776156829 69826913286658738791058811)
  ·
    refine ⟨104740369929988108186588217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69826913286658738791058811 104740369929988108186588217)
    ·
      refine ⟨78555277447491081139941163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104740369929988108186588217 78555277447491081139941163)
      ·
        refine ⟨117832916171236621709911745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78555277447491081139941163 117832916171236621709911745)
        ·
          refine ⟨88374687128427466282433809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117832916171236621709911745 88374687128427466282433809)
          ·
            refine ⟨66281015346320599711825357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88374687128427466282433809 66281015346320599711825357)
            ·
              refine ⟨24855380754870224891934509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66281015346320599711825357 24855380754870224891934509)
              ·
                refine ⟨9320767783076334334475441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24855380754870224891934509 9320767783076334334475441)
                ·
                  refine ⟨6990575837307250750856581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9320767783076334334475441 6990575837307250750856581)
                  ·
                    refine ⟨1310732969495109515785609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6990575837307250750856581 1310732969495109515785609)
                    ·
                      rfl

theorem cell23_7657930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 3, 2, 4].length) (baseStart_7657930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7657930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7657930 prefixEnd_7657930 := by exact prefixLift 7657930
  have htrace : WordTrace (prefixWord ++ tailWord_7657930) baseStart_7657930 baseEnd_7657930 := by
    simpa [prefixWord, tailWord_7657930, baseEnd_7657930] using wordTrace_append hprefix tailTrace_7657930
  have hstable : (prefixWord ++ tailWord_7657930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7657930).length < 2 ^ (prefixWord ++ tailWord_7657930).sum := by decide
  have hdescent : baseEnd_7657930 < baseStart_7657930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7657930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7657957 : List Nat := [1, 3, 1, 5, 2, 2, 1, 1, 1, 1, 5]
def baseStart_7657957 : Nat := 118140960795 + 7657957 * 2 ^ 59
def prefixEnd_7657957 : Nat := 4983230072969 + 3 ^ 40 * 7657957 * 2
def baseEnd_7657957 : Nat := 3932212772462999941719203

theorem tailTrace_7657957 : CollatzResearch.WordTrace tailWord_7657957 prefixEnd_7657957 3932212772462999941719203 := by
  unfold tailWord_7657957
  simp only [CollatzResearch.WordTrace]
  refine ⟨279308637917537138775468125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186205758611691425850312083 279308637917537138775468125)
  ·
    refine ⟨104740739219076427040800547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279308637917537138775468125 104740739219076427040800547)
    ·
      refine ⟨157111108828614640561200821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104740739219076427040800547 157111108828614640561200821)
      ·
        refine ⟨14729166452682622552612577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 157111108828614640561200821 14729166452682622552612577)
        ·
          refine ⟨11046874839511966914459433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14729166452682622552612577 11046874839511966914459433)
          ·
            refine ⟨8285156129633975185844575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11046874839511966914459433 8285156129633975185844575)
            ·
              refine ⟨12427734194450962778766863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8285156129633975185844575 12427734194450962778766863)
              ·
                refine ⟨18641601291676444168150295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12427734194450962778766863 18641601291676444168150295)
                ·
                  refine ⟨27962401937514666252225443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18641601291676444168150295 27962401937514666252225443)
                  ·
                    refine ⟨41943602906271999378338165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27962401937514666252225443 41943602906271999378338165)
                    ·
                      refine ⟨3932212772462999941719203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41943602906271999378338165 3932212772462999941719203)
                      ·
                        rfl

theorem cell23_7657957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_7657957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7657957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7657957 prefixEnd_7657957 := by exact prefixLift 7657957
  have htrace : WordTrace (prefixWord ++ tailWord_7657957) baseStart_7657957 baseEnd_7657957 := by
    simpa [prefixWord, tailWord_7657957, baseEnd_7657957] using wordTrace_append hprefix tailTrace_7657957
  have hstable : (prefixWord ++ tailWord_7657957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7657957).length < 2 ^ (prefixWord ++ tailWord_7657957).sum := by decide
  have hdescent : baseEnd_7657957 < baseStart_7657957 := by decide
  rcases family_descends (prefixWord ++ tailWord_7657957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658033 : List Nat := [1, 2, 2, 3, 1, 1, 3, 3, 7]
def baseStart_7658033 : Nat := 118140960795 + 7658033 * 2 ^ 59
def prefixEnd_7658033 : Nat := 4983230072969 + 3 ^ 40 * 7658033 * 2
def baseEnd_7658033 : Nat := 436916866332526849374317

theorem tailTrace_7658033 : CollatzResearch.WordTrace tailWord_7658033 prefixEnd_7658033 436916866332526849374317 := by
  unfold tailWord_7658033
  simp only [CollatzResearch.WordTrace]
  refine ⟨279311409865261803755234753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186207606576841202503489835 279311409865261803755234753)
  ·
    refine ⟨209483557398946352816426065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279311409865261803755234753 209483557398946352816426065)
    ·
      refine ⟨157112668049209764612319549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209483557398946352816426065 157112668049209764612319549)
      ·
        refine ⟨58917250518453661729619831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157112668049209764612319549 58917250518453661729619831)
        ·
          refine ⟨88375875777680492594429747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58917250518453661729619831 88375875777680492594429747)
          ·
            refine ⟨132563813666520738891644621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88375875777680492594429747 132563813666520738891644621)
            ·
              refine ⟨49711430124945277084366733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132563813666520738891644621 49711430124945277084366733)
              ·
                refine ⟨18641786296854478906637525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49711430124945277084366733 18641786296854478906637525)
                ·
                  refine ⟨436916866332526849374317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18641786296854478906637525 436916866332526849374317)
                  ·
                    rfl

theorem cell23_7658033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 7].length) (baseStart_7658033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658033 prefixEnd_7658033 := by exact prefixLift 7658033
  have htrace : WordTrace (prefixWord ++ tailWord_7658033) baseStart_7658033 baseEnd_7658033 := by
    simpa [prefixWord, tailWord_7658033, baseEnd_7658033] using wordTrace_append hprefix tailTrace_7658033
  have hstable : (prefixWord ++ tailWord_7658033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658033).length < 2 ^ (prefixWord ++ tailWord_7658033).sum := by decide
  have hdescent : baseEnd_7658033 < baseStart_7658033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658043 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 5, 5, 3]
def baseStart_7658043 : Nat := 118140960795 + 7658043 * 2 ^ 59
def prefixEnd_7658043 : Nat := 4983230072969 + 3 ^ 40 * 7658043 * 2
def baseEnd_7658043 : Nat := 3932256931799286605243807

theorem tailTrace_7658043 : CollatzResearch.WordTrace tailWord_7658043 prefixEnd_7658043 3932256931799286605243807 := by
  unfold tailWord_7658043
  simp only [CollatzResearch.WordTrace]
  refine ⟨279311774595225575463098783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186207849730150383642065855 279311774595225575463098783)
  ·
    refine ⟨418967661892838363194648175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279311774595225575463098783 418967661892838363194648175)
    ·
      refine ⟨628451492839257544791972263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418967661892838363194648175 628451492839257544791972263)
      ·
        refine ⟨942677239258886317187958395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 628451492839257544791972263 942677239258886317187958395)
        ·
          refine ⟨1414015858888329475781937593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 942677239258886317187958395 1414015858888329475781937593)
          ·
            refine ⟨1060511894166247106836453195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1414015858888329475781937593 1060511894166247106836453195)
            ·
              refine ⟨1590767841249370660254679793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1060511894166247106836453195 1590767841249370660254679793)
              ·
                refine ⟨1193075880937027995191009845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1590767841249370660254679793 1193075880937027995191009845)
                ·
                  refine ⟨111850863837846374549157173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1193075880937027995191009845 111850863837846374549157173)
                  ·
                    refine ⟨10486018484798097613983485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 111850863837846374549157173 10486018484798097613983485)
                    ·
                      refine ⟨3932256931799286605243807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10486018484798097613983485 3932256931799286605243807)
                      ·
                        rfl

theorem cell23_7658043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 5, 3].length) (baseStart_7658043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658043 prefixEnd_7658043 := by exact prefixLift 7658043
  have htrace : WordTrace (prefixWord ++ tailWord_7658043) baseStart_7658043 baseEnd_7658043 := by
    simpa [prefixWord, tailWord_7658043, baseEnd_7658043] using wordTrace_append hprefix tailTrace_7658043
  have hstable : (prefixWord ++ tailWord_7658043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658043).length < 2 ^ (prefixWord ++ tailWord_7658043).sum := by decide
  have hdescent : baseEnd_7658043 < baseStart_7658043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658044 : List Nat := [2, 2, 2, 2, 3, 3, 1, 1, 1, 4, 2]
def baseStart_7658044 : Nat := 118140960795 + 7658044 * 2 ^ 59
def prefixEnd_7658044 : Nat := 4983230072969 + 3 ^ 40 * 7658044 * 2
def baseEnd_7658044 : Nat := 3932257445279941101331303

theorem tailTrace_7658044 : CollatzResearch.WordTrace tailWord_7658044 prefixEnd_7658044 3932257445279941101331303 := by
  unfold tailWord_7658044
  simp only [CollatzResearch.WordTrace]
  refine ⟨139655905534110976316942593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186207874045481301755923457 139655905534110976316942593)
  ·
    refine ⟨104741929150583232237706945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139655905534110976316942593 104741929150583232237706945)
    ·
      refine ⟨78556446862937424178280209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104741929150583232237706945 78556446862937424178280209)
      ·
        refine ⟨58917335147203068133710157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78556446862937424178280209 58917335147203068133710157)
        ·
          refine ⟨22094000680201150550141309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58917335147203068133710157 22094000680201150550141309)
          ·
            refine ⟨8285250255075431456302991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22094000680201150550141309 8285250255075431456302991)
            ·
              refine ⟨12427875382613147184454487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8285250255075431456302991 12427875382613147184454487)
              ·
                refine ⟨18641813073919720776681731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12427875382613147184454487 18641813073919720776681731)
                ·
                  refine ⟨27962719610879581165022597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18641813073919720776681731 27962719610879581165022597)
                  ·
                    refine ⟨5243009927039921468441737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27962719610879581165022597 5243009927039921468441737)
                    ·
                      refine ⟨3932257445279941101331303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5243009927039921468441737 3932257445279941101331303)
                      ·
                        rfl

theorem cell23_7658044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 1, 4, 2].length) (baseStart_7658044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658044 prefixEnd_7658044 := by exact prefixLift 7658044
  have htrace : WordTrace (prefixWord ++ tailWord_7658044) baseStart_7658044 baseEnd_7658044 := by
    simpa [prefixWord, tailWord_7658044, baseEnd_7658044] using wordTrace_append hprefix tailTrace_7658044
  have hstable : (prefixWord ++ tailWord_7658044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658044).length < 2 ^ (prefixWord ++ tailWord_7658044).sum := by decide
  have hdescent : baseEnd_7658044 < baseStart_7658044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658063 : List Nat := [1, 1, 2, 1, 1, 2, 6, 1, 1, 7]
def baseStart_7658063 : Nat := 118140960795 + 7658063 * 2 ^ 59
def prefixEnd_7658063 : Nat := 4983230072969 + 3 ^ 40 * 7658063 * 2
def baseEnd_7658063 : Nat := 1310755733804125508997905

theorem tailTrace_7658063 : CollatzResearch.WordTrace tailWord_7658063 prefixEnd_7658063 1310755733804125508997905 := by
  unfold tailWord_7658063
  simp only [CollatzResearch.WordTrace]
  refine ⟨279312504055153118878826843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186208336036768745919217895 279312504055153118878826843)
  ·
    refine ⟨418968756082729678318240265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279312504055153118878826843 418968756082729678318240265)
    ·
      refine ⟨314226567062047258738680199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418968756082729678318240265 314226567062047258738680199)
      ·
        refine ⟨471339850593070888108020299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314226567062047258738680199 471339850593070888108020299)
        ·
          refine ⟨707009775889606332162030449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471339850593070888108020299 707009775889606332162030449)
          ·
            refine ⟨530257331917204749121522837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 707009775889606332162030449 530257331917204749121522837)
            ·
              refine ⟨24855812433618972615071383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 530257331917204749121522837 24855812433618972615071383)
              ·
                refine ⟨37283718650428458922607075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24855812433618972615071383 37283718650428458922607075)
                ·
                  refine ⟨55925577975642688383910613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37283718650428458922607075 55925577975642688383910613)
                  ·
                    refine ⟨1310755733804125508997905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55925577975642688383910613 1310755733804125508997905)
                    ·
                      rfl

theorem cell23_7658063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 7].length) (baseStart_7658063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658063 prefixEnd_7658063 := by exact prefixLift 7658063
  have htrace : WordTrace (prefixWord ++ tailWord_7658063) baseStart_7658063 baseEnd_7658063 := by
    simpa [prefixWord, tailWord_7658063, baseEnd_7658063] using wordTrace_append hprefix tailTrace_7658063
  have hstable : (prefixWord ++ tailWord_7658063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658063).length < 2 ^ (prefixWord ++ tailWord_7658063).sum := by decide
  have hdescent : baseEnd_7658063 < baseStart_7658063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658090 : List Nat := [3, 1, 3, 2, 1, 1, 3, 1, 1, 2, 5]
def baseStart_7658090 : Nat := 118140960795 + 7658090 * 2 ^ 59
def prefixEnd_7658090 : Nat := 4983230072969 + 3 ^ 40 * 7658090 * 2
def baseEnd_7658090 : Nat := 3932281065390047921356091

theorem tailTrace_7658090 : CollatzResearch.WordTrace tailWord_7658090 prefixEnd_7658090 3932281065390047921356091 := by
  unfold tailWord_7658090
  simp only [CollatzResearch.WordTrace]
  refine ⟨69828372206513825622514931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186208992550703534993373149 69828372206513825622514931)
  ·
    refine ⟨104742558309770738433772397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69828372206513825622514931 104742558309770738433772397)
    ·
      refine ⟨39278459366164026912664649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104742558309770738433772397 39278459366164026912664649)
      ·
        refine ⟨29458844524623020184498487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39278459366164026912664649 29458844524623020184498487)
        ·
          refine ⟨44188266786934530276747731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29458844524623020184498487 44188266786934530276747731)
          ·
            refine ⟨66282400180401795415121597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44188266786934530276747731 66282400180401795415121597)
            ·
              refine ⟨24855900067650673280670599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66282400180401795415121597 24855900067650673280670599)
              ·
                refine ⟨37283850101476009921005899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24855900067650673280670599 37283850101476009921005899)
                ·
                  refine ⟨55925775152214014881508849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37283850101476009921005899 55925775152214014881508849)
                  ·
                    refine ⟨41944331364160511161131637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55925775152214014881508849 41944331364160511161131637)
                    ·
                      refine ⟨3932281065390047921356091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41944331364160511161131637 3932281065390047921356091)
                      ·
                        rfl

theorem cell23_7658090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_7658090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658090 prefixEnd_7658090 := by exact prefixLift 7658090
  have htrace : WordTrace (prefixWord ++ tailWord_7658090) baseStart_7658090 baseEnd_7658090 := by
    simpa [prefixWord, tailWord_7658090, baseEnd_7658090] using wordTrace_append hprefix tailTrace_7658090
  have hstable : (prefixWord ++ tailWord_7658090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658090).length < 2 ^ (prefixWord ++ tailWord_7658090).sum := by decide
  have hdescent : baseEnd_7658090 < baseStart_7658090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658117 : List Nat := [1, 3, 1, 1, 4, 3, 2, 1, 2, 1, 4]
def baseStart_7658117 : Nat := 118140960795 + 7658117 * 2 ^ 59
def prefixEnd_7658117 : Nat := 4983230072969 + 3 ^ 40 * 7658117 * 2
def baseEnd_7658117 : Nat := 3932294929367719315718467

theorem tailTrace_7658117 : CollatzResearch.WordTrace tailWord_7658117 prefixEnd_7658117 3932294929367719315718467 := by
  unfold tailWord_7658117
  simp only [CollatzResearch.WordTrace]
  refine ⟨279314473596957486101292605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186209649064638324067528403 279314473596957486101292605)
  ·
    refine ⟨104742927598859057287984727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279314473596957486101292605 104742927598859057287984727)
    ·
      refine ⟨157114391398288585931977091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104742927598859057287984727 157114391398288585931977091)
      ·
        refine ⟨235671587097432878897965637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157114391398288585931977091 235671587097432878897965637)
        ·
          refine ⟨44188422580768664793368557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 235671587097432878897965637 44188422580768664793368557)
          ·
            refine ⟨16570658467788249297513209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44188422580768664793368557 16570658467788249297513209)
            ·
              refine ⟨12427993850841186973134907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16570658467788249297513209 12427993850841186973134907)
              ·
                refine ⟨18641990776261780459702361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12427993850841186973134907 18641990776261780459702361)
                ·
                  refine ⟨13981493082196335344776771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18641990776261780459702361 13981493082196335344776771)
                  ·
                    refine ⟨20972239623294503017165157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13981493082196335344776771 20972239623294503017165157)
                    ·
                      refine ⟨3932294929367719315718467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20972239623294503017165157 3932294929367719315718467)
                      ·
                        rfl

theorem cell23_7658117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 2, 1, 4].length) (baseStart_7658117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658117 prefixEnd_7658117 := by exact prefixLift 7658117
  have htrace : WordTrace (prefixWord ++ tailWord_7658117) baseStart_7658117 baseEnd_7658117 := by
    simpa [prefixWord, tailWord_7658117, baseEnd_7658117] using wordTrace_append hprefix tailTrace_7658117
  have hstable : (prefixWord ++ tailWord_7658117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658117).length < 2 ^ (prefixWord ++ tailWord_7658117).sum := by decide
  have hdescent : baseEnd_7658117 < baseStart_7658117 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658123 : List Nat := [1, 1, 1, 1, 4, 1, 2, 4, 8]
def baseStart_7658123 : Nat := 118140960795 + 7658123 * 2 ^ 59
def prefixEnd_7658123 : Nat := 4983230072969 + 3 ^ 40 * 7658123 * 2
def baseEnd_7658123 : Nat := 436922001139071810249271

theorem tailTrace_7658123 : CollatzResearch.WordTrace tailWord_7658123 prefixEnd_7658123 436922001139071810249271 := by
  unfold tailWord_7658123
  simp only [CollatzResearch.WordTrace]
  refine ⟨279314692434935749126011023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186209794956623832750674015 279314692434935749126011023)
  ·
    refine ⟨418972038652403623689016535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279314692434935749126011023 418972038652403623689016535)
    ·
      refine ⟨628458057978605435533524803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418972038652403623689016535 628458057978605435533524803)
      ·
        refine ⟨942687086967908153300287205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 628458057978605435533524803 942687086967908153300287205)
        ·
          refine ⟨176753828806482778743803851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 942687086967908153300287205 176753828806482778743803851)
          ·
            refine ⟨265130743209724168115705777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176753828806482778743803851 265130743209724168115705777)
            ·
              refine ⟨198848057407293126086779333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265130743209724168115705777 198848057407293126086779333)
              ·
                refine ⟨37284010763867461141271125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 198848057407293126086779333 37284010763867461141271125)
                ·
                  refine ⟨436922001139071810249271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37284010763867461141271125 436922001139071810249271)
                  ·
                    rfl

theorem cell23_7658123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 8].length) (baseStart_7658123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658123 prefixEnd_7658123 := by exact prefixLift 7658123
  have htrace : WordTrace (prefixWord ++ tailWord_7658123) baseStart_7658123 baseEnd_7658123 := by
    simpa [prefixWord, tailWord_7658123, baseEnd_7658123] using wordTrace_append hprefix tailTrace_7658123
  have hstable : (prefixWord ++ tailWord_7658123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658123).length < 2 ^ (prefixWord ++ tailWord_7658123).sum := by decide
  have hdescent : baseEnd_7658123 < baseStart_7658123 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658151 : List Nat := [1, 1, 6, 3, 1, 1, 1, 1, 2, 4, 2]
def baseStart_7658151 : Nat := 118140960795 + 7658151 * 2 ^ 59
def prefixEnd_7658151 : Nat := 4983230072969 + 3 ^ 40 * 7658151 * 2
def baseEnd_7658151 : Nat := 3932312387709972182693311

theorem tailTrace_7658151 : CollatzResearch.WordTrace tailWord_7658151 prefixEnd_7658151 3932312387709972182693311 := by
  unfold tailWord_7658151
  simp only [CollatzResearch.WordTrace]
  refine ⟨279315713678834309908030307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186210475785889539938686871 279315713678834309908030307)
  ·
    refine ⟨418973570518251464862045461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279315713678834309908030307 418973570518251464862045461)
    ·
      refine ⟨19639386118043037415408381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 418973570518251464862045461 19639386118043037415408381)
      ·
        refine ⟨7364769794266139030778143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19639386118043037415408381 7364769794266139030778143)
        ·
          refine ⟨11047154691399208546167215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7364769794266139030778143 11047154691399208546167215)
          ·
            refine ⟨16570732037098812819250823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11047154691399208546167215 16570732037098812819250823)
            ·
              refine ⟨24856098055648219228876235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16570732037098812819250823 24856098055648219228876235)
              ·
                refine ⟨37284147083472328843314353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24856098055648219228876235 37284147083472328843314353)
                ·
                  refine ⟨27963110312604246632485765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37284147083472328843314353 27963110312604246632485765)
                  ·
                    refine ⟨5243083183613296243591081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27963110312604246632485765 5243083183613296243591081)
                    ·
                      refine ⟨3932312387709972182693311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5243083183613296243591081 3932312387709972182693311)
                      ·
                        rfl

theorem cell23_7658151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_7658151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658151 prefixEnd_7658151 := by exact prefixLift 7658151
  have htrace : WordTrace (prefixWord ++ tailWord_7658151) baseStart_7658151 baseEnd_7658151 := by
    simpa [prefixWord, tailWord_7658151, baseEnd_7658151] using wordTrace_append hprefix tailTrace_7658151
  have hstable : (prefixWord ++ tailWord_7658151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658151).length < 2 ^ (prefixWord ++ tailWord_7658151).sum := by decide
  have hdescent : baseEnd_7658151 < baseStart_7658151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658153 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 2, 9]
def baseStart_7658153 : Nat := 118140960795 + 7658153 * 2 ^ 59
def prefixEnd_7658153 : Nat := 4983230072969 + 3 ^ 40 * 7658153 * 2
def baseEnd_7658153 : Nat := 1310771138223760391622767

theorem tailTrace_7658153 : CollatzResearch.WordTrace tailWord_7658153 prefixEnd_7658153 1310771138223760391622767 := by
  unfold tailWord_7658153
  simp only [CollatzResearch.WordTrace]
  refine ⟨279315786624827064249603113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186210524416551376166402075 279315786624827064249603113)
  ·
    refine ⟨209486839968620298187202335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279315786624827064249603113 209486839968620298187202335)
    ·
      refine ⟨314230259952930447280803503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209486839968620298187202335 314230259952930447280803503)
      ·
        refine ⟨471345389929395670921205255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314230259952930447280803503 471345389929395670921205255)
        ·
          refine ⟨707018084894093506381807883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471345389929395670921205255 707018084894093506381807883)
          ·
            refine ⟨1060527127341140259572711825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 707018084894093506381807883 1060527127341140259572711825)
            ·
              refine ⟨795395345505855194679533869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1060527127341140259572711825 795395345505855194679533869)
              ·
                refine ⟨298273254564695698004825201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 795395345505855194679533869 298273254564695698004825201)
                ·
                  refine ⟨223704940923521773503618901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 298273254564695698004825201 223704940923521773503618901)
                  ·
                    refine ⟨1310771138223760391622767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 223704940923521773503618901 1310771138223760391622767)
                    ·
                      rfl

theorem cell23_7658153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 9].length) (baseStart_7658153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658153 prefixEnd_7658153 := by exact prefixLift 7658153
  have htrace : WordTrace (prefixWord ++ tailWord_7658153) baseStart_7658153 baseEnd_7658153 := by
    simpa [prefixWord, tailWord_7658153, baseEnd_7658153] using wordTrace_append hprefix tailTrace_7658153
  have hstable : (prefixWord ++ tailWord_7658153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658153).length < 2 ^ (prefixWord ++ tailWord_7658153).sum := by decide
  have hdescent : baseEnd_7658153 < baseStart_7658153 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658157 : List Nat := [1, 5, 2, 1, 1, 2, 2, 3, 6]
def baseStart_7658157 : Nat := 118140960795 + 7658157 * 2 ^ 59
def prefixEnd_7658157 : Nat := 4983230072969 + 3 ^ 40 * 7658157 * 2
def baseEnd_7658157 : Nat := 436923940954877684357587

theorem tailTrace_7658157 : CollatzResearch.WordTrace tailWord_7658157 prefixEnd_7658157 436923940954877684357587 := by
  unfold tailWord_7658157
  simp only [CollatzResearch.WordTrace]
  refine ⟨279315932516812572932748725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186210621677875048621832483 279315932516812572932748725)
  ·
    refine ⟨26185868673451178712445193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 279315932516812572932748725 26185868673451178712445193)
    ·
      refine ⟨19639401505088384034333895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26185868673451178712445193 19639401505088384034333895)
      ·
        refine ⟨29459102257632576051500843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19639401505088384034333895 29459102257632576051500843)
        ·
          refine ⟨44188653386448864077251265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29459102257632576051500843 44188653386448864077251265)
          ·
            refine ⟨33141490039836648057938449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44188653386448864077251265 33141490039836648057938449)
            ·
              refine ⟨24856117529877486043453837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33141490039836648057938449 24856117529877486043453837)
              ·
                refine ⟨9321044073704057266295189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24856117529877486043453837 9321044073704057266295189)
                ·
                  refine ⟨436923940954877684357587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9321044073704057266295189 436923940954877684357587)
                  ·
                    rfl

theorem cell23_7658157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_7658157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658157 prefixEnd_7658157 := by exact prefixLift 7658157
  have htrace : WordTrace (prefixWord ++ tailWord_7658157) baseStart_7658157 baseEnd_7658157 := by
    simpa [prefixWord, tailWord_7658157, baseEnd_7658157] using wordTrace_append hprefix tailTrace_7658157
  have hstable : (prefixWord ++ tailWord_7658157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658157).length < 2 ^ (prefixWord ++ tailWord_7658157).sum := by decide
  have hdescent : baseEnd_7658157 < baseStart_7658157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658170 : List Nat := [3, 1, 1, 1, 2, 3, 1, 3, 3, 5]
def baseStart_7658170 : Nat := 118140960795 + 7658170 * 2 ^ 59
def prefixEnd_7658170 : Nat := 4983230072969 + 3 ^ 40 * 7658170 * 2
def baseEnd_7658170 : Nat := 1310774047947469202785241

theorem tailTrace_7658170 : CollatzResearch.WordTrace tailWord_7658170 prefixEnd_7658170 1310774047947469202785241 := by
  unfold tailWord_7658170
  simp only [CollatzResearch.WordTrace]
  refine ⟨69829101666441369038242991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186210937777176984101981309 69829101666441369038242991)
  ·
    refine ⟨104743652499662053557364487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69829101666441369038242991 104743652499662053557364487)
    ·
      refine ⟨157115478749493080336046731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104743652499662053557364487 157115478749493080336046731)
      ·
        refine ⟨235673218124239620504070097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157115478749493080336046731 235673218124239620504070097)
        ·
          refine ⟨176754913593179715378052573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235673218124239620504070097 176754913593179715378052573)
          ·
            refine ⟨66283092597442393266769715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176754913593179715378052573 66283092597442393266769715)
            ·
              refine ⟨99424638896163589900154573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66283092597442393266769715 99424638896163589900154573)
              ·
                refine ⟨37284239586061346212557965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99424638896163589900154573 37284239586061346212557965)
                ·
                  refine ⟨13981589844773004829709237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37284239586061346212557965 13981589844773004829709237)
                  ·
                    refine ⟨1310774047947469202785241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13981589844773004829709237 1310774047947469202785241)
                    ·
                      rfl

theorem cell23_7658170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 3, 5].length) (baseStart_7658170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658170 prefixEnd_7658170 := by exact prefixLift 7658170
  have htrace : WordTrace (prefixWord ++ tailWord_7658170) baseStart_7658170 baseEnd_7658170 := by
    simpa [prefixWord, tailWord_7658170, baseEnd_7658170] using wordTrace_append hprefix tailTrace_7658170
  have hstable : (prefixWord ++ tailWord_7658170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658170).length < 2 ^ (prefixWord ++ tailWord_7658170).sum := by decide
  have hdescent : baseEnd_7658170 < baseStart_7658170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658217 : List Nat := [1, 2, 1, 1, 1, 2, 4, 5, 2, 4]
def baseStart_7658217 : Nat := 118140960795 + 7658217 * 2 ^ 59
def prefixEnd_7658217 : Nat := 4983230072969 + 3 ^ 40 * 7658217 * 2
def baseEnd_7658217 : Nat := 1310782092477722974822669

theorem tailTrace_7658217 : CollatzResearch.WordTrace tailWord_7658217 prefixEnd_7658217 1310782092477722974822669 := by
  unfold tailWord_7658217
  simp only [CollatzResearch.WordTrace]
  refine ⟨279318120896595203179932905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186212080597730135453288603 279318120896595203179932905)
  ·
    refine ⟨209488590672446402384949679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279318120896595203179932905 209488590672446402384949679)
    ·
      refine ⟨314232886008669603577424519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209488590672446402384949679 314232886008669603577424519)
      ·
        refine ⟨471349329013004405366136779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314232886008669603577424519 471349329013004405366136779)
        ·
          refine ⟨707023993519506608049205169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471349329013004405366136779 707023993519506608049205169)
          ·
            refine ⟨530267995139629956036903877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 707023993519506608049205169 530267995139629956036903877)
            ·
              refine ⟨99425249088680616756919477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 530267995139629956036903877 99425249088680616756919477)
              ·
                refine ⟨9321117102063807820961201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99425249088680616756919477 9321117102063807820961201)
                ·
                  refine ⟨6990837826547855865720901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9321117102063807820961201 6990837826547855865720901)
                  ·
                    refine ⟨1310782092477722974822669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6990837826547855865720901 1310782092477722974822669)
                    ·
                      rfl

theorem cell23_7658217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 5, 2, 4].length) (baseStart_7658217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658217 prefixEnd_7658217 := by exact prefixLift 7658217
  have htrace : WordTrace (prefixWord ++ tailWord_7658217) baseStart_7658217 baseEnd_7658217 := by
    simpa [prefixWord, tailWord_7658217, baseEnd_7658217] using wordTrace_append hprefix tailTrace_7658217
  have hstable : (prefixWord ++ tailWord_7658217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658217).length < 2 ^ (prefixWord ++ tailWord_7658217).sum := by decide
  have hdescent : baseEnd_7658217 < baseStart_7658217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658224 : List Nat := [2, 1, 1, 1, 3, 1, 3, 4, 3, 2, 2]
def baseStart_7658224 : Nat := 118140960795 + 7658224 * 2 ^ 59
def prefixEnd_7658224 : Nat := 4983230072969 + 3 ^ 40 * 7658224 * 2
def baseEnd_7658224 : Nat := 3932349871797750397080475

theorem tailTrace_7658224 : CollatzResearch.WordTrace tailWord_7658224 prefixEnd_7658224 3932349871797750397080475 := by
  unfold tailWord_7658224
  simp only [CollatzResearch.WordTrace]
  refine ⟨139659188103784921687718863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186212250805046562250291817 139659188103784921687718863)
  ·
    refine ⟨209488782155677382531578295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139659188103784921687718863 209488782155677382531578295)
    ·
      refine ⟨314233173233516073797367443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209488782155677382531578295 314233173233516073797367443)
      ·
        refine ⟨471349759850274110696051165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314233173233516073797367443 471349759850274110696051165)
        ·
          refine ⟨176756159943852791511019187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 471349759850274110696051165 176756159943852791511019187)
          ·
            refine ⟨265134239915779187266528781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176756159943852791511019187 265134239915779187266528781)
            ·
              refine ⟨99425339968417195224948293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 265134239915779187266528781 99425339968417195224948293)
              ·
                refine ⟨18642251244078224104677805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99425339968417195224948293 18642251244078224104677805)
                ·
                  refine ⟨6990844216529334039254177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18642251244078224104677805 6990844216529334039254177)
                  ·
                    refine ⟨5243133162397000529440633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6990844216529334039254177 5243133162397000529440633)
                    ·
                      refine ⟨3932349871797750397080475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5243133162397000529440633 3932349871797750397080475)
                      ·
                        rfl

theorem cell23_7658224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 3, 2, 2].length) (baseStart_7658224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658224 prefixEnd_7658224 := by exact prefixLift 7658224
  have htrace : WordTrace (prefixWord ++ tailWord_7658224) baseStart_7658224 baseEnd_7658224 := by
    simpa [prefixWord, tailWord_7658224, baseEnd_7658224] using wordTrace_append hprefix tailTrace_7658224
  have hstable : (prefixWord ++ tailWord_7658224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658224).length < 2 ^ (prefixWord ++ tailWord_7658224).sum := by decide
  have hdescent : baseEnd_7658224 < baseStart_7658224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658244 : List Nat := [2, 3, 2, 2, 1, 1, 1, 5, 1, 2, 3]
def baseStart_7658244 : Nat := 118140960795 + 7658244 * 2 ^ 59
def prefixEnd_7658244 : Nat := 4983230072969 + 3 ^ 40 * 7658244 * 2
def baseEnd_7658244 : Nat := 3932360141410840318830383

theorem tailTrace_7658244 : CollatzResearch.WordTrace tailWord_7658244 prefixEnd_7658244 3932360141410840318830383 := by
  unfold tailWord_7658244
  simp only [CollatzResearch.WordTrace]
  refine ⟨139659552833748693395582893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186212737111664924527443857 139659552833748693395582893)
  ·
    refine ⟨52372332312655760023343585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139659552833748693395582893 52372332312655760023343585)
    ·
      refine ⟨39279249234491820017507689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52372332312655760023343585 39279249234491820017507689)
      ·
        refine ⟨29459436925868865013130767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39279249234491820017507689 29459436925868865013130767)
        ·
          refine ⟨44189155388803297519696151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29459436925868865013130767 44189155388803297519696151)
          ·
            refine ⟨66283733083204946279544227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44189155388803297519696151 66283733083204946279544227)
            ·
              refine ⟨99425599624807419419316341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66283733083204946279544227 99425599624807419419316341)
              ·
                refine ⟨9321149964825695570560907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99425599624807419419316341 9321149964825695570560907)
                ·
                  refine ⟨13981724947238543355841361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9321149964825695570560907 13981724947238543355841361)
                  ·
                    refine ⟨10486293710428907516881021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13981724947238543355841361 10486293710428907516881021)
                    ·
                      refine ⟨3932360141410840318830383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10486293710428907516881021 3932360141410840318830383)
                      ·
                        rfl

theorem cell23_7658244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_7658244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658244 prefixEnd_7658244 := by exact prefixLift 7658244
  have htrace : WordTrace (prefixWord ++ tailWord_7658244) baseStart_7658244 baseEnd_7658244 := by
    simpa [prefixWord, tailWord_7658244, baseEnd_7658244] using wordTrace_append hprefix tailTrace_7658244
  have hstable : (prefixWord ++ tailWord_7658244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658244).length < 2 ^ (prefixWord ++ tailWord_7658244).sum := by decide
  have hdescent : baseEnd_7658244 < baseStart_7658244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658247 : List Nat := [1, 1, 4, 4, 1, 3, 9]
def baseStart_7658247 : Nat := 118140960795 + 7658247 * 2 ^ 59
def prefixEnd_7658247 : Nat := 4983230072969 + 3 ^ 40 * 7658247 * 2
def baseEnd_7658247 : Nat := 48547675084602516136949

theorem tailTrace_7658247 : CollatzResearch.WordTrace tailWord_7658247 prefixEnd_7658247 48547675084602516136949 := by
  unfold tailWord_7658247
  simp only [CollatzResearch.WordTrace]
  refine ⟨279319215086486518303524995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186212810057657678869016663 279319215086486518303524995)
  ·
    refine ⟨418978822629729777455287493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279319215086486518303524995 418978822629729777455287493)
    ·
      refine ⟨78558529243074333272866405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 418978822629729777455287493 78558529243074333272866405)
      ·
        refine ⟨14729724233076437488662451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78558529243074333272866405 14729724233076437488662451)
        ·
          refine ⟨22094586349614656232993677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14729724233076437488662451 22094586349614656232993677)
          ·
            refine ⟨8285469881105496087372629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22094586349614656232993677 8285469881105496087372629)
            ·
              refine ⟨48547675084602516136949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8285469881105496087372629 48547675084602516136949)
              ·
                rfl

theorem cell23_7658247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 9].length) (baseStart_7658247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658247 prefixEnd_7658247 := by exact prefixLift 7658247
  have htrace : WordTrace (prefixWord ++ tailWord_7658247) baseStart_7658247 baseEnd_7658247 := by
    simpa [prefixWord, tailWord_7658247, baseEnd_7658247] using wordTrace_append hprefix tailTrace_7658247
  have hstable : (prefixWord ++ tailWord_7658247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658247).length < 2 ^ (prefixWord ++ tailWord_7658247).sum := by decide
  have hdescent : baseEnd_7658247 < baseStart_7658247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
