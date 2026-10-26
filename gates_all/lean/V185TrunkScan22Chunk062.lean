import V185TrunkScan22Chunk061

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_557439 : List Nat := [1, 1, 2, 2, 1, 1, 2, 4, 5, 3]
def baseStart_557439 : Nat := 118140960795 + 557439 * 2 ^ 59
def prefixEnd_557439 : Nat := 4983230072969 + 3 ^ 40 * 557439 * 2
def baseEnd_557439 : Nat := 190822761707833167365927

theorem tailTrace_557439 : CollatzResearch.WordTrace tailWord_557439 prefixEnd_557439 190822761707833167365927 := by
  unfold tailWord_557439
  simp only [CollatzResearch.WordTrace]
  refine ⟨20331470627501180846811371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13554313751667453897874247 20331470627501180846811371)
  ·
    refine ⟨30497205941251771270217057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20331470627501180846811371 30497205941251771270217057)
    ·
      refine ⟨22872904455938828452662793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30497205941251771270217057 22872904455938828452662793)
      ·
        refine ⟨17154678341954121339497095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22872904455938828452662793 17154678341954121339497095)
        ·
          refine ⟨25732017512931182009245643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17154678341954121339497095 25732017512931182009245643)
          ·
            refine ⟨38598026269396773013868465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25732017512931182009245643 38598026269396773013868465)
            ·
              refine ⟨28948519702047579760401349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38598026269396773013868465 28948519702047579760401349)
              ·
                refine ⟨5427847444133921205075253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28948519702047579760401349 5427847444133921205075253)
                ·
                  refine ⟨508860697887555112975805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5427847444133921205075253 508860697887555112975805)
                  ·
                    refine ⟨190822761707833167365927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 508860697887555112975805 190822761707833167365927)
                    ·
                      rfl

theorem cell22_557439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 5, 3].length) (baseStart_557439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_557439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_557439 prefixEnd_557439 := by exact prefixLift 557439
  have htrace : WordTrace (prefixWord ++ tailWord_557439) baseStart_557439 baseEnd_557439 := by
    simpa [prefixWord, tailWord_557439, baseEnd_557439] using wordTrace_append hprefix tailTrace_557439
  have hstable : (prefixWord ++ tailWord_557439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557439).length < 2 ^ (prefixWord ++ tailWord_557439).sum := by decide
  have hdescent : baseEnd_557439 < baseStart_557439 := by decide
  rcases family_descends (prefixWord ++ tailWord_557439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557462 : List Nat := [5, 3, 1, 2, 1, 1, 2, 1, 1, 5]
def baseStart_557462 : Nat := 118140960795 + 557462 * 2 ^ 59
def prefixEnd_557462 : Nat := 4983230072969 + 3 ^ 40 * 557462 * 2
def baseEnd_557462 : Nat := 190830635077868774040857

theorem tailTrace_557462 : CollatzResearch.WordTrace tailWord_557462 prefixEnd_557462 190830635077868774040857 := by
  unfold tailWord_557462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1270769344151115985931165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13554873004278570516599093 1270769344151115985931165)
  ·
    refine ⟨476538504056668494724187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1270769344151115985931165 476538504056668494724187)
    ·
      refine ⟨714807756085002742086281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 476538504056668494724187 714807756085002742086281)
      ·
        refine ⟨536105817063752056564711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 714807756085002742086281 536105817063752056564711)
        ·
          refine ⟨804158725595628084847067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 536105817063752056564711 804158725595628084847067)
          ·
            refine ⟨1206238088393442127270601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 804158725595628084847067 1206238088393442127270601)
            ·
              refine ⟨904678566295081595452951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1206238088393442127270601 904678566295081595452951)
              ·
                refine ⟨1357017849442622393179427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 904678566295081595452951 1357017849442622393179427)
                ·
                  refine ⟨2035526774163933589769141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1357017849442622393179427 2035526774163933589769141)
                  ·
                    refine ⟨190830635077868774040857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2035526774163933589769141 190830635077868774040857)
                    ·
                      rfl

theorem cell22_557462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_557462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_557462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_557462 prefixEnd_557462 := by exact prefixLift 557462
  have htrace : WordTrace (prefixWord ++ tailWord_557462) baseStart_557462 baseEnd_557462 := by
    simpa [prefixWord, tailWord_557462, baseEnd_557462] using wordTrace_append hprefix tailTrace_557462
  have hstable : (prefixWord ++ tailWord_557462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557462).length < 2 ^ (prefixWord ++ tailWord_557462).sum := by decide
  have hdescent : baseEnd_557462 < baseStart_557462 := by decide
  rcases family_descends (prefixWord ++ tailWord_557462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557533 : List Nat := [1, 4, 3, 1, 1, 1, 4, 2, 1, 4]
def baseStart_557533 : Nat := 118140960795 + 557533 * 2 ^ 59
def prefixEnd_557533 : Nat := 4983230072969 + 3 ^ 40 * 557533 * 2
def baseEnd_557533 : Nat := 190854939828848255515639

theorem tailTrace_557533 : CollatzResearch.WordTrace tailWord_557533 prefixEnd_557533 190854939828848255515639 := by
  unfold tailWord_557533
  simp only [CollatzResearch.WordTrace]
  refine ⟨20334899089160634900733253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13556599392773756600488835 20334899089160634900733253)
  ·
    refine ⟨3812793579217619043887485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20334899089160634900733253 3812793579217619043887485)
    ·
      refine ⟨1429797592206607141457807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3812793579217619043887485 1429797592206607141457807)
      ·
        refine ⟨2144696388309910712186711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1429797592206607141457807 2144696388309910712186711)
        ·
          refine ⟨3217044582464866068280067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2144696388309910712186711 3217044582464866068280067)
          ·
            refine ⟨4825566873697299102420101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3217044582464866068280067 4825566873697299102420101)
            ·
              refine ⟨904793788818243581703769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4825566873697299102420101 904793788818243581703769)
              ·
                refine ⟨678595341613682686277827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 904793788818243581703769 678595341613682686277827)
                ·
                  refine ⟨1017893012420524029416741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 678595341613682686277827 1017893012420524029416741)
                  ·
                    refine ⟨190854939828848255515639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1017893012420524029416741 190854939828848255515639)
                    ·
                      rfl

theorem cell22_557533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_557533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_557533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_557533 prefixEnd_557533 := by exact prefixLift 557533
  have htrace : WordTrace (prefixWord ++ tailWord_557533) baseStart_557533 baseEnd_557533 := by
    simpa [prefixWord, tailWord_557533, baseEnd_557533] using wordTrace_append hprefix tailTrace_557533
  have hstable : (prefixWord ++ tailWord_557533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557533).length < 2 ^ (prefixWord ++ tailWord_557533).sum := by decide
  have hdescent : baseEnd_557533 < baseStart_557533 := by decide
  rcases family_descends (prefixWord ++ tailWord_557533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557580 : List Nat := [2, 2, 1, 2, 4, 1, 4, 1, 2, 3]
def baseStart_557580 : Nat := 118140960795 + 557580 * 2 ^ 59
def prefixEnd_557580 : Nat := 4983230072969 + 3 ^ 40 * 557580 * 2
def baseEnd_557580 : Nat := 190871028889355799590495

theorem tailTrace_557580 : CollatzResearch.WordTrace tailWord_557580 prefixEnd_557580 190871028889355799590495 := by
  unfold tailWord_557580
  simp only [CollatzResearch.WordTrace]
  refine ⟨10168306659995180963847097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13557742213326907951796129 10168306659995180963847097)
  ·
    refine ⟨7626229994996385722885323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10168306659995180963847097 7626229994996385722885323)
    ·
      refine ⟨11439344992494578584327985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7626229994996385722885323 11439344992494578584327985)
      ·
        refine ⟨8579508744370933938245989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11439344992494578584327985 8579508744370933938245989)
        ·
          refine ⟨1608657889569550113421123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8579508744370933938245989 1608657889569550113421123)
          ·
            refine ⟨2412986834354325170131685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1608657889569550113421123 2412986834354325170131685)
            ·
              refine ⟨452435031441435969399691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2412986834354325170131685 452435031441435969399691)
              ·
                refine ⟨678652547162153954099537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 452435031441435969399691 678652547162153954099537)
                ·
                  refine ⟨508989410371615465574653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 678652547162153954099537 508989410371615465574653)
                  ·
                    refine ⟨190871028889355799590495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 508989410371615465574653 190871028889355799590495)
                    ·
                      rfl

theorem cell22_557580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 1, 2, 3].length) (baseStart_557580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_557580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_557580 prefixEnd_557580 := by exact prefixLift 557580
  have htrace : WordTrace (prefixWord ++ tailWord_557580) baseStart_557580 baseEnd_557580 := by
    simpa [prefixWord, tailWord_557580, baseEnd_557580] using wordTrace_append hprefix tailTrace_557580
  have hstable : (prefixWord ++ tailWord_557580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557580).length < 2 ^ (prefixWord ++ tailWord_557580).sum := by decide
  have hdescent : baseEnd_557580 < baseStart_557580 := by decide
  rcases family_descends (prefixWord ++ tailWord_557580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557625 : List Nat := [1, 2, 1, 5, 1, 1, 3, 4, 1, 3]
def baseStart_557625 : Nat := 118140960795 + 557625 * 2 ^ 59
def prefixEnd_557625 : Nat := 4983230072969 + 3 ^ 40 * 557625 * 2
def baseEnd_557625 : Nat := 190886433308990682215357

theorem tailTrace_557625 : CollatzResearch.WordTrace tailWord_557625 prefixEnd_557625 190886433308990682215357 := by
  unfold tailWord_557625
  simp only [CollatzResearch.WordTrace]
  refine ⟨20338254604827334613082329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13558836403218223075388219 20338254604827334613082329)
  ·
    refine ⟨15253690953620500959811747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20338254604827334613082329 15253690953620500959811747)
    ·
      refine ⟨22880536430430751439717621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15253690953620500959811747 22880536430430751439717621)
      ·
        refine ⟨2145050290352882947473527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22880536430430751439717621 2145050290352882947473527)
        ·
          refine ⟨3217575435529324421210291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2145050290352882947473527 3217575435529324421210291)
          ·
            refine ⟨4826363153293986631815437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3217575435529324421210291 4826363153293986631815437)
            ·
              refine ⟨1809886182485244986930789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4826363153293986631815437 1809886182485244986930789)
              ·
                refine ⟨339353659215983435049523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1809886182485244986930789 339353659215983435049523)
                ·
                  refine ⟨509030488823975152574285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 339353659215983435049523 509030488823975152574285)
                  ·
                    refine ⟨190886433308990682215357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 509030488823975152574285 190886433308990682215357)
                    ·
                      rfl

theorem cell22_557625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 4, 1, 3].length) (baseStart_557625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_557625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_557625 prefixEnd_557625 := by exact prefixLift 557625
  have htrace : WordTrace (prefixWord ++ tailWord_557625) baseStart_557625 baseEnd_557625 := by
    simpa [prefixWord, tailWord_557625, baseEnd_557625] using wordTrace_append hprefix tailTrace_557625
  have hstable : (prefixWord ++ tailWord_557625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557625).length < 2 ^ (prefixWord ++ tailWord_557625).sum := by decide
  have hdescent : baseEnd_557625 < baseStart_557625 := by decide
  rcases family_descends (prefixWord ++ tailWord_557625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557668 : List Nat := [2, 3, 1, 1, 2, 2, 3, 3, 1, 4]
def baseStart_557668 : Nat := 118140960795 + 557668 * 2 ^ 59
def prefixEnd_557668 : Nat := 4983230072969 + 3 ^ 40 * 557668 * 2
def baseEnd_557668 : Nat := 190901153087752903390225

theorem tailTrace_557668 : CollatzResearch.WordTrace tailWord_557668 prefixEnd_557668 190901153087752903390225 := by
  unfold tailWord_557668
  simp only [CollatzResearch.WordTrace]
  refine ⟨10169911471835776478448829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13559881962447701971265105 10169911471835776478448829)
  ·
    refine ⟨3813716801938416179418311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10169911471835776478448829 3813716801938416179418311)
    ·
      refine ⟨5720575202907624269127467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3813716801938416179418311 5720575202907624269127467)
      ·
        refine ⟨8580862804361436403691201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5720575202907624269127467 8580862804361436403691201)
        ·
          refine ⟨6435647103271077302768401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8580862804361436403691201 6435647103271077302768401)
          ·
            refine ⟨4826735327453307977076301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6435647103271077302768401 4826735327453307977076301)
            ·
              refine ⟨1810025747794990491403613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4826735327453307977076301 1810025747794990491403613)
              ·
                refine ⟨678759655423121434276355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1810025747794990491403613 678759655423121434276355)
                ·
                  refine ⟨1018139483134682151414533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 678759655423121434276355 1018139483134682151414533)
                  ·
                    refine ⟨190901153087752903390225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1018139483134682151414533 190901153087752903390225)
                    ·
                      rfl

theorem cell22_557668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_557668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_557668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_557668 prefixEnd_557668 := by exact prefixLift 557668
  have htrace : WordTrace (prefixWord ++ tailWord_557668) baseStart_557668 baseEnd_557668 := by
    simpa [prefixWord, tailWord_557668, baseEnd_557668] using wordTrace_append hprefix tailTrace_557668
  have hstable : (prefixWord ++ tailWord_557668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557668).length < 2 ^ (prefixWord ++ tailWord_557668).sum := by decide
  have hdescent : baseEnd_557668 < baseStart_557668 := by decide
  rcases family_descends (prefixWord ++ tailWord_557668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557672 : List Nat := [2, 1, 4, 3, 3, 1, 1, 2, 5]
def baseStart_557672 : Nat := 118140960795 + 557672 * 2 ^ 59
def prefixEnd_557672 : Nat := 4983230072969 + 3 ^ 40 * 557672 * 2
def baseEnd_557672 : Nat := 63634174123166075430071

theorem tailTrace_557672 : CollatzResearch.WordTrace tailWord_557672 prefixEnd_557672 63634174123166075430071 := by
  unfold tailWord_557672
  simp only [CollatzResearch.WordTrace]
  refine ⟨10169984417828530820021635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13559979223771374426695513 10169984417828530820021635)
  ·
    refine ⟨15254976626742796230032453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10169984417828530820021635 15254976626742796230032453)
    ·
      refine ⟨2860308117514274293131085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15254976626742796230032453 2860308117514274293131085)
      ·
        refine ⟨1072615544067852859924157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2860308117514274293131085 1072615544067852859924157)
        ·
          refine ⟨402230829025444822471559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1072615544067852859924157 402230829025444822471559)
          ·
            refine ⟨603346243538167233707339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 402230829025444822471559 603346243538167233707339)
            ·
              refine ⟨905019365307250850561009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 603346243538167233707339 905019365307250850561009)
              ·
                refine ⟨678764523980438137920757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 905019365307250850561009 678764523980438137920757)
                ·
                  refine ⟨63634174123166075430071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 678764523980438137920757 63634174123166075430071)
                  ·
                    rfl

theorem cell22_557672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 2, 5].length) (baseStart_557672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_557672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_557672 prefixEnd_557672 := by exact prefixLift 557672
  have htrace : WordTrace (prefixWord ++ tailWord_557672) baseStart_557672 baseEnd_557672 := by
    simpa [prefixWord, tailWord_557672, baseEnd_557672] using wordTrace_append hprefix tailTrace_557672
  have hstable : (prefixWord ++ tailWord_557672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557672).length < 2 ^ (prefixWord ++ tailWord_557672).sum := by decide
  have hdescent : baseEnd_557672 < baseStart_557672 := by decide
  rcases family_descends (prefixWord ++ tailWord_557672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557696 : List Nat := [2, 1, 1, 2, 1, 5, 1, 2, 1, 6]
def baseStart_557696 : Nat := 118140960795 + 557696 * 2 ^ 59
def prefixEnd_557696 : Nat := 4983230072969 + 3 ^ 40 * 557696 * 2
def baseEnd_557696 : Nat := 190910738059970163690139

theorem tailTrace_557696 : CollatzResearch.WordTrace tailWord_557696 prefixEnd_557696 190910738059970163690139 := by
  unfold tailWord_557696
  simp only [CollatzResearch.WordTrace]
  refine ⟨10170422093785056869458471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13560562791713409159277961 10170422093785056869458471)
  ·
    refine ⟨15255633140677585304187707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10170422093785056869458471 15255633140677585304187707)
    ·
      refine ⟨22883449711016377956281561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15255633140677585304187707 22883449711016377956281561)
      ·
        refine ⟨17162587283262283467211171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22883449711016377956281561 17162587283262283467211171)
        ·
          refine ⟨25743880924893425200816757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17162587283262283467211171 25743880924893425200816757)
          ·
            refine ⟨2413488836708758612576571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25743880924893425200816757 2413488836708758612576571)
            ·
              refine ⟨3620233255063137918864857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2413488836708758612576571 3620233255063137918864857)
              ·
                refine ⟨2715174941297353439148643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3620233255063137918864857 2715174941297353439148643)
                ·
                  refine ⟨4072762411946030158722965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2715174941297353439148643 4072762411946030158722965)
                  ·
                    refine ⟨190910738059970163690139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4072762411946030158722965 190910738059970163690139)
                    ·
                      rfl

theorem cell22_557696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 1, 6].length) (baseStart_557696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_557696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_557696 prefixEnd_557696 := by exact prefixLift 557696
  have htrace : WordTrace (prefixWord ++ tailWord_557696) baseStart_557696 baseEnd_557696 := by
    simpa [prefixWord, tailWord_557696, baseEnd_557696] using wordTrace_append hprefix tailTrace_557696
  have hstable : (prefixWord ++ tailWord_557696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557696).length < 2 ^ (prefixWord ++ tailWord_557696).sum := by decide
  have hdescent : baseEnd_557696 < baseStart_557696 := by decide
  rcases family_descends (prefixWord ++ tailWord_557696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557728 : List Nat := [2, 1, 1, 4, 4, 2, 8]
def baseStart_557728 : Nat := 118140960795 + 557728 * 2 ^ 59
def prefixEnd_557728 : Nat := 4983230072969 + 3 ^ 40 * 557728 * 2
def baseEnd_557728 : Nat := 7071173789404916551483

theorem tailTrace_557728 : CollatzResearch.WordTrace tailWord_557728 prefixEnd_557728 7071173789404916551483 := by
  unfold tailWord_557728
  simp only [CollatzResearch.WordTrace]
  refine ⟨10171005661727091602040919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13561340882302788802721225 10171005661727091602040919)
  ·
    refine ⟨15256508492590637403061379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10171005661727091602040919 15256508492590637403061379)
    ·
      refine ⟨22884762738885956104592069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15256508492590637403061379 22884762738885956104592069)
      ·
        refine ⟨4290893013541116769611013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22884762738885956104592069 4290893013541116769611013)
        ·
          refine ⟨804542440038959394302065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4290893013541116769611013 804542440038959394302065)
          ·
            refine ⟨603406830029219545726549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 804542440038959394302065 603406830029219545726549)
            ·
              refine ⟨7071173789404916551483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 603406830029219545726549 7071173789404916551483)
              ·
                rfl

theorem cell22_557728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 8].length) (baseStart_557728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_557728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_557728 prefixEnd_557728 := by exact prefixLift 557728
  have htrace : WordTrace (prefixWord ++ tailWord_557728) baseStart_557728 baseEnd_557728 := by
    simpa [prefixWord, tailWord_557728, baseEnd_557728] using wordTrace_append hprefix tailTrace_557728
  have hstable : (prefixWord ++ tailWord_557728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557728).length < 2 ^ (prefixWord ++ tailWord_557728).sum := by decide
  have hdescent : baseEnd_557728 < baseStart_557728 := by decide
  rcases family_descends (prefixWord ++ tailWord_557728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557745 : List Nat := [1, 2, 2, 6, 1, 1, 2, 7]
def baseStart_557745 : Nat := 118140960795 + 557745 * 2 ^ 59
def prefixEnd_557745 : Nat := 4983230072969 + 3 ^ 40 * 557745 * 2
def baseEnd_557745 : Nat := 21214167973483374357221

theorem tailTrace_557745 : CollatzResearch.WordTrace tailWord_557745 prefixEnd_557745 21214167973483374357221 := by
  unfold tailWord_557745
  simp only [CollatzResearch.WordTrace]
  refine ⟨20342631364392595107450689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13561754242928396738300459 20342631364392595107450689)
  ·
    refine ⟨15256973523294446330588017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20342631364392595107450689 15256973523294446330588017)
    ·
      refine ⟨11442730142470834747941013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15256973523294446330588017 11442730142470834747941013)
      ·
        refine ⟨536377975428320378809735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11442730142470834747941013 536377975428320378809735)
        ·
          refine ⟨804566963142480568214603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 536377975428320378809735 804566963142480568214603)
          ·
            refine ⟨1206850444713720852321905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 804566963142480568214603 1206850444713720852321905)
            ·
              refine ⟨905137833535290639241429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1206850444713720852321905 905137833535290639241429)
              ·
                refine ⟨21214167973483374357221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 905137833535290639241429 21214167973483374357221)
                ·
                  rfl

theorem cell22_557745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 7].length) (baseStart_557745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_557745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_557745 prefixEnd_557745 := by exact prefixLift 557745
  have htrace : WordTrace (prefixWord ++ tailWord_557745) baseStart_557745 baseEnd_557745 := by
    simpa [prefixWord, tailWord_557745, baseEnd_557745] using wordTrace_append hprefix tailTrace_557745
  have hstable : (prefixWord ++ tailWord_557745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557745).length < 2 ^ (prefixWord ++ tailWord_557745).sum := by decide
  have hdescent : baseEnd_557745 < baseStart_557745 := by decide
  rcases family_descends (prefixWord ++ tailWord_557745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557749 : List Nat := [1, 3, 3, 3, 1, 3, 2, 1, 2, 3]
def baseStart_557749 : Nat := 118140960795 + 557749 * 2 ^ 59
def prefixEnd_557749 : Nat := 4983230072969 + 3 ^ 40 * 557749 * 2
def baseEnd_557749 : Nat := 190928881043095692114977

theorem tailTrace_557749 : CollatzResearch.WordTrace tailWord_557749 prefixEnd_557749 190928881043095692114977 := by
  unfold tailWord_557749
  simp only [CollatzResearch.WordTrace]
  refine ⟨20342777256378103790596301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13561851504252069193730867 20342777256378103790596301)
  ·
    refine ⟨7628541471141788921473613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20342777256378103790596301 7628541471141788921473613)
    ·
      refine ⟨2860703051678170845552605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7628541471141788921473613 2860703051678170845552605)
      ·
        refine ⟨1072763644379314067082227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2860703051678170845552605 1072763644379314067082227)
        ·
          refine ⟨1609145466568971100623341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1072763644379314067082227 1609145466568971100623341)
          ·
            refine ⟨603429549963364162733753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1609145466568971100623341 603429549963364162733753)
            ·
              refine ⟨452572162472523122050315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 603429549963364162733753 452572162472523122050315)
              ·
                refine ⟨678858243708784683075473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 452572162472523122050315 678858243708784683075473)
                ·
                  refine ⟨509143682781588512306605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 678858243708784683075473 509143682781588512306605)
                  ·
                    refine ⟨190928881043095692114977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 509143682781588512306605 190928881043095692114977)
                    ·
                      rfl

theorem cell22_557749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_557749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_557749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_557749 prefixEnd_557749 := by exact prefixLift 557749
  have htrace : WordTrace (prefixWord ++ tailWord_557749) baseStart_557749 baseEnd_557749 := by
    simpa [prefixWord, tailWord_557749, baseEnd_557749] using wordTrace_append hprefix tailTrace_557749
  have hstable : (prefixWord ++ tailWord_557749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557749).length < 2 ^ (prefixWord ++ tailWord_557749).sum := by decide
  have hdescent : baseEnd_557749 < baseStart_557749 := by decide
  rcases family_descends (prefixWord ++ tailWord_557749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557771 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 6, 5]
def baseStart_557771 : Nat := 118140960795 + 557771 * 2 ^ 59
def prefixEnd_557771 : Nat := 4983230072969 + 3 ^ 40 * 557771 * 2
def baseEnd_557771 : Nat := 190936412092694968064909

theorem tailTrace_557771 : CollatzResearch.WordTrace tailWord_557771 prefixEnd_557771 190936412092694968064909 := by
  unfold tailWord_557771
  simp only [CollatzResearch.WordTrace]
  refine ⟨20343579662298401547897167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13562386441532267698598111 20343579662298401547897167)
  ·
    refine ⟨30515369493447602321845751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20343579662298401547897167 30515369493447602321845751)
    ·
      refine ⟨45773054240171403482768627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30515369493447602321845751 45773054240171403482768627)
      ·
        refine ⟨68659581360257105224152941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45773054240171403482768627 68659581360257105224152941)
        ·
          refine ⟨25747343010096414459057353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68659581360257105224152941 25747343010096414459057353)
          ·
            refine ⟨19310507257572310844293015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25747343010096414459057353 19310507257572310844293015)
            ·
              refine ⟨28965760886358466266439523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19310507257572310844293015 28965760886358466266439523)
              ·
                refine ⟨43448641329537699399659285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28965760886358466266439523 43448641329537699399659285)
                ·
                  refine ⟨2036655062322079659359029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 43448641329537699399659285 2036655062322079659359029)
                  ·
                    refine ⟨190936412092694968064909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2036655062322079659359029 190936412092694968064909)
                    ·
                      rfl

theorem cell22_557771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 5].length) (baseStart_557771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_557771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_557771 prefixEnd_557771 := by exact prefixLift 557771
  have htrace : WordTrace (prefixWord ++ tailWord_557771) baseStart_557771 baseEnd_557771 := by
    simpa [prefixWord, tailWord_557771, baseEnd_557771] using wordTrace_append hprefix tailTrace_557771
  have hstable : (prefixWord ++ tailWord_557771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557771).length < 2 ^ (prefixWord ++ tailWord_557771).sum := by decide
  have hdescent : baseEnd_557771 < baseStart_557771 := by decide
  rcases family_descends (prefixWord ++ tailWord_557771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557833 : List Nat := [1, 2, 1, 1, 3, 2, 4, 2, 1, 5]
def baseStart_557833 : Nat := 118140960795 + 557833 * 2 ^ 59
def prefixEnd_557833 : Nat := 4983230072969 + 3 ^ 40 * 557833 * 2
def baseEnd_557833 : Nat := 190957635959747473014719

theorem tailTrace_557833 : CollatzResearch.WordTrace tailWord_557833 prefixEnd_557833 190957635959747473014719 := by
  unfold tailWord_557833
  simp only [CollatzResearch.WordTrace]
  refine ⟨20345840988073786136654153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13563893992049190757769435 20345840988073786136654153)
  ·
    refine ⟨15259380741055339602490615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20345840988073786136654153 15259380741055339602490615)
    ·
      refine ⟨22889071111583009403735923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15259380741055339602490615 22889071111583009403735923)
      ·
        refine ⟨34333606667374514105603885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22889071111583009403735923 34333606667374514105603885)
        ·
          refine ⟨12875102500265442789601457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34333606667374514105603885 12875102500265442789601457)
          ·
            refine ⟨9656326875199082092201093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12875102500265442789601457 9656326875199082092201093)
            ·
              refine ⟨1810561289099827892287705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9656326875199082092201093 1810561289099827892287705)
              ·
                refine ⟨1357920966824870919215779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1810561289099827892287705 1357920966824870919215779)
                ·
                  refine ⟨2036881450237306378823669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1357920966824870919215779 2036881450237306378823669)
                  ·
                    refine ⟨190957635959747473014719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2036881450237306378823669 190957635959747473014719)
                    ·
                      rfl

theorem cell22_557833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 5].length) (baseStart_557833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_557833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_557833 prefixEnd_557833 := by exact prefixLift 557833
  have htrace : WordTrace (prefixWord ++ tailWord_557833) baseStart_557833 baseEnd_557833 := by
    simpa [prefixWord, tailWord_557833, baseEnd_557833] using wordTrace_append hprefix tailTrace_557833
  have hstable : (prefixWord ++ tailWord_557833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557833).length < 2 ^ (prefixWord ++ tailWord_557833).sum := by decide
  have hdescent : baseEnd_557833 < baseStart_557833 := by decide
  rcases family_descends (prefixWord ++ tailWord_557833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557848 : List Nat := [2, 1, 2, 3, 1, 1, 1, 3, 4, 4]
def baseStart_557848 : Nat := 118140960795 + 557848 * 2 ^ 59
def prefixEnd_557848 : Nat := 4983230072969 + 3 ^ 40 * 557848 * 2
def baseEnd_557848 : Nat := 190962770766292433889673

theorem tailTrace_557848 : CollatzResearch.WordTrace tailWord_557848 prefixEnd_557848 190962770766292433889673 := by
  unfold tailWord_557848
  simp only [CollatzResearch.WordTrace]
  refine ⟨10173194041509721849225099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13564258722012962465633465 10173194041509721849225099)
  ·
    refine ⟨15259791062264582773837649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10173194041509721849225099 15259791062264582773837649)
    ·
      refine ⟨11444843296698437080378237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15259791062264582773837649 11444843296698437080378237)
      ·
        refine ⟨4291816236261913905141839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11444843296698437080378237 4291816236261913905141839)
        ·
          refine ⟨6437724354392870857712759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4291816236261913905141839 6437724354392870857712759)
          ·
            refine ⟨9656586531589306286569139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6437724354392870857712759 9656586531589306286569139)
            ·
              refine ⟨14484879797383959429853709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9656586531589306286569139 14484879797383959429853709)
              ·
                refine ⟨5431829924018984786195141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14484879797383959429853709 5431829924018984786195141)
                ·
                  refine ⟨1018468110753559647411589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5431829924018984786195141 1018468110753559647411589)
                  ·
                    refine ⟨190962770766292433889673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1018468110753559647411589 190962770766292433889673)
                    ·
                      rfl

theorem cell22_557848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 4, 4].length) (baseStart_557848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_557848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_557848 prefixEnd_557848 := by exact prefixLift 557848
  have htrace : WordTrace (prefixWord ++ tailWord_557848) baseStart_557848 baseEnd_557848 := by
    simpa [prefixWord, tailWord_557848, baseEnd_557848] using wordTrace_append hprefix tailTrace_557848
  have hstable : (prefixWord ++ tailWord_557848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557848).length < 2 ^ (prefixWord ++ tailWord_557848).sum := by decide
  have hdescent : baseEnd_557848 < baseStart_557848 := by decide
  rcases family_descends (prefixWord ++ tailWord_557848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557850 : List Nat := [3, 1, 1, 3, 2, 1, 3, 1, 4, 3]
def baseStart_557850 : Nat := 118140960795 + 557850 * 2 ^ 59
def prefixEnd_557850 : Nat := 4983230072969 + 3 ^ 40 * 557850 * 2
def baseEnd_557850 : Nat := 190963455407165095339667

theorem tailTrace_557850 : CollatzResearch.WordTrace tailWord_557850 prefixEnd_557850 190963455407165095339667 := by
  unfold tailWord_557850
  simp only [CollatzResearch.WordTrace]
  refine ⟨5086615257253049510005751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13564307352674798693348669 5086615257253049510005751)
  ·
    refine ⟨7629922885879574265008627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5086615257253049510005751 7629922885879574265008627)
    ·
      refine ⟨11444884328819361397512941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7629922885879574265008627 11444884328819361397512941)
      ·
        refine ⟨4291831623307260524067353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11444884328819361397512941 4291831623307260524067353)
        ·
          refine ⟨3218873717480445393050515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4291831623307260524067353 3218873717480445393050515)
          ·
            refine ⟨4828310576220668089575773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3218873717480445393050515 4828310576220668089575773)
            ·
              refine ⟨1810616466082750533590915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4828310576220668089575773 1810616466082750533590915)
              ·
                refine ⟨2715924699124125800386373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1810616466082750533590915 2715924699124125800386373)
                ·
                  refine ⟨509235881085773587572445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2715924699124125800386373 509235881085773587572445)
                  ·
                    refine ⟨190963455407165095339667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 509235881085773587572445 190963455407165095339667)
                    ·
                      rfl

theorem cell22_557850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 4, 3].length) (baseStart_557850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_557850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_557850 prefixEnd_557850 := by exact prefixLift 557850
  have htrace : WordTrace (prefixWord ++ tailWord_557850) baseStart_557850 baseEnd_557850 := by
    simpa [prefixWord, tailWord_557850, baseEnd_557850] using wordTrace_append hprefix tailTrace_557850
  have hstable : (prefixWord ++ tailWord_557850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557850).length < 2 ^ (prefixWord ++ tailWord_557850).sum := by decide
  have hdescent : baseEnd_557850 < baseStart_557850 := by decide
  rcases family_descends (prefixWord ++ tailWord_557850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557886 : List Nat := [4, 2, 1, 2, 4, 1, 1, 3, 4]
def baseStart_557886 : Nat := 118140960795 + 557886 * 2 ^ 59
def prefixEnd_557886 : Nat := 4983230072969 + 3 ^ 40 * 557886 * 2
def baseEnd_557886 : Nat := 63658592980957667146519

theorem tailTrace_557886 : CollatzResearch.WordTrace tailWord_557886 prefixEnd_557886 63658592980957667146519 := by
  unfold tailWord_557886
  simp only [CollatzResearch.WordTrace]
  refine ⟨2543471757110222023541689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13565182704587850792222341 2543471757110222023541689)
  ·
    refine ⟨1907603817832666517656267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2543471757110222023541689 1907603817832666517656267)
    ·
      refine ⟨2861405726748999776484401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1907603817832666517656267 2861405726748999776484401)
      ·
        refine ⟨2146054295061749832363301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2861405726748999776484401 2146054295061749832363301)
        ·
          refine ⟨402385180324078093568119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2146054295061749832363301 402385180324078093568119)
          ·
            refine ⟨603577770486117140352179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 402385180324078093568119 603577770486117140352179)
            ·
              refine ⟨905366655729175710528269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 603577770486117140352179 905366655729175710528269)
              ·
                refine ⟨339512495898440891448101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 905366655729175710528269 339512495898440891448101)
                ·
                  refine ⟨63658592980957667146519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 339512495898440891448101 63658592980957667146519)
                  ·
                    rfl

theorem cell22_557886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_557886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_557886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_557886 prefixEnd_557886 := by exact prefixLift 557886
  have htrace : WordTrace (prefixWord ++ tailWord_557886) baseStart_557886 baseEnd_557886 := by
    simpa [prefixWord, tailWord_557886, baseEnd_557886] using wordTrace_append hprefix tailTrace_557886
  have hstable : (prefixWord ++ tailWord_557886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557886).length < 2 ^ (prefixWord ++ tailWord_557886).sum := by decide
  have hdescent : baseEnd_557886 < baseStart_557886 := by decide
  rcases family_descends (prefixWord ++ tailWord_557886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557912 : List Nat := [2, 1, 2, 2, 1, 1, 1, 8, 1, 3]
def baseStart_557912 : Nat := 118140960795 + 557912 * 2 ^ 59
def prefixEnd_557912 : Nat := 4983230072969 + 3 ^ 40 * 557912 * 2
def baseEnd_557912 : Nat := 190984679274217600289477

theorem tailTrace_557912 : CollatzResearch.WordTrace tailWord_557912 prefixEnd_557912 190984679274217600289477 := by
  unfold tailWord_557912
  simp only [CollatzResearch.WordTrace]
  refine ⟨10174361177393791314389995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13565814903191721752519993 10174361177393791314389995)
  ·
    refine ⟨15261541766090686971584993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10174361177393791314389995 15261541766090686971584993)
    ·
      refine ⟨11446156324568015228688745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15261541766090686971584993 11446156324568015228688745)
      ·
        refine ⟨8584617243426011421516559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11446156324568015228688745 8584617243426011421516559)
        ·
          refine ⟨12876925865139017132274839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8584617243426011421516559 12876925865139017132274839)
          ·
            refine ⟨19315388797708525698412259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12876925865139017132274839 19315388797708525698412259)
            ·
              refine ⟨28973083196562788547618389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19315388797708525698412259 28973083196562788547618389)
              ·
                refine ⟨339528318709720178292403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 28973083196562788547618389 339528318709720178292403)
                ·
                  refine ⟨509292478064580267438605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 339528318709720178292403 509292478064580267438605)
                  ·
                    refine ⟨190984679274217600289477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 509292478064580267438605 190984679274217600289477)
                    ·
                      rfl

theorem cell22_557912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 8, 1, 3].length) (baseStart_557912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_557912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_557912 prefixEnd_557912 := by exact prefixLift 557912
  have htrace : WordTrace (prefixWord ++ tailWord_557912) baseStart_557912 baseEnd_557912 := by
    simpa [prefixWord, tailWord_557912, baseEnd_557912] using wordTrace_append hprefix tailTrace_557912
  have hstable : (prefixWord ++ tailWord_557912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557912).length < 2 ^ (prefixWord ++ tailWord_557912).sum := by decide
  have hdescent : baseEnd_557912 < baseStart_557912 := by decide
  rcases family_descends (prefixWord ++ tailWord_557912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557974 : List Nat := [5, 3, 1, 1, 1, 1, 1, 1, 1, 7]
def baseStart_557974 : Nat := 118140960795 + 557974 * 2 ^ 59
def prefixEnd_557974 : Nat := 4983230072969 + 3 ^ 40 * 557974 * 2
def baseEnd_557974 : Nat := 191005903141270105239287

theorem tailTrace_557974 : CollatzResearch.WordTrace tailWord_557974 prefixEnd_557974 191005903141270105239287 := by
  unfold tailWord_557974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1271936480035185451096061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13567322453708644811691317 1271936480035185451096061)
  ·
    refine ⟨476976180013194544161023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1271936480035185451096061 476976180013194544161023)
    ·
      refine ⟨715464270019791816241535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 476976180013194544161023 715464270019791816241535)
      ·
        refine ⟨1073196405029687724362303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 715464270019791816241535 1073196405029687724362303)
        ·
          refine ⟨1609794607544531586543455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1073196405029687724362303 1609794607544531586543455)
          ·
            refine ⟨2414691911316797379815183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1609794607544531586543455 2414691911316797379815183)
            ·
              refine ⟨3622037866975196069722775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2414691911316797379815183 3622037866975196069722775)
              ·
                refine ⟨5433056800462794104584163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3622037866975196069722775 5433056800462794104584163)
                ·
                  refine ⟨8149585200694191156876245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5433056800462794104584163 8149585200694191156876245)
                  ·
                    refine ⟨191005903141270105239287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8149585200694191156876245 191005903141270105239287)
                    ·
                      rfl

theorem cell22_557974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_557974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_557974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_557974 prefixEnd_557974 := by exact prefixLift 557974
  have htrace : WordTrace (prefixWord ++ tailWord_557974) baseStart_557974 baseEnd_557974 := by
    simpa [prefixWord, tailWord_557974, baseEnd_557974] using wordTrace_append hprefix tailTrace_557974
  have hstable : (prefixWord ++ tailWord_557974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557974).length < 2 ^ (prefixWord ++ tailWord_557974).sum := by decide
  have hdescent : baseEnd_557974 < baseStart_557974 := by decide
  rcases family_descends (prefixWord ++ tailWord_557974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558036 : List Nat := [2, 4, 1, 2, 1, 3, 3, 1, 2, 3]
def baseStart_558036 : Nat := 118140960795 + 558036 * 2 ^ 59
def prefixEnd_558036 : Nat := 4983230072969 + 3 ^ 40 * 558036 * 2
def baseEnd_558036 : Nat := 191027127008322610189097

theorem tailTrace_558036 : CollatzResearch.WordTrace tailWord_558036 prefixEnd_558036 191027127008322610189097 := by
  unfold tailWord_558036
  simp only [CollatzResearch.WordTrace]
  refine ⟨10176622503169175903146981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13568830004225567870862641 10176622503169175903146981)
  ·
    refine ⟨1908116719344220481840059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10176622503169175903146981 1908116719344220481840059)
    ·
      refine ⟨2862175079016330722760089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1908116719344220481840059 2862175079016330722760089)
      ·
        refine ⟨2146631309262248042070067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2862175079016330722760089 2146631309262248042070067)
        ·
          refine ⟨3219946963893372063105101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2146631309262248042070067 3219946963893372063105101)
          ·
            refine ⟨1207480111460014523664413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3219946963893372063105101 1207480111460014523664413)
            ·
              refine ⟨452805041797505446374155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1207480111460014523664413 452805041797505446374155)
              ·
                refine ⟨679207562696258169561233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 452805041797505446374155 679207562696258169561233)
                ·
                  refine ⟨509405672022193627170925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 679207562696258169561233 509405672022193627170925)
                  ·
                    refine ⟨191027127008322610189097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 509405672022193627170925 191027127008322610189097)
                    ·
                      rfl

theorem cell22_558036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_558036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_558036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_558036 prefixEnd_558036 := by exact prefixLift 558036
  have htrace : WordTrace (prefixWord ++ tailWord_558036) baseStart_558036 baseEnd_558036 := by
    simpa [prefixWord, tailWord_558036, baseEnd_558036] using wordTrace_append hprefix tailTrace_558036
  have hstable : (prefixWord ++ tailWord_558036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558036).length < 2 ^ (prefixWord ++ tailWord_558036).sum := by decide
  have hdescent : baseEnd_558036 < baseStart_558036 := by decide
  rcases family_descends (prefixWord ++ tailWord_558036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558094 : List Nat := [4, 1, 1, 2, 2, 2, 4, 1, 5]
def baseStart_558094 : Nat := 118140960795 + 558094 * 2 ^ 59
def prefixEnd_558094 : Nat := 4983230072969 + 3 ^ 40 * 558094 * 2
def baseEnd_558094 : Nat := 63682327197876597412973

theorem tailTrace_558094 : CollatzResearch.WordTrace tailWord_558094 prefixEnd_558094 63682327197876597412973 := by
  unfold tailWord_558094
  simp only [CollatzResearch.WordTrace]
  refine ⟨2544420055016028463988167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13570240293418818474603557 2544420055016028463988167)
  ·
    refine ⟨3816630082524042695982251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2544420055016028463988167 3816630082524042695982251)
    ·
      refine ⟨5724945123786064043973377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3816630082524042695982251 5724945123786064043973377)
      ·
        refine ⟨4293708842839548032980033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5724945123786064043973377 4293708842839548032980033)
        ·
          refine ⟨3220281632129661024735025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4293708842839548032980033 3220281632129661024735025)
          ·
            refine ⟨2415211224097245768551269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3220281632129661024735025 2415211224097245768551269)
            ·
              refine ⟨452852104518233581603363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2415211224097245768551269 452852104518233581603363)
              ·
                refine ⟨679278156777350372405045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 452852104518233581603363 679278156777350372405045)
                ·
                  refine ⟨63682327197876597412973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 679278156777350372405045 63682327197876597412973)
                  ·
                    rfl

theorem cell22_558094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 1, 5].length) (baseStart_558094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_558094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_558094 prefixEnd_558094 := by exact prefixLift 558094
  have htrace : WordTrace (prefixWord ++ tailWord_558094) baseStart_558094 baseEnd_558094 := by
    simpa [prefixWord, tailWord_558094, baseEnd_558094] using wordTrace_append hprefix tailTrace_558094
  have hstable : (prefixWord ++ tailWord_558094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558094).length < 2 ^ (prefixWord ++ tailWord_558094).sum := by decide
  have hdescent : baseEnd_558094 < baseStart_558094 := by decide
  rcases family_descends (prefixWord ++ tailWord_558094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558105 : List Nat := [1, 2, 1, 2, 1, 1, 4, 4, 6]
def baseStart_558105 : Nat := 118140960795 + 558105 * 2 ^ 59
def prefixEnd_558105 : Nat := 4983230072969 + 3 ^ 40 * 558105 * 2
def baseEnd_558105 : Nat := 63683582372809810071295

theorem tailTrace_558105 : CollatzResearch.WordTrace tailWord_558105 prefixEnd_558105 63683582372809810071295 := by
  unfold tailWord_558105
  simp only [CollatzResearch.WordTrace]
  refine ⟨20355761643088376590555769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13570507762058917727037179 20355761643088376590555769)
  ·
    refine ⟨15266821232316282442916827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20355761643088376590555769 15266821232316282442916827)
    ·
      refine ⟨22900231848474423664375241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15266821232316282442916827 22900231848474423664375241)
      ·
        refine ⟨17175173886355817748281431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22900231848474423664375241 17175173886355817748281431)
        ·
          refine ⟨25762760829533726622422147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17175173886355817748281431 25762760829533726622422147)
          ·
            refine ⟨38644141244300589933633221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25762760829533726622422147 38644141244300589933633221)
            ·
              refine ⟨7245776483306360612556229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38644141244300589933633221 7245776483306360612556229)
              ·
                refine ⟨1358583090619942614854293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7245776483306360612556229 1358583090619942614854293)
                ·
                  refine ⟨63683582372809810071295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1358583090619942614854293 63683582372809810071295)
                  ·
                    rfl

theorem cell22_558105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 6].length) (baseStart_558105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_558105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_558105 prefixEnd_558105 := by exact prefixLift 558105
  have htrace : WordTrace (prefixWord ++ tailWord_558105) baseStart_558105 baseEnd_558105 := by
    simpa [prefixWord, tailWord_558105, baseEnd_558105] using wordTrace_append hprefix tailTrace_558105
  have hstable : (prefixWord ++ tailWord_558105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558105).length < 2 ^ (prefixWord ++ tailWord_558105).sum := by decide
  have hdescent : baseEnd_558105 < baseStart_558105 := by decide
  rcases family_descends (prefixWord ++ tailWord_558105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558124 : List Nat := [2, 2, 1, 1, 1, 2, 7, 1, 1, 4]
def baseStart_558124 : Nat := 118140960795 + 558124 * 2 ^ 59
def prefixEnd_558124 : Nat := 4983230072969 + 3 ^ 40 * 558124 * 2
def baseEnd_558124 : Nat := 191057251206719713988827

theorem tailTrace_558124 : CollatzResearch.WordTrace tailWord_558124 prefixEnd_558124 191057251206719713988827 := by
  unfold tailWord_558124
  simp only [CollatzResearch.WordTrace]
  refine ⟨10178227315009771417748713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13570969753346361890331617 10178227315009771417748713)
  ·
    refine ⟨7633670486257328563311535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10178227315009771417748713 7633670486257328563311535)
    ·
      refine ⟨11450505729385992844967303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7633670486257328563311535 11450505729385992844967303)
      ·
        refine ⟨17175758594078989267450955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11450505729385992844967303 17175758594078989267450955)
        ·
          refine ⟨25763637891118483901176433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17175758594078989267450955 25763637891118483901176433)
          ·
            refine ⟨19322728418338862925882325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25763637891118483901176433 19322728418338862925882325)
            ·
              refine ⟨452876447304817099825367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 19322728418338862925882325 452876447304817099825367)
              ·
                refine ⟨679314670957225649738051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 452876447304817099825367 679314670957225649738051)
                ·
                  refine ⟨1018972006435838474607077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 679314670957225649738051 1018972006435838474607077)
                  ·
                    refine ⟨191057251206719713988827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1018972006435838474607077 191057251206719713988827)
                    ·
                      rfl

theorem cell22_558124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 4].length) (baseStart_558124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_558124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_558124 prefixEnd_558124 := by exact prefixLift 558124
  have htrace : WordTrace (prefixWord ++ tailWord_558124) baseStart_558124 baseEnd_558124 := by
    simpa [prefixWord, tailWord_558124, baseEnd_558124] using wordTrace_append hprefix tailTrace_558124
  have hstable : (prefixWord ++ tailWord_558124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558124).length < 2 ^ (prefixWord ++ tailWord_558124).sum := by decide
  have hdescent : baseEnd_558124 < baseStart_558124 := by decide
  rcases family_descends (prefixWord ++ tailWord_558124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558135 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 3, 6]
def baseStart_558135 : Nat := 118140960795 + 558135 * 2 ^ 59
def prefixEnd_558135 : Nat := 4983230072969 + 3 ^ 40 * 558135 * 2
def baseEnd_558135 : Nat := 191061016731519351963793

theorem tailTrace_558135 : CollatzResearch.WordTrace tailWord_558135 prefixEnd_558135 191061016731519351963793 := by
  unfold tailWord_558135
  simp only [CollatzResearch.WordTrace]
  refine ⟨20356855832979691714147859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13571237221986461142765239 20356855832979691714147859)
  ·
    refine ⟨30535283749469537571221789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20356855832979691714147859 30535283749469537571221789)
    ·
      refine ⟨11450731406051076589208171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30535283749469537571221789 11450731406051076589208171)
      ·
        refine ⟨17176097109076614883812257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11450731406051076589208171 17176097109076614883812257)
        ·
          refine ⟨12882072831807461162859193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17176097109076614883812257 12882072831807461162859193)
          ·
            refine ⟨9661554623855595872144395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12882072831807461162859193 9661554623855595872144395)
            ·
              refine ⟨14492331935783393808216593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9661554623855595872144395 14492331935783393808216593)
              ·
                refine ⟨10869248951837545356162445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14492331935783393808216593 10869248951837545356162445)
                ·
                  refine ⟨4075968356939079508560917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10869248951837545356162445 4075968356939079508560917)
                  ·
                    refine ⟨191061016731519351963793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4075968356939079508560917 191061016731519351963793)
                    ·
                      rfl

theorem cell22_558135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_558135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_558135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_558135 prefixEnd_558135 := by exact prefixLift 558135
  have htrace : WordTrace (prefixWord ++ tailWord_558135) baseStart_558135 baseEnd_558135 := by
    simpa [prefixWord, tailWord_558135, baseEnd_558135] using wordTrace_append hprefix tailTrace_558135
  have hstable : (prefixWord ++ tailWord_558135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558135).length < 2 ^ (prefixWord ++ tailWord_558135).sum := by decide
  have hdescent : baseEnd_558135 < baseStart_558135 := by decide
  rcases family_descends (prefixWord ++ tailWord_558135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558154 : List Nat := [3, 1, 2, 1, 1, 2, 4, 3, 2, 3]
def baseStart_558154 : Nat := 118140960795 + 558154 * 2 ^ 59
def prefixEnd_558154 : Nat := 4983230072969 + 3 ^ 40 * 558154 * 2
def baseEnd_558154 : Nat := 191067520819809635738735

theorem tailTrace_558154 : CollatzResearch.WordTrace tailWord_558154 prefixEnd_558154 191067520819809635738735 := by
  unfold tailWord_558154
  simp only [CollatzResearch.WordTrace]
  refine ⟨5089387204977714489772379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13571699213273905306059677 5089387204977714489772379)
  ·
    refine ⟨7634080807466571734658569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5089387204977714489772379 7634080807466571734658569)
    ·
      refine ⟨5725560605599928800993927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7634080807466571734658569 5725560605599928800993927)
      ·
        refine ⟨8588340908399893201490891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5725560605599928800993927 8588340908399893201490891)
        ·
          refine ⟨12882511362599839802236337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8588340908399893201490891 12882511362599839802236337)
          ·
            refine ⟨9661883521949879851677253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12882511362599839802236337 9661883521949879851677253)
            ·
              refine ⟨1811603160365602472189485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9661883521949879851677253 1811603160365602472189485)
              ·
                refine ⟨679351185137100927071057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1811603160365602472189485 679351185137100927071057)
                ·
                  refine ⟨509513388852825695303293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 679351185137100927071057 509513388852825695303293)
                  ·
                    refine ⟨191067520819809635738735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 509513388852825695303293 191067520819809635738735)
                    ·
                      rfl

theorem cell22_558154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 3, 2, 3].length) (baseStart_558154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_558154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_558154 prefixEnd_558154 := by exact prefixLift 558154
  have htrace : WordTrace (prefixWord ++ tailWord_558154) baseStart_558154 baseEnd_558154 := by
    simpa [prefixWord, tailWord_558154, baseEnd_558154] using wordTrace_append hprefix tailTrace_558154
  have hstable : (prefixWord ++ tailWord_558154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558154).length < 2 ^ (prefixWord ++ tailWord_558154).sum := by decide
  have hdescent : baseEnd_558154 < baseStart_558154 := by decide
  rcases family_descends (prefixWord ++ tailWord_558154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558173 : List Nat := [1, 4, 4, 1, 2, 1, 2, 3, 4]
def baseStart_558173 : Nat := 118140960795 + 558173 * 2 ^ 59
def prefixEnd_558173 : Nat := 4983230072969 + 3 ^ 40 * 558173 * 2
def baseEnd_558173 : Nat := 63691341636033306504559

theorem tailTrace_558173 : CollatzResearch.WordTrace tailWord_558173 prefixEnd_558173 63691341636033306504559 := by
  unfold tailWord_558173
  simp only [CollatzResearch.WordTrace]
  refine ⟨20358241806842024204031173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13572161204561349469354115 20358241806842024204031173)
  ·
    refine ⟨3817170338782879538255845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20358241806842024204031173 3817170338782879538255845)
    ·
      refine ⟨715719438521789913422971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3817170338782879538255845 715719438521789913422971)
      ·
        refine ⟨1073579157782684870134457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 715719438521789913422971 1073579157782684870134457)
        ·
          refine ⟨805184368337013652600843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1073579157782684870134457 805184368337013652600843)
          ·
            refine ⟨1207776552505520478901265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 805184368337013652600843 1207776552505520478901265)
            ·
              refine ⟨905832414379140359175949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1207776552505520478901265 905832414379140359175949)
              ·
                refine ⟨339687155392177634690981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 905832414379140359175949 339687155392177634690981)
                ·
                  refine ⟨63691341636033306504559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 339687155392177634690981 63691341636033306504559)
                  ·
                    rfl

theorem cell22_558173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 3, 4].length) (baseStart_558173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_558173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_558173 prefixEnd_558173 := by exact prefixLift 558173
  have htrace : WordTrace (prefixWord ++ tailWord_558173) baseStart_558173 baseEnd_558173 := by
    simpa [prefixWord, tailWord_558173, baseEnd_558173] using wordTrace_append hprefix tailTrace_558173
  have hstable : (prefixWord ++ tailWord_558173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558173).length < 2 ^ (prefixWord ++ tailWord_558173).sum := by decide
  have hdescent : baseEnd_558173 < baseStart_558173 := by decide
  rcases family_descends (prefixWord ++ tailWord_558173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558184 : List Nat := [2, 1, 4, 4, 1, 1, 9]
def baseStart_558184 : Nat := 118140960795 + 558184 * 2 ^ 59
def prefixEnd_558184 : Nat := 4983230072969 + 3 ^ 40 * 558184 * 2
def baseEnd_558184 : Nat := 7076955201218502129209

theorem tailTrace_558184 : CollatzResearch.WordTrace tailWord_558184 prefixEnd_558184 7076955201218502129209 := by
  unfold tailWord_558184
  simp only [CollatzResearch.WordTrace]
  refine ⟨10179321504901086541340803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13572428673201448721787737 10179321504901086541340803)
  ·
    refine ⟨15268982257351629812011205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10179321504901086541340803 15268982257351629812011205)
    ·
      refine ⟨2862934173253430589752101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15268982257351629812011205 2862934173253430589752101)
      ·
        refine ⟨536800157485018235578519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2862934173253430589752101 536800157485018235578519)
        ·
          refine ⟨805200236227527353367779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 536800157485018235578519 805200236227527353367779)
          ·
            refine ⟨1207800354341291030051669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 805200236227527353367779 1207800354341291030051669)
            ·
              refine ⟨7076955201218502129209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1207800354341291030051669 7076955201218502129209)
              ·
                rfl

theorem cell22_558184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 9].length) (baseStart_558184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_558184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_558184 prefixEnd_558184 := by exact prefixLift 558184
  have htrace : WordTrace (prefixWord ++ tailWord_558184) baseStart_558184 baseEnd_558184 := by
    simpa [prefixWord, tailWord_558184, baseEnd_558184] using wordTrace_append hprefix tailTrace_558184
  have hstable : (prefixWord ++ tailWord_558184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558184).length < 2 ^ (prefixWord ++ tailWord_558184).sum := by decide
  have hdescent : baseEnd_558184 < baseStart_558184 := by decide
  rcases family_descends (prefixWord ++ tailWord_558184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558199 : List Nat := [1, 1, 3, 1, 1, 4, 4, 1, 3, 3]
def baseStart_558199 : Nat := 118140960795 + 558199 * 2 ^ 59
def prefixEnd_558199 : Nat := 4983230072969 + 3 ^ 40 * 558199 * 2
def baseEnd_558199 : Nat := 191082925239444518363597

theorem tailTrace_558199 : CollatzResearch.WordTrace tailWord_558199 prefixEnd_558199 191082925239444518363597 := by
  unfold tailWord_558199
  simp only [CollatzResearch.WordTrace]
  refine ⟨20359190104747830644477651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13572793403165220429651767 20359190104747830644477651)
  ·
    refine ⟨30538785157121745966716477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20359190104747830644477651 30538785157121745966716477)
    ·
      refine ⟨11452044433920654737518679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30538785157121745966716477 11452044433920654737518679)
      ·
        refine ⟨17178066650880982106278019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11452044433920654737518679 17178066650880982106278019)
        ·
          refine ⟨25767099976321473159417029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17178066650880982106278019 25767099976321473159417029)
          ·
            refine ⟨4831331245560276217390693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25767099976321473159417029 4831331245560276217390693)
            ·
              refine ⟨905874608542551790760755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4831331245560276217390693 905874608542551790760755)
              ·
                refine ⟨1358811912813827686141133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 905874608542551790760755 1358811912813827686141133)
                ·
                  refine ⟨509554467305185382302925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1358811912813827686141133 509554467305185382302925)
                  ·
                    refine ⟨191082925239444518363597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 509554467305185382302925 191082925239444518363597)
                    ·
                      rfl

theorem cell22_558199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 3, 3].length) (baseStart_558199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_558199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_558199 prefixEnd_558199 := by exact prefixLift 558199
  have htrace : WordTrace (prefixWord ++ tailWord_558199) baseStart_558199 baseEnd_558199 := by
    simpa [prefixWord, tailWord_558199, baseEnd_558199] using wordTrace_append hprefix tailTrace_558199
  have hstable : (prefixWord ++ tailWord_558199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558199).length < 2 ^ (prefixWord ++ tailWord_558199).sum := by decide
  have hdescent : baseEnd_558199 < baseStart_558199 := by decide
  rcases family_descends (prefixWord ++ tailWord_558199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558276 : List Nat := [2, 3, 3, 1, 3, 1, 1, 1, 3, 4]
def baseStart_558276 : Nat := 118140960795 + 558276 * 2 ^ 59
def prefixEnd_558276 : Nat := 4983230072969 + 3 ^ 40 * 558276 * 2
def baseEnd_558276 : Nat := 191109283913041984188361

theorem tailTrace_558276 : CollatzResearch.WordTrace tailWord_558276 prefixEnd_558276 191109283913041984188361 := by
  unfold tailWord_558276
  simp only [CollatzResearch.WordTrace]
  refine ⟨10180999262734436397515341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13574665683645915196687121 10180999262734436397515341)
  ·
    refine ⟨3817874723525413649068253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10180999262734436397515341 3817874723525413649068253)
    ·
      refine ⟨1431703021322030118400595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3817874723525413649068253 1431703021322030118400595)
      ·
        refine ⟨2147554531983045177600893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1431703021322030118400595 2147554531983045177600893)
        ·
          refine ⟨805332949493641941600335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2147554531983045177600893 805332949493641941600335)
          ·
            refine ⟨1207999424240462912400503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 805332949493641941600335 1207999424240462912400503)
            ·
              refine ⟨1811999136360694368600755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1207999424240462912400503 1811999136360694368600755)
              ·
                refine ⟨2717998704541041552901133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1811999136360694368600755 2717998704541041552901133)
                ·
                  refine ⟨1019249514202890582337925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2717998704541041552901133 1019249514202890582337925)
                  ·
                    refine ⟨191109283913041984188361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1019249514202890582337925 191109283913041984188361)
                    ·
                      rfl

theorem cell22_558276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_558276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_558276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_558276 prefixEnd_558276 := by exact prefixLift 558276
  have htrace : WordTrace (prefixWord ++ tailWord_558276) baseStart_558276 baseEnd_558276 := by
    simpa [prefixWord, tailWord_558276, baseEnd_558276] using wordTrace_append hprefix tailTrace_558276
  have hstable : (prefixWord ++ tailWord_558276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558276).length < 2 ^ (prefixWord ++ tailWord_558276).sum := by decide
  have hdescent : baseEnd_558276 < baseStart_558276 := by decide
  rcases family_descends (prefixWord ++ tailWord_558276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558293 : List Nat := [1, 3, 2, 4, 1, 2, 3, 1, 1, 4]
def baseStart_558293 : Nat := 118140960795 + 558293 * 2 ^ 59
def prefixEnd_558293 : Nat := 4983230072969 + 3 ^ 40 * 558293 * 2
def baseEnd_558293 : Nat := 191115103360459606513309

theorem tailTrace_558293 : CollatzResearch.WordTrace tailWord_558293 prefixEnd_558293 191115103360459606513309 := by
  unfold tailWord_558293
  simp only [CollatzResearch.WordTrace]
  refine ⟨20362618566407284698399533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13575079044271523132266355 20362618566407284698399533)
  ·
    refine ⟨7635981962402731761899825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20362618566407284698399533 7635981962402731761899825)
    ·
      refine ⟨5726986471802048821424869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7635981962402731761899825 5726986471802048821424869)
      ·
        refine ⟨1073809963462884154017163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5726986471802048821424869 1073809963462884154017163)
        ·
          refine ⟨1610714945194326231025745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1073809963462884154017163 1610714945194326231025745)
          ·
            refine ⟨1208036208895744673269309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1610714945194326231025745 1208036208895744673269309)
            ·
              refine ⟨453013578335904252475991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1208036208895744673269309 453013578335904252475991)
              ·
                refine ⟨679520367503856378713987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 453013578335904252475991 679520367503856378713987)
                ·
                  refine ⟨1019280551255784568070981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 679520367503856378713987 1019280551255784568070981)
                  ·
                    refine ⟨191115103360459606513309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1019280551255784568070981 191115103360459606513309)
                    ·
                      rfl

theorem cell22_558293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 1, 1, 4].length) (baseStart_558293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_558293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_558293 prefixEnd_558293 := by exact prefixLift 558293
  have htrace : WordTrace (prefixWord ++ tailWord_558293) baseStart_558293 baseEnd_558293 := by
    simpa [prefixWord, tailWord_558293, baseEnd_558293] using wordTrace_append hprefix tailTrace_558293
  have hstable : (prefixWord ++ tailWord_558293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558293).length < 2 ^ (prefixWord ++ tailWord_558293).sum := by decide
  have hdescent : baseEnd_558293 < baseStart_558293 := by decide
  rcases family_descends (prefixWord ++ tailWord_558293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558304 : List Nat := [2, 1, 1, 3, 1, 4, 2, 2, 2, 4]
def baseStart_558304 : Nat := 118140960795 + 558304 * 2 ^ 59
def prefixEnd_558304 : Nat := 4983230072969 + 3 ^ 40 * 558304 * 2
def baseEnd_558304 : Nat := 191118868885259244488275

theorem tailTrace_558304 : CollatzResearch.WordTrace tailWord_558304 prefixEnd_558304 191118868885259244488275 := by
  unfold tailWord_558304
  simp only [CollatzResearch.WordTrace]
  refine ⟨10181509884683716788524983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13575346512911622384699977 10181509884683716788524983)
  ·
    refine ⟨15272264827025575182787475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10181509884683716788524983 15272264827025575182787475)
    ·
      refine ⟨22908397240538362774181213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15272264827025575182787475 22908397240538362774181213)
      ·
        refine ⟨8590648965201886040317955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22908397240538362774181213 8590648965201886040317955)
        ·
          refine ⟨12885973447802829060476933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8590648965201886040317955 12885973447802829060476933)
          ·
            refine ⟨2416120021463030448839425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12885973447802829060476933 2416120021463030448839425)
            ·
              refine ⟨1812090016097272836629569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2416120021463030448839425 1812090016097272836629569)
              ·
                refine ⟨1359067512072954627472177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1812090016097272836629569 1359067512072954627472177)
                ·
                  refine ⟨1019300634054715970604133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1359067512072954627472177 1019300634054715970604133)
                  ·
                    refine ⟨191118868885259244488275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1019300634054715970604133 191118868885259244488275)
                    ·
                      rfl

theorem cell22_558304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 2, 4].length) (baseStart_558304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_558304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_558304 prefixEnd_558304 := by exact prefixLift 558304
  have htrace : WordTrace (prefixWord ++ tailWord_558304) baseStart_558304 baseEnd_558304 := by
    simpa [prefixWord, tailWord_558304, baseEnd_558304] using wordTrace_append hprefix tailTrace_558304
  have hstable : (prefixWord ++ tailWord_558304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558304).length < 2 ^ (prefixWord ++ tailWord_558304).sum := by decide
  have hdescent : baseEnd_558304 < baseStart_558304 := by decide
  rcases family_descends (prefixWord ++ tailWord_558304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558368 : List Nat := [2, 1, 1, 5, 3, 1, 2, 1, 3, 3]
def baseStart_558368 : Nat := 118140960795 + 558368 * 2 ^ 59
def prefixEnd_558368 : Nat := 4983230072969 + 3 ^ 40 * 558368 * 2
def baseEnd_558368 : Nat := 191140777393184410888079

theorem tailTrace_558368 : CollatzResearch.WordTrace tailWord_558368 prefixEnd_558368 191140777393184410888079 := by
  unfold tailWord_558368
  simp only [CollatzResearch.WordTrace]
  refine ⟨10182677020567786253689879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13576902694090381671586505 10182677020567786253689879)
  ·
    refine ⟨15274015530851679380534819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10182677020567786253689879 15274015530851679380534819)
    ·
      refine ⟨22911023296277519070802229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15274015530851679380534819 22911023296277519070802229)
      ·
        refine ⟨2147908434026017412887709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22911023296277519070802229 2147908434026017412887709)
        ·
          refine ⟨805465662759756529832891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2147908434026017412887709 805465662759756529832891)
          ·
            refine ⟨1208198494139634794749337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 805465662759756529832891 1208198494139634794749337)
            ·
              refine ⟨906148870604726096062003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1208198494139634794749337 906148870604726096062003)
              ·
                refine ⟨1359223305907089144093005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 906148870604726096062003 1359223305907089144093005)
                ·
                  refine ⟨509708739715158429034877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1359223305907089144093005 509708739715158429034877)
                  ·
                    refine ⟨191140777393184410888079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 509708739715158429034877 191140777393184410888079)
                    ·
                      rfl

theorem cell22_558368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 3, 3].length) (baseStart_558368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_558368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_558368 prefixEnd_558368 := by exact prefixLift 558368
  have htrace : WordTrace (prefixWord ++ tailWord_558368) baseStart_558368 baseEnd_558368 := by
    simpa [prefixWord, tailWord_558368, baseEnd_558368] using wordTrace_append hprefix tailTrace_558368
  have hstable : (prefixWord ++ tailWord_558368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558368).length < 2 ^ (prefixWord ++ tailWord_558368).sum := by decide
  have hdescent : baseEnd_558368 < baseStart_558368 := by decide
  rcases family_descends (prefixWord ++ tailWord_558368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558426 : List Nat := [3, 1, 1, 2, 1, 2, 2, 6, 4]
def baseStart_558426 : Nat := 118140960795 + 558426 * 2 ^ 59
def prefixEnd_558426 : Nat := 4983230072969 + 3 ^ 40 * 558426 * 2
def baseEnd_558426 : Nat := 63720210659497197645967

theorem tailTrace_558426 : CollatzResearch.WordTrace tailWord_558426 prefixEnd_558426 63720210659497197645967 := by
  unfold tailWord_558426
  simp only [CollatzResearch.WordTrace]
  refine ⟨5091867368731362103247783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13578312983283632275327421 5091867368731362103247783)
  ·
    refine ⟨7637801053097043154871675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5091867368731362103247783 7637801053097043154871675)
    ·
      refine ⟨11456701579645564732307513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7637801053097043154871675 11456701579645564732307513)
      ·
        refine ⟨8592526184734173549230635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11456701579645564732307513 8592526184734173549230635)
        ·
          refine ⟨12888789277101260323845953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8592526184734173549230635 12888789277101260323845953)
          ·
            refine ⟨9666591957825945242884465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12888789277101260323845953 9666591957825945242884465)
            ·
              refine ⟨7249943968369458932163349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9666591957825945242884465 7249943968369458932163349)
              ·
                refine ⟨339841123517318387445157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7249943968369458932163349 339841123517318387445157)
                ·
                  refine ⟨63720210659497197645967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 339841123517318387445157 63720210659497197645967)
                  ·
                    rfl

theorem cell22_558426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 6, 4].length) (baseStart_558426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_558426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_558426 prefixEnd_558426 := by exact prefixLift 558426
  have htrace : WordTrace (prefixWord ++ tailWord_558426) baseStart_558426 baseEnd_558426 := by
    simpa [prefixWord, tailWord_558426, baseEnd_558426] using wordTrace_append hprefix tailTrace_558426
  have hstable : (prefixWord ++ tailWord_558426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558426).length < 2 ^ (prefixWord ++ tailWord_558426).sum := by decide
  have hdescent : baseEnd_558426 < baseStart_558426 := by decide
  rcases family_descends (prefixWord ++ tailWord_558426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558488 : List Nat := [2, 1, 2, 5, 2, 2, 1, 7]
def baseStart_558488 : Nat := 118140960795 + 558488 * 2 ^ 59
def prefixEnd_558488 : Nat := 4983230072969 + 3 ^ 40 * 558488 * 2
def baseEnd_558488 : Nat := 21242428427282677543079

theorem tailTrace_558488 : CollatzResearch.WordTrace tailWord_558488 prefixEnd_558488 21242428427282677543079 := by
  unfold tailWord_558488
  simp only [CollatzResearch.WordTrace]
  refine ⟨10184865400350416500874059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13579820533800555334498745 10184865400350416500874059)
  ·
    refine ⟨15277298100525624751311089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10184865400350416500874059 15277298100525624751311089)
    ·
      refine ⟨11457973575394218563483317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15277298100525624751311089 11457973575394218563483317)
      ·
        refine ⟨1074185022693207990326561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11457973575394218563483317 1074185022693207990326561)
        ·
          refine ⟨805638767019905992744921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1074185022693207990326561 805638767019905992744921)
          ·
            refine ⟨604229075264929494558691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 805638767019905992744921 604229075264929494558691)
            ·
              refine ⟨906343612897394241838037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 604229075264929494558691 906343612897394241838037)
              ·
                refine ⟨21242428427282677543079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 906343612897394241838037 21242428427282677543079)
                ·
                  rfl

theorem cell22_558488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 7].length) (baseStart_558488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_558488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_558488 prefixEnd_558488 := by exact prefixLift 558488
  have htrace : WordTrace (prefixWord ++ tailWord_558488) baseStart_558488 baseEnd_558488 := by
    simpa [prefixWord, tailWord_558488, baseEnd_558488] using wordTrace_append hprefix tailTrace_558488
  have hstable : (prefixWord ++ tailWord_558488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558488).length < 2 ^ (prefixWord ++ tailWord_558488).sum := by decide
  have hdescent : baseEnd_558488 < baseStart_558488 := by decide
  rcases family_descends (prefixWord ++ tailWord_558488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558503 : List Nat := [1, 1, 6, 1, 1, 1, 3, 2, 3, 3]
def baseStart_558503 : Nat := 118140960795 + 558503 * 2 ^ 59
def prefixEnd_558503 : Nat := 4983230072969 + 3 ^ 40 * 558503 * 2
def baseEnd_558503 : Nat := 191186990652089058762665

theorem tailTrace_558503 : CollatzResearch.WordTrace tailWord_558503 prefixEnd_558503 191186990652089058762665 := by
  unfold tailWord_558503
  simp only [CollatzResearch.WordTrace]
  refine ⟨20370277895646490563544163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13580185263764327042362775 20370277895646490563544163)
  ·
    refine ⟨30555416843469735845316245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20370277895646490563544163 30555416843469735845316245)
    ·
      refine ⟨1432285164537643867749199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 30555416843469735845316245 1432285164537643867749199)
      ·
        refine ⟨2148427746806465801623799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1432285164537643867749199 2148427746806465801623799)
        ·
          refine ⟨3222641620209698702435699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2148427746806465801623799 3222641620209698702435699)
          ·
            refine ⟨4833962430314548053653549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3222641620209698702435699 4833962430314548053653549)
            ·
              refine ⟨1812735911367955520120081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4833962430314548053653549 1812735911367955520120081)
              ·
                refine ⟨1359551933525966640090061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1812735911367955520120081 1359551933525966640090061)
                ·
                  refine ⟨509831975072237490033773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1359551933525966640090061 509831975072237490033773)
                  ·
                    refine ⟨191186990652089058762665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 509831975072237490033773 191186990652089058762665)
                    ·
                      rfl

theorem cell22_558503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_558503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_558503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_558503 prefixEnd_558503 := by exact prefixLift 558503
  have htrace : WordTrace (prefixWord ++ tailWord_558503) baseStart_558503 baseEnd_558503 := by
    simpa [prefixWord, tailWord_558503, baseEnd_558503] using wordTrace_append hprefix tailTrace_558503
  have hstable : (prefixWord ++ tailWord_558503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558503).length < 2 ^ (prefixWord ++ tailWord_558503).sum := by decide
  have hdescent : baseEnd_558503 < baseStart_558503 := by decide
  rcases family_descends (prefixWord ++ tailWord_558503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558544 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 10]
def baseStart_558544 : Nat := 118140960795 + 558544 * 2 ^ 59
def prefixEnd_558544 : Nat := 4983230072969 + 3 ^ 40 * 558544 * 2
def baseEnd_558544 : Nat := 63733675263326206162513

theorem tailTrace_558544 : CollatzResearch.WordTrace tailWord_558544 prefixEnd_558544 63733675263326206162513 := by
  unfold tailWord_558544
  simp only [CollatzResearch.WordTrace]
  refine ⟨10185886644248977282893343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13581182192331969710524457 10185886644248977282893343)
  ·
    refine ⟨15278829966373465924340015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10185886644248977282893343 15278829966373465924340015)
    ·
      refine ⟨22918244949560198886510023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15278829966373465924340015 22918244949560198886510023)
      ·
        refine ⟨34377367424340298329765035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22918244949560198886510023 34377367424340298329765035)
        ·
          refine ⟨51566051136510447494647553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34377367424340298329765035 51566051136510447494647553)
          ·
            refine ⟨38674538352382835620985665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51566051136510447494647553 38674538352382835620985665)
            ·
              refine ⟨29005903764287126715739249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38674538352382835620985665 29005903764287126715739249)
              ·
                refine ⟨21754427823215345036804437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29005903764287126715739249 21754427823215345036804437)
                ·
                  refine ⟨63733675263326206162513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 21754427823215345036804437 63733675263326206162513)
                  ·
                    rfl

theorem cell22_558544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 10].length) (baseStart_558544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_558544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_558544 prefixEnd_558544 := by exact prefixLift 558544
  have htrace : WordTrace (prefixWord ++ tailWord_558544) baseStart_558544 baseEnd_558544 := by
    simpa [prefixWord, tailWord_558544, baseEnd_558544] using wordTrace_append hprefix tailTrace_558544
  have hstable : (prefixWord ++ tailWord_558544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558544).length < 2 ^ (prefixWord ++ tailWord_558544).sum := by decide
  have hdescent : baseEnd_558544 < baseStart_558544 := by decide
  rcases family_descends (prefixWord ++ tailWord_558544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558561 : List Nat := [1, 2, 3, 1, 2, 3, 2, 2, 6]
def baseStart_558561 : Nat := 118140960795 + 558561 * 2 ^ 59
def prefixEnd_558561 : Nat := 4983230072969 + 3 ^ 40 * 558561 * 2
def baseEnd_558561 : Nat := 63735615079132080270829

theorem tailTrace_558561 : CollatzResearch.WordTrace tailWord_558561 prefixEnd_558561 63735615079132080270829 := by
  unfold tailWord_558561
  simp only [CollatzResearch.WordTrace]
  refine ⟨20372393329436366469155537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13581595552957577646103691 20372393329436366469155537)
  ·
    refine ⟨15279294997077274851866653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20372393329436366469155537 15279294997077274851866653)
    ·
      refine ⟨5729735623903978069449995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15279294997077274851866653 5729735623903978069449995)
      ·
        refine ⟨8594603435855967104174993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5729735623903978069449995 8594603435855967104174993)
        ·
          refine ⟨6445952576891975328131245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8594603435855967104174993 6445952576891975328131245)
          ·
            refine ⟨2417232216334490748049217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6445952576891975328131245 2417232216334490748049217)
            ·
              refine ⟨1812924162250868061036913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2417232216334490748049217 1812924162250868061036913)
              ·
                refine ⟨1359693121688151045777685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1812924162250868061036913 1359693121688151045777685)
                ·
                  refine ⟨63735615079132080270829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1359693121688151045777685 63735615079132080270829)
                  ·
                    rfl

theorem cell22_558561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 6].length) (baseStart_558561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_558561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_558561 prefixEnd_558561 := by exact prefixLift 558561
  have htrace : WordTrace (prefixWord ++ tailWord_558561) baseStart_558561 baseEnd_558561 := by
    simpa [prefixWord, tailWord_558561, baseEnd_558561] using wordTrace_append hprefix tailTrace_558561
  have hstable : (prefixWord ++ tailWord_558561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558561).length < 2 ^ (prefixWord ++ tailWord_558561).sum := by decide
  have hdescent : baseEnd_558561 < baseStart_558561 := by decide
  rcases family_descends (prefixWord ++ tailWord_558561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558563 : List Nat := [1, 1, 1, 6, 2, 1, 1, 4, 1, 4]
def baseStart_558563 : Nat := 118140960795 + 558563 * 2 ^ 59
def prefixEnd_558563 : Nat := 4983230072969 + 3 ^ 40 * 558563 * 2
def baseEnd_558563 : Nat := 191207529878268902262481

theorem tailTrace_558563 : CollatzResearch.WordTrace tailWord_558563 prefixEnd_558563 191207529878268902262481 := by
  unfold tailWord_558563
  simp only [CollatzResearch.WordTrace]
  refine ⟨20372466275429120810728343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13581644183619413873818895 20372466275429120810728343)
  ·
    refine ⟨30558699413143681216092515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20372466275429120810728343 30558699413143681216092515)
    ·
      refine ⟨45838049119715521824138773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30558699413143681216092515 45838049119715521824138773)
      ·
        refine ⟨2148658552486665085506505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 45838049119715521824138773 2148658552486665085506505)
        ·
          refine ⟨1611493914364998814129879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2148658552486665085506505 1611493914364998814129879)
          ·
            refine ⟨2417240871547498221194819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1611493914364998814129879 2417240871547498221194819)
            ·
              refine ⟨3625861307321247331792229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2417240871547498221194819 3625861307321247331792229)
              ·
                refine ⟨679848995122733874711043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3625861307321247331792229 679848995122733874711043)
                ·
                  refine ⟨1019773492684100812066565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 679848995122733874711043 1019773492684100812066565)
                  ·
                    refine ⟨191207529878268902262481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1019773492684100812066565 191207529878268902262481)
                    ·
                      rfl

theorem cell22_558563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 4, 1, 4].length) (baseStart_558563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_558563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_558563 prefixEnd_558563 := by exact prefixLift 558563
  have htrace : WordTrace (prefixWord ++ tailWord_558563) baseStart_558563 baseEnd_558563 := by
    simpa [prefixWord, tailWord_558563, baseEnd_558563] using wordTrace_append hprefix tailTrace_558563
  have hstable : (prefixWord ++ tailWord_558563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558563).length < 2 ^ (prefixWord ++ tailWord_558563).sum := by decide
  have hdescent : baseEnd_558563 < baseStart_558563 := by decide
  rcases family_descends (prefixWord ++ tailWord_558563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558646 : List Nat := [5, 1, 2, 1, 4, 1, 2, 2, 4]
def baseStart_558646 : Nat := 118140960795 + 558646 * 2 ^ 59
def prefixEnd_558646 : Nat := 4983230072969 + 3 ^ 40 * 558646 * 2
def baseEnd_558646 : Nat := 63745314158161450812409

theorem tailTrace_558646 : CollatzResearch.WordTrace tailWord_558646 prefixEnd_558646 63745314158161450812409 := by
  unfold tailWord_558646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1273468345883026624124987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13583662356085617323999861 1273468345883026624124987)
  ·
    refine ⟨1910202518824539936187481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1273468345883026624124987 1910202518824539936187481)
    ·
      refine ⟨1432651889118404952140611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1910202518824539936187481 1432651889118404952140611)
      ·
        refine ⟨2148977833677607428210917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1432651889118404952140611 2148977833677607428210917)
        ·
          refine ⟨402933343814551392789547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2148977833677607428210917 402933343814551392789547)
          ·
            refine ⟨604400015721827089184321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 402933343814551392789547 604400015721827089184321)
            ·
              refine ⟨453300011791370316888241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 604400015721827089184321 453300011791370316888241)
              ·
                refine ⟨339975008843527737666181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 453300011791370316888241 339975008843527737666181)
                ·
                  refine ⟨63745314158161450812409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 339975008843527737666181 63745314158161450812409)
                  ·
                    rfl

theorem cell22_558646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_558646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_558646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_558646 prefixEnd_558646 := by exact prefixLift 558646
  have htrace : WordTrace (prefixWord ++ tailWord_558646) baseStart_558646 baseEnd_558646 := by
    simpa [prefixWord, tailWord_558646, baseEnd_558646] using wordTrace_append hprefix tailTrace_558646
  have hstable : (prefixWord ++ tailWord_558646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558646).length < 2 ^ (prefixWord ++ tailWord_558646).sum := by decide
  have hdescent : baseEnd_558646 < baseStart_558646 := by decide
  rcases family_descends (prefixWord ++ tailWord_558646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558668 : List Nat := [2, 2, 1, 3, 1, 3, 2, 3, 5]
def baseStart_558668 : Nat := 118140960795 + 558668 * 2 ^ 59
def prefixEnd_558668 : Nat := 4983230072969 + 3 ^ 40 * 558668 * 2
def baseEnd_558668 : Nat := 63747824508027876129053

theorem tailTrace_558668 : CollatzResearch.WordTrace tailWord_558668 prefixEnd_558668 63747824508027876129053 := by
  unfold tailWord_558668
  simp only [CollatzResearch.WordTrace]
  refine ⟨10188147970024361871650329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13584197293365815828867105 10188147970024361871650329)
  ·
    refine ⟨7641110977518271403737747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10188147970024361871650329 7641110977518271403737747)
    ·
      refine ⟨11461666466277407105606621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7641110977518271403737747 11461666466277407105606621)
      ·
        refine ⟨4298124924854027664602483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11461666466277407105606621 4298124924854027664602483)
        ·
          refine ⟨6447187387281041496903725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4298124924854027664602483 6447187387281041496903725)
          ·
            refine ⟨2417695270230390561338897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6447187387281041496903725 2417695270230390561338897)
            ·
              refine ⟨1813271452672792921004173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2417695270230390561338897 1813271452672792921004173)
              ·
                refine ⟨679976794752297345376565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1813271452672792921004173 679976794752297345376565)
                ·
                  refine ⟨63747824508027876129053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 679976794752297345376565 63747824508027876129053)
                  ·
                    rfl

theorem cell22_558668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 3, 5].length) (baseStart_558668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_558668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_558668 prefixEnd_558668 := by exact prefixLift 558668
  have htrace : WordTrace (prefixWord ++ tailWord_558668) baseStart_558668 baseEnd_558668 := by
    simpa [prefixWord, tailWord_558668, baseEnd_558668] using wordTrace_append hprefix tailTrace_558668
  have hstable : (prefixWord ++ tailWord_558668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558668).length < 2 ^ (prefixWord ++ tailWord_558668).sum := by decide
  have hdescent : baseEnd_558668 < baseStart_558668 := by decide
  rcases family_descends (prefixWord ++ tailWord_558668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558702 : List Nat := [4, 1, 2, 2, 3, 2, 1, 2, 5]
def baseStart_558702 : Nat := 118140960795 + 558702 * 2 ^ 59
def prefixEnd_558702 : Nat := 4983230072969 + 3 ^ 40 * 558702 * 2
def baseEnd_558702 : Nat := 63751704139639624345685

theorem tailTrace_558702 : CollatzResearch.WordTrace tailWord_558702 prefixEnd_558702 63751704139639624345685 := by
  unfold tailWord_558702
  simp only [CollatzResearch.WordTrace]
  refine ⟨2547192002740693443754795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13585024014617031700025573 2547192002740693443754795)
  ·
    refine ⟨3820788004111040165632193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2547192002740693443754795 3820788004111040165632193)
    ·
      refine ⟨2865591003083280124224145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3820788004111040165632193 2865591003083280124224145)
      ·
        refine ⟨2149193252312460093168109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2865591003083280124224145 2149193252312460093168109)
        ·
          refine ⟨805947469617172534938041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2149193252312460093168109 805947469617172534938041)
          ·
            refine ⟨604460602212879401203531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 805947469617172534938041 604460602212879401203531)
            ·
              refine ⟨906690903319319101805297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 604460602212879401203531 906690903319319101805297)
              ·
                refine ⟨680018177489489326353973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 906690903319319101805297 680018177489489326353973)
                ·
                  refine ⟨63751704139639624345685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 680018177489489326353973 63751704139639624345685)
                  ·
                    rfl

theorem cell22_558702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 2, 5].length) (baseStart_558702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_558702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_558702 prefixEnd_558702 := by exact prefixLift 558702
  have htrace : WordTrace (prefixWord ++ tailWord_558702) baseStart_558702 baseEnd_558702 := by
    simpa [prefixWord, tailWord_558702, baseEnd_558702] using wordTrace_append hprefix tailTrace_558702
  have hstable : (prefixWord ++ tailWord_558702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558702).length < 2 ^ (prefixWord ++ tailWord_558702).sum := by decide
  have hdescent : baseEnd_558702 < baseStart_558702 := by decide
  rcases family_descends (prefixWord ++ tailWord_558702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558713 : List Nat := [1, 2, 1, 3, 3, 1, 4, 1, 6]
def baseStart_558713 : Nat := 118140960795 + 558713 * 2 ^ 59
def prefixEnd_558713 : Nat := 4983230072969 + 3 ^ 40 * 558713 * 2
def baseEnd_558713 : Nat := 63752959314572837004007

theorem tailTrace_558713 : CollatzResearch.WordTrace tailWord_558713 prefixEnd_558713 63752959314572837004007 := by
  unfold tailWord_558713
  simp only [CollatzResearch.WordTrace]
  refine ⟨20377937224885696428688793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13585291483257130952459195 20377937224885696428688793)
  ·
    refine ⟨15283452918664272321516595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20377937224885696428688793 15283452918664272321516595)
    ·
      refine ⟨22925179377996408482274893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15283452918664272321516595 22925179377996408482274893)
      ·
        refine ⟨8596942266748653180853085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22925179377996408482274893 8596942266748653180853085)
        ·
          refine ⟨3223853350030744942819907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8596942266748653180853085 3223853350030744942819907)
          ·
            refine ⟨4835780025046117414229861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3223853350030744942819907 4835780025046117414229861)
            ·
              refine ⟨906708754696147015168099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4835780025046117414229861 906708754696147015168099)
              ·
                refine ⟨1360063132044220522752149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 906708754696147015168099 1360063132044220522752149)
                ·
                  refine ⟨63752959314572837004007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1360063132044220522752149 63752959314572837004007)
                  ·
                    rfl

theorem cell22_558713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 6].length) (baseStart_558713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_558713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_558713 prefixEnd_558713 := by exact prefixLift 558713
  have htrace : WordTrace (prefixWord ++ tailWord_558713) baseStart_558713 baseEnd_558713 := by
    simpa [prefixWord, tailWord_558713, baseEnd_558713] using wordTrace_append hprefix tailTrace_558713
  have hstable : (prefixWord ++ tailWord_558713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558713).length < 2 ^ (prefixWord ++ tailWord_558713).sum := by decide
  have hdescent : baseEnd_558713 < baseStart_558713 := by decide
  rcases family_descends (prefixWord ++ tailWord_558713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558743 : List Nat := [1, 1, 3, 3, 2, 2, 2, 1, 1, 6]
def baseStart_558743 : Nat := 118140960795 + 558743 * 2 ^ 59
def prefixEnd_558743 : Nat := 4983230072969 + 3 ^ 40 * 558743 * 2
def baseEnd_558743 : Nat := 191269147556808432761929

theorem tailTrace_558743 : CollatzResearch.WordTrace tailWord_558743 prefixEnd_558743 191269147556808432761929 := by
  unfold tailWord_558743
  simp only [CollatzResearch.WordTrace]
  refine ⟨20379031414777011552280883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13586020943184674368187255 20379031414777011552280883)
  ·
    refine ⟨30568547122165517328421325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20379031414777011552280883 30568547122165517328421325)
    ·
      refine ⟨11463205170812068998157997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30568547122165517328421325 11463205170812068998157997)
      ·
        refine ⟨4298701939054525874309249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11463205170812068998157997 4298701939054525874309249)
        ·
          refine ⟨3224026454290894405731937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4298701939054525874309249 3224026454290894405731937)
          ·
            refine ⟨2418019840718170804298953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3224026454290894405731937 2418019840718170804298953)
            ·
              refine ⟨1813514880538628103224215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2418019840718170804298953 1813514880538628103224215)
              ·
                refine ⟨2720272320807942154836323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1813514880538628103224215 2720272320807942154836323)
                ·
                  refine ⟨4080408481211913232254485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2720272320807942154836323 4080408481211913232254485)
                  ·
                    refine ⟨191269147556808432761929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4080408481211913232254485 191269147556808432761929)
                    ·
                      rfl

theorem cell22_558743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 6].length) (baseStart_558743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_558743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_558743 prefixEnd_558743 := by exact prefixLift 558743
  have htrace : WordTrace (prefixWord ++ tailWord_558743) baseStart_558743 baseEnd_558743 := by
    simpa [prefixWord, tailWord_558743, baseEnd_558743] using wordTrace_append hprefix tailTrace_558743
  have hstable : (prefixWord ++ tailWord_558743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558743).length < 2 ^ (prefixWord ++ tailWord_558743).sum := by decide
  have hdescent : baseEnd_558743 < baseStart_558743 := by decide
  rcases family_descends (prefixWord ++ tailWord_558743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558807 : List Nat := [1, 1, 3, 2, 1, 3, 2, 5, 1, 3]
def baseStart_558807 : Nat := 118140960795 + 558807 * 2 ^ 59
def prefixEnd_558807 : Nat := 4983230072969 + 3 ^ 40 * 558807 * 2
def baseEnd_558807 : Nat := 191291056064733599161733

theorem tailTrace_558807 : CollatzResearch.WordTrace tailWord_558807 prefixEnd_558807 191291056064733599161733 := by
  unfold tailWord_558807
  simp only [CollatzResearch.WordTrace]
  refine ⟨20381365686545150482610675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13587577124363433655073783 20381365686545150482610675)
  ·
    refine ⟨30572048529817725723916013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20381365686545150482610675 30572048529817725723916013)
    ·
      refine ⟨11464518198681647146468505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30572048529817725723916013 11464518198681647146468505)
      ·
        refine ⟨8598388649011235359851379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11464518198681647146468505 8598388649011235359851379)
        ·
          refine ⟨12897582973516853039777069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8598388649011235359851379 12897582973516853039777069)
          ·
            refine ⟨4836593615068819889916401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12897582973516853039777069 4836593615068819889916401)
            ·
              refine ⟨3627445211301614917437301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4836593615068819889916401 3627445211301614917437301)
              ·
                refine ⟨340072988559526398509747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3627445211301614917437301 340072988559526398509747)
                ·
                  refine ⟨510109482839289597764621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 340072988559526398509747 510109482839289597764621)
                  ·
                    refine ⟨191291056064733599161733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 510109482839289597764621 191291056064733599161733)
                    ·
                      rfl

theorem cell22_558807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 5, 1, 3].length) (baseStart_558807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_558807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_558807 prefixEnd_558807 := by exact prefixLift 558807
  have htrace : WordTrace (prefixWord ++ tailWord_558807) baseStart_558807 baseEnd_558807 := by
    simpa [prefixWord, tailWord_558807, baseEnd_558807] using wordTrace_append hprefix tailTrace_558807
  have hstable : (prefixWord ++ tailWord_558807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558807).length < 2 ^ (prefixWord ++ tailWord_558807).sum := by decide
  have hdescent : baseEnd_558807 < baseStart_558807 := by decide
  rcases family_descends (prefixWord ++ tailWord_558807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558820 : List Nat := [2, 3, 1, 1, 1, 3, 4, 2, 5]
def baseStart_558820 : Nat := 118140960795 + 558820 * 2 ^ 59
def prefixEnd_558820 : Nat := 4983230072969 + 3 ^ 40 * 558820 * 2
def baseEnd_558820 : Nat := 63765168743468632862231

theorem tailTrace_558820 : CollatzResearch.WordTrace tailWord_558820 prefixEnd_558820 63765168743468632862231 := by
  unfold tailWord_558820
  simp only [CollatzResearch.WordTrace]
  refine ⟨10190919917749026851416957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13587893223665369135222609 10190919917749026851416957)
  ·
    refine ⟨3821594969155885069281359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10190919917749026851416957 3821594969155885069281359)
    ·
      refine ⟨5732392453733827603922039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3821594969155885069281359 5732392453733827603922039)
      ·
        refine ⟨8598588680600741405883059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5732392453733827603922039 8598588680600741405883059)
        ·
          refine ⟨12897883020901112108824589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8598588680600741405883059 12897883020901112108824589)
          ·
            refine ⟨4836706132837917040809221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12897883020901112108824589 4836706132837917040809221)
            ·
              refine ⟨906882399907109445151729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4836706132837917040809221 906882399907109445151729)
              ·
                refine ⟨680161799930332083863797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 906882399907109445151729 680161799930332083863797)
                ·
                  refine ⟨63765168743468632862231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 680161799930332083863797 63765168743468632862231)
                  ·
                    rfl

theorem cell22_558820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_558820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_558820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_558820 prefixEnd_558820 := by exact prefixLift 558820
  have htrace : WordTrace (prefixWord ++ tailWord_558820) baseStart_558820 baseEnd_558820 := by
    simpa [prefixWord, tailWord_558820, baseEnd_558820] using wordTrace_append hprefix tailTrace_558820
  have hstable : (prefixWord ++ tailWord_558820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558820).length < 2 ^ (prefixWord ++ tailWord_558820).sum := by decide
  have hdescent : baseEnd_558820 < baseStart_558820 := by decide
  rcases family_descends (prefixWord ++ tailWord_558820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558824 : List Nat := [2, 1, 4, 1, 3, 2, 1, 4, 1, 3]
def baseStart_558824 : Nat := 118140960795 + 558824 * 2 ^ 59
def prefixEnd_558824 : Nat := 4983230072969 + 3 ^ 40 * 558824 * 2
def baseEnd_558824 : Nat := 191296875512151221486681

theorem tailTrace_558824 : CollatzResearch.WordTrace tailWord_558824 prefixEnd_558824 191296875512151221486681 := by
  unfold tailWord_558824
  simp only [CollatzResearch.WordTrace]
  refine ⟨10190992863741781192989763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13587990484989041590653017 10190992863741781192989763)
  ·
    refine ⟨15286489295612671789484645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10190992863741781192989763 15286489295612671789484645)
    ·
      refine ⟨2866216742927375960528371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15286489295612671789484645 2866216742927375960528371)
      ·
        refine ⟨4299325114391063940792557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2866216742927375960528371 4299325114391063940792557)
        ·
          refine ⟨1612246917896648977797209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4299325114391063940792557 1612246917896648977797209)
          ·
            refine ⟨1209185188422486733347907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1612246917896648977797209 1209185188422486733347907)
            ·
              refine ⟨1813777782633730100021861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1209185188422486733347907 1813777782633730100021861)
              ·
                refine ⟨340083334243824393754099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1813777782633730100021861 340083334243824393754099)
                ·
                  refine ⟨510125001365736590631149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 340083334243824393754099 510125001365736590631149)
                  ·
                    refine ⟨191296875512151221486681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 510125001365736590631149 191296875512151221486681)
                    ·
                      rfl

theorem cell22_558824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_558824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_558824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_558824 prefixEnd_558824 := by exact prefixLift 558824
  have htrace : WordTrace (prefixWord ++ tailWord_558824) baseStart_558824 baseEnd_558824 := by
    simpa [prefixWord, tailWord_558824, baseEnd_558824] using wordTrace_append hprefix tailTrace_558824
  have hstable : (prefixWord ++ tailWord_558824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558824).length < 2 ^ (prefixWord ++ tailWord_558824).sum := by decide
  have hdescent : baseEnd_558824 < baseStart_558824 := by decide
  rcases family_descends (prefixWord ++ tailWord_558824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558848 : List Nat := [2, 1, 1, 2, 1, 1, 2, 6, 6]
def baseStart_558848 : Nat := 118140960795 + 558848 * 2 ^ 59
def prefixEnd_558848 : Nat := 4983230072969 + 3 ^ 40 * 558848 * 2
def baseEnd_558848 : Nat := 63768363734207719628869

theorem tailTrace_558848 : CollatzResearch.WordTrace tailWord_558848 prefixEnd_558848 63768363734207719628869 := by
  unfold tailWord_558848
  simp only [CollatzResearch.WordTrace]
  refine ⟨10191430539698307242426599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13588574052931076323235465 10191430539698307242426599)
  ·
    refine ⟨15287145809547460863639899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10191430539698307242426599 15287145809547460863639899)
    ·
      refine ⟨22930718714321191295459849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15287145809547460863639899 22930718714321191295459849)
      ·
        refine ⟨17198039035740893471594887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22930718714321191295459849 17198039035740893471594887)
        ·
          refine ⟨25797058553611340207392331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17198039035740893471594887 25797058553611340207392331)
          ·
            refine ⟨38695587830417010311088497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25797058553611340207392331 38695587830417010311088497)
            ·
              refine ⟨29021690872812757733316373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38695587830417010311088497 29021690872812757733316373)
              ·
                refine ⟨1360391759663098018749205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29021690872812757733316373 1360391759663098018749205)
                ·
                  refine ⟨63768363734207719628869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1360391759663098018749205 63768363734207719628869)
                  ·
                    rfl

theorem cell22_558848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 6].length) (baseStart_558848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_558848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_558848 prefixEnd_558848 := by exact prefixLift 558848
  have htrace : WordTrace (prefixWord ++ tailWord_558848) baseStart_558848 baseEnd_558848 := by
    simpa [prefixWord, tailWord_558848, baseEnd_558848] using wordTrace_append hprefix tailTrace_558848
  have hstable : (prefixWord ++ tailWord_558848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558848).length < 2 ^ (prefixWord ++ tailWord_558848).sum := by decide
  have hdescent : baseEnd_558848 < baseStart_558848 := by decide
  rcases family_descends (prefixWord ++ tailWord_558848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558863 : List Nat := [1, 1, 2, 1, 1, 1, 4, 3, 3, 5]
def baseStart_558863 : Nat := 118140960795 + 558863 * 2 ^ 59
def prefixEnd_558863 : Nat := 4983230072969 + 3 ^ 40 * 558863 * 2
def baseEnd_558863 : Nat := 191310226009168119761561

theorem tailTrace_558863 : CollatzResearch.WordTrace tailWord_558863 prefixEnd_558863 191310226009168119761561 := by
  unfold tailWord_558863
  simp only [CollatzResearch.WordTrace]
  refine ⟨20383408174342272046649243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13588938782894848031099495 20383408174342272046649243)
  ·
    refine ⟨30575112261513408069973865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20383408174342272046649243 30575112261513408069973865)
    ·
      refine ⟨22931334196135056052480399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30575112261513408069973865 22931334196135056052480399)
      ·
        refine ⟨34397001294202584078720599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22931334196135056052480399 34397001294202584078720599)
        ·
          refine ⟨51595501941303876118080899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34397001294202584078720599 51595501941303876118080899)
          ·
            refine ⟨77393252911955814177121349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51595501941303876118080899 77393252911955814177121349)
            ·
              refine ⟨14511234920991715158210253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77393252911955814177121349 14511234920991715158210253)
              ·
                refine ⟨5441713095371893184328845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14511234920991715158210253 5441713095371893184328845)
                ·
                  refine ⟨2040642410764459944123317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5441713095371893184328845 2040642410764459944123317)
                  ·
                    refine ⟨191310226009168119761561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2040642410764459944123317 191310226009168119761561)
                    ·
                      rfl

theorem cell22_558863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 5].length) (baseStart_558863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_558863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_558863 prefixEnd_558863 := by exact prefixLift 558863
  have htrace : WordTrace (prefixWord ++ tailWord_558863) baseStart_558863 baseEnd_558863 := by
    simpa [prefixWord, tailWord_558863, baseEnd_558863] using wordTrace_append hprefix tailTrace_558863
  have hstable : (prefixWord ++ tailWord_558863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558863).length < 2 ^ (prefixWord ++ tailWord_558863).sum := by decide
  have hdescent : baseEnd_558863 < baseStart_558863 := by decide
  rcases family_descends (prefixWord ++ tailWord_558863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558882 : List Nat := [3, 3, 1, 1, 2, 1, 1, 6, 4]
def baseStart_558882 : Nat := 118140960795 + 558882 * 2 ^ 59
def prefixEnd_558882 : Nat := 4983230072969 + 3 ^ 40 * 558882 * 2
def baseEnd_558882 : Nat := 63772243365819467845501

theorem tailTrace_558882 : CollatzResearch.WordTrace tailWord_558882 prefixEnd_558882 63772243365819467845501 := by
  unfold tailWord_558882
  simp only [CollatzResearch.WordTrace]
  refine ⟨5096025290318359572897725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13589400774182292194393933 5096025290318359572897725)
  ·
    refine ⟨1911009483869384839836647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5096025290318359572897725 1911009483869384839836647)
    ·
      refine ⟨2866514225804077259754971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1911009483869384839836647 2866514225804077259754971)
      ·
        refine ⟨4299771338706115889632457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2866514225804077259754971 4299771338706115889632457)
        ·
          refine ⟨3224828504029586917224343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4299771338706115889632457 3224828504029586917224343)
          ·
            refine ⟨4837242756044380375836515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3224828504029586917224343 4837242756044380375836515)
            ·
              refine ⟨7255864134066570563754773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4837242756044380375836515 7255864134066570563754773)
              ·
                refine ⟨340118631284370495176005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7255864134066570563754773 340118631284370495176005)
                ·
                  refine ⟨63772243365819467845501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 340118631284370495176005 63772243365819467845501)
                  ·
                    rfl

theorem cell22_558882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_558882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_558882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_558882 prefixEnd_558882 := by exact prefixLift 558882
  have htrace : WordTrace (prefixWord ++ tailWord_558882) baseStart_558882 baseEnd_558882 := by
    simpa [prefixWord, tailWord_558882, baseEnd_558882] using wordTrace_append hprefix tailTrace_558882
  have hstable : (prefixWord ++ tailWord_558882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558882).length < 2 ^ (prefixWord ++ tailWord_558882).sum := by decide
  have hdescent : baseEnd_558882 < baseStart_558882 := by decide
  rcases family_descends (prefixWord ++ tailWord_558882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558897 : List Nat := [1, 2, 2, 3, 2, 4, 1, 1, 1, 5]
def baseStart_558897 : Nat := 118140960795 + 558897 * 2 ^ 59
def prefixEnd_558897 : Nat := 4983230072969 + 3 ^ 40 * 558897 * 2
def baseEnd_558897 : Nat := 191321864904003364411457

theorem tailTrace_558897 : CollatzResearch.WordTrace tailWord_558897 prefixEnd_558897 191321864904003364411457 := by
  unfold tailWord_558897
  simp only [CollatzResearch.WordTrace]
  refine ⟨20384648256219095853386945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13589765504146063902257963 20384648256219095853386945)
  ·
    refine ⟨15288486192164321890040209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20384648256219095853386945 15288486192164321890040209)
    ·
      refine ⟨11466364644123241417530157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15288486192164321890040209 11466364644123241417530157)
      ·
        refine ⟨4299886741546215531573809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11466364644123241417530157 4299886741546215531573809)
        ·
          refine ⟨3224915056159661648680357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4299886741546215531573809 3224915056159661648680357)
          ·
            refine ⟨604671573029936559127567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3224915056159661648680357 604671573029936559127567)
            ·
              refine ⟨907007359544904838691351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 604671573029936559127567 907007359544904838691351)
              ·
                refine ⟨1360511039317357258037027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 907007359544904838691351 1360511039317357258037027)
                ·
                  refine ⟨2040766558976035887055541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1360511039317357258037027 2040766558976035887055541)
                  ·
                    refine ⟨191321864904003364411457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2040766558976035887055541 191321864904003364411457)
                    ·
                      rfl

theorem cell22_558897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 5].length) (baseStart_558897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_558897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_558897 prefixEnd_558897 := by exact prefixLift 558897
  have htrace : WordTrace (prefixWord ++ tailWord_558897) baseStart_558897 baseEnd_558897 := by
    simpa [prefixWord, tailWord_558897, baseEnd_558897] using wordTrace_append hprefix tailTrace_558897
  have hstable : (prefixWord ++ tailWord_558897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558897).length < 2 ^ (prefixWord ++ tailWord_558897).sum := by decide
  have hdescent : baseEnd_558897 < baseStart_558897 := by decide
  rcases family_descends (prefixWord ++ tailWord_558897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558948 : List Nat := [2, 3, 1, 1, 6, 1, 2, 1, 2, 3]
def baseStart_558948 : Nat := 118140960795 + 558948 * 2 ^ 59
def prefixEnd_558948 : Nat := 4983230072969 + 3 ^ 40 * 558948 * 2
def baseEnd_558948 : Nat := 191339323246256231386301

theorem tailTrace_558948 : CollatzResearch.WordTrace tailWord_558948 prefixEnd_558948 191339323246256231386301 := by
  unfold tailWord_558948
  simp only [CollatzResearch.WordTrace]
  refine ⟨10193254189517165781746749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13591005586022887708995665 10193254189517165781746749)
  ·
    refine ⟨3822470321068937168155031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10193254189517165781746749 3822470321068937168155031)
    ·
      refine ⟨5733705481603405752232547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3822470321068937168155031 5733705481603405752232547)
      ·
        refine ⟨8600558222405108628348821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5733705481603405752232547 8600558222405108628348821)
        ·
          refine ⟨403151166675239466953851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8600558222405108628348821 403151166675239466953851)
          ·
            refine ⟨604726750012859200430777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 403151166675239466953851 604726750012859200430777)
            ·
              refine ⟨453545062509644400323083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 604726750012859200430777 453545062509644400323083)
              ·
                refine ⟨680317593764466600484625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 453545062509644400323083 680317593764466600484625)
                ·
                  refine ⟨510238195323349950363469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 680317593764466600484625 510238195323349950363469)
                  ·
                    refine ⟨191339323246256231386301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 510238195323349950363469 191339323246256231386301)
                    ·
                      rfl

theorem cell22_558948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 1, 2, 3].length) (baseStart_558948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_558948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_558948 prefixEnd_558948 := by exact prefixLift 558948
  have htrace : WordTrace (prefixWord ++ tailWord_558948) baseStart_558948 baseEnd_558948 := by
    simpa [prefixWord, tailWord_558948, baseEnd_558948] using wordTrace_append hprefix tailTrace_558948
  have hstable : (prefixWord ++ tailWord_558948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558948).length < 2 ^ (prefixWord ++ tailWord_558948).sum := by decide
  have hdescent : baseEnd_558948 < baseStart_558948 := by decide
  rcases family_descends (prefixWord ++ tailWord_558948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559002 : List Nat := [3, 1, 1, 4, 2, 1, 1, 2, 3, 4]
def baseStart_559002 : Nat := 118140960795 + 559002 * 2 ^ 59
def prefixEnd_559002 : Nat := 4983230072969 + 3 ^ 40 * 559002 * 2
def baseEnd_559002 : Nat := 191357808549818090536135

theorem tailTrace_559002 : CollatzResearch.WordTrace tailWord_559002 prefixEnd_559002 191357808549818090536135 := by
  unfold tailWord_559002
  simp only [CollatzResearch.WordTrace]
  refine ⟨5097119480209674696489815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13592318613892465857306173 5097119480209674696489815)
  ·
    refine ⟨7645679220314512044734723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5097119480209674696489815 7645679220314512044734723)
    ·
      refine ⟨11468518830471768067102085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7645679220314512044734723 11468518830471768067102085)
      ·
        refine ⟨2150347280713456512581641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11468518830471768067102085 2150347280713456512581641)
        ·
          refine ⟨1612760460535092384436231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2150347280713456512581641 1612760460535092384436231)
          ·
            refine ⟨2419140690802638576654347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1612760460535092384436231 2419140690802638576654347)
            ·
              refine ⟨3628711036203957864981521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2419140690802638576654347 3628711036203957864981521)
              ·
                refine ⟨2721533277152968398736141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3628711036203957864981521 2721533277152968398736141)
                ·
                  refine ⟨1020574978932363149526053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2721533277152968398736141 1020574978932363149526053)
                  ·
                    refine ⟨191357808549818090536135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1020574978932363149526053 191357808549818090536135)
                    ·
                      rfl

theorem cell22_559002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 3, 4].length) (baseStart_559002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_559002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_559002 prefixEnd_559002 := by exact prefixLift 559002
  have htrace : WordTrace (prefixWord ++ tailWord_559002) baseStart_559002 baseEnd_559002 := by
    simpa [prefixWord, tailWord_559002, baseEnd_559002] using wordTrace_append hprefix tailTrace_559002
  have hstable : (prefixWord ++ tailWord_559002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559002).length < 2 ^ (prefixWord ++ tailWord_559002).sum := by decide
  have hdescent : baseEnd_559002 < baseStart_559002 := by decide
  rcases family_descends (prefixWord ++ tailWord_559002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559032 : List Nat := [2, 1, 2, 1, 2, 3, 2, 2, 4, 3]
def baseStart_559032 : Nat := 118140960795 + 559032 * 2 ^ 59
def prefixEnd_559032 : Nat := 4983230072969 + 3 ^ 40 * 559032 * 2
def baseEnd_559032 : Nat := 191368078162908012286043

theorem tailTrace_559032 : CollatzResearch.WordTrace tailWord_559032 prefixEnd_559032 191368078162908012286043 := by
  unfold tailWord_559032
  simp only [CollatzResearch.WordTrace]
  refine ⟨10194786055365006954775675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13593048073820009273034233 10194786055365006954775675)
  ·
    refine ⟨15292179083047510432163513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10194786055365006954775675 15292179083047510432163513)
    ·
      refine ⟨11469134312285632824122635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15292179083047510432163513 11469134312285632824122635)
      ·
        refine ⟨17203701468428449236183953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11469134312285632824122635 17203701468428449236183953)
        ·
          refine ⟨12902776101321336927137965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17203701468428449236183953 12902776101321336927137965)
          ·
            refine ⟨4838541037995501347676737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12902776101321336927137965 4838541037995501347676737)
            ·
              refine ⟨3628905778496626010757553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4838541037995501347676737 3628905778496626010757553)
              ·
                refine ⟨2721679333872469508068165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3628905778496626010757553 2721679333872469508068165)
                ·
                  refine ⟨510314875101088032762781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2721679333872469508068165 510314875101088032762781)
                  ·
                    refine ⟨191368078162908012286043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 510314875101088032762781 191368078162908012286043)
                    ·
                      rfl

theorem cell22_559032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 4, 3].length) (baseStart_559032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_559032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_559032 prefixEnd_559032 := by exact prefixLift 559032
  have htrace : WordTrace (prefixWord ++ tailWord_559032) baseStart_559032 baseEnd_559032 := by
    simpa [prefixWord, tailWord_559032, baseEnd_559032] using wordTrace_append hprefix tailTrace_559032
  have hstable : (prefixWord ++ tailWord_559032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559032).length < 2 ^ (prefixWord ++ tailWord_559032).sum := by decide
  have hdescent : baseEnd_559032 < baseStart_559032 := by decide
  rcases family_descends (prefixWord ++ tailWord_559032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559036 : List Nat := [2, 2, 2, 5, 1, 1, 1, 3, 1, 4]
def baseStart_559036 : Nat := 118140960795 + 559036 * 2 ^ 59
def prefixEnd_559036 : Nat := 4983230072969 + 3 ^ 40 * 559036 * 2
def baseEnd_559036 : Nat := 191369447444653335186031

theorem tailTrace_559036 : CollatzResearch.WordTrace tailWord_559036 prefixEnd_559036 191369447444653335186031 := by
  unfold tailWord_559036
  simp only [CollatzResearch.WordTrace]
  refine ⟨10194859001357761296348481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13593145335143681728464641 10194859001357761296348481)
  ·
    refine ⟨7646144251018320972261361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10194859001357761296348481 7646144251018320972261361)
    ·
      refine ⟨5734608188263740729196021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7646144251018320972261361 5734608188263740729196021)
      ·
        refine ⟨537619517649725693362127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5734608188263740729196021 537619517649725693362127)
        ·
          refine ⟨806429276474588540043191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 537619517649725693362127 806429276474588540043191)
          ·
            refine ⟨1209643914711882810064787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 806429276474588540043191 1209643914711882810064787)
            ·
              refine ⟨1814465872067824215097181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1209643914711882810064787 1814465872067824215097181)
              ·
                refine ⟨680424702025434080661443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1814465872067824215097181 680424702025434080661443)
                ·
                  refine ⟨1020637053038151120992165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 680424702025434080661443 1020637053038151120992165)
                  ·
                    refine ⟨191369447444653335186031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1020637053038151120992165 191369447444653335186031)
                    ·
                      rfl

theorem cell22_559036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 3, 1, 4].length) (baseStart_559036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_559036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_559036 prefixEnd_559036 := by exact prefixLift 559036
  have htrace : WordTrace (prefixWord ++ tailWord_559036) baseStart_559036 baseEnd_559036 := by
    simpa [prefixWord, tailWord_559036, baseEnd_559036] using wordTrace_append hprefix tailTrace_559036
  have hstable : (prefixWord ++ tailWord_559036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559036).length < 2 ^ (prefixWord ++ tailWord_559036).sum := by decide
  have hdescent : baseEnd_559036 < baseStart_559036 := by decide
  rcases family_descends (prefixWord ++ tailWord_559036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559066 : List Nat := [3, 1, 1, 2, 6, 1, 1, 1, 1, 5]
def baseStart_559066 : Nat := 118140960795 + 559066 * 2 ^ 59
def prefixEnd_559066 : Nat := 4983230072969 + 3 ^ 40 * 559066 * 2
def baseEnd_559066 : Nat := 191379717057743256935939

theorem tailTrace_559066 : CollatzResearch.WordTrace tailWord_559066 prefixEnd_559066 191379717057743256935939 := by
  unfold tailWord_559066
  simp only [CollatzResearch.WordTrace]
  refine ⟨5097703048151709429072263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13593874795071225144192701 5097703048151709429072263)
  ·
    refine ⟨7646554572227564143608395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5097703048151709429072263 7646554572227564143608395)
    ·
      refine ⟨11469831858341346215412593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7646554572227564143608395 11469831858341346215412593)
      ·
        refine ⟨8602373893756009661559445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11469831858341346215412593 8602373893756009661559445)
        ·
          refine ⟨403236276269812952885599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8602373893756009661559445 403236276269812952885599)
          ·
            refine ⟨604854414404719429328399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 403236276269812952885599 604854414404719429328399)
            ·
              refine ⟨907281621607079143992599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 604854414404719429328399 907281621607079143992599)
              ·
                refine ⟨1360922432410618715988899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 907281621607079143992599 1360922432410618715988899)
                ·
                  refine ⟨2041383648615928073983349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1360922432410618715988899 2041383648615928073983349)
                  ·
                    refine ⟨191379717057743256935939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2041383648615928073983349 191379717057743256935939)
                    ·
                      rfl

theorem cell22_559066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 1, 5].length) (baseStart_559066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_559066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_559066 prefixEnd_559066 := by exact prefixLift 559066
  have htrace : WordTrace (prefixWord ++ tailWord_559066) baseStart_559066 baseEnd_559066 := by
    simpa [prefixWord, tailWord_559066, baseEnd_559066] using wordTrace_append hprefix tailTrace_559066
  have hstable : (prefixWord ++ tailWord_559066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559066).length < 2 ^ (prefixWord ++ tailWord_559066).sum := by decide
  have hdescent : baseEnd_559066 < baseStart_559066 := by decide
  rcases family_descends (prefixWord ++ tailWord_559066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559085 : List Nat := [1, 5, 1, 4, 2, 1, 1, 3, 4]
def baseStart_559085 : Nat := 118140960795 + 559085 * 2 ^ 59
def prefixEnd_559085 : Nat := 4983230072969 + 3 ^ 40 * 559085 * 2
def baseEnd_559085 : Nat := 63795407048677846903627

theorem tailTrace_559085 : CollatzResearch.WordTrace tailWord_559085 prefixEnd_559085 63795407048677846903627 := by
  unfold tailWord_559085
  simp only [CollatzResearch.WordTrace]
  refine ⟨20391505179538003961230709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13594336786358669307487139 20391505179538003961230709)
  ·
    refine ⟨1911703610581687871365379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20391505179538003961230709 1911703610581687871365379)
    ·
      refine ⟨2867555415872531807048069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1911703610581687871365379 2867555415872531807048069)
      ·
        refine ⟨537666640476099713821513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2867555415872531807048069 537666640476099713821513)
        ·
          refine ⟨403249980357074785366135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 537666640476099713821513 403249980357074785366135)
          ·
            refine ⟨604874970535612178049203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 403249980357074785366135 604874970535612178049203)
            ·
              refine ⟨907312455803418267073805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 604874970535612178049203 907312455803418267073805)
              ·
                refine ⟨340242170926281850152677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 907312455803418267073805 340242170926281850152677)
                ·
                  refine ⟨63795407048677846903627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 340242170926281850152677 63795407048677846903627)
                  ·
                    rfl

theorem cell22_559085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_559085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_559085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_559085 prefixEnd_559085 := by exact prefixLift 559085
  have htrace : WordTrace (prefixWord ++ tailWord_559085) baseStart_559085 baseEnd_559085 := by
    simpa [prefixWord, tailWord_559085, baseEnd_559085] using wordTrace_append hprefix tailTrace_559085
  have hstable : (prefixWord ++ tailWord_559085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559085).length < 2 ^ (prefixWord ++ tailWord_559085).sum := by decide
  have hdescent : baseEnd_559085 < baseStart_559085 := by decide
  rcases family_descends (prefixWord ++ tailWord_559085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559111 : List Nat := [1, 1, 4, 3, 1, 4, 1, 1, 3, 3]
def baseStart_559111 : Nat := 118140960795 + 559111 * 2 ^ 59
def prefixEnd_559111 : Nat := 4983230072969 + 3 ^ 40 * 559111 * 2
def baseEnd_559111 : Nat := 191395121477378139560801

theorem tailTrace_559111 : CollatzResearch.WordTrace tailWord_559111 prefixEnd_559111 191395121477378139560801 := by
  unfold tailWord_559111
  simp only [CollatzResearch.WordTrace]
  refine ⟨20392453477443810401677187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13594968984962540267784791 20392453477443810401677187)
  ·
    refine ⟨30588680216165715602515781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20392453477443810401677187 30588680216165715602515781)
    ·
      refine ⟨5735377540531071675471709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30588680216165715602515781 5735377540531071675471709)
      ·
        refine ⟨2150766577699151878301891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5735377540531071675471709 2150766577699151878301891)
        ·
          refine ⟨3226149866548727817452837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2150766577699151878301891 3226149866548727817452837)
          ·
            refine ⟨604903099977886465772407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3226149866548727817452837 604903099977886465772407)
            ·
              refine ⟨907354649966829698658611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 604903099977886465772407 907354649966829698658611)
              ·
                refine ⟨1361031974950244547987917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 907354649966829698658611 1361031974950244547987917)
                ·
                  refine ⟨510386990606341705495469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1361031974950244547987917 510386990606341705495469)
                  ·
                    refine ⟨191395121477378139560801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 510386990606341705495469 191395121477378139560801)
                    ·
                      rfl

theorem cell22_559111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 3, 3].length) (baseStart_559111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_559111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_559111 prefixEnd_559111 := by exact prefixLift 559111
  have htrace : WordTrace (prefixWord ++ tailWord_559111) baseStart_559111 baseEnd_559111 := by
    simpa [prefixWord, tailWord_559111, baseEnd_559111] using wordTrace_append hprefix tailTrace_559111
  have hstable : (prefixWord ++ tailWord_559111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559111).length < 2 ^ (prefixWord ++ tailWord_559111).sum := by decide
  have hdescent : baseEnd_559111 < baseStart_559111 := by decide
  rcases family_descends (prefixWord ++ tailWord_559111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559218 : List Nat := [3, 2, 1, 2, 2, 4, 1, 2, 2, 3]
def baseStart_559218 : Nat := 118140960795 + 559218 * 2 ^ 59
def prefixEnd_559218 : Nat := 4983230072969 + 3 ^ 40 * 559218 * 2
def baseEnd_559218 : Nat := 191431749764065527135473

theorem tailTrace_559218 : CollatzResearch.WordTrace tailWord_559218 prefixEnd_559218 191431749764065527135473 := by
  unfold tailWord_559218
  simp only [CollatzResearch.WordTrace]
  refine ⟨5099089022014041918955577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13597570725370778450548205 5099089022014041918955577)
  ·
    refine ⟨3824316766510531439216683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5099089022014041918955577 3824316766510531439216683)
    ·
      refine ⟨5736475149765797158825025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3824316766510531439216683 5736475149765797158825025)
      ·
        refine ⟨4302356362324347869118769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5736475149765797158825025 4302356362324347869118769)
        ·
          refine ⟨3226767271743260901839077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4302356362324347869118769 3226767271743260901839077)
          ·
            refine ⟨605018863451861419094827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3226767271743260901839077 605018863451861419094827)
            ·
              refine ⟨907528295177792128642241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 605018863451861419094827 907528295177792128642241)
              ·
                refine ⟨680646221383344096481681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 907528295177792128642241 680646221383344096481681)
                ·
                  refine ⟨510484666037508072361261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 680646221383344096481681 510484666037508072361261)
                  ·
                    refine ⟨191431749764065527135473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 510484666037508072361261 191431749764065527135473)
                    ·
                      rfl

theorem cell22_559218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 2, 2, 3].length) (baseStart_559218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_559218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_559218 prefixEnd_559218 := by exact prefixLift 559218
  have htrace : WordTrace (prefixWord ++ tailWord_559218) baseStart_559218 baseEnd_559218 := by
    simpa [prefixWord, tailWord_559218, baseEnd_559218] using wordTrace_append hprefix tailTrace_559218
  have hstable : (prefixWord ++ tailWord_559218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559218).length < 2 ^ (prefixWord ++ tailWord_559218).sum := by decide
  have hdescent : baseEnd_559218 < baseStart_559218 := by decide
  rcases family_descends (prefixWord ++ tailWord_559218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559257 : List Nat := [1, 2, 1, 2, 1, 2, 1, 4, 1, 7]
def baseStart_559257 : Nat := 118140960795 + 559257 * 2 ^ 59
def prefixEnd_559257 : Nat := 4983230072969 + 3 ^ 40 * 559257 * 2
def baseEnd_559257 : Nat := 191445100261082425410353

theorem tailTrace_559257 : CollatzResearch.WordTrace tailWord_559257 prefixEnd_559257 191445100261082425410353 := by
  unfold tailWord_559257
  simp only [CollatzResearch.WordTrace]
  refine ⟨20397778534914877336492025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13598519023276584890994683 20397778534914877336492025)
  ·
    refine ⟨15298333901186158002369019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20397778534914877336492025 15298333901186158002369019)
    ·
      refine ⟨22947500851779237003553529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15298333901186158002369019 22947500851779237003553529)
      ·
        refine ⟨17210625638834427752665147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22947500851779237003553529 17210625638834427752665147)
        ·
          refine ⟨25815938458251641628997721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17210625638834427752665147 25815938458251641628997721)
          ·
            refine ⟨19361953843688731221748291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25815938458251641628997721 19361953843688731221748291)
            ·
              refine ⟨29042930765533096832622437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19361953843688731221748291 29042930765533096832622437)
              ·
                refine ⟨5445549518537455656116707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29042930765533096832622437 5445549518537455656116707)
                ·
                  refine ⟨8168324277806183484175061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5445549518537455656116707 8168324277806183484175061)
                  ·
                    refine ⟨191445100261082425410353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8168324277806183484175061 191445100261082425410353)
                    ·
                      rfl

theorem cell22_559257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 7].length) (baseStart_559257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_559257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_559257 prefixEnd_559257 := by exact prefixLift 559257
  have htrace : WordTrace (prefixWord ++ tailWord_559257) baseStart_559257 baseEnd_559257 := by
    simpa [prefixWord, tailWord_559257, baseEnd_559257] using wordTrace_append hprefix tailTrace_559257
  have hstable : (prefixWord ++ tailWord_559257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559257).length < 2 ^ (prefixWord ++ tailWord_559257).sum := by decide
  have hdescent : baseEnd_559257 < baseStart_559257 := by decide
  rcases family_descends (prefixWord ++ tailWord_559257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559289 : List Nat := [1, 2, 1, 4, 1, 2, 2, 2, 3, 4]
def baseStart_559289 : Nat := 118140960795 + 559289 * 2 ^ 59
def prefixEnd_559289 : Nat := 4983230072969 + 3 ^ 40 * 559289 * 2
def baseEnd_559289 : Nat := 191456054515045008610255

theorem tailTrace_559289 : CollatzResearch.WordTrace tailWord_559289 prefixEnd_559289 191456054515045008610255 := by
  unfold tailWord_559289
  simp only [CollatzResearch.WordTrace]
  refine ⟨20398945670798946801656921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13599297113865964534437947 20398945670798946801656921)
  ·
    refine ⟨15299209253099210101242691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20398945670798946801656921 15299209253099210101242691)
    ·
      refine ⟨22948813879648815151864037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15299209253099210101242691 22948813879648815151864037)
      ·
        refine ⟨4302902602434152840974507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22948813879648815151864037 4302902602434152840974507)
        ·
          refine ⟨6454353903651229261461761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4302902602434152840974507 6454353903651229261461761)
          ·
            refine ⟨4840765427738421946096321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6454353903651229261461761 4840765427738421946096321)
            ·
              refine ⟨3630574070803816459572241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4840765427738421946096321 3630574070803816459572241)
              ·
                refine ⟨2722930553102862344679181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3630574070803816459572241 2722930553102862344679181)
                ·
                  refine ⟨1021098957413573379254693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2722930553102862344679181 1021098957413573379254693)
                  ·
                    refine ⟨191456054515045008610255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1021098957413573379254693 191456054515045008610255)
                    ·
                      rfl

theorem cell22_559289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 3, 4].length) (baseStart_559289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_559289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_559289 prefixEnd_559289 := by exact prefixLift 559289
  have htrace : WordTrace (prefixWord ++ tailWord_559289) baseStart_559289 baseEnd_559289 := by
    simpa [prefixWord, tailWord_559289, baseEnd_559289] using wordTrace_append hprefix tailTrace_559289
  have hstable : (prefixWord ++ tailWord_559289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559289).length < 2 ^ (prefixWord ++ tailWord_559289).sum := by decide
  have hdescent : baseEnd_559289 < baseStart_559289 := by decide
  rcases family_descends (prefixWord ++ tailWord_559289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559368 : List Nat := [2, 1, 3, 2, 3, 3, 1, 1, 2, 4]
def baseStart_559368 : Nat := 118140960795 + 559368 * 2 ^ 59
def prefixEnd_559368 : Nat := 4983230072969 + 3 ^ 40 * 559368 * 2
def baseEnd_559368 : Nat := 191483097829515135885013

theorem tailTrace_559368 : CollatzResearch.WordTrace tailWord_559368 prefixEnd_559368 191483097829515135885013 := by
  unfold tailWord_559368
  simp only [CollatzResearch.WordTrace]
  refine ⟨10200913518756371646891379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13601218025008495529188505 10200913518756371646891379)
  ·
    refine ⟨15301370278134557470337069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10200913518756371646891379 15301370278134557470337069)
    ·
      refine ⟨5738013854300459051376401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15301370278134557470337069 5738013854300459051376401)
      ·
        refine ⟨4303510390725344288532301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5738013854300459051376401 4303510390725344288532301)
        ·
          refine ⟨1613816396522004108199613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4303510390725344288532301 1613816396522004108199613)
          ·
            refine ⟨605181148695751540574855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1613816396522004108199613 605181148695751540574855)
            ·
              refine ⟨907771723043627310862283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 605181148695751540574855 907771723043627310862283)
              ·
                refine ⟨1361657584565440966293425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 907771723043627310862283 1361657584565440966293425)
                ·
                  refine ⟨1021243188424080724720069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1361657584565440966293425 1021243188424080724720069)
                  ·
                    refine ⟨191483097829515135885013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1021243188424080724720069 191483097829515135885013)
                    ·
                      rfl

theorem cell22_559368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 2, 4].length) (baseStart_559368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_559368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_559368 prefixEnd_559368 := by exact prefixLift 559368
  have htrace : WordTrace (prefixWord ++ tailWord_559368) baseStart_559368 baseEnd_559368 := by
    simpa [prefixWord, tailWord_559368, baseEnd_559368] using wordTrace_append hprefix tailTrace_559368
  have hstable : (prefixWord ++ tailWord_559368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559368).length < 2 ^ (prefixWord ++ tailWord_559368).sum := by decide
  have hdescent : baseEnd_559368 < baseStart_559368 := by decide
  rcases family_descends (prefixWord ++ tailWord_559368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559471 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 6, 3]
def baseStart_559471 : Nat := 118140960795 + 559471 * 2 ^ 59
def prefixEnd_559471 : Nat := 4983230072969 + 3 ^ 40 * 559471 * 2
def baseEnd_559471 : Nat := 191518356834457200559697

theorem tailTrace_559471 : CollatzResearch.WordTrace tailWord_559471 prefixEnd_559471 191518356834457200559697 := by
  unfold tailWord_559471
  simp only [CollatzResearch.WordTrace]
  refine ⟨20405583756139591884782267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13603722504093061256521511 20405583756139591884782267)
  ·
    refine ⟨30608375634209387827173401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20405583756139591884782267 30608375634209387827173401)
    ·
      refine ⟨22956281725657040870380051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30608375634209387827173401 22956281725657040870380051)
      ·
        refine ⟨34434422588485561305570077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22956281725657040870380051 34434422588485561305570077)
        ·
          refine ⟨12912908470682085489588779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34434422588485561305570077 12912908470682085489588779)
          ·
            refine ⟨19369362706023128234383169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12912908470682085489588779 19369362706023128234383169)
            ·
              refine ⟨14527022029517346175787377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19369362706023128234383169 14527022029517346175787377)
              ·
                refine ⟨10895266522138009631840533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14527022029517346175787377 10895266522138009631840533)
                ·
                  refine ⟨510715618225219201492525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10895266522138009631840533 510715618225219201492525)
                  ·
                    refine ⟨191518356834457200559697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 510715618225219201492525 191518356834457200559697)
                    ·
                      rfl

theorem cell22_559471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 6, 3].length) (baseStart_559471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_559471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_559471 prefixEnd_559471 := by exact prefixLift 559471
  have htrace : WordTrace (prefixWord ++ tailWord_559471) baseStart_559471 baseEnd_559471 := by
    simpa [prefixWord, tailWord_559471, baseEnd_559471] using wordTrace_append hprefix tailTrace_559471
  have hstable : (prefixWord ++ tailWord_559471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559471).length < 2 ^ (prefixWord ++ tailWord_559471).sum := by decide
  have hdescent : baseEnd_559471 < baseStart_559471 := by decide
  rcases family_descends (prefixWord ++ tailWord_559471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559561 : List Nat := [1, 2, 1, 1, 2, 1, 5, 2, 2, 5]
def baseStart_559561 : Nat := 118140960795 + 559561 * 2 ^ 59
def prefixEnd_559561 : Nat := 4983230072969 + 3 ^ 40 * 559561 * 2
def baseEnd_559561 : Nat := 191549165673726965809421

theorem tailTrace_559561 : CollatzResearch.WordTrace tailWord_559561 prefixEnd_559561 191549165673726965809421 := by
  unfold tailWord_559561
  simp only [CollatzResearch.WordTrace]
  refine ⟨20408866325813537255558537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13605910883875691503705691 20408866325813537255558537)
  ·
    refine ⟨15306649744360152941668903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20408866325813537255558537 15306649744360152941668903)
    ·
      refine ⟨22959974616540229412503355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15306649744360152941668903 22959974616540229412503355)
      ·
        refine ⟨34439961924810344118755033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22959974616540229412503355 34439961924810344118755033)
        ·
          refine ⟨25829971443607758089066275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34439961924810344118755033 25829971443607758089066275)
          ·
            refine ⟨38744957165411637133599413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25829971443607758089066275 38744957165411637133599413)
            ·
              refine ⟨3632339734257340981274945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38744957165411637133599413 3632339734257340981274945)
              ·
                refine ⟨2724254800693005735956209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3632339734257340981274945 2724254800693005735956209)
                ·
                  refine ⟨2043191100519754301967157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2724254800693005735956209 2043191100519754301967157)
                  ·
                    refine ⟨191549165673726965809421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2043191100519754301967157 191549165673726965809421)
                    ·
                      rfl

theorem cell22_559561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 5].length) (baseStart_559561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_559561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_559561 prefixEnd_559561 := by exact prefixLift 559561
  have htrace : WordTrace (prefixWord ++ tailWord_559561) baseStart_559561 baseEnd_559561 := by
    simpa [prefixWord, tailWord_559561, baseEnd_559561] using wordTrace_append hprefix tailTrace_559561
  have hstable : (prefixWord ++ tailWord_559561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559561).length < 2 ^ (prefixWord ++ tailWord_559561).sum := by decide
  have hdescent : baseEnd_559561 < baseStart_559561 := by decide
  rcases family_descends (prefixWord ++ tailWord_559561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559762 : List Nat := [3, 2, 3, 1, 2, 1, 1, 4, 1, 4]
def baseStart_559762 : Nat := 118140960795 + 559762 * 2 ^ 59
def prefixEnd_559762 : Nat := 4983230072969 + 3 ^ 40 * 559762 * 2
def baseEnd_559762 : Nat := 191617972081429441533805

theorem tailTrace_559762 : CollatzResearch.WordTrace tailWord_559762 prefixEnd_559762 191617972081429441533805 := by
  unfold tailWord_559762
  simp only [CollatzResearch.WordTrace]
  refine ⟨5104049349521337145906385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13610798265390232389083693 5104049349521337145906385)
  ·
    refine ⟨3828037012141002859429789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5104049349521337145906385 3828037012141002859429789)
    ·
      refine ⟨1435513879552876072286171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3828037012141002859429789 1435513879552876072286171)
      ·
        refine ⟨2153270819329314108429257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1435513879552876072286171 2153270819329314108429257)
        ·
          refine ⟨1614953114496985581321943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2153270819329314108429257 1614953114496985581321943)
          ·
            refine ⟨2422429671745478371982915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1614953114496985581321943 2422429671745478371982915)
            ·
              refine ⟨3633644507618217557974373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2422429671745478371982915 3633644507618217557974373)
              ·
                refine ⟨681308345178415792120195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3633644507618217557974373 681308345178415792120195)
                ·
                  refine ⟨1021962517767623688180293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 681308345178415792120195 1021962517767623688180293)
                  ·
                    refine ⟨191617972081429441533805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1021962517767623688180293 191617972081429441533805)
                    ·
                      rfl

theorem cell22_559762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_559762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_559762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_559762 prefixEnd_559762 := by exact prefixLift 559762
  have htrace : WordTrace (prefixWord ++ tailWord_559762) baseStart_559762 baseEnd_559762 := by
    simpa [prefixWord, tailWord_559762, baseEnd_559762] using wordTrace_append hprefix tailTrace_559762
  have hstable : (prefixWord ++ tailWord_559762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559762).length < 2 ^ (prefixWord ++ tailWord_559762).sum := by decide
  have hdescent : baseEnd_559762 < baseStart_559762 := by decide
  rcases family_descends (prefixWord ++ tailWord_559762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559805 : List Nat := [1, 4, 1, 2, 1, 4, 2, 7]
def baseStart_559805 : Nat := 118140960795 + 559805 * 2 ^ 59
def prefixEnd_559805 : Nat := 4983230072969 + 3 ^ 40 * 559805 * 2
def baseEnd_559805 : Nat := 21292521317799073634297

theorem tailTrace_559805 : CollatzResearch.WordTrace tailWord_559805 prefixEnd_559805 21292521317799073634297 := by
  unfold tailWord_559805
  simp only [CollatzResearch.WordTrace]
  refine ⟨20417765736929566927440869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13611843824619711284960579 20417765736929566927440869)
  ·
    refine ⟨3828331075674293798895163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20417765736929566927440869 3828331075674293798895163)
    ·
      refine ⟨5742496613511440698342745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3828331075674293798895163 5742496613511440698342745)
      ·
        refine ⟨4306872460133580523757059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5742496613511440698342745 4306872460133580523757059)
        ·
          refine ⟨6460308690200370785635589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4306872460133580523757059 6460308690200370785635589)
          ·
            refine ⟨1211307879412569522306673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6460308690200370785635589 1211307879412569522306673)
            ·
              refine ⟨908480909559427141730005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1211307879412569522306673 908480909559427141730005)
              ·
                refine ⟨21292521317799073634297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 908480909559427141730005 21292521317799073634297)
                ·
                  rfl

theorem cell22_559805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 7].length) (baseStart_559805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_559805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_559805 prefixEnd_559805 := by exact prefixLift 559805
  have htrace : WordTrace (prefixWord ++ tailWord_559805) baseStart_559805 baseEnd_559805 := by
    simpa [prefixWord, tailWord_559805, baseEnd_559805] using wordTrace_append hprefix tailTrace_559805
  have hstable : (prefixWord ++ tailWord_559805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559805).length < 2 ^ (prefixWord ++ tailWord_559805).sum := by decide
  have hdescent : baseEnd_559805 < baseStart_559805 := by decide
  rcases family_descends (prefixWord ++ tailWord_559805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559901 : List Nat := [1, 4, 2, 4, 1, 2, 1, 2, 5]
def baseStart_559901 : Nat := 118140960795 + 559901 * 2 ^ 59
def prefixEnd_559901 : Nat := 4983230072969 + 3 ^ 40 * 559901 * 2
def baseEnd_559901 : Nat := 63888518207359804102793

theorem tailTrace_559901 : CollatzResearch.WordTrace tailWord_559901 prefixEnd_559901 63888518207359804102793 := by
  unfold tailWord_559901
  simp only [CollatzResearch.WordTrace]
  refine ⟨20421267144581775322935557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13614178096387850215290371 20421267144581775322935557)
  ·
    refine ⟨3828987589609082873050417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20421267144581775322935557 3828987589609082873050417)
    ·
      refine ⟨2871740692206812154787813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3828987589609082873050417 2871740692206812154787813)
      ·
        refine ⟨538451379788777279022715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2871740692206812154787813 538451379788777279022715)
        ·
          refine ⟨807677069683165918534073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 538451379788777279022715 807677069683165918534073)
          ·
            refine ⟨605757802262374438900555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 807677069683165918534073 605757802262374438900555)
            ·
              refine ⟨908636703393561658350833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 605757802262374438900555 908636703393561658350833)
              ·
                refine ⟨681477527545171243763125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 908636703393561658350833 681477527545171243763125)
                ·
                  refine ⟨63888518207359804102793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 681477527545171243763125 63888518207359804102793)
                  ·
                    rfl

theorem cell22_559901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 2, 5].length) (baseStart_559901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_559901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_559901 prefixEnd_559901 := by exact prefixLift 559901
  have htrace : WordTrace (prefixWord ++ tailWord_559901) baseStart_559901 baseEnd_559901 := by
    simpa [prefixWord, tailWord_559901, baseEnd_559901] using wordTrace_append hprefix tailTrace_559901
  have hstable : (prefixWord ++ tailWord_559901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559901).length < 2 ^ (prefixWord ++ tailWord_559901).sum := by decide
  have hdescent : baseEnd_559901 < baseStart_559901 := by decide
  rcases family_descends (prefixWord ++ tailWord_559901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559912 : List Nat := [2, 1, 5, 1, 1, 1, 4, 1, 6]
def baseStart_559912 : Nat := 118140960795 + 559912 * 2 ^ 59
def prefixEnd_559912 : Nat := 4983230072969 + 3 ^ 40 * 559912 * 2
def baseEnd_559912 : Nat := 63889773382293016761115

theorem tailTrace_559912 : CollatzResearch.WordTrace tailWord_559912 prefixEnd_559912 63889773382293016761115 := by
  unfold tailWord_559912
  simp only [CollatzResearch.WordTrace]
  refine ⟨10210834173770962100792995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13614445565027949467723993 10210834173770962100792995)
  ·
    refine ⟨15316251260656443151189493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10210834173770962100792995 15316251260656443151189493)
    ·
      refine ⟨1435898555686541545424015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15316251260656443151189493 1435898555686541545424015)
      ·
        refine ⟨2153847833529812318136023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1435898555686541545424015 2153847833529812318136023)
        ·
          refine ⟨3230771750294718477204035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2153847833529812318136023 3230771750294718477204035)
          ·
            refine ⟨4846157625442077715806053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3230771750294718477204035 4846157625442077715806053)
            ·
              refine ⟨908654554770389571713635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4846157625442077715806053 908654554770389571713635)
              ·
                refine ⟨1362981832155584357570453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 908654554770389571713635 1362981832155584357570453)
                ·
                  refine ⟨63889773382293016761115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1362981832155584357570453 63889773382293016761115)
                  ·
                    rfl

theorem cell22_559912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 6].length) (baseStart_559912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_559912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_559912 prefixEnd_559912 := by exact prefixLift 559912
  have htrace : WordTrace (prefixWord ++ tailWord_559912) baseStart_559912 baseEnd_559912 := by
    simpa [prefixWord, tailWord_559912, baseEnd_559912] using wordTrace_append hprefix tailTrace_559912
  have hstable : (prefixWord ++ tailWord_559912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559912).length < 2 ^ (prefixWord ++ tailWord_559912).sum := by decide
  have hdescent : baseEnd_559912 < baseStart_559912 := by decide
  rcases family_descends (prefixWord ++ tailWord_559912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560000 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 3, 7]
def baseStart_560000 : Nat := 118140960795 + 560000 * 2 ^ 59
def prefixEnd_560000 : Nat := 4983230072969 + 3 ^ 40 * 560000 * 2
def baseEnd_560000 : Nat := 191699444345276154083075

theorem tailTrace_560000 : CollatzResearch.WordTrace tailWord_560000 prefixEnd_560000 191699444345276154083075 := by
  unfold tailWord_560000
  simp only [CollatzResearch.WordTrace]
  refine ⟨10212438985611557615394727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13616585314148743487192969 10212438985611557615394727)
  ·
    refine ⟨15318658478417336423092091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10212438985611557615394727 15318658478417336423092091)
    ·
      refine ⟨22977987717626004634638137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15318658478417336423092091 22977987717626004634638137)
      ·
        refine ⟨17233490788219503475978603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22977987717626004634638137 17233490788219503475978603)
        ·
          refine ⟨25850236182329255213967905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17233490788219503475978603 25850236182329255213967905)
          ·
            refine ⟨19387677136746941410475929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25850236182329255213967905 19387677136746941410475929)
            ·
              refine ⟨14540757852560206057856947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19387677136746941410475929 14540757852560206057856947)
              ·
                refine ⟨21811136778840309086785421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14540757852560206057856947 21811136778840309086785421)
                ·
                  refine ⟨8179176292065115907544533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21811136778840309086785421 8179176292065115907544533)
                  ·
                    refine ⟨191699444345276154083075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8179176292065115907544533 191699444345276154083075)
                    ·
                      rfl

theorem cell22_560000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 3, 7].length) (baseStart_560000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_560000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_560000 prefixEnd_560000 := by exact prefixLift 560000
  have htrace : WordTrace (prefixWord ++ tailWord_560000) baseStart_560000 baseEnd_560000 := by
    simpa [prefixWord, tailWord_560000, baseEnd_560000] using wordTrace_append hprefix tailTrace_560000
  have hstable : (prefixWord ++ tailWord_560000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560000).length < 2 ^ (prefixWord ++ tailWord_560000).sum := by decide
  have hdescent : baseEnd_560000 < baseStart_560000 := by decide
  rcases family_descends (prefixWord ++ tailWord_560000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560032 : List Nat := [2, 1, 1, 4, 1, 1, 3, 2, 3, 4]
def baseStart_560032 : Nat := 118140960795 + 560032 * 2 ^ 59
def prefixEnd_560032 : Nat := 4983230072969 + 3 ^ 40 * 560032 * 2
def baseEnd_560032 : Nat := 191710398599238737282977

theorem tailTrace_560032 : CollatzResearch.WordTrace tailWord_560032 prefixEnd_560032 191710398599238737282977 := by
  unfold tailWord_560032
  simp only [CollatzResearch.WordTrace]
  refine ⟨10213022553553592347977175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13617363404738123130636233 10213022553553592347977175)
  ·
    refine ⟨15319533830330388521965763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10213022553553592347977175 15319533830330388521965763)
    ·
      refine ⟨22979300745495582782948645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15319533830330388521965763 22979300745495582782948645)
      ·
        refine ⟨4308618889780421771802871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22979300745495582782948645 4308618889780421771802871)
        ·
          refine ⟨6462928334670632657704307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4308618889780421771802871 6462928334670632657704307)
          ·
            refine ⟨9694392502005948986556461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6462928334670632657704307 9694392502005948986556461)
            ·
              refine ⟨3635397188252230869958673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9694392502005948986556461 3635397188252230869958673)
              ·
                refine ⟨2726547891189173152469005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3635397188252230869958673 2726547891189173152469005)
                ·
                  refine ⟨1022455459195939932175877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2726547891189173152469005 1022455459195939932175877)
                  ·
                    refine ⟨191710398599238737282977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1022455459195939932175877 191710398599238737282977)
                    ·
                      rfl

theorem cell22_560032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 3, 4].length) (baseStart_560032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_560032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_560032 prefixEnd_560032 := by exact prefixLift 560032
  have htrace : WordTrace (prefixWord ++ tailWord_560032) baseStart_560032 baseEnd_560032 := by
    simpa [prefixWord, tailWord_560032, baseEnd_560032] using wordTrace_append hprefix tailTrace_560032
  have hstable : (prefixWord ++ tailWord_560032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560032).length < 2 ^ (prefixWord ++ tailWord_560032).sum := by decide
  have hdescent : baseEnd_560032 < baseStart_560032 := by decide
  rcases family_descends (prefixWord ++ tailWord_560032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560034 : List Nat := [3, 3, 1, 2, 2, 2, 1, 1, 2, 5]
def baseStart_560034 : Nat := 118140960795 + 560034 * 2 ^ 59
def prefixEnd_560034 : Nat := 4983230072969 + 3 ^ 40 * 560034 * 2
def baseEnd_560034 : Nat := 191711083240111398732971

theorem tailTrace_560034 : CollatzResearch.WordTrace tailWord_560034 prefixEnd_560034 191711083240111398732971 := by
  unfold tailWord_560034
  simp only [CollatzResearch.WordTrace]
  refine ⟨5106529513274984759381789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13617412035399959358351437 5106529513274984759381789)
  ·
    refine ⟨1914948567478119284768171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5106529513274984759381789 1914948567478119284768171)
    ·
      refine ⟨2872422851217178927152257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1914948567478119284768171 2872422851217178927152257)
      ·
        refine ⟨2154317138412884195364193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2872422851217178927152257 2154317138412884195364193)
        ·
          refine ⟨1615737853809663146523145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2154317138412884195364193 1615737853809663146523145)
          ·
            refine ⟨1211803390357247359892359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1615737853809663146523145 1211803390357247359892359)
            ·
              refine ⟨1817705085535871039838539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1211803390357247359892359 1817705085535871039838539)
              ·
                refine ⟨2726557628303806559757809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1817705085535871039838539 2726557628303806559757809)
                ·
                  refine ⟨2044918221227854919818357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2726557628303806559757809 2044918221227854919818357)
                  ·
                    refine ⟨191711083240111398732971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2044918221227854919818357 191711083240111398732971)
                    ·
                      rfl

theorem cell22_560034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_560034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_560034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_560034 prefixEnd_560034 := by exact prefixLift 560034
  have htrace : WordTrace (prefixWord ++ tailWord_560034) baseStart_560034 baseEnd_560034 := by
    simpa [prefixWord, tailWord_560034, baseEnd_560034] using wordTrace_append hprefix tailTrace_560034
  have hstable : (prefixWord ++ tailWord_560034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560034).length < 2 ^ (prefixWord ++ tailWord_560034).sum := by decide
  have hdescent : baseEnd_560034 < baseStart_560034 := by decide
  rcases family_descends (prefixWord ++ tailWord_560034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560064 : List Nat := [2, 1, 1, 2, 3, 3, 1, 5, 4]
def baseStart_560064 : Nat := 118140960795 + 560064 * 2 ^ 59
def prefixEnd_560064 : Nat := 4983230072969 + 3 ^ 40 * 560064 * 2
def baseEnd_560064 : Nat := 63907117617733773494293

theorem tailTrace_560064 : CollatzResearch.WordTrace tailWord_560064 prefixEnd_560064 63907117617733773494293 := by
  unfold tailWord_560064
  simp only [CollatzResearch.WordTrace]
  refine ⟨10213606121495627080559623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13618141495327502774079497 10213606121495627080559623)
  ·
    refine ⟨15320409182243440620839435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10213606121495627080559623 15320409182243440620839435)
    ·
      refine ⟨22980613773365160931259153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15320409182243440620839435 22980613773365160931259153)
      ·
        refine ⟨17235460330023870698444365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22980613773365160931259153 17235460330023870698444365)
        ·
          refine ⟨6463297623758951511916637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17235460330023870698444365 6463297623758951511916637)
          ·
            refine ⟨2423736608909606816968739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6463297623758951511916637 2423736608909606816968739)
            ·
              refine ⟨3635604913364410225453109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2423736608909606816968739 3635604913364410225453109)
              ·
                refine ⟨340837960627913458636229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3635604913364410225453109 340837960627913458636229)
                ·
                  refine ⟨63907117617733773494293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 340837960627913458636229 63907117617733773494293)
                  ·
                    rfl

theorem cell22_560064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 5, 4].length) (baseStart_560064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_560064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_560064 prefixEnd_560064 := by exact prefixLift 560064
  have htrace : WordTrace (prefixWord ++ tailWord_560064) baseStart_560064 baseEnd_560064 := by
    simpa [prefixWord, tailWord_560064, baseEnd_560064] using wordTrace_append hprefix tailTrace_560064
  have hstable : (prefixWord ++ tailWord_560064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560064).length < 2 ^ (prefixWord ++ tailWord_560064).sum := by decide
  have hdescent : baseEnd_560064 < baseStart_560064 := by decide
  rcases family_descends (prefixWord ++ tailWord_560064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560070 : List Nat := [6, 1, 3, 1, 1, 1, 1, 1, 7]
def baseStart_560070 : Nat := 118140960795 + 560070 * 2 ^ 59
def prefixEnd_560070 : Nat := 4983230072969 + 3 ^ 40 * 560070 * 2
def baseEnd_560070 : Nat := 63907802258606434944287

theorem tailTrace_560070 : CollatzResearch.WordTrace tailWord_560070 prefixEnd_560070 63907802258606434944287 := by
  unfold tailWord_560070
  simp only [CollatzResearch.WordTrace]
  refine ⟨638357221280297412057427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13618287387313011457225109 638357221280297412057427)
  ·
    refine ⟨957535831920446118086141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 638357221280297412057427 957535831920446118086141)
    ·
      refine ⟨359075936970167294282303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 957535831920446118086141 359075936970167294282303)
      ·
        refine ⟨538613905455250941423455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359075936970167294282303 538613905455250941423455)
        ·
          refine ⟨807920858182876412135183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 538613905455250941423455 807920858182876412135183)
          ·
            refine ⟨1211881287274314618202775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 807920858182876412135183 1211881287274314618202775)
            ·
              refine ⟨1817821930911471927304163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1211881287274314618202775 1817821930911471927304163)
              ·
                refine ⟨2726732896367207890956245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1817821930911471927304163 2726732896367207890956245)
                ·
                  refine ⟨63907802258606434944287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2726732896367207890956245 63907802258606434944287)
                  ·
                    rfl

theorem cell22_560070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_560070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_560070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_560070 prefixEnd_560070 := by exact prefixLift 560070
  have htrace : WordTrace (prefixWord ++ tailWord_560070) baseStart_560070 baseEnd_560070 := by
    simpa [prefixWord, tailWord_560070, baseEnd_560070] using wordTrace_append hprefix tailTrace_560070
  have hstable : (prefixWord ++ tailWord_560070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560070).length < 2 ^ (prefixWord ++ tailWord_560070).sum := by decide
  have hdescent : baseEnd_560070 < baseStart_560070 := by decide
  rcases family_descends (prefixWord ++ tailWord_560070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560079 : List Nat := [1, 1, 2, 1, 1, 7, 1, 1, 4, 3]
def baseStart_560079 : Nat := 118140960795 + 560079 * 2 ^ 59
def prefixEnd_560079 : Nat := 4983230072969 + 3 ^ 40 * 560079 * 2
def baseEnd_560079 : Nat := 191726487659746281357833

theorem tailTrace_560079 : CollatzResearch.WordTrace tailWord_560079 prefixEnd_560079 191726487659746281357833 := by
  unfold tailWord_560079
  simp only [CollatzResearch.WordTrace]
  refine ⟨20427759337936911722915291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13618506225291274481943527 20427759337936911722915291)
  ·
    refine ⟨30641639006905367584372937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20427759337936911722915291 30641639006905367584372937)
    ·
      refine ⟨22981229255179025688279703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30641639006905367584372937 22981229255179025688279703)
      ·
        refine ⟨34471843882768538532419555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22981229255179025688279703 34471843882768538532419555)
        ·
          refine ⟨51707765824152807798629333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34471843882768538532419555 51707765824152807798629333)
          ·
            refine ⟨1211900761503581432780375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 51707765824152807798629333 1211900761503581432780375)
            ·
              refine ⟨1817851142255372149170563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1211900761503581432780375 1817851142255372149170563)
              ·
                refine ⟨2726776713383058223755845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1817851142255372149170563 2726776713383058223755845)
                ·
                  refine ⟨511270633759323416954221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2726776713383058223755845 511270633759323416954221)
                  ·
                    refine ⟨191726487659746281357833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 511270633759323416954221 191726487659746281357833)
                    ·
                      rfl

theorem cell22_560079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 4, 3].length) (baseStart_560079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_560079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_560079 prefixEnd_560079 := by exact prefixLift 560079
  have htrace : WordTrace (prefixWord ++ tailWord_560079) baseStart_560079 baseEnd_560079 := by
    simpa [prefixWord, tailWord_560079, baseEnd_560079] using wordTrace_append hprefix tailTrace_560079
  have hstable : (prefixWord ++ tailWord_560079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560079).length < 2 ^ (prefixWord ++ tailWord_560079).sum := by decide
  have hdescent : baseEnd_560079 < baseStart_560079 := by decide
  rcases family_descends (prefixWord ++ tailWord_560079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560126 : List Nat := [4, 2, 2, 2, 2, 2, 8]
def baseStart_560126 : Nat := 118140960795 + 560126 * 2 ^ 59
def prefixEnd_560126 : Nat := 4983230072969 + 3 ^ 40 * 560126 * 2
def baseEnd_560126 : Nat := 7101576915564956497507

theorem tailTrace_560126 : CollatzResearch.WordTrace tailWord_560126 prefixEnd_560126 7101576915564956497507 := by
  unfold tailWord_560126
  simp only [CollatzResearch.WordTrace]
  refine ⟨2553684196095829843734529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13619649045844425833250821 2553684196095829843734529)
  ·
    refine ⟨1915263147071872382800897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2553684196095829843734529 1915263147071872382800897)
    ·
      refine ⟨1436447360303904287100673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1915263147071872382800897 1436447360303904287100673)
      ·
        refine ⟨1077335520227928215325505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1436447360303904287100673 1077335520227928215325505)
        ·
          refine ⟨808001640170946161494129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1077335520227928215325505 808001640170946161494129)
          ·
            refine ⟨606001230128209621120597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 808001640170946161494129 606001230128209621120597)
            ·
              refine ⟨7101576915564956497507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 606001230128209621120597 7101576915564956497507)
              ·
                rfl

theorem cell22_560126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 8].length) (baseStart_560126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_560126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_560126 prefixEnd_560126 := by exact prefixLift 560126
  have htrace : WordTrace (prefixWord ++ tailWord_560126) baseStart_560126 baseEnd_560126 := by
    simpa [prefixWord, tailWord_560126, baseEnd_560126] using wordTrace_append hprefix tailTrace_560126
  have hstable : (prefixWord ++ tailWord_560126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560126).length < 2 ^ (prefixWord ++ tailWord_560126).sum := by decide
  have hdescent : baseEnd_560126 < baseStart_560126 := by decide
  rcases family_descends (prefixWord ++ tailWord_560126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560154 : List Nat := [3, 1, 1, 3, 1, 2, 3, 3, 5]
def baseStart_560154 : Nat := 118140960795 + 560154 * 2 ^ 59
def prefixEnd_560154 : Nat := 4983230072969 + 3 ^ 40 * 560154 * 2
def baseEnd_560154 : Nat := 63917387230823695244201

theorem tailTrace_560154 : CollatzResearch.WordTrace tailWord_560154 prefixEnd_560154 63917387230823695244201 := by
  unfold tailWord_560154
  simp only [CollatzResearch.WordTrace]
  refine ⟨5107623703166299882973879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13620329875110133021263677 5107623703166299882973879)
  ·
    refine ⟨7661435554749449824460819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5107623703166299882973879 7661435554749449824460819)
    ·
      refine ⟨11492153332124174736691229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7661435554749449824460819 11492153332124174736691229)
      ·
        refine ⟨4309557499546565526259211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11492153332124174736691229 4309557499546565526259211)
        ·
          refine ⟨6464336249319848289388817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4309557499546565526259211 6464336249319848289388817)
          ·
            refine ⟨4848252186989886217041613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6464336249319848289388817 4848252186989886217041613)
            ·
              refine ⟨1818094570121207331390605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4848252186989886217041613 1818094570121207331390605)
              ·
                refine ⟨681785463795452749271477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1818094570121207331390605 681785463795452749271477)
                ·
                  refine ⟨63917387230823695244201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 681785463795452749271477 63917387230823695244201)
                  ·
                    rfl

theorem cell22_560154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 3, 5].length) (baseStart_560154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_560154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_560154 prefixEnd_560154 := by exact prefixLift 560154
  have htrace : WordTrace (prefixWord ++ tailWord_560154) baseStart_560154 baseEnd_560154 := by
    simpa [prefixWord, tailWord_560154, baseEnd_560154] using wordTrace_append hprefix tailTrace_560154
  have hstable : (prefixWord ++ tailWord_560154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560154).length < 2 ^ (prefixWord ++ tailWord_560154).sum := by decide
  have hdescent : baseEnd_560154 < baseStart_560154 := by decide
  rcases family_descends (prefixWord ++ tailWord_560154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560229 : List Nat := [1, 3, 1, 3, 2, 1, 3, 1, 1, 6]
def baseStart_560229 : Nat := 118140960795 + 560229 * 2 ^ 59
def prefixEnd_560229 : Nat := 4983230072969 + 3 ^ 40 * 560229 * 2
def baseEnd_560229 : Nat := 191777835725195890107373

theorem tailTrace_560229 : CollatzResearch.WordTrace tailWord_560229 prefixEnd_560229 191777835725195890107373 := by
  unfold tailWord_560229
  simp only [CollatzResearch.WordTrace]
  refine ⟨20433230287393487340875741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13622153524928991560583827 20433230287393487340875741)
  ·
    refine ⟨7662461357772557752828403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20433230287393487340875741 7662461357772557752828403)
    ·
      refine ⟨11493692036658836629242605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7662461357772557752828403 11493692036658836629242605)
      ·
        refine ⟨4310134513747063735965977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11493692036658836629242605 4310134513747063735965977)
        ·
          refine ⟨3232600885310297801974483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4310134513747063735965977 3232600885310297801974483)
          ·
            refine ⟨4848901327965446702961725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3232600885310297801974483 4848901327965446702961725)
            ·
              refine ⟨1818337997987042513610647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4848901327965446702961725 1818337997987042513610647)
              ·
                refine ⟨2727506996980563770415971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1818337997987042513610647 2727506996980563770415971)
                ·
                  refine ⟨4091260495470845655623957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2727506996980563770415971 4091260495470845655623957)
                  ·
                    refine ⟨191777835725195890107373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4091260495470845655623957 191777835725195890107373)
                    ·
                      rfl

theorem cell22_560229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 6].length) (baseStart_560229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_560229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_560229 prefixEnd_560229 := by exact prefixLift 560229
  have htrace : WordTrace (prefixWord ++ tailWord_560229) baseStart_560229 baseEnd_560229 := by
    simpa [prefixWord, tailWord_560229, baseEnd_560229] using wordTrace_append hprefix tailTrace_560229
  have hstable : (prefixWord ++ tailWord_560229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560229).length < 2 ^ (prefixWord ++ tailWord_560229).sum := by decide
  have hdescent : baseEnd_560229 < baseStart_560229 := by decide
  rcases family_descends (prefixWord ++ tailWord_560229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560246 : List Nat := [5, 1, 1, 2, 1, 1, 2, 1, 4, 4]
def baseStart_560246 : Nat := 118140960795 + 560246 * 2 ^ 59
def prefixEnd_560246 : Nat := 4983230072969 + 3 ^ 40 * 560246 * 2
def baseEnd_560246 : Nat := 191783655172613512432321

theorem tailTrace_560246 : CollatzResearch.WordTrace tailWord_560246 prefixEnd_560246 191783655172613512432321 := by
  unfold tailWord_560246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1277115645520743702765287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13622566885554599496163061 1277115645520743702765287)
  ·
    refine ⟨1915673468281115554147931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1277115645520743702765287 1915673468281115554147931)
    ·
      refine ⟨2873510202421673331221897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1915673468281115554147931 2873510202421673331221897)
      ·
        refine ⟨2155132651816254998416423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2873510202421673331221897 2155132651816254998416423)
        ·
          refine ⟨3232698977724382497624635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2155132651816254998416423 3232698977724382497624635)
          ·
            refine ⟨4849048466586573746436953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3232698977724382497624635 4849048466586573746436953)
            ·
              refine ⟨3636786349939930309827715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4849048466586573746436953 3636786349939930309827715)
              ·
                refine ⟨5455179524909895464741573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3636786349939930309827715 5455179524909895464741573)
                ·
                  refine ⟨1022846160920605399639045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5455179524909895464741573 1022846160920605399639045)
                  ·
                    refine ⟨191783655172613512432321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1022846160920605399639045 191783655172613512432321)
                    ·
                      rfl

theorem cell22_560246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_560246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_560246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_560246 prefixEnd_560246 := by exact prefixLift 560246
  have htrace : WordTrace (prefixWord ++ tailWord_560246) baseStart_560246 baseEnd_560246 := by
    simpa [prefixWord, tailWord_560246, baseEnd_560246] using wordTrace_append hprefix tailTrace_560246
  have hstable : (prefixWord ++ tailWord_560246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560246).length < 2 ^ (prefixWord ++ tailWord_560246).sum := by decide
  have hdescent : baseEnd_560246 < baseStart_560246 := by decide
  rcases family_descends (prefixWord ++ tailWord_560246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560289 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 9]
def baseStart_560289 : Nat := 118140960795 + 560289 * 2 ^ 59
def prefixEnd_560289 : Nat := 4983230072969 + 3 ^ 40 * 560289 * 2
def baseEnd_560289 : Nat := 63932791650458577869063

theorem tailTrace_560289 : CollatzResearch.WordTrace tailWord_560289 prefixEnd_560289 63932791650458577869063 := by
  unfold tailWord_560289
  simp only [CollatzResearch.WordTrace]
  refine ⟨20435418667176117588059921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13623612444784078392039947 20435418667176117588059921)
  ·
    refine ⟨15326564000382088191044941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20435418667176117588059921 15326564000382088191044941)
    ·
      refine ⟨5747461500143283071641853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15326564000382088191044941 5747461500143283071641853)
      ·
        refine ⟨2155298062553731151865695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5747461500143283071641853 2155298062553731151865695)
        ·
          refine ⟨3232947093830596727798543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2155298062553731151865695 3232947093830596727798543)
          ·
            refine ⟨4849420640745895091697815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3232947093830596727798543 4849420640745895091697815)
            ·
              refine ⟨7274130961118842637546723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4849420640745895091697815 7274130961118842637546723)
              ·
                refine ⟨10911196441678263956320085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7274130961118842637546723 10911196441678263956320085)
                ·
                  refine ⟨63932791650458577869063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 10911196441678263956320085 63932791650458577869063)
                  ·
                    rfl

theorem cell22_560289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 9].length) (baseStart_560289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_560289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_560289 prefixEnd_560289 := by exact prefixLift 560289
  have htrace : WordTrace (prefixWord ++ tailWord_560289) baseStart_560289 baseEnd_560289 := by
    simpa [prefixWord, tailWord_560289, baseEnd_560289] using wordTrace_append hprefix tailTrace_560289
  have hstable : (prefixWord ++ tailWord_560289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560289).length < 2 ^ (prefixWord ++ tailWord_560289).sum := by decide
  have hdescent : baseEnd_560289 < baseStart_560289 := by decide
  rcases family_descends (prefixWord ++ tailWord_560289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560372 : List Nat := [2, 6, 1, 2, 1, 1, 1, 1, 2, 5]
def baseStart_560372 : Nat := 118140960795 + 560372 * 2 ^ 59
def prefixEnd_560372 : Nat := 4983230072969 + 3 ^ 40 * 560372 * 2
def baseEnd_560372 : Nat := 191826787547591183781935

theorem tailTrace_560372 : CollatzResearch.WordTrace tailWord_560372 prefixEnd_560372 191826787547591183781935 := by
  unfold tailWord_560372
  simp only [CollatzResearch.WordTrace]
  refine ⟨10219222962937711381665685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13625630617250281842220913 10219222962937711381665685)
  ·
    refine ⟨479026076387705221015579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10219222962937711381665685 479026076387705221015579)
    ·
      refine ⟨718539114581557831523369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 479026076387705221015579 718539114581557831523369)
      ·
        refine ⟨538904335936168373642527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 718539114581557831523369 538904335936168373642527)
        ·
          refine ⟨808356503904252560463791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 538904335936168373642527 808356503904252560463791)
          ·
            refine ⟨1212534755856378840695687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 808356503904252560463791 1212534755856378840695687)
            ·
              refine ⟨1818802133784568261043531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1212534755856378840695687 1818802133784568261043531)
              ·
                refine ⟨2728203200676852391565297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1818802133784568261043531 2728203200676852391565297)
                ·
                  refine ⟨2046152400507639293673973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2728203200676852391565297 2046152400507639293673973)
                  ·
                    refine ⟨191826787547591183781935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2046152400507639293673973 191826787547591183781935)
                    ·
                      rfl

theorem cell22_560372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_560372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_560372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_560372 prefixEnd_560372 := by exact prefixLift 560372
  have htrace : WordTrace (prefixWord ++ tailWord_560372) baseStart_560372 baseEnd_560372 := by
    simpa [prefixWord, tailWord_560372, baseEnd_560372] using wordTrace_append hprefix tailTrace_560372
  have hstable : (prefixWord ++ tailWord_560372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560372).length < 2 ^ (prefixWord ++ tailWord_560372).sum := by decide
  have hdescent : baseEnd_560372 < baseStart_560372 := by decide
  rcases family_descends (prefixWord ++ tailWord_560372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560383 : List Nat := [1, 1, 2, 2, 1, 5, 2, 3, 2, 3]
def baseStart_560383 : Nat := 118140960795 + 560383 * 2 ^ 59
def prefixEnd_560383 : Nat := 4983230072969 + 3 ^ 40 * 560383 * 2
def baseEnd_560383 : Nat := 191830553072390821756901

theorem tailTrace_560383 : CollatzResearch.WordTrace tailWord_560383 prefixEnd_560383 191830553072390821756901 := by
  unfold tailWord_560383
  simp only [CollatzResearch.WordTrace]
  refine ⟨20438847128835571641981803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13625898085890381094654535 20438847128835571641981803)
  ·
    refine ⟨30658270693253357462972705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20438847128835571641981803 30658270693253357462972705)
    ·
      refine ⟨22993703019940018097229529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30658270693253357462972705 22993703019940018097229529)
      ·
        refine ⟨17245277264955013572922147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22993703019940018097229529 17245277264955013572922147)
        ·
          refine ⟨25867915897432520359383221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17245277264955013572922147 25867915897432520359383221)
          ·
            refine ⟨2425117115384298783692177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25867915897432520359383221 2425117115384298783692177)
            ·
              refine ⟨1818837836538224087769133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2425117115384298783692177 1818837836538224087769133)
              ·
                refine ⟨682064188701834032913425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1818837836538224087769133 682064188701834032913425)
                ·
                  refine ⟨511548141526375524685069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 682064188701834032913425 511548141526375524685069)
                  ·
                    refine ⟨191830553072390821756901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 511548141526375524685069 191830553072390821756901)
                    ·
                      rfl

theorem cell22_560383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 3, 2, 3].length) (baseStart_560383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_560383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_560383 prefixEnd_560383 := by exact prefixLift 560383
  have htrace : WordTrace (prefixWord ++ tailWord_560383) baseStart_560383 baseEnd_560383 := by
    simpa [prefixWord, tailWord_560383, baseEnd_560383] using wordTrace_append hprefix tailTrace_560383
  have hstable : (prefixWord ++ tailWord_560383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560383).length < 2 ^ (prefixWord ++ tailWord_560383).sum := by decide
  have hdescent : baseEnd_560383 < baseStart_560383 := by decide
  rcases family_descends (prefixWord ++ tailWord_560383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560398 : List Nat := [4, 1, 1, 2, 1, 3, 3, 1, 2, 4]
def baseStart_560398 : Nat := 118140960795 + 560398 * 2 ^ 59
def prefixEnd_560398 : Nat := 4983230072969 + 3 ^ 40 * 560398 * 2
def baseEnd_560398 : Nat := 191835687878935782631855

theorem tailTrace_560398 : CollatzResearch.WordTrace tailWord_560398 prefixEnd_560398 191835687878935782631855 := by
  unfold tailWord_560398
  simp only [CollatzResearch.WordTrace]
  refine ⟨2554924277972653650472231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13626262815854152802518565 2554924277972653650472231)
  ·
    refine ⟨3832386416958980475708347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2554924277972653650472231 3832386416958980475708347)
    ·
      refine ⟨5748579625438470713562521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3832386416958980475708347 5748579625438470713562521)
      ·
        refine ⟨4311434719078853035171891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5748579625438470713562521 4311434719078853035171891)
        ·
          refine ⟨6467152078618279552757837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4311434719078853035171891 6467152078618279552757837)
          ·
            refine ⟨2425182029481854832284189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6467152078618279552757837 2425182029481854832284189)
            ·
              refine ⟨909443261055695562106571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2425182029481854832284189 909443261055695562106571)
              ·
                refine ⟨1364164891583543343159857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 909443261055695562106571 1364164891583543343159857)
                ·
                  refine ⟨1023123668687657507369893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1364164891583543343159857 1023123668687657507369893)
                  ·
                    refine ⟨191835687878935782631855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1023123668687657507369893 191835687878935782631855)
                    ·
                      rfl

theorem cell22_560398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_560398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_560398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_560398 prefixEnd_560398 := by exact prefixLift 560398
  have htrace : WordTrace (prefixWord ++ tailWord_560398) baseStart_560398 baseEnd_560398 := by
    simpa [prefixWord, tailWord_560398, baseEnd_560398] using wordTrace_append hprefix tailTrace_560398
  have hstable : (prefixWord ++ tailWord_560398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560398).length < 2 ^ (prefixWord ++ tailWord_560398).sum := by decide
  have hdescent : baseEnd_560398 < baseStart_560398 := by decide
  rcases family_descends (prefixWord ++ tailWord_560398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560411 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 7, 3]
def baseStart_560411 : Nat := 118140960795 + 560411 * 2 ^ 59
def prefixEnd_560411 : Nat := 4983230072969 + 3 ^ 40 * 560411 * 2
def baseEnd_560411 : Nat := 191840138044608082056815

theorem tailTrace_560411 : CollatzResearch.WordTrace tailWord_560411 prefixEnd_560411 191840138044608082056815 := by
  unfold tailWord_560411
  simp only [CollatzResearch.WordTrace]
  refine ⟨20439868372734132424001087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13626578915156088282667391 20439868372734132424001087)
  ·
    refine ⟨30659802559101198636001631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20439868372734132424001087 30659802559101198636001631)
    ·
      refine ⟨45989703838651797954002447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30659802559101198636001631 45989703838651797954002447)
      ·
        refine ⟨68984555757977696931003671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45989703838651797954002447 68984555757977696931003671)
        ·
          refine ⟨103476833636966545396505507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68984555757977696931003671 103476833636966545396505507)
          ·
            refine ⟨155215250455449818094758261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103476833636966545396505507 155215250455449818094758261)
            ·
              refine ⟨14551429730198420446383587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 155215250455449818094758261 14551429730198420446383587)
              ·
                refine ⟨21827144595297630669575381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14551429730198420446383587 21827144595297630669575381)
                ·
                  refine ⟨511573701452288218818173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 21827144595297630669575381 511573701452288218818173)
                  ·
                    refine ⟨191840138044608082056815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 511573701452288218818173 191840138044608082056815)
                    ·
                      rfl

theorem cell22_560411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 7, 3].length) (baseStart_560411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_560411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_560411 prefixEnd_560411 := by exact prefixLift 560411
  have htrace : WordTrace (prefixWord ++ tailWord_560411) baseStart_560411 baseEnd_560411 := by
    simpa [prefixWord, tailWord_560411, baseEnd_560411] using wordTrace_append hprefix tailTrace_560411
  have hstable : (prefixWord ++ tailWord_560411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560411).length < 2 ^ (prefixWord ++ tailWord_560411).sum := by decide
  have hdescent : baseEnd_560411 < baseStart_560411 := by decide
  rcases family_descends (prefixWord ++ tailWord_560411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560533 : List Nat := [1, 3, 2, 1, 1, 2, 4, 2, 2, 4]
def baseStart_560533 : Nat := 118140960795 + 560533 * 2 ^ 59
def prefixEnd_560533 : Nat := 4983230072969 + 3 ^ 40 * 560533 * 2
def baseEnd_560533 : Nat := 191881901137840430506441

theorem tailTrace_560533 : CollatzResearch.WordTrace tailWord_560533 prefixEnd_560533 191881901137840430506441 := by
  unfold tailWord_560533
  simp only [CollatzResearch.WordTrace]
  refine ⟨20444318078292147259942253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13629545385528098173294835 20444318078292147259942253)
  ·
    refine ⟨7666619279359555222478345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20444318078292147259942253 7666619279359555222478345)
    ·
      refine ⟨5749964459519666416858759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7666619279359555222478345 5749964459519666416858759)
      ·
        refine ⟨8624946689279499625288139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5749964459519666416858759 8624946689279499625288139)
        ·
          refine ⟨12937420033919249437932209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8624946689279499625288139 12937420033919249437932209)
          ·
            refine ⟨9703065025439437078449157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12937420033919249437932209 9703065025439437078449157)
            ·
              refine ⟨1819324692269894452209217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9703065025439437078449157 1819324692269894452209217)
              ·
                refine ⟨1364493519202420839156913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1819324692269894452209217 1364493519202420839156913)
                ·
                  refine ⟨1023370139401815629367685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1364493519202420839156913 1023370139401815629367685)
                  ·
                    refine ⟨191881901137840430506441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1023370139401815629367685 191881901137840430506441)
                    ·
                      rfl

theorem cell22_560533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_560533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_560533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_560533 prefixEnd_560533 := by exact prefixLift 560533
  have htrace : WordTrace (prefixWord ++ tailWord_560533) baseStart_560533 baseEnd_560533 := by
    simpa [prefixWord, tailWord_560533, baseEnd_560533] using wordTrace_append hprefix tailTrace_560533
  have hstable : (prefixWord ++ tailWord_560533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560533).length < 2 ^ (prefixWord ++ tailWord_560533).sum := by decide
  have hdescent : baseEnd_560533 < baseStart_560533 := by decide
  rcases family_descends (prefixWord ++ tailWord_560533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560537 : List Nat := [1, 2, 1, 2, 1, 7, 2, 2, 4]
def baseStart_560537 : Nat := 118140960795 + 560537 * 2 ^ 59
def prefixEnd_560537 : Nat := 4983230072969 + 3 ^ 40 * 560537 * 2
def baseEnd_560537 : Nat := 63961090139861917802143

theorem tailTrace_560537 : CollatzResearch.WordTrace tailWord_560537 prefixEnd_560537 63961090139861917802143 := by
  unfold tailWord_560537
  simp only [CollatzResearch.WordTrace]
  refine ⟨20444463970277655943087865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13629642646851770628725243 20444463970277655943087865)
  ·
    refine ⟨15333347977708241957315899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20444463970277655943087865 15333347977708241957315899)
    ·
      refine ⟨23000021966562362935973849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15333347977708241957315899 23000021966562362935973849)
      ·
        refine ⟨17250016474921772201980387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23000021966562362935973849 17250016474921772201980387)
        ·
          refine ⟨25875024712382658302970581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17250016474921772201980387 25875024712382658302970581)
          ·
            refine ⟨606445891696468553975873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 25875024712382658302970581 606445891696468553975873)
            ·
              refine ⟨454834418772351415481905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 606445891696468553975873 454834418772351415481905)
              ·
                refine ⟨341125814079263561611429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 454834418772351415481905 341125814079263561611429)
                ·
                  refine ⟨63961090139861917802143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 341125814079263561611429 63961090139861917802143)
                  ·
                    rfl

theorem cell22_560537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 2, 4].length) (baseStart_560537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_560537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_560537 prefixEnd_560537 := by exact prefixLift 560537
  have htrace : WordTrace (prefixWord ++ tailWord_560537) baseStart_560537 baseEnd_560537 := by
    simpa [prefixWord, tailWord_560537, baseEnd_560537] using wordTrace_append hprefix tailTrace_560537
  have hstable : (prefixWord ++ tailWord_560537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560537).length < 2 ^ (prefixWord ++ tailWord_560537).sum := by decide
  have hdescent : baseEnd_560537 < baseStart_560537 := by decide
  rcases family_descends (prefixWord ++ tailWord_560537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560552 : List Nat := [2, 1, 6, 1, 2, 1, 2, 1, 1, 5]
def baseStart_560552 : Nat := 118140960795 + 560552 * 2 ^ 59
def prefixEnd_560552 : Nat := 4983230072969 + 3 ^ 40 * 560552 * 2
def baseEnd_560552 : Nat := 191888405226130714281383

theorem tailTrace_560552 : CollatzResearch.WordTrace tailWord_560552 prefixEnd_560552 191888405226130714281383 := by
  unfold tailWord_560552
  simp only [CollatzResearch.WordTrace]
  refine ⟨10222505532611656752441955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13630007376815542336589273 10222505532611656752441955)
  ·
    refine ⟨15333758298917485128662933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10222505532611656752441955 15333758298917485128662933)
    ·
      refine ⟨718769920261757115406075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15333758298917485128662933 718769920261757115406075)
      ·
        refine ⟨1078154880392635673109113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 718769920261757115406075 1078154880392635673109113)
        ·
          refine ⟨808616160294476754831835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1078154880392635673109113 808616160294476754831835)
          ·
            refine ⟨1212924240441715132247753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 808616160294476754831835 1212924240441715132247753)
            ·
              refine ⟨909693180331286349185815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1212924240441715132247753 909693180331286349185815)
              ·
                refine ⟨1364539770496929523778723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 909693180331286349185815 1364539770496929523778723)
                ·
                  refine ⟨2046809655745394285668085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1364539770496929523778723 2046809655745394285668085)
                  ·
                    refine ⟨191888405226130714281383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2046809655745394285668085 191888405226130714281383)
                    ·
                      rfl

theorem cell22_560552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_560552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_560552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_560552 prefixEnd_560552 := by exact prefixLift 560552
  have htrace : WordTrace (prefixWord ++ tailWord_560552) baseStart_560552 baseEnd_560552 := by
    simpa [prefixWord, tailWord_560552, baseEnd_560552] using wordTrace_append hprefix tailTrace_560552
  have hstable : (prefixWord ++ tailWord_560552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560552).length < 2 ^ (prefixWord ++ tailWord_560552).sum := by decide
  have hdescent : baseEnd_560552 < baseStart_560552 := by decide
  rcases family_descends (prefixWord ++ tailWord_560552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560565 : List Nat := [1, 3, 3, 2, 2, 2, 3, 6]
def baseStart_560565 : Nat := 118140960795 + 560565 * 2 ^ 59
def prefixEnd_560565 : Nat := 4983230072969 + 3 ^ 40 * 560565 * 2
def baseEnd_560565 : Nat := 21321428376867001522927

theorem tailTrace_560565 : CollatzResearch.WordTrace tailWord_560565 prefixEnd_560565 21321428376867001522927 := by
  unfold tailWord_560565
  simp only [CollatzResearch.WordTrace]
  refine ⟨20445485214176216725107149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13630323476117477816738099 20445485214176216725107149)
  ·
    refine ⟨7667056955316081271915181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20445485214176216725107149 7667056955316081271915181)
    ·
      refine ⟨2875146358243530476968193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7667056955316081271915181 2875146358243530476968193)
      ·
        refine ⟨2156359768682647857726145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2875146358243530476968193 2156359768682647857726145)
        ·
          refine ⟨1617269826511985893294609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2156359768682647857726145 1617269826511985893294609)
          ·
            refine ⟨1212952369883989419970957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1617269826511985893294609 1212952369883989419970957)
            ·
              refine ⟨454857138706496032489109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1212952369883989419970957 454857138706496032489109)
              ·
                refine ⟨21321428376867001522927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 454857138706496032489109 21321428376867001522927)
                ·
                  rfl

theorem cell22_560565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 6].length) (baseStart_560565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_560565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_560565 prefixEnd_560565 := by exact prefixLift 560565
  have htrace : WordTrace (prefixWord ++ tailWord_560565) baseStart_560565 baseEnd_560565 := by
    simpa [prefixWord, tailWord_560565, baseEnd_560565] using wordTrace_append hprefix tailTrace_560565
  have hstable : (prefixWord ++ tailWord_560565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560565).length < 2 ^ (prefixWord ++ tailWord_560565).sum := by decide
  have hdescent : baseEnd_560565 < baseStart_560565 := by decide
  rcases family_descends (prefixWord ++ tailWord_560565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560597 : List Nat := [1, 3, 2, 3, 1, 1, 1, 6, 1, 3]
def baseStart_560597 : Nat := 118140960795 + 560597 * 2 ^ 59
def prefixEnd_560597 : Nat := 4983230072969 + 3 ^ 40 * 560597 * 2
def baseEnd_560597 : Nat := 191903809645765596906245

theorem tailTrace_560597 : CollatzResearch.WordTrace tailWord_560597 prefixEnd_560597 191903809645765596906245 := by
  unfold tailWord_560597
  simp only [CollatzResearch.WordTrace]
  refine ⟨20446652350060286190272045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13631101566706857460181363 20446652350060286190272045)
  ·
    refine ⟨7667494631272607321352017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20446652350060286190272045 7667494631272607321352017)
    ·
      refine ⟨5750620973454455491014013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7667494631272607321352017 5750620973454455491014013)
      ·
        refine ⟨2156482865045420809130255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5750620973454455491014013 2156482865045420809130255)
        ·
          refine ⟨3234724297568131213695383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2156482865045420809130255 3234724297568131213695383)
          ·
            refine ⟨4852086446352196820543075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3234724297568131213695383 4852086446352196820543075)
            ·
              refine ⟨7278129669528295230814613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4852086446352196820543075 7278129669528295230814613)
              ·
                refine ⟨341162328259138838944435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7278129669528295230814613 341162328259138838944435)
                ·
                  refine ⟨511743492388708258416653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 341162328259138838944435 511743492388708258416653)
                  ·
                    refine ⟨191903809645765596906245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 511743492388708258416653 191903809645765596906245)
                    ·
                      rfl

theorem cell22_560597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 6, 1, 3].length) (baseStart_560597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_560597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_560597 prefixEnd_560597 := by exact prefixLift 560597
  have htrace : WordTrace (prefixWord ++ tailWord_560597) baseStart_560597 baseEnd_560597 := by
    simpa [prefixWord, tailWord_560597, baseEnd_560597] using wordTrace_append hprefix tailTrace_560597
  have hstable : (prefixWord ++ tailWord_560597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560597).length < 2 ^ (prefixWord ++ tailWord_560597).sum := by decide
  have hdescent : baseEnd_560597 < baseStart_560597 := by decide
  rcases family_descends (prefixWord ++ tailWord_560597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560623 : List Nat := [1, 1, 2, 1, 4, 1, 2, 3, 3, 4]
def baseStart_560623 : Nat := 118140960795 + 560623 * 2 ^ 59
def prefixEnd_560623 : Nat := 4983230072969 + 3 ^ 40 * 560623 * 2
def baseEnd_560623 : Nat := 191912709977110195756165

theorem tailTrace_560623 : CollatzResearch.WordTrace tailWord_560623 prefixEnd_560623 191912709977110195756165 := by
  unfold tailWord_560623
  simp only [CollatzResearch.WordTrace]
  refine ⟨20447600647966092630718523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13631733765310728420479015 20447600647966092630718523)
  ·
    refine ⟨30671400971949138946077785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20447600647966092630718523 30671400971949138946077785)
    ·
      refine ⟨23003550728961854209558339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30671400971949138946077785 23003550728961854209558339)
      ·
        refine ⟨34505326093442781314337509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23003550728961854209558339 34505326093442781314337509)
        ·
          refine ⟨6469748642520521496438283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34505326093442781314337509 6469748642520521496438283)
          ·
            refine ⟨9704622963780782244657425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6469748642520521496438283 9704622963780782244657425)
            ·
              refine ⟨7278467222835586683493069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9704622963780782244657425 7278467222835586683493069)
              ·
                refine ⟨2729425208563345006309901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7278467222835586683493069 2729425208563345006309901)
                ·
                  refine ⟨1023534453211254377366213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2729425208563345006309901 1023534453211254377366213)
                  ·
                    refine ⟨191912709977110195756165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1023534453211254377366213 191912709977110195756165)
                    ·
                      rfl

theorem cell22_560623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 3, 4].length) (baseStart_560623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_560623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_560623 prefixEnd_560623 := by exact prefixLift 560623
  have htrace : WordTrace (prefixWord ++ tailWord_560623) baseStart_560623 baseEnd_560623 := by
    simpa [prefixWord, tailWord_560623, baseEnd_560623] using wordTrace_append hprefix tailTrace_560623
  have hstable : (prefixWord ++ tailWord_560623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560623).length < 2 ^ (prefixWord ++ tailWord_560623).sum := by decide
  have hdescent : baseEnd_560623 < baseStart_560623 := by decide
  rcases family_descends (prefixWord ++ tailWord_560623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560700 : List Nat := [2, 2, 2, 2, 5, 9]
def baseStart_560700 : Nat := 118140960795 + 560700 * 2 ^ 59
def prefixEnd_560700 : Nat := 4983230072969 + 3 ^ 40 * 560700 * 2
def baseEnd_560700 : Nat := 2369618131490218044209

theorem tailTrace_560700 : CollatzResearch.WordTrace tailWord_560700 prefixEnd_560700 2369618131490218044209 := by
  unfold tailWord_560700
  simp only [CollatzResearch.WordTrace]
  refine ⟨10225204534343567390635777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13633606045791423187514369 10225204534343567390635777)
  ·
    refine ⟨7668903400757675542976833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10225204534343567390635777 7668903400757675542976833)
    ·
      refine ⟨5751677550568256657232625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7668903400757675542976833 5751677550568256657232625)
      ·
        refine ⟨4313758162926192492924469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5751677550568256657232625 4313758162926192492924469)
        ·
          refine ⟨404414827774330546211669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4313758162926192492924469 404414827774330546211669)
          ·
            refine ⟨2369618131490218044209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 404414827774330546211669 2369618131490218044209)
            ·
              rfl

theorem cell22_560700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 9].length) (baseStart_560700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_560700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_560700 prefixEnd_560700 := by exact prefixLift 560700
  have htrace : WordTrace (prefixWord ++ tailWord_560700) baseStart_560700 baseEnd_560700 := by
    simpa [prefixWord, tailWord_560700, baseEnd_560700] using wordTrace_append hprefix tailTrace_560700
  have hstable : (prefixWord ++ tailWord_560700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560700).length < 2 ^ (prefixWord ++ tailWord_560700).sum := by decide
  have hdescent : baseEnd_560700 < baseStart_560700 := by decide
  rcases family_descends (prefixWord ++ tailWord_560700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560715 : List Nat := [1, 1, 1, 1, 3, 1, 3, 5, 3, 3]
def baseStart_560715 : Nat := 118140960795 + 560715 * 2 ^ 59
def prefixEnd_560715 : Nat := 4983230072969 + 3 ^ 40 * 560715 * 2
def baseEnd_560715 : Nat := 191944203457252622455883

theorem tailTrace_560715 : CollatzResearch.WordTrace tailWord_560715 prefixEnd_560715 191944203457252622455883 := by
  unfold tailWord_560715
  simp only [CollatzResearch.WordTrace]
  refine ⟨20450956163632792343067599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13633970775755194895378399 20450956163632792343067599)
  ·
    refine ⟨30676434245449188514601399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20450956163632792343067599 30676434245449188514601399)
    ·
      refine ⟨46014651368173782771902099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30676434245449188514601399 46014651368173782771902099)
      ·
        refine ⟨69021977052260674157853149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46014651368173782771902099 69021977052260674157853149)
        ·
          refine ⟨25883241394597752809194931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69021977052260674157853149 25883241394597752809194931)
          ·
            refine ⟨38824862091896629213792397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25883241394597752809194931 38824862091896629213792397)
            ·
              refine ⟨14559323284461235955172149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38824862091896629213792397 14559323284461235955172149)
              ·
                refine ⟨1364936557918240870797389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14559323284461235955172149 1364936557918240870797389)
                ·
                  refine ⟨511851209219340326549021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1364936557918240870797389 511851209219340326549021)
                  ·
                    refine ⟨191944203457252622455883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 511851209219340326549021 191944203457252622455883)
                    ·
                      rfl

theorem cell22_560715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 3, 3].length) (baseStart_560715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_560715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_560715 prefixEnd_560715 := by exact prefixLift 560715
  have htrace : WordTrace (prefixWord ++ tailWord_560715) baseStart_560715 baseEnd_560715 := by
    simpa [prefixWord, tailWord_560715, baseEnd_560715] using wordTrace_append hprefix tailTrace_560715
  have hstable : (prefixWord ++ tailWord_560715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560715).length < 2 ^ (prefixWord ++ tailWord_560715).sum := by decide
  have hdescent : baseEnd_560715 < baseStart_560715 := by decide
  rcases family_descends (prefixWord ++ tailWord_560715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560728 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 9]
def baseStart_560728 : Nat := 118140960795 + 560728 * 2 ^ 59
def prefixEnd_560728 : Nat := 4983230072969 + 3 ^ 40 * 560728 * 2
def baseEnd_560728 : Nat := 63982884540974973960281

theorem tailTrace_560728 : CollatzResearch.WordTrace tailWord_560728 prefixEnd_560728 63982884540974973960281 := by
  unfold tailWord_560728
  simp only [CollatzResearch.WordTrace]
  refine ⟨10225715156292847781645419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13634286875057130375527225 10225715156292847781645419)
  ·
    refine ⟨15338572734439271672468129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10225715156292847781645419 15338572734439271672468129)
    ·
      refine ⟨11503929550829453754351097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15338572734439271672468129 11503929550829453754351097)
      ·
        refine ⟨8627947163122090315763323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11503929550829453754351097 8627947163122090315763323)
        ·
          refine ⟨12941920744683135473644985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8627947163122090315763323 12941920744683135473644985)
          ·
            refine ⟨9706440558512351605233739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12941920744683135473644985 9706440558512351605233739)
            ·
              refine ⟨14559660837768527407850609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9706440558512351605233739 14559660837768527407850609)
              ·
                refine ⟨10919745628326395555887957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14559660837768527407850609 10919745628326395555887957)
                ·
                  refine ⟨63982884540974973960281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 10919745628326395555887957 63982884540974973960281)
                  ·
                    rfl

theorem cell22_560728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 9].length) (baseStart_560728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_560728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_560728 prefixEnd_560728 := by exact prefixLift 560728
  have htrace : WordTrace (prefixWord ++ tailWord_560728) baseStart_560728 baseEnd_560728 := by
    simpa [prefixWord, tailWord_560728, baseEnd_560728] using wordTrace_append hprefix tailTrace_560728
  have hstable : (prefixWord ++ tailWord_560728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560728).length < 2 ^ (prefixWord ++ tailWord_560728).sum := by decide
  have hdescent : baseEnd_560728 < baseStart_560728 := by decide
  rcases family_descends (prefixWord ++ tailWord_560728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560732 : List Nat := [2, 2, 4, 1, 2, 1, 1, 1, 5, 3]
def baseStart_560732 : Nat := 118140960795 + 560732 * 2 ^ 59
def prefixEnd_560732 : Nat := 4983230072969 + 3 ^ 40 * 560732 * 2
def baseEnd_560732 : Nat := 191950022904670244780831

theorem tailTrace_560732 : CollatzResearch.WordTrace tailWord_560732 prefixEnd_560732 191950022904670244780831 := by
  unfold tailWord_560732
  simp only [CollatzResearch.WordTrace]
  refine ⟨10225788102285602123218225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13634384136380802830957633 10225788102285602123218225)
  ·
    refine ⟨7669341076714201592413669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10225788102285602123218225 7669341076714201592413669)
    ·
      refine ⟨1438001451883912798577563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7669341076714201592413669 1438001451883912798577563)
      ·
        refine ⟨2157002177825869197866345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1438001451883912798577563 2157002177825869197866345)
        ·
          refine ⟨1617751633369401898399759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2157002177825869197866345 1617751633369401898399759)
          ·
            refine ⟨2426627450054102847599639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1617751633369401898399759 2426627450054102847599639)
            ·
              refine ⟨3639941175081154271399459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2426627450054102847599639 3639941175081154271399459)
              ·
                refine ⟨5459911762621731407099189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3639941175081154271399459 5459911762621731407099189)
                ·
                  refine ⟨511866727745787319415549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5459911762621731407099189 511866727745787319415549)
                  ·
                    refine ⟨191950022904670244780831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 511866727745787319415549 191950022904670244780831)
                    ·
                      rfl

theorem cell22_560732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_560732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_560732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_560732 prefixEnd_560732 := by exact prefixLift 560732
  have htrace : WordTrace (prefixWord ++ tailWord_560732) baseStart_560732 baseEnd_560732 := by
    simpa [prefixWord, tailWord_560732, baseEnd_560732] using wordTrace_append hprefix tailTrace_560732
  have hstable : (prefixWord ++ tailWord_560732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560732).length < 2 ^ (prefixWord ++ tailWord_560732).sum := by decide
  have hdescent : baseEnd_560732 < baseStart_560732 := by decide
  rcases family_descends (prefixWord ++ tailWord_560732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560792 : List Nat := [2, 1, 2, 4, 1, 2, 1, 4, 1, 4]
def baseStart_560792 : Nat := 118140960795 + 560792 * 2 ^ 59
def prefixEnd_560792 : Nat := 4983230072969 + 3 ^ 40 * 560792 * 2
def baseEnd_560792 : Nat := 191970562130850088280647

theorem tailTrace_560792 : CollatzResearch.WordTrace tailWord_560792 prefixEnd_560792 191970562130850088280647 := by
  unfold tailWord_560792
  simp only [CollatzResearch.WordTrace]
  refine ⟨10226882292176917246810315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13635843056235889662413753 10226882292176917246810315)
  ·
    refine ⟨15340323438265375870215473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10226882292176917246810315 15340323438265375870215473)
    ·
      refine ⟨11505242578699031902661605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15340323438265375870215473 11505242578699031902661605)
      ·
        refine ⟨2157232983506068481749051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11505242578699031902661605 2157232983506068481749051)
        ·
          refine ⟨3235849475259102722623577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2157232983506068481749051 3235849475259102722623577)
          ·
            refine ⟨2426887106444327041967683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3235849475259102722623577 2426887106444327041967683)
            ·
              refine ⟨3640330659666490562951525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2426887106444327041967683 3640330659666490562951525)
              ·
                refine ⟨682561998687466980553411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3640330659666490562951525 682561998687466980553411)
                ·
                  refine ⟨1023842998031200470830117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 682561998687466980553411 1023842998031200470830117)
                  ·
                    refine ⟨191970562130850088280647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1023842998031200470830117 191970562130850088280647)
                    ·
                      rfl

theorem cell22_560792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 4, 1, 4].length) (baseStart_560792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_560792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_560792 prefixEnd_560792 := by exact prefixLift 560792
  have htrace : WordTrace (prefixWord ++ tailWord_560792) baseStart_560792 baseEnd_560792 := by
    simpa [prefixWord, tailWord_560792, baseEnd_560792] using wordTrace_append hprefix tailTrace_560792
  have hstable : (prefixWord ++ tailWord_560792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560792).length < 2 ^ (prefixWord ++ tailWord_560792).sum := by decide
  have hdescent : baseEnd_560792 < baseStart_560792 := by decide
  rcases family_descends (prefixWord ++ tailWord_560792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560805 : List Nat := [1, 3, 1, 2, 1, 2, 2, 4, 1, 5]
def baseStart_560805 : Nat := 118140960795 + 560805 * 2 ^ 59
def prefixEnd_560805 : Nat := 4983230072969 + 3 ^ 40 * 560805 * 2
def baseEnd_560805 : Nat := 191975012296522387705607

theorem tailTrace_560805 : CollatzResearch.WordTrace tailWord_560805 prefixEnd_560805 191975012296522387705607 := by
  unfold tailWord_560805
  simp only [CollatzResearch.WordTrace]
  refine ⟨20454238733306737713843869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13636159155537825142562579 20454238733306737713843869)
  ·
    refine ⟨7670339524990026642691451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20454238733306737713843869 7670339524990026642691451)
    ·
      refine ⟨11505509287485039964037177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7670339524990026642691451 11505509287485039964037177)
      ·
        refine ⟨8629131965613779973027883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11505509287485039964037177 8629131965613779973027883)
        ·
          refine ⟨12943697948420669959541825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8629131965613779973027883 12943697948420669959541825)
          ·
            refine ⟨9707773461315502469656369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12943697948420669959541825 9707773461315502469656369)
            ·
              refine ⟨7280830095986626852242277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9707773461315502469656369 7280830095986626852242277)
              ·
                refine ⟨1365155642997492534795427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7280830095986626852242277 1365155642997492534795427)
                ·
                  refine ⟨2047733464496238802193141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1365155642997492534795427 2047733464496238802193141)
                  ·
                    refine ⟨191975012296522387705607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2047733464496238802193141 191975012296522387705607)
                    ·
                      rfl

theorem cell22_560805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 5].length) (baseStart_560805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_560805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_560805 prefixEnd_560805 := by exact prefixLift 560805
  have htrace : WordTrace (prefixWord ++ tailWord_560805) baseStart_560805 baseEnd_560805 := by
    simpa [prefixWord, tailWord_560805, baseEnd_560805] using wordTrace_append hprefix tailTrace_560805
  have hstable : (prefixWord ++ tailWord_560805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560805).length < 2 ^ (prefixWord ++ tailWord_560805).sum := by decide
  have hdescent : baseEnd_560805 < baseStart_560805 := by decide
  rcases family_descends (prefixWord ++ tailWord_560805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560852 : List Nat := [2, 4, 1, 3, 1, 1, 2, 8]
def baseStart_560852 : Nat := 118140960795 + 560852 * 2 ^ 59
def prefixEnd_560852 : Nat := 4983230072969 + 3 ^ 40 * 560852 * 2
def baseEnd_560852 : Nat := 21332344595225547975607

theorem tailTrace_560852 : CollatzResearch.WordTrace tailWord_560852 prefixEnd_560852 21332344595225547975607 := by
  unfold tailWord_560852
  simp only [CollatzResearch.WordTrace]
  refine ⟨10227976482068232370402405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13637301976090976493869873 10227976482068232370402405)
  ·
    refine ⟨1917745590387793569450451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10227976482068232370402405 1917745590387793569450451)
    ·
      refine ⟨2876618385581690354175677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1917745590387793569450451 2876618385581690354175677)
      ·
        refine ⟨1078731894593133882815879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2876618385581690354175677 1078731894593133882815879)
        ·
          refine ⟨1618097841889700824223819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1078731894593133882815879 1618097841889700824223819)
          ·
            refine ⟨2427146762834551236335729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1618097841889700824223819 2427146762834551236335729)
            ·
              refine ⟨1820360072125913427251797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2427146762834551236335729 1820360072125913427251797)
              ·
                refine ⟨21332344595225547975607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1820360072125913427251797 21332344595225547975607)
                ·
                  rfl

theorem cell22_560852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 8].length) (baseStart_560852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_560852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_560852 prefixEnd_560852 := by exact prefixLift 560852
  have htrace : WordTrace (prefixWord ++ tailWord_560852) baseStart_560852 baseEnd_560852 := by
    simpa [prefixWord, tailWord_560852, baseEnd_560852] using wordTrace_append hprefix tailTrace_560852
  have hstable : (prefixWord ++ tailWord_560852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560852).length < 2 ^ (prefixWord ++ tailWord_560852).sum := by decide
  have hdescent : baseEnd_560852 < baseStart_560852 := by decide
  rcases family_descends (prefixWord ++ tailWord_560852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560895 : List Nat := [1, 1, 2, 2, 1, 3, 3, 1, 1, 7]
def baseStart_560895 : Nat := 118140960795 + 560895 * 2 ^ 59
def prefixEnd_560895 : Nat := 4983230072969 + 3 ^ 40 * 560895 * 2
def baseEnd_560895 : Nat := 192005821135792152955331

theorem tailTrace_560895 : CollatzResearch.WordTrace tailWord_560895 prefixEnd_560895 192005821135792152955331 := by
  unfold tailWord_560895
  simp only [CollatzResearch.WordTrace]
  refine ⟨20457521302980683084620139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13638347535320455389746759 20457521302980683084620139)
  ·
    refine ⟨30686281954471024626930209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20457521302980683084620139 30686281954471024626930209)
    ·
      refine ⟨23014711465853268470197657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30686281954471024626930209 23014711465853268470197657)
      ·
        refine ⟨17261033599389951352648243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23014711465853268470197657 17261033599389951352648243)
        ·
          refine ⟨25891550399084927028972365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17261033599389951352648243 25891550399084927028972365)
          ·
            refine ⟨9709331399656847635864637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25891550399084927028972365 9709331399656847635864637)
            ·
              refine ⟨3640999274871317863449239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9709331399656847635864637 3640999274871317863449239)
              ·
                refine ⟨5461498912306976795173859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3640999274871317863449239 5461498912306976795173859)
                ·
                  refine ⟨8192248368460465192760789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5461498912306976795173859 8192248368460465192760789)
                  ·
                    refine ⟨192005821135792152955331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8192248368460465192760789 192005821135792152955331)
                    ·
                      rfl

theorem cell22_560895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 7].length) (baseStart_560895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_560895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_560895 prefixEnd_560895 := by exact prefixLift 560895
  have htrace : WordTrace (prefixWord ++ tailWord_560895) baseStart_560895 baseEnd_560895 := by
    simpa [prefixWord, tailWord_560895, baseEnd_560895] using wordTrace_append hprefix tailTrace_560895
  have hstable : (prefixWord ++ tailWord_560895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560895).length < 2 ^ (prefixWord ++ tailWord_560895).sum := by decide
  have hdescent : baseEnd_560895 < baseStart_560895 := by decide
  rcases family_descends (prefixWord ++ tailWord_560895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560897 : List Nat := [1, 2, 4, 1, 1, 1, 4, 3, 5]
def baseStart_560897 : Nat := 118140960795 + 560897 * 2 ^ 59
def prefixEnd_560897 : Nat := 4983230072969 + 3 ^ 40 * 560897 * 2
def baseEnd_560897 : Nat := 64002168592221604801775

theorem tailTrace_560897 : CollatzResearch.WordTrace tailWord_560897 prefixEnd_560897 64002168592221604801775 := by
  unfold tailWord_560897
  simp only [CollatzResearch.WordTrace]
  refine ⟨20457594248973437426192945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13638396165982291617461963 20457594248973437426192945)
  ·
    refine ⟨15343195686730078069644709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20457594248973437426192945 15343195686730078069644709)
    ·
      refine ⟨2876849191261889638058383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15343195686730078069644709 2876849191261889638058383)
      ·
        refine ⟨4315273786892834457087575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2876849191261889638058383 4315273786892834457087575)
        ·
          refine ⟨6472910680339251685631363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4315273786892834457087575 6472910680339251685631363)
          ·
            refine ⟨9709366020508877528447045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6472910680339251685631363 9709366020508877528447045)
            ·
              refine ⟨1820506128845414536583821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9709366020508877528447045 1820506128845414536583821)
              ·
                refine ⟨682689798317030451218933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1820506128845414536583821 682689798317030451218933)
                ·
                  refine ⟨64002168592221604801775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 682689798317030451218933 64002168592221604801775)
                  ·
                    rfl

theorem cell22_560897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 3, 5].length) (baseStart_560897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_560897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_560897 prefixEnd_560897 := by exact prefixLift 560897
  have htrace : WordTrace (prefixWord ++ tailWord_560897) baseStart_560897 baseEnd_560897 := by
    simpa [prefixWord, tailWord_560897, baseEnd_560897] using wordTrace_append hprefix tailTrace_560897
  have hstable : (prefixWord ++ tailWord_560897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560897).length < 2 ^ (prefixWord ++ tailWord_560897).sum := by decide
  have hdescent : baseEnd_560897 < baseStart_560897 := by decide
  rcases family_descends (prefixWord ++ tailWord_560897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561036 : List Nat := [2, 2, 1, 2, 1, 2, 1, 7, 1, 3]
def baseStart_561036 : Nat := 118140960795 + 561036 * 2 ^ 59
def prefixEnd_561036 : Nat := 4983230072969 + 3 ^ 40 * 561036 * 2
def baseEnd_561036 : Nat := 192054088317314785179899

theorem tailTrace_561036 : CollatzResearch.WordTrace tailWord_561036 prefixEnd_561036 192054088317314785179899 := by
  unfold tailWord_561036
  simp only [CollatzResearch.WordTrace]
  refine ⟨10231331997734932082751481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13641775996979909443668641 10231331997734932082751481)
  ·
    refine ⟨7673498998301199062063611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10231331997734932082751481 7673498998301199062063611)
    ·
      refine ⟨11510248497451798593095417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7673498998301199062063611 11510248497451798593095417)
      ·
        refine ⟨8632686373088848944821563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11510248497451798593095417 8632686373088848944821563)
        ·
          refine ⟨12949029559633273417232345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8632686373088848944821563 12949029559633273417232345)
          ·
            refine ⟨9711772169724955062924259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12949029559633273417232345 9711772169724955062924259)
            ·
              refine ⟨14567658254587432594386389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9711772169724955062924259 14567658254587432594386389)
              ·
                refine ⟨341429490341892951430931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 14567658254587432594386389 341429490341892951430931)
                ·
                  refine ⟨512144235512839427146397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 341429490341892951430931 512144235512839427146397)
                  ·
                    refine ⟨192054088317314785179899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 512144235512839427146397 192054088317314785179899)
                    ·
                      rfl

theorem cell22_561036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 7, 1, 3].length) (baseStart_561036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_561036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_561036 prefixEnd_561036 := by exact prefixLift 561036
  have htrace : WordTrace (prefixWord ++ tailWord_561036) baseStart_561036 baseEnd_561036 := by
    simpa [prefixWord, tailWord_561036, baseEnd_561036] using wordTrace_append hprefix tailTrace_561036
  have hstable : (prefixWord ++ tailWord_561036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561036).length < 2 ^ (prefixWord ++ tailWord_561036).sum := by decide
  have hdescent : baseEnd_561036 < baseStart_561036 := by decide
  rcases family_descends (prefixWord ++ tailWord_561036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561053 : List Nat := [1, 4, 2, 1, 2, 3, 1, 4, 1, 3]
def baseStart_561053 : Nat := 118140960795 + 561053 * 2 ^ 59
def prefixEnd_561053 : Nat := 4983230072969 + 3 ^ 40 * 561053 * 2
def baseEnd_561053 : Nat := 192059907764732407504847

theorem tailTrace_561053 : CollatzResearch.WordTrace tailWord_561053 prefixEnd_561053 192059907764732407504847 := by
  unfold tailWord_561053
  simp only [CollatzResearch.WordTrace]
  refine ⟨20463284036408276068871813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13642189357605517379247875 20463284036408276068871813)
  ·
    refine ⟨3836865756826551762913465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20463284036408276068871813 3836865756826551762913465)
    ·
      refine ⟨2877649317619913822185099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3836865756826551762913465 2877649317619913822185099)
      ·
        refine ⟨4316473976429870733277649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2877649317619913822185099 4316473976429870733277649)
        ·
          refine ⟨3237355482322403049958237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4316473976429870733277649 3237355482322403049958237)
          ·
            refine ⟨1214008305870901143734339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3237355482322403049958237 1214008305870901143734339)
            ·
              refine ⟨1821012458806351715601509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1214008305870901143734339 1821012458806351715601509)
              ·
                refine ⟨341439836026190946675283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1821012458806351715601509 341439836026190946675283)
                ·
                  refine ⟨512159754039286420012925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 341439836026190946675283 512159754039286420012925)
                  ·
                    refine ⟨192059907764732407504847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 512159754039286420012925 192059907764732407504847)
                    ·
                      rfl

theorem cell22_561053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_561053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_561053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_561053 prefixEnd_561053 := by exact prefixLift 561053
  have htrace : WordTrace (prefixWord ++ tailWord_561053) baseStart_561053 baseEnd_561053 := by
    simpa [prefixWord, tailWord_561053, baseEnd_561053] using wordTrace_append hprefix tailTrace_561053
  have hstable : (prefixWord ++ tailWord_561053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561053).length < 2 ^ (prefixWord ++ tailWord_561053).sum := by decide
  have hdescent : baseEnd_561053 < baseStart_561053 := by decide
  rcases family_descends (prefixWord ++ tailWord_561053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561079 : List Nat := [1, 1, 3, 1, 3, 1, 1, 6, 1, 4]
def baseStart_561079 : Nat := 118140960795 + 561079 * 2 ^ 59
def prefixEnd_561079 : Nat := 4983230072969 + 3 ^ 40 * 561079 * 2
def baseEnd_561079 : Nat := 192068808096077006354767

theorem tailTrace_561079 : CollatzResearch.WordTrace tailWord_561079 prefixEnd_561079 192068808096077006354767 := by
  unfold tailWord_561079
  simp only [CollatzResearch.WordTrace]
  refine ⟨20464232334314082509318291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13642821556209388339545527 20464232334314082509318291)
  ·
    refine ⟨30696348501471123763977437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20464232334314082509318291 30696348501471123763977437)
    ·
      refine ⟨11511130688051671411491539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30696348501471123763977437 11511130688051671411491539)
      ·
        refine ⟨17266696032077507117237309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11511130688051671411491539 17266696032077507117237309)
        ·
          refine ⟨6475011012029065168963991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17266696032077507117237309 6475011012029065168963991)
          ·
            refine ⟨9712516518043597753445987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6475011012029065168963991 9712516518043597753445987)
            ·
              refine ⟨14568774777065396630168981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9712516518043597753445987 14568774777065396630168981)
              ·
                refine ⟨682911317674940467039171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14568774777065396630168981 682911317674940467039171)
                ·
                  refine ⟨1024366976512410700558757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 682911317674940467039171 1024366976512410700558757)
                  ·
                    refine ⟨192068808096077006354767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1024366976512410700558757 192068808096077006354767)
                    ·
                      rfl

theorem cell22_561079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 6, 1, 4].length) (baseStart_561079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_561079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_561079 prefixEnd_561079 := by exact prefixLift 561079
  have htrace : WordTrace (prefixWord ++ tailWord_561079) baseStart_561079 baseEnd_561079 := by
    simpa [prefixWord, tailWord_561079, baseEnd_561079] using wordTrace_append hprefix tailTrace_561079
  have hstable : (prefixWord ++ tailWord_561079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561079).length < 2 ^ (prefixWord ++ tailWord_561079).sum := by decide
  have hdescent : baseEnd_561079 < baseStart_561079 := by decide
  rcases family_descends (prefixWord ++ tailWord_561079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561096 : List Nat := [2, 1, 3, 1, 4, 2, 1, 3, 1, 4]
def baseStart_561096 : Nat := 118140960795 + 561096 * 2 ^ 59
def prefixEnd_561096 : Nat := 4983230072969 + 3 ^ 40 * 561096 * 2
def baseEnd_561096 : Nat := 192074627543494628679715

theorem tailTrace_561096 : CollatzResearch.WordTrace tailWord_561096 prefixEnd_561096 192074627543494628679715 := by
  unfold tailWord_561096
  simp only [CollatzResearch.WordTrace]
  refine ⟨10232426187626247206343571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13643234916834996275124761 10232426187626247206343571)
  ·
    refine ⟨15348639281439370809515357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10232426187626247206343571 15348639281439370809515357)
    ·
      refine ⟨5755739730539764053568259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15348639281439370809515357 5755739730539764053568259)
      ·
        refine ⟨8633609595809646080352389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5755739730539764053568259 8633609595809646080352389)
        ·
          refine ⟨1618801799214308640066073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8633609595809646080352389 1618801799214308640066073)
          ·
            refine ⟨1214101349410731480049555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1618801799214308640066073 1214101349410731480049555)
            ·
              refine ⟨1821152024116097220074333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1214101349410731480049555 1821152024116097220074333)
              ·
                refine ⟨682932009043536457527875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1821152024116097220074333 682932009043536457527875)
                ·
                  refine ⟨1024398013565304686291813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 682932009043536457527875 1024398013565304686291813)
                  ·
                    refine ⟨192074627543494628679715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1024398013565304686291813 192074627543494628679715)
                    ·
                      rfl

theorem cell22_561096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_561096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_561096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_561096 prefixEnd_561096 := by exact prefixLift 561096
  have htrace : WordTrace (prefixWord ++ tailWord_561096) baseStart_561096 baseEnd_561096 := by
    simpa [prefixWord, tailWord_561096, baseEnd_561096] using wordTrace_append hprefix tailTrace_561096
  have hstable : (prefixWord ++ tailWord_561096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561096).length < 2 ^ (prefixWord ++ tailWord_561096).sum := by decide
  have hdescent : baseEnd_561096 < baseStart_561096 := by decide
  rcases family_descends (prefixWord ++ tailWord_561096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561171 : List Nat := [1, 1, 1, 2, 1, 4, 5, 1, 3, 3]
def baseStart_561171 : Nat := 118140960795 + 561171 * 2 ^ 59
def prefixEnd_561171 : Nat := 4983230072969 + 3 ^ 40 * 561171 * 2
def baseEnd_561171 : Nat := 192100301576219433054485

theorem tailTrace_561171 : CollatzResearch.WordTrace tailWord_561171 prefixEnd_561171 192100301576219433054485 := by
  unfold tailWord_561171
  simp only [CollatzResearch.WordTrace]
  refine ⟨20467587849980782221667367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13645058566653854814444911 20467587849980782221667367)
  ·
    refine ⟨30701381774971173332501051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20467587849980782221667367 30701381774971173332501051)
    ·
      refine ⟨46052072662456759998751577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30701381774971173332501051 46052072662456759998751577)
      ·
        refine ⟨34539054496842569999063683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46052072662456759998751577 34539054496842569999063683)
        ·
          refine ⟨51808581745263854998595525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34539054496842569999063683 51808581745263854998595525)
          ·
            refine ⟨9714109077236972812236661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51808581745263854998595525 9714109077236972812236661)
            ·
              refine ⟨910697725990966201147187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9714109077236972812236661 910697725990966201147187)
              ·
                refine ⟨1366046588986449301720781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 910697725990966201147187 1366046588986449301720781)
                ·
                  refine ⟨512267470869918488145293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1366046588986449301720781 512267470869918488145293)
                  ·
                    refine ⟨192100301576219433054485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 512267470869918488145293 192100301576219433054485)
                    ·
                      rfl

theorem cell22_561171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 3, 3].length) (baseStart_561171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_561171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_561171 prefixEnd_561171 := by exact prefixLift 561171
  have htrace : WordTrace (prefixWord ++ tailWord_561171) baseStart_561171 baseEnd_561171 := by
    simpa [prefixWord, tailWord_561171, baseEnd_561171] using wordTrace_append hprefix tailTrace_561171
  have hstable : (prefixWord ++ tailWord_561171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561171).length < 2 ^ (prefixWord ++ tailWord_561171).sum := by decide
  have hdescent : baseEnd_561171 < baseStart_561171 := by decide
  rcases family_descends (prefixWord ++ tailWord_561171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561222 : List Nat := [6, 1, 1, 1, 1, 1, 3, 4, 1, 3]
def baseStart_561222 : Nat := 118140960795 + 561222 * 2 ^ 59
def prefixEnd_561222 : Nat := 4983230072969 + 3 ^ 40 * 561222 * 2
def baseEnd_561222 : Nat := 192117759918472300029329

theorem tailTrace_561222 : CollatzResearch.WordTrace tailWord_561222 prefixEnd_561222 192117759918472300029329 := by
  unfold tailWord_561222
  simp only [CollatzResearch.WordTrace]
  refine ⟨639670249149875560367935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13646298648530678621182613 639670249149875560367935)
  ·
    refine ⟨959505373724813340551903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 639670249149875560367935 959505373724813340551903)
    ·
      refine ⟨1439258060587220010827855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 959505373724813340551903 1439258060587220010827855)
      ·
        refine ⟨2158887090880830016241783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1439258060587220010827855 2158887090880830016241783)
        ·
          refine ⟨3238330636321245024362675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2158887090880830016241783 3238330636321245024362675)
          ·
            refine ⟨4857495954481867536544013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3238330636321245024362675 4857495954481867536544013)
            ·
              refine ⟨1821560982930700326204005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4857495954481867536544013 1821560982930700326204005)
              ·
                refine ⟨341542684299506311163251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1821560982930700326204005 341542684299506311163251)
                ·
                  refine ⟨512314026449259466744877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 341542684299506311163251 512314026449259466744877)
                  ·
                    refine ⟨192117759918472300029329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 512314026449259466744877 192117759918472300029329)
                    ·
                      rfl

theorem cell22_561222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_561222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_561222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_561222 prefixEnd_561222 := by exact prefixLift 561222
  have htrace : WordTrace (prefixWord ++ tailWord_561222) baseStart_561222 baseEnd_561222 := by
    simpa [prefixWord, tailWord_561222, baseEnd_561222] using wordTrace_append hprefix tailTrace_561222
  have hstable : (prefixWord ++ tailWord_561222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561222).length < 2 ^ (prefixWord ++ tailWord_561222).sum := by decide
  have hdescent : baseEnd_561222 < baseStart_561222 := by decide
  rcases family_descends (prefixWord ++ tailWord_561222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561261 : List Nat := [1, 5, 1, 1, 2, 1, 1, 4, 1, 5]
def baseStart_561261 : Nat := 118140960795 + 561261 * 2 ^ 59
def prefixEnd_561261 : Nat := 4983230072969 + 3 ^ 40 * 561261 * 2
def baseEnd_561261 : Nat := 192131110415489198304209

theorem tailTrace_561261 : CollatzResearch.WordTrace tailWord_561261 prefixEnd_561261 192131110415489198304209 := by
  unfold tailWord_561261
  simp only [CollatzResearch.WordTrace]
  refine ⟨20470870419654727592443637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13647246946436485061629091 20470870419654727592443637)
  ·
    refine ⟨1919144101842630711791591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20470870419654727592443637 1919144101842630711791591)
    ·
      refine ⟨2878716152763946067687387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1919144101842630711791591 2878716152763946067687387)
      ·
        refine ⟨4318074229145919101531081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2878716152763946067687387 4318074229145919101531081)
        ·
          refine ⟨3238555671859439326148311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4318074229145919101531081 3238555671859439326148311)
          ·
            refine ⟨4857833507789158989222467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3238555671859439326148311 4857833507789158989222467)
            ·
              refine ⟨7286750261683738483833701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4857833507789158989222467 7286750261683738483833701)
              ·
                refine ⟨1366265674065700965718819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7286750261683738483833701 1366265674065700965718819)
                ·
                  refine ⟨2049398511098551448578229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1366265674065700965718819 2049398511098551448578229)
                  ·
                    refine ⟨192131110415489198304209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2049398511098551448578229 192131110415489198304209)
                    ·
                      rfl

theorem cell22_561261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_561261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_561261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_561261 prefixEnd_561261 := by exact prefixLift 561261
  have htrace : WordTrace (prefixWord ++ tailWord_561261) baseStart_561261 baseEnd_561261 := by
    simpa [prefixWord, tailWord_561261, baseEnd_561261] using wordTrace_append hprefix tailTrace_561261
  have hstable : (prefixWord ++ tailWord_561261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561261).length < 2 ^ (prefixWord ++ tailWord_561261).sum := by decide
  have hdescent : baseEnd_561261 < baseStart_561261 := by decide
  rcases family_descends (prefixWord ++ tailWord_561261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561263 : List Nat := [1, 1, 2, 1, 3, 5, 2, 3, 4]
def baseStart_561263 : Nat := 118140960795 + 561263 * 2 ^ 59
def prefixEnd_561263 : Nat := 4983230072969 + 3 ^ 40 * 561263 * 2
def baseEnd_561263 : Nat := 64043931685453953251401

theorem tailTrace_561263 : CollatzResearch.WordTrace tailWord_561263 prefixEnd_561263 64043931685453953251401 := by
  unfold tailWord_561263
  simp only [CollatzResearch.WordTrace]
  refine ⟨20470943365647481934016443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13647295577098321289344295 20470943365647481934016443)
  ·
    refine ⟨30706415048471222901024665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20470943365647481934016443 30706415048471222901024665)
    ·
      refine ⟨23029811286353417175768499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30706415048471222901024665 23029811286353417175768499)
      ·
        refine ⟨34544716929530125763652749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23029811286353417175768499 34544716929530125763652749)
        ·
          refine ⟨12954268848573797161369781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34544716929530125763652749 12954268848573797161369781)
          ·
            refine ⟨1214462704553793483878417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12954268848573797161369781 1214462704553793483878417)
            ·
              refine ⟨910847028415345112908813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1214462704553793483878417 910847028415345112908813)
              ·
                refine ⟨341567635655754417340805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 910847028415345112908813 341567635655754417340805)
                ·
                  refine ⟨64043931685453953251401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 341567635655754417340805 64043931685453953251401)
                  ·
                    rfl

theorem cell22_561263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 3, 4].length) (baseStart_561263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_561263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_561263 prefixEnd_561263 := by exact prefixLift 561263
  have htrace : WordTrace (prefixWord ++ tailWord_561263) baseStart_561263 baseEnd_561263 := by
    simpa [prefixWord, tailWord_561263, baseEnd_561263] using wordTrace_append hprefix tailTrace_561263
  have hstable : (prefixWord ++ tailWord_561263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561263).length < 2 ^ (prefixWord ++ tailWord_561263).sum := by decide
  have hdescent : baseEnd_561263 < baseStart_561263 := by decide
  rcases family_descends (prefixWord ++ tailWord_561263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561336 : List Nat := [2, 1, 2, 1, 2, 1, 4, 4, 5]
def baseStart_561336 : Nat := 118140960795 + 561336 * 2 ^ 59
def prefixEnd_561336 : Nat := 4983230072969 + 3 ^ 40 * 561336 * 2
def baseEnd_561336 : Nat := 64052261482738000892993

theorem tailTrace_561336 : CollatzResearch.WordTrace tailWord_561336 prefixEnd_561336 64052261482738000892993 := by
  unfold tailWord_561336
  simp only [CollatzResearch.WordTrace]
  refine ⟨10236802947191507700711931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13649070596255343600949241 10236802947191507700711931)
  ·
    refine ⟨15355204420787261551067897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10236802947191507700711931 15355204420787261551067897)
    ·
      refine ⟨11516403315590446163300923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15355204420787261551067897 11516403315590446163300923)
      ·
        refine ⟨17274604973385669244951385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11516403315590446163300923 17274604973385669244951385)
        ·
          refine ⟨12955953730039251933713539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17274604973385669244951385 12955953730039251933713539)
          ·
            refine ⟨19433930595058877900570309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12955953730039251933713539 19433930595058877900570309)
            ·
              refine ⟨3643861986573539606356933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19433930595058877900570309 3643861986573539606356933)
              ·
                refine ⟨683224122482538676191925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3643861986573539606356933 683224122482538676191925)
                ·
                  refine ⟨64052261482738000892993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 683224122482538676191925 64052261482738000892993)
                  ·
                    rfl

theorem cell22_561336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 4, 5].length) (baseStart_561336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_561336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_561336 prefixEnd_561336 := by exact prefixLift 561336
  have htrace : WordTrace (prefixWord ++ tailWord_561336) baseStart_561336 baseEnd_561336 := by
    simpa [prefixWord, tailWord_561336, baseEnd_561336] using wordTrace_append hprefix tailTrace_561336
  have hstable : (prefixWord ++ tailWord_561336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561336).length < 2 ^ (prefixWord ++ tailWord_561336).sum := by decide
  have hdescent : baseEnd_561336 < baseStart_561336 := by decide
  rcases family_descends (prefixWord ++ tailWord_561336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561346 : List Nat := [3, 5, 1, 1, 1, 3, 2, 1, 2, 3]
def baseStart_561346 : Nat := 118140960795 + 561346 * 2 ^ 59
def prefixEnd_561346 : Nat := 4983230072969 + 3 ^ 40 * 561346 * 2
def baseEnd_561346 : Nat := 192160207652577309928949

theorem tailTrace_561346 : CollatzResearch.WordTrace tailWord_561346 prefixEnd_561346 192160207652577309928949 := by
  unfold tailWord_561346
  simp only [CollatzResearch.WordTrace]
  refine ⟨5118492656086696777321973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13649313749564524739525261 5118492656086696777321973)
  ·
    refine ⟨479858686508127822873935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5118492656086696777321973 479858686508127822873935)
    ·
      refine ⟨719788029762191734310903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 479858686508127822873935 719788029762191734310903)
      ·
        refine ⟨1079682044643287601466355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 719788029762191734310903 1079682044643287601466355)
        ·
          refine ⟨1619523066964931402199533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1079682044643287601466355 1619523066964931402199533)
          ·
            refine ⟨607321150111849275824825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1619523066964931402199533 607321150111849275824825)
            ·
              refine ⟨455490862583886956868619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 607321150111849275824825 455490862583886956868619)
              ·
                refine ⟨683236293875830435302929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 455490862583886956868619 683236293875830435302929)
                ·
                  refine ⟨512427220406872826477197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 683236293875830435302929 512427220406872826477197)
                  ·
                    refine ⟨192160207652577309928949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 512427220406872826477197 192160207652577309928949)
                    ·
                      rfl

theorem cell22_561346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_561346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_561346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_561346 prefixEnd_561346 := by exact prefixLift 561346
  have htrace : WordTrace (prefixWord ++ tailWord_561346) baseStart_561346 baseEnd_561346 := by
    simpa [prefixWord, tailWord_561346, baseEnd_561346] using wordTrace_append hprefix tailTrace_561346
  have hstable : (prefixWord ++ tailWord_561346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561346).length < 2 ^ (prefixWord ++ tailWord_561346).sum := by decide
  have hdescent : baseEnd_561346 < baseStart_561346 := by decide
  rcases family_descends (prefixWord ++ tailWord_561346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561411 : List Nat := [1, 1, 1, 3, 2, 3, 2, 2, 1, 6]
def baseStart_561411 : Nat := 118140960795 + 561411 * 2 ^ 59
def prefixEnd_561411 : Nat := 4983230072969 + 3 ^ 40 * 561411 * 2
def baseEnd_561411 : Nat := 192182458480938807053749

theorem tailTrace_561411 : CollatzResearch.WordTrace tailWord_561411 prefixEnd_561411 192182458480938807053749 := by
  unfold tailWord_561411
  simp only [CollatzResearch.WordTrace]
  refine ⟨20476341369111303210404087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13650894246074202140269391 20476341369111303210404087)
  ·
    refine ⟨30714512053666954815606131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20476341369111303210404087 30714512053666954815606131)
    ·
      refine ⟨46071768080500432223409197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30714512053666954815606131 46071768080500432223409197)
      ·
        refine ⟨17276913030187662083778449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46071768080500432223409197 17276913030187662083778449)
        ·
          refine ⟨12957684772640746562833837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17276913030187662083778449 12957684772640746562833837)
          ·
            refine ⟨4859131789740279961062689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12957684772640746562833837 4859131789740279961062689)
            ·
              refine ⟨3644348842305209970797017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4859131789740279961062689 3644348842305209970797017)
              ·
                refine ⟨2733261631728907478097763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3644348842305209970797017 2733261631728907478097763)
                ·
                  refine ⟨4099892447593361217146645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2733261631728907478097763 4099892447593361217146645)
                  ·
                    refine ⟨192182458480938807053749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4099892447593361217146645 192182458480938807053749)
                    ·
                      rfl

theorem cell22_561411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 6].length) (baseStart_561411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_561411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_561411 prefixEnd_561411 := by exact prefixLift 561411
  have htrace : WordTrace (prefixWord ++ tailWord_561411) baseStart_561411 baseEnd_561411 := by
    simpa [prefixWord, tailWord_561411, baseEnd_561411] using wordTrace_append hprefix tailTrace_561411
  have hstable : (prefixWord ++ tailWord_561411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561411).length < 2 ^ (prefixWord ++ tailWord_561411).sum := by decide
  have hdescent : baseEnd_561411 < baseStart_561411 := by decide
  rcases family_descends (prefixWord ++ tailWord_561411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561415 : List Nat := [1, 1, 4, 5, 1, 1, 1, 2, 6]
def baseStart_561415 : Nat := 118140960795 + 561415 * 2 ^ 59
def prefixEnd_561415 : Nat := 4983230072969 + 3 ^ 40 * 561415 * 2
def baseEnd_561415 : Nat := 64061275920894709984579

theorem tailTrace_561415 : CollatzResearch.WordTrace tailWord_561415 prefixEnd_561415 64061275920894709984579 := by
  unfold tailWord_561415
  simp only [CollatzResearch.WordTrace]
  refine ⟨20476487261096811893549699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13650991507397874595699799 20476487261096811893549699)
  ·
    refine ⟨30714730891645217840324549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20476487261096811893549699 30714730891645217840324549)
    ·
      refine ⟨5759012042183478345060853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30714730891645217840324549 5759012042183478345060853)
      ·
        refine ⟨539907378954701094849455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5759012042183478345060853 539907378954701094849455)
        ·
          refine ⟨809861068432051642274183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 539907378954701094849455 809861068432051642274183)
          ·
            refine ⟨1214791602648077463411275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 809861068432051642274183 1214791602648077463411275)
            ·
              refine ⟨1822187403972116195116913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1214791602648077463411275 1822187403972116195116913)
              ·
                refine ⟨1366640552979087146337685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1822187403972116195116913 1366640552979087146337685)
                ·
                  refine ⟨64061275920894709984579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1366640552979087146337685 64061275920894709984579)
                  ·
                    rfl

theorem cell22_561415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 6].length) (baseStart_561415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_561415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_561415 prefixEnd_561415 := by exact prefixLift 561415
  have htrace : WordTrace (prefixWord ++ tailWord_561415) baseStart_561415 baseEnd_561415 := by
    simpa [prefixWord, tailWord_561415, baseEnd_561415] using wordTrace_append hprefix tailTrace_561415
  have hstable : (prefixWord ++ tailWord_561415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561415).length < 2 ^ (prefixWord ++ tailWord_561415).sum := by decide
  have hdescent : baseEnd_561415 < baseStart_561415 := by decide
  rcases family_descends (prefixWord ++ tailWord_561415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561434 : List Nat := [3, 1, 1, 3, 5, 1, 2, 1, 1, 4]
def baseStart_561434 : Nat := 118140960795 + 561434 * 2 ^ 59
def prefixEnd_561434 : Nat := 4983230072969 + 3 ^ 40 * 561434 * 2
def baseEnd_561434 : Nat := 192190331850974413728679

theorem tailTrace_561434 : CollatzResearch.WordTrace tailWord_561434 prefixEnd_561434 192190331850974413728679 := by
  unfold tailWord_561434
  simp only [CollatzResearch.WordTrace]
  refine ⟨5119295062006994534622839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13651453498685318758994237 5119295062006994534622839)
  ·
    refine ⟨7678942593010491801934259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5119295062006994534622839 7678942593010491801934259)
    ·
      refine ⟨11518413889515737702901389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7678942593010491801934259 11518413889515737702901389)
      ·
        refine ⟨4319405208568401638588021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11518413889515737702901389 4319405208568401638588021)
        ·
          refine ⟨404944238303287653617627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4319405208568401638588021 404944238303287653617627)
          ·
            refine ⟨607416357454931480426441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404944238303287653617627 607416357454931480426441)
            ·
              refine ⟨455562268091198610319831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 607416357454931480426441 455562268091198610319831)
              ·
                refine ⟨683343402136797915479747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 455562268091198610319831 683343402136797915479747)
                ·
                  refine ⟨1025015103205196873219621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 683343402136797915479747 1025015103205196873219621)
                  ·
                    refine ⟨192190331850974413728679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1025015103205196873219621 192190331850974413728679)
                    ·
                      rfl

theorem cell22_561434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 1, 1, 4].length) (baseStart_561434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_561434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_561434 prefixEnd_561434 := by exact prefixLift 561434
  have htrace : WordTrace (prefixWord ++ tailWord_561434) baseStart_561434 baseEnd_561434 := by
    simpa [prefixWord, tailWord_561434, baseEnd_561434] using wordTrace_append hprefix tailTrace_561434
  have hstable : (prefixWord ++ tailWord_561434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561434).length < 2 ^ (prefixWord ++ tailWord_561434).sum := by decide
  have hdescent : baseEnd_561434 < baseStart_561434 := by decide
  rcases family_descends (prefixWord ++ tailWord_561434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561456 : List Nat := [2, 1, 1, 1, 2, 2, 2, 3, 2, 6]
def baseStart_561456 : Nat := 118140960795 + 561456 * 2 ^ 59
def prefixEnd_561456 : Nat := 4983230072969 + 3 ^ 40 * 561456 * 2
def baseEnd_561456 : Nat := 192197862900573689678611

theorem tailTrace_561456 : CollatzResearch.WordTrace tailWord_561456 prefixEnd_561456 192197862900573689678611 := by
  unfold tailWord_561456
  simp only [CollatzResearch.WordTrace]
  refine ⟨10238991326974137947896111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13651988435965517263861481 10238991326974137947896111)
  ·
    refine ⟨15358486990461206921844167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10238991326974137947896111 15358486990461206921844167)
    ·
      refine ⟨23037730485691810382766251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15358486990461206921844167 23037730485691810382766251)
      ·
        refine ⟨34556595728537715574149377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23037730485691810382766251 34556595728537715574149377)
        ·
          refine ⟨25917446796403286680612033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34556595728537715574149377 25917446796403286680612033)
          ·
            refine ⟨19438085097302465010459025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25917446796403286680612033 19438085097302465010459025)
            ·
              refine ⟨14578563822976848757844269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19438085097302465010459025 14578563822976848757844269)
              ·
                refine ⟨5466961433616318284191601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14578563822976848757844269 5466961433616318284191601)
                ·
                  refine ⟨4100221075212238713143701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5466961433616318284191601 4100221075212238713143701)
                  ·
                    refine ⟨192197862900573689678611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4100221075212238713143701 192197862900573689678611)
                    ·
                      rfl

theorem cell22_561456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 2, 6].length) (baseStart_561456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_561456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_561456 prefixEnd_561456 := by exact prefixLift 561456
  have htrace : WordTrace (prefixWord ++ tailWord_561456) baseStart_561456 baseEnd_561456 := by
    simpa [prefixWord, tailWord_561456, baseEnd_561456] using wordTrace_append hprefix tailTrace_561456
  have hstable : (prefixWord ++ tailWord_561456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561456).length < 2 ^ (prefixWord ++ tailWord_561456).sum := by decide
  have hdescent : baseEnd_561456 < baseStart_561456 := by decide
  rcases family_descends (prefixWord ++ tailWord_561456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561509 : List Nat := [1, 3, 1, 3, 1, 4, 3, 2, 1, 3]
def baseStart_561509 : Nat := 118140960795 + 561509 * 2 ^ 59
def prefixEnd_561509 : Nat := 4983230072969 + 3 ^ 40 * 561509 * 2
def baseEnd_561509 : Nat := 192216005883699218103449

theorem tailTrace_561509 : CollatzResearch.WordTrace tailWord_561509 prefixEnd_561509 192216005883699218103449 := by
  unfold tailWord_561509
  simp only [CollatzResearch.WordTrace]
  refine ⟨20479915722756265947471581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13653277148504177298314387 20479915722756265947471581)
  ·
    refine ⟨7679968396033599730301843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20479915722756265947471581 7679968396033599730301843)
    ·
      refine ⟨11519952594050399595452765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7679968396033599730301843 11519952594050399595452765)
      ·
        refine ⟨4319982222768899848294787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11519952594050399595452765 4319982222768899848294787)
        ·
          refine ⟨6479973334153349772442181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4319982222768899848294787 6479973334153349772442181)
          ·
            refine ⟨1214995000153753082332909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6479973334153349772442181 1214995000153753082332909)
            ·
              refine ⟨455623125057657405874841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1214995000153753082332909 455623125057657405874841)
              ·
                refine ⟨341717343793243054406131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 455623125057657405874841 341717343793243054406131)
                ·
                  refine ⟨512576015689864581609197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 341717343793243054406131 512576015689864581609197)
                  ·
                    refine ⟨192216005883699218103449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 512576015689864581609197 192216005883699218103449)
                    ·
                      rfl

theorem cell22_561509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 2, 1, 3].length) (baseStart_561509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_561509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_561509 prefixEnd_561509 := by exact prefixLift 561509
  have htrace : WordTrace (prefixWord ++ tailWord_561509) baseStart_561509 baseEnd_561509 := by
    simpa [prefixWord, tailWord_561509, baseEnd_561509] using wordTrace_append hprefix tailTrace_561509
  have hstable : (prefixWord ++ tailWord_561509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561509).length < 2 ^ (prefixWord ++ tailWord_561509).sum := by decide
  have hdescent : baseEnd_561509 < baseStart_561509 := by decide
  rcases family_descends (prefixWord ++ tailWord_561509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561522 : List Nat := [3, 2, 1, 2, 1, 5, 2, 1, 5]
def baseStart_561522 : Nat := 118140960795 + 561522 * 2 ^ 59
def prefixEnd_561522 : Nat := 4983230072969 + 3 ^ 40 * 561522 * 2
def baseEnd_561522 : Nat := 64073485349790505842803

theorem tailTrace_561522 : CollatzResearch.WordTrace tailWord_561522 prefixEnd_561522 64073485349790505842803 := by
  unfold tailWord_561522
  simp only [CollatzResearch.WordTrace]
  refine ⟨5120097467927292291923705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13653593247806112778463213 5120097467927292291923705)
  ·
    refine ⟨3840073100945469218942779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5120097467927292291923705 3840073100945469218942779)
    ·
      refine ⟨5760109651418203828414169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3840073100945469218942779 5760109651418203828414169)
      ·
        refine ⟨4320082238563652871310627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5760109651418203828414169 4320082238563652871310627)
        ·
          refine ⟨6480123357845479306965941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4320082238563652871310627 6480123357845479306965941)
          ·
            refine ⟨607511564798013685028057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6480123357845479306965941 607511564798013685028057)
            ·
              refine ⟨455633673598510263771043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 607511564798013685028057 455633673598510263771043)
              ·
                refine ⟨683450510397765395656565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 455633673598510263771043 683450510397765395656565)
                ·
                  refine ⟨64073485349790505842803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 683450510397765395656565 64073485349790505842803)
                  ·
                    rfl

theorem cell22_561522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 1, 5].length) (baseStart_561522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_561522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_561522 prefixEnd_561522 := by exact prefixLift 561522
  have htrace : WordTrace (prefixWord ++ tailWord_561522) baseStart_561522 baseEnd_561522 := by
    simpa [prefixWord, tailWord_561522, baseEnd_561522] using wordTrace_append hprefix tailTrace_561522
  have hstable : (prefixWord ++ tailWord_561522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561522).length < 2 ^ (prefixWord ++ tailWord_561522).sum := by decide
  have hdescent : baseEnd_561522 < baseStart_561522 := by decide
  rcases family_descends (prefixWord ++ tailWord_561522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561548 : List Nat := [2, 2, 1, 2, 1, 4, 1, 1, 3, 5]
def baseStart_561548 : Nat := 118140960795 + 561548 * 2 ^ 59
def prefixEnd_561548 : Nat := 4983230072969 + 3 ^ 40 * 561548 * 2
def baseEnd_561548 : Nat := 192229356380716116378329

theorem tailTrace_561548 : CollatzResearch.WordTrace tailWord_561548 prefixEnd_561548 192229356380716116378329 := by
  unfold tailWord_561548
  simp only [CollatzResearch.WordTrace]
  refine ⟨10240669084807487804070649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13654225446409983738760865 10240669084807487804070649)
  ·
    refine ⟨7680501813605615853052987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10240669084807487804070649 7680501813605615853052987)
    ·
      refine ⟨11520752720408423779579481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7680501813605615853052987 11520752720408423779579481)
      ·
        refine ⟨8640564540306317834684611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11520752720408423779579481 8640564540306317834684611)
        ·
          refine ⟨12960846810459476752026917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8640564540306317834684611 12960846810459476752026917)
          ·
            refine ⟨2430158776961151891005047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12960846810459476752026917 2430158776961151891005047)
            ·
              refine ⟨3645238165441727836507571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2430158776961151891005047 3645238165441727836507571)
              ·
                refine ⟨5467857248162591754761357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3645238165441727836507571 5467857248162591754761357)
                ·
                  refine ⟨2050446468060971908035509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5467857248162591754761357 2050446468060971908035509)
                  ·
                    refine ⟨192229356380716116378329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2050446468060971908035509 192229356380716116378329)
                    ·
                      rfl

theorem cell22_561548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_561548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_561548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_561548 prefixEnd_561548 := by exact prefixLift 561548
  have htrace : WordTrace (prefixWord ++ tailWord_561548) baseStart_561548 baseEnd_561548 := by
    simpa [prefixWord, tailWord_561548, baseEnd_561548] using wordTrace_append hprefix tailTrace_561548
  have hstable : (prefixWord ++ tailWord_561548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561548).length < 2 ^ (prefixWord ++ tailWord_561548).sum := by decide
  have hdescent : baseEnd_561548 < baseStart_561548 := by decide
  rcases family_descends (prefixWord ++ tailWord_561548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561597 : List Nat := [1, 4, 1, 2, 2, 4, 1, 1, 2, 4]
def baseStart_561597 : Nat := 118140960795 + 561597 * 2 ^ 59
def prefixEnd_561597 : Nat := 4983230072969 + 3 ^ 40 * 561597 * 2
def baseEnd_561597 : Nat := 192246130082096321903179

theorem tailTrace_561597 : CollatzResearch.WordTrace tailWord_561597 prefixEnd_561597 192246130082096321903179 := by
  unfold tailWord_561597
  simp only [CollatzResearch.WordTrace]
  refine ⟨20483125346437456976675045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13655416897624971317783363 20483125346437456976675045)
  ·
    refine ⟨3840586002457023183126571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20483125346437456976675045 3840586002457023183126571)
    ·
      refine ⟨5760879003685534774689857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3840586002457023183126571 5760879003685534774689857)
      ·
        refine ⟨4320659252764151081017393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5760879003685534774689857 4320659252764151081017393)
        ·
          refine ⟨3240494439573113310763045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4320659252764151081017393 3240494439573113310763045)
          ·
            refine ⟨607592707419958745768071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3240494439573113310763045 607592707419958745768071)
            ·
              refine ⟨911389061129938118652107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 607592707419958745768071 911389061129938118652107)
              ·
                refine ⟨1367083591694907177978161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 911389061129938118652107 1367083591694907177978161)
                ·
                  refine ⟨1025312693771180383483621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1367083591694907177978161 1025312693771180383483621)
                  ·
                    refine ⟨192246130082096321903179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1025312693771180383483621 192246130082096321903179)
                    ·
                      rfl

theorem cell22_561597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 2, 4].length) (baseStart_561597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_561597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_561597 prefixEnd_561597 := by exact prefixLift 561597
  have htrace : WordTrace (prefixWord ++ tailWord_561597) baseStart_561597 baseEnd_561597 := by
    simpa [prefixWord, tailWord_561597, baseEnd_561597] using wordTrace_append hprefix tailTrace_561597
  have hstable : (prefixWord ++ tailWord_561597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561597).length < 2 ^ (prefixWord ++ tailWord_561597).sum := by decide
  have hdescent : baseEnd_561597 < baseStart_561597 := by decide
  rcases family_descends (prefixWord ++ tailWord_561597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561610 : List Nat := [3, 1, 2, 1, 2, 2, 1, 2, 5, 3]
def baseStart_561610 : Nat := 118140960795 + 561610 * 2 ^ 59
def prefixEnd_561610 : Nat := 4983230072969 + 3 ^ 40 * 561610 * 2
def baseEnd_561610 : Nat := 192250580247768621328139

theorem tailTrace_561610 : CollatzResearch.WordTrace tailWord_561610 prefixEnd_561610 192250580247768621328139 := by
  unfold tailWord_561610
  simp only [CollatzResearch.WordTrace]
  refine ⟨5120899873847590049224571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13655732996926906797932189 5120899873847590049224571)
  ·
    refine ⟨7681349810771385073836857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5120899873847590049224571 7681349810771385073836857)
    ·
      refine ⟨5761012358078538805377643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7681349810771385073836857 5761012358078538805377643)
      ·
        refine ⟨8641518537117808208066465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5761012358078538805377643 8641518537117808208066465)
        ·
          refine ⟨6481138902838356156049849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8641518537117808208066465 6481138902838356156049849)
          ·
            refine ⟨4860854177128767117037387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6481138902838356156049849 4860854177128767117037387)
            ·
              refine ⟨7291281265693150675556081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4860854177128767117037387 7291281265693150675556081)
              ·
                refine ⟨5468460949269863006667061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7291281265693150675556081 5468460949269863006667061)
                ·
                  refine ⟨512668213994049656875037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5468460949269863006667061 512668213994049656875037)
                  ·
                    refine ⟨192250580247768621328139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 512668213994049656875037 192250580247768621328139)
                    ·
                      rfl

theorem cell22_561610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 5, 3].length) (baseStart_561610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_561610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_561610 prefixEnd_561610 := by exact prefixLift 561610
  have htrace : WordTrace (prefixWord ++ tailWord_561610) baseStart_561610 baseEnd_561610 := by
    simpa [prefixWord, tailWord_561610, baseEnd_561610] using wordTrace_append hprefix tailTrace_561610
  have hstable : (prefixWord ++ tailWord_561610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561610).length < 2 ^ (prefixWord ++ tailWord_561610).sum := by decide
  have hdescent : baseEnd_561610 < baseStart_561610 := by decide
  rcases family_descends (prefixWord ++ tailWord_561610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561704 : List Nat := [2, 1, 5, 2, 1, 1, 3, 2, 1, 4]
def baseStart_561704 : Nat := 118140960795 + 561704 * 2 ^ 59
def prefixEnd_561704 : Nat := 4983230072969 + 3 ^ 40 * 561704 * 2
def baseEnd_561704 : Nat := 192282758368783709477851

theorem tailTrace_561704 : CollatzResearch.WordTrace tailWord_561704 prefixEnd_561704 192282758368783709477851 := by
  unfold tailWord_561704
  simp only [CollatzResearch.WordTrace]
  refine ⟨10243513978524907125410083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13658018638033209500546777 10243513978524907125410083)
  ·
    refine ⟨15365270967787360688115125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10243513978524907125410083 15365270967787360688115125)
    ·
      refine ⟨1440494153230065064510793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15365270967787360688115125 1440494153230065064510793)
      ·
        refine ⟨1080370614922548798383095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1440494153230065064510793 1080370614922548798383095)
        ·
          refine ⟨1620555922383823197574643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1080370614922548798383095 1620555922383823197574643)
          ·
            refine ⟨2430833883575734796361965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1620555922383823197574643 2430833883575734796361965)
            ·
              refine ⟨911562706340900548635737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2430833883575734796361965 911562706340900548635737)
              ·
                refine ⟨683672029755675411476803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 911562706340900548635737 683672029755675411476803)
                ·
                  refine ⟨1025508044633513117215205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 683672029755675411476803 1025508044633513117215205)
                  ·
                    refine ⟨192282758368783709477851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1025508044633513117215205 192282758368783709477851)
                    ·
                      rfl

theorem cell22_561704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_561704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_561704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_561704 prefixEnd_561704 := by exact prefixLift 561704
  have htrace : WordTrace (prefixWord ++ tailWord_561704) baseStart_561704 baseEnd_561704 := by
    simpa [prefixWord, tailWord_561704, baseEnd_561704] using wordTrace_append hprefix tailTrace_561704
  have hstable : (prefixWord ++ tailWord_561704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561704).length < 2 ^ (prefixWord ++ tailWord_561704).sum := by decide
  have hdescent : baseEnd_561704 < baseStart_561704 := by decide
  rcases family_descends (prefixWord ++ tailWord_561704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561792 : List Nat := [2, 1, 1, 2, 1, 5, 3, 2, 5]
def baseStart_561792 : Nat := 118140960795 + 561792 * 2 ^ 59
def prefixEnd_561792 : Nat := 4983230072969 + 3 ^ 40 * 561792 * 2
def baseEnd_561792 : Nat := 64104294189060271092527

theorem tailTrace_561792 : CollatzResearch.WordTrace tailWord_561792 prefixEnd_561792 64104294189060271092527 := by
  unfold tailWord_561792
  simp only [CollatzResearch.WordTrace]
  refine ⟨10245118790365502640011815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13660158387154003520015753 10245118790365502640011815)
  ·
    refine ⟨15367678185548253960017723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10245118790365502640011815 15367678185548253960017723)
    ·
      refine ⟨23051517278322380940026585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15367678185548253960017723 23051517278322380940026585)
      ·
        refine ⟨17288637958741785705019939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23051517278322380940026585 17288637958741785705019939)
        ·
          refine ⟨25932956938112678557529909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17288637958741785705019939 25932956938112678557529909)
          ·
            refine ⟨2431214712948063614768429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25932956938112678557529909 2431214712948063614768429)
            ·
              refine ⟨911705517355523855538161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2431214712948063614768429 911705517355523855538161)
              ·
                refine ⟨683779138016642891653621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 911705517355523855538161 683779138016642891653621)
                ·
                  refine ⟨64104294189060271092527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 683779138016642891653621 64104294189060271092527)
                  ·
                    rfl

theorem cell22_561792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 2, 5].length) (baseStart_561792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_561792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_561792 prefixEnd_561792 := by exact prefixLift 561792
  have htrace : WordTrace (prefixWord ++ tailWord_561792) baseStart_561792 baseEnd_561792 := by
    simpa [prefixWord, tailWord_561792, baseEnd_561792] using wordTrace_append hprefix tailTrace_561792
  have hstable : (prefixWord ++ tailWord_561792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561792).length < 2 ^ (prefixWord ++ tailWord_561792).sum := by decide
  have hdescent : baseEnd_561792 < baseStart_561792 := by decide
  rcases family_descends (prefixWord ++ tailWord_561792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561796 : List Nat := [2, 3, 2, 1, 3, 1, 2, 4, 1, 3]
def baseStart_561796 : Nat := 118140960795 + 561796 * 2 ^ 59
def prefixEnd_561796 : Nat := 4983230072969 + 3 ^ 40 * 561796 * 2
def baseEnd_561796 : Nat := 192314251848926136177569

theorem tailTrace_561796 : CollatzResearch.WordTrace tailWord_561796 prefixEnd_561796 192314251848926136177569 := by
  unfold tailWord_561796
  simp only [CollatzResearch.WordTrace]
  refine ⟨10245191736358256981584621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13660255648477675975446161 10245191736358256981584621)
  ·
    refine ⟨3841946901134346368094233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10245191736358256981584621 3841946901134346368094233)
    ·
      refine ⟨2881460175850759776070675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3841946901134346368094233 2881460175850759776070675)
      ·
        refine ⟨4322190263776139664106013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2881460175850759776070675 4322190263776139664106013)
        ·
          refine ⟨1620821348916052374039755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4322190263776139664106013 1620821348916052374039755)
          ·
            refine ⟨2431232023374078561059633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1620821348916052374039755 2431232023374078561059633)
            ·
              refine ⟨1823424017530558920794725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2431232023374078561059633 1823424017530558920794725)
              ·
                refine ⟨341892003286979797649011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1823424017530558920794725 341892003286979797649011)
                ·
                  refine ⟨512838004930469696473517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 341892003286979797649011 512838004930469696473517)
                  ·
                    refine ⟨192314251848926136177569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 512838004930469696473517 192314251848926136177569)
                    ·
                      rfl

theorem cell22_561796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_561796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_561796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_561796 prefixEnd_561796 := by exact prefixLift 561796
  have htrace : WordTrace (prefixWord ++ tailWord_561796) baseStart_561796 baseEnd_561796 := by
    simpa [prefixWord, tailWord_561796, baseEnd_561796] using wordTrace_append hprefix tailTrace_561796
  have hstable : (prefixWord ++ tailWord_561796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561796).length < 2 ^ (prefixWord ++ tailWord_561796).sum := by decide
  have hdescent : baseEnd_561796 < baseStart_561796 := by decide
  rcases family_descends (prefixWord ++ tailWord_561796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561948 : List Nat := [2, 2, 3, 1, 1, 4, 2, 3, 1, 3]
def baseStart_561948 : Nat := 118140960795 + 561948 * 2 ^ 59
def prefixEnd_561948 : Nat := 4983230072969 + 3 ^ 40 * 561948 * 2
def baseEnd_561948 : Nat := 192366284555248406377103

theorem tailTrace_561948 : CollatzResearch.WordTrace tailWord_561948 prefixEnd_561948 192366284555248406377103 := by
  unfold tailWord_561948
  simp only [CollatzResearch.WordTrace]
  refine ⟨10247963684082921961351249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13663951578777229281801665 10247963684082921961351249)
  ·
    refine ⟨7685972763062191471013437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10247963684082921961351249 7685972763062191471013437)
    ·
      refine ⟨2882239786148321801630039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7685972763062191471013437 2882239786148321801630039)
      ·
        refine ⟨4323359679222482702445059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2882239786148321801630039 4323359679222482702445059)
        ·
          refine ⟨6485039518833724053667589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4323359679222482702445059 6485039518833724053667589)
          ·
            refine ⟨1215944909781323260062673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6485039518833724053667589 1215944909781323260062673)
            ·
              refine ⟨911958682335992445047005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1215944909781323260062673 911958682335992445047005)
              ·
                refine ⟨341984505875997166892627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 911958682335992445047005 341984505875997166892627)
                ·
                  refine ⟨512976758813995750338941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 341984505875997166892627 512976758813995750338941)
                  ·
                    refine ⟨192366284555248406377103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 512976758813995750338941 192366284555248406377103)
                    ·
                      rfl

theorem cell22_561948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_561948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_561948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_561948 prefixEnd_561948 := by exact prefixLift 561948
  have htrace : WordTrace (prefixWord ++ tailWord_561948) baseStart_561948 baseEnd_561948 := by
    simpa [prefixWord, tailWord_561948, baseEnd_561948] using wordTrace_append hprefix tailTrace_561948
  have hstable : (prefixWord ++ tailWord_561948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561948).length < 2 ^ (prefixWord ++ tailWord_561948).sum := by decide
  have hdescent : baseEnd_561948 < baseStart_561948 := by decide
  rcases family_descends (prefixWord ++ tailWord_561948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561965 : List Nat := [1, 5, 3, 2, 1, 1, 2, 1, 3, 3]
def baseStart_561965 : Nat := 118140960795 + 561965 * 2 ^ 59
def prefixEnd_561965 : Nat := 4983230072969 + 3 ^ 40 * 561965 * 2
def baseEnd_561965 : Nat := 192372104002666028702051

theorem tailTrace_561965 : CollatzResearch.WordTrace tailWord_561965 prefixEnd_561965 192372104002666028702051 := by
  unfold tailWord_561965
  simp only [CollatzResearch.WordTrace]
  refine ⟨20496547409104255826071349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13664364939402837217380899 20496547409104255826071349)
  ·
    refine ⟨1921551319603523983694189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20496547409104255826071349 1921551319603523983694189)
    ·
      refine ⟨720581744851321493885321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1921551319603523983694189 720581744851321493885321)
      ·
        refine ⟨540436308638491120413991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 720581744851321493885321 540436308638491120413991)
        ·
          refine ⟨810654462957736680620987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 540436308638491120413991 810654462957736680620987)
          ·
            refine ⟨1215981694436605020931481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 810654462957736680620987 1215981694436605020931481)
            ·
              refine ⟨911986270827453765698611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1215981694436605020931481 911986270827453765698611)
              ·
                refine ⟨1367979406241180648547917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 911986270827453765698611 1367979406241180648547917)
                ·
                  refine ⟨512992277340442743205469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1367979406241180648547917 512992277340442743205469)
                  ·
                    refine ⟨192372104002666028702051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 512992277340442743205469 192372104002666028702051)
                    ·
                      rfl

theorem cell22_561965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_561965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_561965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_561965 prefixEnd_561965 := by exact prefixLift 561965
  have htrace : WordTrace (prefixWord ++ tailWord_561965) baseStart_561965 baseEnd_561965 := by
    simpa [prefixWord, tailWord_561965, baseEnd_561965] using wordTrace_append hprefix tailTrace_561965
  have hstable : (prefixWord ++ tailWord_561965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561965).length < 2 ^ (prefixWord ++ tailWord_561965).sum := by decide
  have hdescent : baseEnd_561965 < baseStart_561965 := by decide
  rcases family_descends (prefixWord ++ tailWord_561965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562019 : List Nat := [1, 1, 1, 5, 3, 1, 1, 1, 4, 4]
def baseStart_562019 : Nat := 118140960795 + 562019 * 2 ^ 59
def prefixEnd_562019 : Nat := 4983230072969 + 3 ^ 40 * 562019 * 2
def baseEnd_562019 : Nat := 192390589306227887851885

theorem tailTrace_562019 : CollatzResearch.WordTrace tailWord_562019 prefixEnd_562019 192390589306227887851885 := by
  unfold tailWord_562019
  simp only [CollatzResearch.WordTrace]
  refine ⟨20498516950908623048537111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13665677967272415365691407 20498516950908623048537111)
  ·
    refine ⟨30747775426362934572805667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20498516950908623048537111 30747775426362934572805667)
    ·
      refine ⟨46121663139544401859208501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30747775426362934572805667 46121663139544401859208501)
      ·
        refine ⟨4323905919332287674300797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46121663139544401859208501 4323905919332287674300797)
        ·
          refine ⟨1621464719749607877862799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4323905919332287674300797 1621464719749607877862799)
          ·
            refine ⟨2432197079624411816794199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1621464719749607877862799 2432197079624411816794199)
            ·
              refine ⟨3648295619436617725191299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2432197079624411816794199 3648295619436617725191299)
              ·
                refine ⟨5472443429154926587786949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3648295619436617725191299 5472443429154926587786949)
                ·
                  refine ⟨1026083142966548735210053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5472443429154926587786949 1026083142966548735210053)
                  ·
                    refine ⟨192390589306227887851885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1026083142966548735210053 192390589306227887851885)
                    ·
                      rfl

theorem cell22_562019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 4, 4].length) (baseStart_562019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_562019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_562019 prefixEnd_562019 := by exact prefixLift 562019
  have htrace : WordTrace (prefixWord ++ tailWord_562019) baseStart_562019 baseEnd_562019 := by
    simpa [prefixWord, tailWord_562019, baseEnd_562019] using wordTrace_append hprefix tailTrace_562019
  have hstable : (prefixWord ++ tailWord_562019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562019).length < 2 ^ (prefixWord ++ tailWord_562019).sum := by decide
  have hdescent : baseEnd_562019 < baseStart_562019 := by decide
  rcases family_descends (prefixWord ++ tailWord_562019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562023 : List Nat := [1, 1, 5, 1, 2, 3, 3, 2, 4]
def baseStart_562023 : Nat := 118140960795 + 562023 * 2 ^ 59
def prefixEnd_562023 : Nat := 4983230072969 + 3 ^ 40 * 562023 * 2
def baseEnd_562023 : Nat := 64130652862657736917291

theorem tailTrace_562023 : CollatzResearch.WordTrace tailWord_562023 prefixEnd_562023 64130652862657736917291 := by
  unfold tailWord_562023
  simp only [CollatzResearch.WordTrace]
  refine ⟨20498662842894131731682723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13665775228596087821121815 20498662842894131731682723)
  ·
    refine ⟨30747994264341197597524085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20498662842894131731682723 30747994264341197597524085)
    ·
      refine ⟨2882624462281987274767883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30747994264341197597524085 2882624462281987274767883)
      ·
        refine ⟨4323936693422980912151825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2882624462281987274767883 4323936693422980912151825)
        ·
          refine ⟨3242952520067235684113869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4323936693422980912151825 3242952520067235684113869)
          ·
            refine ⟨1216107195025213381542701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3242952520067235684113869 1216107195025213381542701)
            ·
              refine ⟨456040198134455018078513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1216107195025213381542701 456040198134455018078513)
              ·
                refine ⟨342030148600841263558885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 456040198134455018078513 342030148600841263558885)
                ·
                  refine ⟨64130652862657736917291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 342030148600841263558885 64130652862657736917291)
                  ·
                    rfl

theorem cell22_562023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 2, 4].length) (baseStart_562023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_562023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_562023 prefixEnd_562023 := by exact prefixLift 562023
  have htrace : WordTrace (prefixWord ++ tailWord_562023) baseStart_562023 baseEnd_562023 := by
    simpa [prefixWord, tailWord_562023, baseEnd_562023] using wordTrace_append hprefix tailTrace_562023
  have hstable : (prefixWord ++ tailWord_562023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562023).length < 2 ^ (prefixWord ++ tailWord_562023).sum := by decide
  have hdescent : baseEnd_562023 < baseStart_562023 := by decide
  rcases family_descends (prefixWord ++ tailWord_562023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562070 : List Nat := [5, 3, 1, 1, 1, 1, 2, 2, 2, 4]
def baseStart_562070 : Nat := 118140960795 + 562070 * 2 ^ 59
def prefixEnd_562070 : Nat := 4983230072969 + 3 ^ 40 * 562070 * 2
def baseEnd_562070 : Nat := 192408047648480754826729

theorem tailTrace_562070 : CollatzResearch.WordTrace tailWord_562070 prefixEnd_562070 192408047648480754826729 := by
  unfold tailWord_562070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1281273567107741172415229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13666918049149239172429109 1281273567107741172415229)
  ·
    refine ⟨480477587665402939655711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1281273567107741172415229 480477587665402939655711)
    ·
      refine ⟨720716381498104409483567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 480477587665402939655711 720716381498104409483567)
      ·
        refine ⟨1081074572247156614225351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 720716381498104409483567 1081074572247156614225351)
        ·
          refine ⟨1621611858370734921338027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1081074572247156614225351 1621611858370734921338027)
          ·
            refine ⟨2432417787556102382007041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1621611858370734921338027 2432417787556102382007041)
            ·
              refine ⟨1824313340667076786505281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2432417787556102382007041 1824313340667076786505281)
              ·
                refine ⟨1368235005500307589878961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1824313340667076786505281 1368235005500307589878961)
                ·
                  refine ⟨1026176254125230692409221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1368235005500307589878961 1026176254125230692409221)
                  ·
                    refine ⟨192408047648480754826729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1026176254125230692409221 192408047648480754826729)
                    ·
                      rfl

theorem cell22_562070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_562070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_562070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_562070 prefixEnd_562070 := by exact prefixLift 562070
  have htrace : WordTrace (prefixWord ++ tailWord_562070) baseStart_562070 baseEnd_562070 := by
    simpa [prefixWord, tailWord_562070, baseEnd_562070] using wordTrace_append hprefix tailTrace_562070
  have hstable : (prefixWord ++ tailWord_562070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562070).length < 2 ^ (prefixWord ++ tailWord_562070).sum := by decide
  have hdescent : baseEnd_562070 < baseStart_562070 := by decide
  rcases family_descends (prefixWord ++ tailWord_562070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562100 : List Nat := [2, 5, 2, 1, 1, 2, 1, 2, 3, 3]
def baseStart_562100 : Nat := 118140960795 + 562100 * 2 ^ 59
def prefixEnd_562100 : Nat := 4983230072969 + 3 ^ 40 * 562100 * 2
def baseEnd_562100 : Nat := 192418317261570676576637

theorem tailTrace_562100 : CollatzResearch.WordTrace tailWord_562100 prefixEnd_562100 192418317261570676576637 := by
  unfold tailWord_562100
  simp only [CollatzResearch.WordTrace]
  refine ⟨10250735631807586941117877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13667647509076782588157169 10250735631807586941117877)
  ·
    refine ⟨961006465481961275729801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10250735631807586941117877 961006465481961275729801)
    ·
      refine ⟨720754849111470956797351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 961006465481961275729801 720754849111470956797351)
      ·
        refine ⟨1081132273667206435196027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 720754849111470956797351 1081132273667206435196027)
        ·
          refine ⟨1621698410500809652794041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1081132273667206435196027 1621698410500809652794041)
          ·
            refine ⟨1216273807875607239595531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1621698410500809652794041 1216273807875607239595531)
            ·
              refine ⟨1824410711813410859393297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1216273807875607239595531 1824410711813410859393297)
              ·
                refine ⟨1368308033860058144544973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1824410711813410859393297 1368308033860058144544973)
                ·
                  refine ⟨513115512697521804204365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1368308033860058144544973 513115512697521804204365)
                  ·
                    refine ⟨192418317261570676576637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 513115512697521804204365 192418317261570676576637)
                    ·
                      rfl

theorem cell22_562100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_562100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_562100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_562100 prefixEnd_562100 := by exact prefixLift 562100
  have htrace : WordTrace (prefixWord ++ tailWord_562100) baseStart_562100 baseEnd_562100 := by
    simpa [prefixWord, tailWord_562100, baseEnd_562100] using wordTrace_append hprefix tailTrace_562100
  have hstable : (prefixWord ++ tailWord_562100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562100).length < 2 ^ (prefixWord ++ tailWord_562100).sum := by decide
  have hdescent : baseEnd_562100 < baseStart_562100 := by decide
  rcases family_descends (prefixWord ++ tailWord_562100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562102 : List Nat := [5, 1, 4, 1, 1, 1, 3, 6]
def baseStart_562102 : Nat := 118140960795 + 562102 * 2 ^ 59
def prefixEnd_562102 : Nat := 4983230072969 + 3 ^ 40 * 562102 * 2
def baseEnd_562102 : Nat := 21379889100271482002959

theorem tailTrace_562102 : CollatzResearch.WordTrace tailWord_562102 prefixEnd_562102 21379889100271482002959 := by
  unfold tailWord_562102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1281346513100495513988035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13667696139738618815872373 1281346513100495513988035)
  ·
    refine ⟨1922019769650743270982053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1281346513100495513988035 1922019769650743270982053)
    ·
      refine ⟨360378706809514363309135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1922019769650743270982053 360378706809514363309135)
      ·
        refine ⟨540568060214271544963703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 360378706809514363309135 540568060214271544963703)
        ·
          refine ⟨810852090321407317445555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 540568060214271544963703 810852090321407317445555)
          ·
            refine ⟨1216278135482110976168333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 810852090321407317445555 1216278135482110976168333)
            ·
              refine ⟨456104300805791616063125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1216278135482110976168333 456104300805791616063125)
              ·
                refine ⟨21379889100271482002959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 456104300805791616063125 21379889100271482002959)
                ·
                  rfl

theorem cell22_562102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_562102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_562102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_562102 prefixEnd_562102 := by exact prefixLift 562102
  have htrace : WordTrace (prefixWord ++ tailWord_562102) baseStart_562102 baseEnd_562102 := by
    simpa [prefixWord, tailWord_562102, baseEnd_562102] using wordTrace_append hprefix tailTrace_562102
  have hstable : (prefixWord ++ tailWord_562102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562102).length < 2 ^ (prefixWord ++ tailWord_562102).sum := by decide
  have hdescent : baseEnd_562102 < baseStart_562102 := by decide
  rcases family_descends (prefixWord ++ tailWord_562102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562124 : List Nat := [2, 2, 1, 4, 1, 1, 1, 2, 8]
def baseStart_562124 : Nat := 118140960795 + 562124 * 2 ^ 59
def prefixEnd_562124 : Nat := 4983230072969 + 3 ^ 40 * 562124 * 2
def baseEnd_562124 : Nat := 64142177650680871325521

theorem tailTrace_562124 : CollatzResearch.WordTrace tailWord_562124 prefixEnd_562124 64142177650680871325521 := by
  unfold tailWord_562124
  simp only [CollatzResearch.WordTrace]
  refine ⟨10251173307764112990554713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13668231077018817320739617 10251173307764112990554713)
  ·
    refine ⟨7688379980823084742916035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10251173307764112990554713 7688379980823084742916035)
    ·
      refine ⟨11532569971234627114374053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7688379980823084742916035 11532569971234627114374053)
      ·
        refine ⟨2162356869606492583945135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11532569971234627114374053 2162356869606492583945135)
        ·
          refine ⟨3243535304409738875917703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2162356869606492583945135 3243535304409738875917703)
          ·
            refine ⟨4865302956614608313876555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3243535304409738875917703 4865302956614608313876555)
            ·
              refine ⟨7297954434921912470814833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4865302956614608313876555 7297954434921912470814833)
              ·
                refine ⟨5473465826191434353111125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7297954434921912470814833 5473465826191434353111125)
                ·
                  refine ⟨64142177650680871325521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5473465826191434353111125 64142177650680871325521)
                  ·
                    rfl

theorem cell22_562124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 8].length) (baseStart_562124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_562124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_562124 prefixEnd_562124 := by exact prefixLift 562124
  have htrace : WordTrace (prefixWord ++ tailWord_562124) baseStart_562124 baseEnd_562124 := by
    simpa [prefixWord, tailWord_562124, baseEnd_562124] using wordTrace_append hprefix tailTrace_562124
  have hstable : (prefixWord ++ tailWord_562124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562124).length < 2 ^ (prefixWord ++ tailWord_562124).sum := by decide
  have hdescent : baseEnd_562124 < baseStart_562124 := by decide
  rcases family_descends (prefixWord ++ tailWord_562124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562141 : List Nat := [1, 4, 3, 1, 2, 1, 1, 3, 6]
def baseStart_562141 : Nat := 118140960795 + 562141 * 2 ^ 59
def prefixEnd_562141 : Nat := 4983230072969 + 3 ^ 40 * 562141 * 2
def baseEnd_562141 : Nat := 64144117466486745433837

theorem tailTrace_562141 : CollatzResearch.WordTrace tailWord_562141 prefixEnd_562141 64144117466486745433837 := by
  unfold tailWord_562141
  simp only [CollatzResearch.WordTrace]
  refine ⟨20502966656466637884478277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13668644437644425256318851 20502966656466637884478277)
  ·
    refine ⟨3844306248087494603339677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20502966656466637884478277 3844306248087494603339677)
    ·
      refine ⟨1441614843032810476252379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3844306248087494603339677 1441614843032810476252379)
      ·
        refine ⟨2162422264549215714378569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1441614843032810476252379 2162422264549215714378569)
        ·
          refine ⟨1621816698411911785783927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2162422264549215714378569 1621816698411911785783927)
          ·
            refine ⟨2432725047617867678675891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1621816698411911785783927 2432725047617867678675891)
            ·
              refine ⟨3649087571426801518013837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2432725047617867678675891 3649087571426801518013837)
              ·
                refine ⟨1368407839285050569255189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3649087571426801518013837 1368407839285050569255189)
                ·
                  refine ⟨64144117466486745433837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1368407839285050569255189 64144117466486745433837)
                  ·
                    rfl

theorem cell22_562141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_562141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_562141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_562141 prefixEnd_562141 := by exact prefixLift 562141
  have htrace : WordTrace (prefixWord ++ tailWord_562141) baseStart_562141 baseEnd_562141 := by
    simpa [prefixWord, tailWord_562141, baseEnd_562141] using wordTrace_append hprefix tailTrace_562141
  have hstable : (prefixWord ++ tailWord_562141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562141).length < 2 ^ (prefixWord ++ tailWord_562141).sum := by decide
  have hdescent : baseEnd_562141 < baseStart_562141 := by decide
  rcases family_descends (prefixWord ++ tailWord_562141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562169 : List Nat := [1, 2, 1, 3, 1, 3, 3, 8]
def baseStart_562169 : Nat := 118140960795 + 562169 * 2 ^ 59
def prefixEnd_562169 : Nat := 4983230072969 + 3 ^ 40 * 562169 * 2
def baseEnd_562169 : Nat := 21382437485741944066825

theorem tailTrace_562169 : CollatzResearch.WordTrace tailWord_562169 prefixEnd_562169 21382437485741944066825 := by
  unfold tailWord_562169
  simp only [CollatzResearch.WordTrace]
  refine ⟨20503987900365198666497561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13669325266910132444331707 20503987900365198666497561)
  ·
    refine ⟨15377990925273898999873171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20503987900365198666497561 15377990925273898999873171)
    ·
      refine ⟨23066986387910848499809757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15377990925273898999873171 23066986387910848499809757)
      ·
        refine ⟨8650119895466568187428659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23066986387910848499809757 8650119895466568187428659)
        ·
          refine ⟨12975179843199852281142989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8650119895466568187428659 12975179843199852281142989)
          ·
            refine ⟨4865692441199944605428621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12975179843199852281142989 4865692441199944605428621)
            ·
              refine ⟨1824634665449979227035733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4865692441199944605428621 1824634665449979227035733)
              ·
                refine ⟨21382437485741944066825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1824634665449979227035733 21382437485741944066825)
                ·
                  rfl

theorem cell22_562169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 8].length) (baseStart_562169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_562169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_562169 prefixEnd_562169 := by exact prefixLift 562169
  have htrace : WordTrace (prefixWord ++ tailWord_562169) baseStart_562169 baseEnd_562169 := by
    simpa [prefixWord, tailWord_562169, baseEnd_562169] using wordTrace_append hprefix tailTrace_562169
  have hstable : (prefixWord ++ tailWord_562169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562169).length < 2 ^ (prefixWord ++ tailWord_562169).sum := by decide
  have hdescent : baseEnd_562169 < baseStart_562169 := by decide
  rcases family_descends (prefixWord ++ tailWord_562169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562186 : List Nat := [3, 1, 2, 2, 3, 3, 8]
def baseStart_562186 : Nat := 118140960795 + 562186 * 2 ^ 59
def prefixEnd_562186 : Nat := 4983230072969 + 3 ^ 40 * 562186 * 2
def baseEnd_562186 : Nat := 7127694697003522923199

theorem tailTrace_562186 : CollatzResearch.WordTrace tailWord_562186 prefixEnd_562186 7127694697003522923199 := by
  unfold tailWord_562186
  simp only [CollatzResearch.WordTrace]
  refine ⟨5126151985325902642466603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13669738627535740379910941 5126151985325902642466603)
  ·
    refine ⟨7689227977988853963699905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5126151985325902642466603 7689227977988853963699905)
    ·
      refine ⟨5766920983491640472774929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7689227977988853963699905 5766920983491640472774929)
      ·
        refine ⟨4325190737618730354581197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5766920983491640472774929 4325190737618730354581197)
        ·
          refine ⟨1621946526607023882967949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4325190737618730354581197 1621946526607023882967949)
          ·
            refine ⟨608229947477633956112981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1621946526607023882967949 608229947477633956112981)
            ·
              refine ⟨7127694697003522923199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 608229947477633956112981 7127694697003522923199)
              ·
                rfl

theorem cell22_562186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 8].length) (baseStart_562186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_562186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_562186 prefixEnd_562186 := by exact prefixLift 562186
  have htrace : WordTrace (prefixWord ++ tailWord_562186) baseStart_562186 baseEnd_562186 := by
    simpa [prefixWord, tailWord_562186, baseEnd_562186] using wordTrace_append hprefix tailTrace_562186
  have hstable : (prefixWord ++ tailWord_562186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562186).length < 2 ^ (prefixWord ++ tailWord_562186).sum := by decide
  have hdescent : baseEnd_562186 < baseStart_562186 := by decide
  rcases family_descends (prefixWord ++ tailWord_562186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562261 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 5, 4]
def baseStart_562261 : Nat := 118140960795 + 562261 * 2 ^ 59
def prefixEnd_562261 : Nat := 4983230072969 + 3 ^ 40 * 562261 * 2
def baseEnd_562261 : Nat := 192473430851819923301143

theorem tailTrace_562261 : CollatzResearch.WordTrace tailWord_562261 prefixEnd_562261 192473430851819923301143 := by
  unfold tailWord_562261
  simp only [CollatzResearch.WordTrace]
  refine ⟨20507343416031898378846637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13671562277354598919231091 20507343416031898378846637)
  ·
    refine ⟨7690253781011961892067489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20507343416031898378846637 7690253781011961892067489)
    ·
      refine ⟨5767690335758971419050617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7690253781011961892067489 5767690335758971419050617)
      ·
        refine ⟨4325767751819228564287963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5767690335758971419050617 4325767751819228564287963)
        ·
          refine ⟨6488651627728842846431945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4325767751819228564287963 6488651627728842846431945)
          ·
            refine ⟨4866488720796632134823959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6488651627728842846431945 4866488720796632134823959)
            ·
              refine ⟨7299733081194948202235939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4866488720796632134823959 7299733081194948202235939)
              ·
                refine ⟨10949599621792422303353909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7299733081194948202235939 10949599621792422303353909)
                ·
                  refine ⟨1026524964543039590939429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10949599621792422303353909 1026524964543039590939429)
                  ·
                    refine ⟨192473430851819923301143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1026524964543039590939429 192473430851819923301143)
                    ·
                      rfl

theorem cell22_562261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_562261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_562261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_562261 prefixEnd_562261 := by exact prefixLift 562261
  have htrace : WordTrace (prefixWord ++ tailWord_562261) baseStart_562261 baseEnd_562261 := by
    simpa [prefixWord, tailWord_562261, baseEnd_562261] using wordTrace_append hprefix tailTrace_562261
  have hstable : (prefixWord ++ tailWord_562261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562261).length < 2 ^ (prefixWord ++ tailWord_562261).sum := by decide
  have hdescent : baseEnd_562261 < baseStart_562261 := by decide
  rcases family_descends (prefixWord ++ tailWord_562261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562336 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 2, 7]
def baseStart_562336 : Nat := 118140960795 + 562336 * 2 ^ 59
def prefixEnd_562336 : Nat := 4983230072969 + 3 ^ 40 * 562336 * 2
def baseEnd_562336 : Nat := 192499104884544727675913

theorem tailTrace_562336 : CollatzResearch.WordTrace tailWord_562336 prefixEnd_562336 192499104884544727675913 := by
  unfold tailWord_562336
  simp only [CollatzResearch.WordTrace]
  refine ⟨10255039445380093093913431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13673385927173457458551241 10255039445380093093913431)
  ·
    refine ⟨15382559168070139640870147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10255039445380093093913431 15382559168070139640870147)
    ·
      refine ⟨23073838752105209461305221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15382559168070139640870147 23073838752105209461305221)
      ·
        refine ⟨4326344766019726773994729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23073838752105209461305221 4326344766019726773994729)
        ·
          refine ⟨3244758574514795080496047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4326344766019726773994729 3244758574514795080496047)
          ·
            refine ⟨4867137861772192620744071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3244758574514795080496047 4867137861772192620744071)
            ·
              refine ⟨7300706792658288931116107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4867137861772192620744071 7300706792658288931116107)
              ·
                refine ⟨10951060188987433396674161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7300706792658288931116107 10951060188987433396674161)
                ·
                  refine ⟨8213295141740575047505621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10951060188987433396674161 8213295141740575047505621)
                  ·
                    refine ⟨192499104884544727675913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8213295141740575047505621 192499104884544727675913)
                    ·
                      rfl

theorem cell22_562336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 2, 7].length) (baseStart_562336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_562336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_562336 prefixEnd_562336 := by exact prefixLift 562336
  have htrace : WordTrace (prefixWord ++ tailWord_562336) baseStart_562336 baseEnd_562336 := by
    simpa [prefixWord, tailWord_562336, baseEnd_562336] using wordTrace_append hprefix tailTrace_562336
  have hstable : (prefixWord ++ tailWord_562336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562336).length < 2 ^ (prefixWord ++ tailWord_562336).sum := by decide
  have hdescent : baseEnd_562336 < baseStart_562336 := by decide
  rcases family_descends (prefixWord ++ tailWord_562336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562430 : List Nat := [4, 2, 2, 1, 1, 2, 1, 2, 3, 4]
def baseStart_562430 : Nat := 118140960795 + 562430 * 2 ^ 59
def prefixEnd_562430 : Nat := 4983230072969 + 3 ^ 40 * 562430 * 2
def baseEnd_562430 : Nat := 192531283005559815825625

theorem tailTrace_562430 : CollatzResearch.WordTrace tailWord_562430 prefixEnd_562430 192531283005559815825625 := by
  unfold tailWord_562430
  simp only [CollatzResearch.WordTrace]
  refine ⟨2564188419052455030218593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13675671568279760161165829 2564188419052455030218593)
  ·
    refine ⟨1923141314289341272663945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2564188419052455030218593 1923141314289341272663945)
    ·
      refine ⟨1442355985717005954497959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1923141314289341272663945 1442355985717005954497959)
      ·
        refine ⟨2163533978575508931746939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1442355985717005954497959 2163533978575508931746939)
        ·
          refine ⟨3245300967863263397620409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2163533978575508931746939 3245300967863263397620409)
          ·
            refine ⟨2433975725897447548215307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3245300967863263397620409 2433975725897447548215307)
            ·
              refine ⟨3650963588846171322322961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2433975725897447548215307 3650963588846171322322961)
              ·
                refine ⟨2738222691634628491742221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3650963588846171322322961 2738222691634628491742221)
                ·
                  refine ⟨1026833509362985684403333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2738222691634628491742221 1026833509362985684403333)
                  ·
                    refine ⟨192531283005559815825625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1026833509362985684403333 192531283005559815825625)
                    ·
                      rfl

theorem cell22_562430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_562430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_562430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_562430 prefixEnd_562430 := by exact prefixLift 562430
  have htrace : WordTrace (prefixWord ++ tailWord_562430) baseStart_562430 baseEnd_562430 := by
    simpa [prefixWord, tailWord_562430, baseEnd_562430] using wordTrace_append hprefix tailTrace_562430
  have hstable : (prefixWord ++ tailWord_562430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562430).length < 2 ^ (prefixWord ++ tailWord_562430).sum := by decide
  have hdescent : baseEnd_562430 < baseStart_562430 := by decide
  rcases family_descends (prefixWord ++ tailWord_562430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562443 : List Nat := [1, 1, 1, 1, 5, 3, 1, 3, 1, 5]
def baseStart_562443 : Nat := 118140960795 + 562443 * 2 ^ 59
def prefixEnd_562443 : Nat := 4983230072969 + 3 ^ 40 * 562443 * 2
def baseEnd_562443 : Nat := 192535733171232115250585

theorem tailTrace_562443 : CollatzResearch.WordTrace tailWord_562443 prefixEnd_562443 192535733171232115250585 := by
  unfold tailWord_562443
  simp only [CollatzResearch.WordTrace]
  refine ⟨20513981501372543461971983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13675987667581695641314655 20513981501372543461971983)
  ·
    refine ⟨30770972252058815192957975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20513981501372543461971983 30770972252058815192957975)
    ·
      refine ⟨46156458378088222789436963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30770972252058815192957975 46156458378088222789436963)
      ·
        refine ⟨69234687567132334184155445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46156458378088222789436963 69234687567132334184155445)
        ·
          refine ⟨6490751959418656329764573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69234687567132334184155445 6490751959418656329764573)
          ·
            refine ⟨2434031984781996123661715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6490751959418656329764573 2434031984781996123661715)
            ·
              refine ⟨3651047977172994185492573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2434031984781996123661715 3651047977172994185492573)
              ·
                refine ⟨1369142991439872819559715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3651047977172994185492573 1369142991439872819559715)
                ·
                  refine ⟨2053714487159809229339573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1369142991439872819559715 2053714487159809229339573)
                  ·
                    refine ⟨192535733171232115250585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2053714487159809229339573 192535733171232115250585)
                    ·
                      rfl

theorem cell22_562443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 5].length) (baseStart_562443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_562443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_562443 prefixEnd_562443 := by exact prefixLift 562443
  have htrace : WordTrace (prefixWord ++ tailWord_562443) baseStart_562443 baseEnd_562443 := by
    simpa [prefixWord, tailWord_562443, baseEnd_562443] using wordTrace_append hprefix tailTrace_562443
  have hstable : (prefixWord ++ tailWord_562443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562443).length < 2 ^ (prefixWord ++ tailWord_562443).sum := by decide
  have hdescent : baseEnd_562443 < baseStart_562443 := by decide
  rcases family_descends (prefixWord ++ tailWord_562443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562464 : List Nat := [2, 1, 1, 5, 3, 2, 2, 1, 1, 4]
def baseStart_562464 : Nat := 118140960795 + 562464 * 2 ^ 59
def prefixEnd_562464 : Nat := 4983230072969 + 3 ^ 40 * 562464 * 2
def baseEnd_562464 : Nat := 192542921900395060475521

theorem tailTrace_562464 : CollatzResearch.WordTrace tailWord_562464 prefixEnd_562464 192542921900395060475521 := by
  unfold tailWord_562464
  simp only [CollatzResearch.WordTrace]
  refine ⟨10257373717148232024243223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13676498289530976032324297 10257373717148232024243223)
  ·
    refine ⟨15386060575722348036364835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10257373717148232024243223 15386060575722348036364835)
    ·
      refine ⟨23079090863583522054547253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15386060575722348036364835 23079090863583522054547253)
      ·
        refine ⟨2163664768460955192613805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23079090863583522054547253 2163664768460955192613805)
        ·
          refine ⟨811374288172858197230177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2163664768460955192613805 811374288172858197230177)
          ·
            refine ⟨608530716129643647922633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 811374288172858197230177 608530716129643647922633)
            ·
              refine ⟨456398037097232735941975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 608530716129643647922633 456398037097232735941975)
              ·
                refine ⟨684597055645849103912963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 456398037097232735941975 684597055645849103912963)
                ·
                  refine ⟨1026895583468773655869445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 684597055645849103912963 1026895583468773655869445)
                  ·
                    refine ⟨192542921900395060475521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1026895583468773655869445 192542921900395060475521)
                    ·
                      rfl

theorem cell22_562464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 1, 1, 4].length) (baseStart_562464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_562464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_562464 prefixEnd_562464 := by exact prefixLift 562464
  have htrace : WordTrace (prefixWord ++ tailWord_562464) baseStart_562464 baseEnd_562464 := by
    simpa [prefixWord, tailWord_562464, baseEnd_562464] using wordTrace_append hprefix tailTrace_562464
  have hstable : (prefixWord ++ tailWord_562464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562464).length < 2 ^ (prefixWord ++ tailWord_562464).sum := by decide
  have hdescent : baseEnd_562464 < baseStart_562464 := by decide
  rcases family_descends (prefixWord ++ tailWord_562464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562494 : List Nat := [4, 2, 1, 2, 1, 1, 5, 1, 2, 3]
def baseStart_562494 : Nat := 118140960795 + 562494 * 2 ^ 59
def prefixEnd_562494 : Nat := 4983230072969 + 3 ^ 40 * 562494 * 2
def baseEnd_562494 : Nat := 192553191513484982225429

theorem tailTrace_562494 : CollatzResearch.WordTrace tailWord_562494 prefixEnd_562494 192553191513484982225429 := by
  unfold tailWord_562494
  simp only [CollatzResearch.WordTrace]
  refine ⟨2564480203023472396509817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13677227749458519448052357 2564480203023472396509817)
  ·
    refine ⟨1923360152267604297382363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2564480203023472396509817 1923360152267604297382363)
    ·
      refine ⟨2885040228401406446073545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1923360152267604297382363 2885040228401406446073545)
      ·
        refine ⟨2163780171301054834555159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2885040228401406446073545 2163780171301054834555159)
        ·
          refine ⟨3245670256951582251832739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2163780171301054834555159 3245670256951582251832739)
          ·
            refine ⟨4868505385427373377749109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3245670256951582251832739 4868505385427373377749109)
            ·
              refine ⟨456422379883816254163979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4868505385427373377749109 456422379883816254163979)
              ·
                refine ⟨684633569825724381245969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 456422379883816254163979 684633569825724381245969)
                ·
                  refine ⟨513475177369293285934477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 684633569825724381245969 513475177369293285934477)
                  ·
                    refine ⟨192553191513484982225429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 513475177369293285934477 192553191513484982225429)
                    ·
                      rfl

theorem cell22_562494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_562494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_562494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_562494 prefixEnd_562494 := by exact prefixLift 562494
  have htrace : WordTrace (prefixWord ++ tailWord_562494) baseStart_562494 baseEnd_562494 := by
    simpa [prefixWord, tailWord_562494, baseEnd_562494] using wordTrace_append hprefix tailTrace_562494
  have hstable : (prefixWord ++ tailWord_562494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562494).length < 2 ^ (prefixWord ++ tailWord_562494).sum := by decide
  have hdescent : baseEnd_562494 < baseStart_562494 := by decide
  rcases family_descends (prefixWord ++ tailWord_562494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562505 : List Nat := [1, 2, 1, 1, 2, 3, 4, 2, 3, 3]
def baseStart_562505 : Nat := 118140960795 + 562505 * 2 ^ 59
def prefixEnd_562505 : Nat := 4983230072969 + 3 ^ 40 * 562505 * 2
def baseEnd_562505 : Nat := 192556957038284620200395

theorem tailTrace_562505 : CollatzResearch.WordTrace tailWord_562505 prefixEnd_562505 192556957038284620200395 := by
  unfold tailWord_562505
  simp only [CollatzResearch.WordTrace]
  refine ⟨20516242827147928050728969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13677495218098618700485979 20516242827147928050728969)
  ·
    refine ⟨15387182120360946038046727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20516242827147928050728969 15387182120360946038046727)
    ·
      refine ⟨23080773180541419057070091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15387182120360946038046727 23080773180541419057070091)
      ·
        refine ⟨34621159770812128585605137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23080773180541419057070091 34621159770812128585605137)
        ·
          refine ⟨25965869828109096439203853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34621159770812128585605137 25965869828109096439203853)
          ·
            refine ⟨9737201185540911164701445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25965869828109096439203853 9737201185540911164701445)
            ·
              refine ⟨1825725222288920843381521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9737201185540911164701445 1825725222288920843381521)
              ·
                refine ⟨1369293916716690632536141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1825725222288920843381521 1369293916716690632536141)
                ·
                  refine ⟨513485218768758987201053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1369293916716690632536141 513485218768758987201053)
                  ·
                    refine ⟨192556957038284620200395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 513485218768758987201053 192556957038284620200395)
                    ·
                      rfl

theorem cell22_562505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 3, 3].length) (baseStart_562505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_562505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_562505 prefixEnd_562505 := by exact prefixLift 562505
  have htrace : WordTrace (prefixWord ++ tailWord_562505) baseStart_562505 baseEnd_562505 := by
    simpa [prefixWord, tailWord_562505, baseEnd_562505] using wordTrace_append hprefix tailTrace_562505
  have hstable : (prefixWord ++ tailWord_562505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562505).length < 2 ^ (prefixWord ++ tailWord_562505).sum := by decide
  have hdescent : baseEnd_562505 < baseStart_562505 := by decide
  rcases family_descends (prefixWord ++ tailWord_562505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562590 : List Nat := [4, 3, 1, 2, 2, 2, 2, 2, 1, 3]
def baseStart_562590 : Nat := 118140960795 + 562590 * 2 ^ 59
def prefixEnd_562590 : Nat := 4983230072969 + 3 ^ 40 * 562590 * 2
def baseEnd_562590 : Nat := 192586054275372731825135

theorem tailTrace_562590 : CollatzResearch.WordTrace tailWord_562590 prefixEnd_562590 192586054275372731825135 := by
  unfold tailWord_562590
  simp only [CollatzResearch.WordTrace]
  refine ⟨2564917878979998445946653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13679562021226658378382149 2564917878979998445946653)
  ·
    refine ⟨961844204617499417229995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2564917878979998445946653 961844204617499417229995)
    ·
      refine ⟨1442766306926249125844993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 961844204617499417229995 1442766306926249125844993)
      ·
        refine ⟨1082074730194686844383745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1442766306926249125844993 1082074730194686844383745)
        ·
          refine ⟨811556047646015133287809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1082074730194686844383745 811556047646015133287809)
          ·
            refine ⟨608667035734511349965857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 811556047646015133287809 608667035734511349965857)
            ·
              refine ⟨456500276800883512474393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 608667035734511349965857 456500276800883512474393)
              ·
                refine ⟨342375207600662634355795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 456500276800883512474393 342375207600662634355795)
                ·
                  refine ⟨513562811400993951533693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 342375207600662634355795 513562811400993951533693)
                  ·
                    refine ⟨192586054275372731825135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 513562811400993951533693 192586054275372731825135)
                    ·
                      rfl

theorem cell22_562590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_562590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_562590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_562590 prefixEnd_562590 := by exact prefixLift 562590
  have htrace : WordTrace (prefixWord ++ tailWord_562590) baseStart_562590 baseEnd_562590 := by
    simpa [prefixWord, tailWord_562590, baseEnd_562590] using wordTrace_append hprefix tailTrace_562590
  have hstable : (prefixWord ++ tailWord_562590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562590).length < 2 ^ (prefixWord ++ tailWord_562590).sum := by decide
  have hdescent : baseEnd_562590 < baseStart_562590 := by decide
  rcases family_descends (prefixWord ++ tailWord_562590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562608 : List Nat := [2, 1, 1, 1, 2, 1, 1, 13]
def baseStart_562608 : Nat := 118140960795 + 562608 * 2 ^ 59
def prefixEnd_562608 : Nat := 4983230072969 + 3 ^ 40 * 562608 * 2
def baseEnd_562608 : Nat := 21399135115914076097231

theorem tailTrace_562608 : CollatzResearch.WordTrace tailWord_562608 prefixEnd_562608 21399135115914076097231 := by
  unfold tailWord_562608
  simp only [CollatzResearch.WordTrace]
  refine ⟨10259999772887388320864239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13679999697183184427818985 10259999772887388320864239)
  ·
    refine ⟨15389999659331082481296359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10259999772887388320864239 15389999659331082481296359)
    ·
      refine ⟨23084999488996623721944539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15389999659331082481296359 23084999488996623721944539)
      ·
        refine ⟨34627499233494935582916809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23084999488996623721944539 34627499233494935582916809)
        ·
          refine ⟨25970624425121201687187607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34627499233494935582916809 25970624425121201687187607)
          ·
            refine ⟨38955936637681802530781411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25970624425121201687187607 38955936637681802530781411)
            ·
              refine ⟨58433904956522703796172117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38955936637681802530781411 58433904956522703796172117)
              ·
                refine ⟨21399135115914076097231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 58433904956522703796172117 21399135115914076097231)
                ·
                  rfl

theorem cell22_562608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 13].length) (baseStart_562608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_562608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_562608 prefixEnd_562608 := by exact prefixLift 562608
  have htrace : WordTrace (prefixWord ++ tailWord_562608) baseStart_562608 baseEnd_562608 := by
    simpa [prefixWord, tailWord_562608, baseEnd_562608] using wordTrace_append hprefix tailTrace_562608
  have hstable : (prefixWord ++ tailWord_562608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562608).length < 2 ^ (prefixWord ++ tailWord_562608).sum := by decide
  have hdescent : baseEnd_562608 < baseStart_562608 := by decide
  rcases family_descends (prefixWord ++ tailWord_562608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562646 : List Nat := [5, 2, 1, 1, 1, 2, 3, 2, 2, 3]
def baseStart_562646 : Nat := 118140960795 + 562646 * 2 ^ 59
def prefixEnd_562646 : Nat := 4983230072969 + 3 ^ 40 * 562646 * 2
def baseEnd_562646 : Nat := 192605224219807252424963

theorem tailTrace_562646 : CollatzResearch.WordTrace tailWord_562646 prefixEnd_562646 192605224219807252424963 := by
  unfold tailWord_562646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1282586594977319320725737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13680923679758072754407861 1282586594977319320725737)
  ·
    refine ⟨961939946232989490544303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1282586594977319320725737 961939946232989490544303)
    ·
      refine ⟨1442909919349484235816455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 961939946232989490544303 1442909919349484235816455)
      ·
        refine ⟨2164364879024226353724683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1442909919349484235816455 2164364879024226353724683)
        ·
          refine ⟨3246547318536339530587025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2164364879024226353724683 3246547318536339530587025)
          ·
            refine ⟨2434910488902254647940269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3246547318536339530587025 2434910488902254647940269)
            ·
              refine ⟨913091433338345492977601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2434910488902254647940269 913091433338345492977601)
              ·
                refine ⟨684818575003759119733201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 913091433338345492977601 684818575003759119733201)
                ·
                  refine ⟨513613931252819339799901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 684818575003759119733201 513613931252819339799901)
                  ·
                    refine ⟨192605224219807252424963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 513613931252819339799901 192605224219807252424963)
                    ·
                      rfl

theorem cell22_562646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_562646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_562646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_562646 prefixEnd_562646 := by exact prefixLift 562646
  have htrace : WordTrace (prefixWord ++ tailWord_562646) baseStart_562646 baseEnd_562646 := by
    simpa [prefixWord, tailWord_562646, baseEnd_562646] using wordTrace_append hprefix tailTrace_562646
  have hstable : (prefixWord ++ tailWord_562646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562646).length < 2 ^ (prefixWord ++ tailWord_562646).sum := by decide
  have hdescent : baseEnd_562646 < baseStart_562646 := by decide
  rcases family_descends (prefixWord ++ tailWord_562646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562657 : List Nat := [1, 2, 3, 1, 2, 3, 1, 3, 3, 3]
def baseStart_562657 : Nat := 118140960795 + 562657 * 2 ^ 59
def prefixEnd_562657 : Nat := 4983230072969 + 3 ^ 40 * 562657 * 2
def baseEnd_562657 : Nat := 192608989744606890399929

theorem tailTrace_562657 : CollatzResearch.WordTrace tailWord_562657 prefixEnd_562657 192608989744606890399929 := by
  unfold tailWord_562657
  simp only [CollatzResearch.WordTrace]
  refine ⟨20521786722597258010262225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13681191148398172006841483 20521786722597258010262225)
  ·
    refine ⟨15391340041947943507696669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20521786722597258010262225 15391340041947943507696669)
    ·
      refine ⟨5771752515730478815386251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15391340041947943507696669 5771752515730478815386251)
      ·
        refine ⟨8657628773595718223079377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5771752515730478815386251 8657628773595718223079377)
        ·
          refine ⟨6493221580196788667309533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8657628773595718223079377 6493221580196788667309533)
          ·
            refine ⟨2434958092573795750241075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6493221580196788667309533 2434958092573795750241075)
            ·
              refine ⟨3652437138860693625361613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2434958092573795750241075 3652437138860693625361613)
              ·
                refine ⟨1369663927072760109510605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3652437138860693625361613 1369663927072760109510605)
                ·
                  refine ⟨513623972652285041066477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1369663927072760109510605 513623972652285041066477)
                  ·
                    refine ⟨192608989744606890399929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 513623972652285041066477 192608989744606890399929)
                    ·
                      rfl

theorem cell22_562657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 3, 3].length) (baseStart_562657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_562657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_562657 prefixEnd_562657 := by exact prefixLift 562657
  have htrace : WordTrace (prefixWord ++ tailWord_562657) baseStart_562657 baseEnd_562657 := by
    simpa [prefixWord, tailWord_562657, baseEnd_562657] using wordTrace_append hprefix tailTrace_562657
  have hstable : (prefixWord ++ tailWord_562657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562657).length < 2 ^ (prefixWord ++ tailWord_562657).sum := by decide
  have hdescent : baseEnd_562657 < baseStart_562657 := by decide
  rcases family_descends (prefixWord ++ tailWord_562657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562674 : List Nat := [3, 2, 1, 4, 1, 1, 2, 2, 3, 3]
def baseStart_562674 : Nat := 118140960795 + 562674 * 2 ^ 59
def prefixEnd_562674 : Nat := 4983230072969 + 3 ^ 40 * 562674 * 2
def baseEnd_562674 : Nat := 192614809192024512724877

theorem tailTrace_562674 : CollatzResearch.WordTrace tailWord_562674 prefixEnd_562674 192614809192024512724877 := by
  unfold tailWord_562674
  simp only [CollatzResearch.WordTrace]
  refine ⟨5130601690883917478407769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13681604509023779942420717 5130601690883917478407769)
  ·
    refine ⟨3847951268162938108805827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5130601690883917478407769 3847951268162938108805827)
    ·
      refine ⟨5771926902244407163208741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3847951268162938108805827 5771926902244407163208741)
      ·
        refine ⟨1082236294170826343101639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5771926902244407163208741 1082236294170826343101639)
        ·
          refine ⟨1623354441256239514652459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1082236294170826343101639 1623354441256239514652459)
          ·
            refine ⟨2435031661884359271978689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1623354441256239514652459 2435031661884359271978689)
            ·
              refine ⟨1826273746413269453984017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2435031661884359271978689 1826273746413269453984017)
              ·
                refine ⟨1369705309809952090488013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1826273746413269453984017 1369705309809952090488013)
                ·
                  refine ⟨513639491178732033933005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1369705309809952090488013 513639491178732033933005)
                  ·
                    refine ⟨192614809192024512724877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 513639491178732033933005 192614809192024512724877)
                    ·
                      rfl

theorem cell22_562674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 3, 3].length) (baseStart_562674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_562674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_562674 prefixEnd_562674 := by exact prefixLift 562674
  have htrace : WordTrace (prefixWord ++ tailWord_562674) baseStart_562674 baseEnd_562674 := by
    simpa [prefixWord, tailWord_562674, baseEnd_562674] using wordTrace_append hprefix tailTrace_562674
  have hstable : (prefixWord ++ tailWord_562674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562674).length < 2 ^ (prefixWord ++ tailWord_562674).sum := by decide
  have hdescent : baseEnd_562674 < baseStart_562674 := by decide
  rcases family_descends (prefixWord ++ tailWord_562674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562708 : List Nat := [2, 4, 3, 1, 2, 2, 1, 1, 3, 3]
def baseStart_562708 : Nat := 118140960795 + 562708 * 2 ^ 59
def prefixEnd_562708 : Nat := 4983230072969 + 3 ^ 40 * 562708 * 2
def baseEnd_562708 : Nat := 192626448086859757374773

theorem tailTrace_562708 : CollatzResearch.WordTrace tailWord_562708 prefixEnd_562708 192626448086859757374773 := by
  unfold tailWord_562708
  simp only [CollatzResearch.WordTrace]
  refine ⟨10261823422706246860184389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13682431230274995813579185 10261823422706246860184389)
  ·
    refine ⟨1924091891757421286284573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10261823422706246860184389 1924091891757421286284573)
    ·
      refine ⟨721534459409032982356715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1924091891757421286284573 721534459409032982356715)
      ·
        refine ⟨1082301689113549473535073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 721534459409032982356715 1082301689113549473535073)
        ·
          refine ⟨811726266835162105151305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1082301689113549473535073 811726266835162105151305)
          ·
            refine ⟨608794700126371578863479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 811726266835162105151305 608794700126371578863479)
            ·
              refine ⟨913192050189557368295219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 608794700126371578863479 913192050189557368295219)
              ·
                refine ⟨1369788075284336052442829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 913192050189557368295219 1369788075284336052442829)
                ·
                  refine ⟨513670528231626019666061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1369788075284336052442829 513670528231626019666061)
                  ·
                    refine ⟨192626448086859757374773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 513670528231626019666061 192626448086859757374773)
                    ·
                      rfl

theorem cell22_562708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_562708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_562708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_562708 prefixEnd_562708 := by exact prefixLift 562708
  have htrace : WordTrace (prefixWord ++ tailWord_562708) baseStart_562708 baseEnd_562708 := by
    simpa [prefixWord, tailWord_562708, baseEnd_562708] using wordTrace_append hprefix tailTrace_562708
  have hstable : (prefixWord ++ tailWord_562708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562708).length < 2 ^ (prefixWord ++ tailWord_562708).sum := by decide
  have hdescent : baseEnd_562708 < baseStart_562708 := by decide
  rcases family_descends (prefixWord ++ tailWord_562708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562717 : List Nat := [1, 4, 2, 2, 1, 1, 2, 2, 3, 4]
def baseStart_562717 : Nat := 118140960795 + 562717 * 2 ^ 59
def prefixEnd_562717 : Nat := 4983230072969 + 3 ^ 40 * 562717 * 2
def baseEnd_562717 : Nat := 192629528970786733899745

theorem tailTrace_562717 : CollatzResearch.WordTrace tailWord_562717 prefixEnd_562717 192629528970786733899745 := by
  unfold tailWord_562717
  simp only [CollatzResearch.WordTrace]
  refine ⟨20523975102379888257446405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13682650068253258838297603 20523975102379888257446405)
  ·
    refine ⟨3848245331696229048271201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20523975102379888257446405 3848245331696229048271201)
    ·
      refine ⟨2886183998772171786203401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3848245331696229048271201 2886183998772171786203401)
      ·
        refine ⟨2164637999079128839652551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2886183998772171786203401 2164637999079128839652551)
        ·
          refine ⟨3246956998618693259478827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2164637999079128839652551 3246956998618693259478827)
          ·
            refine ⟨4870435497928039889218241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3246956998618693259478827 4870435497928039889218241)
            ·
              refine ⟨3652826623446029916913681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4870435497928039889218241 3652826623446029916913681)
              ·
                refine ⟨2739619967584522437685261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3652826623446029916913681 2739619967584522437685261)
                ·
                  refine ⟨1027357487844195914131973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2739619967584522437685261 1027357487844195914131973)
                  ·
                    refine ⟨192629528970786733899745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1027357487844195914131973 192629528970786733899745)
                    ·
                      rfl

theorem cell22_562717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_562717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_562717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_562717 prefixEnd_562717 := by exact prefixLift 562717
  have htrace : WordTrace (prefixWord ++ tailWord_562717) baseStart_562717 baseEnd_562717 := by
    simpa [prefixWord, tailWord_562717, baseEnd_562717] using wordTrace_append hprefix tailTrace_562717
  have hstable : (prefixWord ++ tailWord_562717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562717).length < 2 ^ (prefixWord ++ tailWord_562717).sum := by decide
  have hdescent : baseEnd_562717 < baseStart_562717 := by decide
  rcases family_descends (prefixWord ++ tailWord_562717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562734 : List Nat := [4, 1, 3, 1, 2, 2, 1, 1, 3, 4]
def baseStart_562734 : Nat := 118140960795 + 562734 * 2 ^ 59
def prefixEnd_562734 : Nat := 4983230072969 + 3 ^ 40 * 562734 * 2
def baseEnd_562734 : Nat := 192635348418204356224693

theorem tailTrace_562734 : CollatzResearch.WordTrace tailWord_562734 prefixEnd_562734 192635348418204356224693 := by
  unfold tailWord_562734
  simp only [CollatzResearch.WordTrace]
  refine ⟨2565574392914787520101907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13683063428878866773876837 2565574392914787520101907)
  ·
    refine ⟨3848361589372181280152861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2565574392914787520101907 3848361589372181280152861)
    ·
      refine ⟨1443135596014567980057323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3848361589372181280152861 1443135596014567980057323)
      ·
        refine ⟨2164703394021851970085985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1443135596014567980057323 2164703394021851970085985)
        ·
          refine ⟨1623527545516388977564489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2164703394021851970085985 1623527545516388977564489)
          ·
            refine ⟨1217645659137291733173367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1623527545516388977564489 1217645659137291733173367)
            ·
              refine ⟨1826468488705937599760051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1217645659137291733173367 1826468488705937599760051)
              ·
                refine ⟨2739702733058906399640077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1826468488705937599760051 2739702733058906399640077)
                ·
                  refine ⟨1027388524897089899865029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2739702733058906399640077 1027388524897089899865029)
                  ·
                    refine ⟨192635348418204356224693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1027388524897089899865029 192635348418204356224693)
                    ·
                      rfl

theorem cell22_562734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_562734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_562734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_562734 prefixEnd_562734 := by exact prefixLift 562734
  have htrace : WordTrace (prefixWord ++ tailWord_562734) baseStart_562734 baseEnd_562734 := by
    simpa [prefixWord, tailWord_562734, baseEnd_562734] using wordTrace_append hprefix tailTrace_562734
  have hstable : (prefixWord ++ tailWord_562734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562734).length < 2 ^ (prefixWord ++ tailWord_562734).sum := by decide
  have hdescent : baseEnd_562734 < baseStart_562734 := by decide
  rcases family_descends (prefixWord ++ tailWord_562734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562762 : List Nat := [3, 1, 2, 1, 1, 3, 1, 4, 2, 4]
def baseStart_562762 : Nat := 118140960795 + 562762 * 2 ^ 59
def prefixEnd_562762 : Nat := 4983230072969 + 3 ^ 40 * 562762 * 2
def baseEnd_562762 : Nat := 192644933390421616524607

theorem tailTrace_562762 : CollatzResearch.WordTrace tailWord_562762 prefixEnd_562762 192644933390421616524607 := by
  unfold tailWord_562762
  simp only [CollatzResearch.WordTrace]
  refine ⟨5131404096804215235708635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13683744258144573961889693 5131404096804215235708635)
  ·
    refine ⟨7697106145206322853562953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5131404096804215235708635 7697106145206322853562953)
    ·
      refine ⟨5772829608904742140172215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7697106145206322853562953 5772829608904742140172215)
      ·
        refine ⟨8659244413357113210258323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5772829608904742140172215 8659244413357113210258323)
        ·
          refine ⟨12988866620035669815387485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8659244413357113210258323 12988866620035669815387485)
          ·
            refine ⟨4870824982513376180770307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12988866620035669815387485 4870824982513376180770307)
            ·
              refine ⟨7306237473770064271155461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4870824982513376180770307 7306237473770064271155461)
              ·
                refine ⟨1369919526331887050841649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7306237473770064271155461 1369919526331887050841649)
                ·
                  refine ⟨1027439644748915288131237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1369919526331887050841649 1027439644748915288131237)
                  ·
                    refine ⟨192644933390421616524607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1027439644748915288131237 192644933390421616524607)
                    ·
                      rfl

theorem cell22_562762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_562762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_562762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_562762 prefixEnd_562762 := by exact prefixLift 562762
  have htrace : WordTrace (prefixWord ++ tailWord_562762) baseStart_562762 baseEnd_562762 := by
    simpa [prefixWord, tailWord_562762, baseEnd_562762] using wordTrace_append hprefix tailTrace_562762
  have hstable : (prefixWord ++ tailWord_562762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562762).length < 2 ^ (prefixWord ++ tailWord_562762).sum := by decide
  have hdescent : baseEnd_562762 < baseStart_562762 := by decide
  rcases family_descends (prefixWord ++ tailWord_562762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562764 : List Nat := [2, 2, 1, 3, 1, 3, 1, 4, 2, 3]
def baseStart_562764 : Nat := 118140960795 + 562764 * 2 ^ 59
def prefixEnd_562764 : Nat := 4983230072969 + 3 ^ 40 * 562764 * 2
def baseEnd_562764 : Nat := 192645618031294277974601

theorem tailTrace_562764 : CollatzResearch.WordTrace tailWord_562764 prefixEnd_562764 192645618031294277974601 := by
  unfold tailWord_562764
  simp only [CollatzResearch.WordTrace]
  refine ⟨10262844666604807642203673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13683792888806410189604897 10262844666604807642203673)
  ·
    refine ⟨7697133499953605731652755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10262844666604807642203673 7697133499953605731652755)
    ·
      refine ⟨11545700249930408597479133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7697133499953605731652755 11545700249930408597479133)
      ·
        refine ⟨4329637593723903224054675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11545700249930408597479133 4329637593723903224054675)
        ·
          refine ⟨6494456390585854836082013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4329637593723903224054675 6494456390585854836082013)
          ·
            refine ⟨2435421146469695563530755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6494456390585854836082013 2435421146469695563530755)
            ·
              refine ⟨3653131719704543345296133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2435421146469695563530755 3653131719704543345296133)
              ·
                refine ⟨684962197444601877243025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3653131719704543345296133 684962197444601877243025)
                ·
                  refine ⟨513721648083451407932269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 684962197444601877243025 513721648083451407932269)
                  ·
                    refine ⟨192645618031294277974601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 513721648083451407932269 192645618031294277974601)
                    ·
                      rfl

theorem cell22_562764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 4, 2, 3].length) (baseStart_562764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_562764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_562764 prefixEnd_562764 := by exact prefixLift 562764
  have htrace : WordTrace (prefixWord ++ tailWord_562764) baseStart_562764 baseEnd_562764 := by
    simpa [prefixWord, tailWord_562764, baseEnd_562764] using wordTrace_append hprefix tailTrace_562764
  have hstable : (prefixWord ++ tailWord_562764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562764).length < 2 ^ (prefixWord ++ tailWord_562764).sum := by decide
  have hdescent : baseEnd_562764 < baseStart_562764 := by decide
  rcases family_descends (prefixWord ++ tailWord_562764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562794 : List Nat := [3, 1, 3, 2, 1, 3, 3, 6]
def baseStart_562794 : Nat := 118140960795 + 562794 * 2 ^ 59
def prefixEnd_562794 : Nat := 4983230072969 + 3 ^ 40 * 562794 * 2
def baseEnd_562794 : Nat := 21406209738264911080501

theorem tailTrace_562794 : CollatzResearch.WordTrace tailWord_562794 prefixEnd_562794 21406209738264911080501 := by
  unfold tailWord_562794
  simp only [CollatzResearch.WordTrace]
  refine ⟨5131695880775232601999859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13684522348733953605332957 5131695880775232601999859)
  ·
    refine ⟨7697543821162848902999789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5131695880775232601999859 7697543821162848902999789)
    ·
      refine ⟨2886578932936068338624921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7697543821162848902999789 2886578932936068338624921)
      ·
        refine ⟨2164934199702051253968691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2886578932936068338624921 2164934199702051253968691)
        ·
          refine ⟨3247401299553076880953037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2164934199702051253968691 3247401299553076880953037)
          ·
            refine ⟨1217775487332403830357389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3247401299553076880953037 1217775487332403830357389)
            ·
              refine ⟨456665807749651436384021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1217775487332403830357389 456665807749651436384021)
              ·
                refine ⟨21406209738264911080501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 456665807749651436384021 21406209738264911080501)
                ·
                  rfl

theorem cell22_562794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 6].length) (baseStart_562794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_562794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_562794 prefixEnd_562794 := by exact prefixLift 562794
  have htrace : WordTrace (prefixWord ++ tailWord_562794) baseStart_562794 baseEnd_562794 := by
    simpa [prefixWord, tailWord_562794, baseEnd_562794] using wordTrace_append hprefix tailTrace_562794
  have hstable : (prefixWord ++ tailWord_562794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562794).length < 2 ^ (prefixWord ++ tailWord_562794).sum := by decide
  have hdescent : baseEnd_562794 < baseStart_562794 := by decide
  rcases family_descends (prefixWord ++ tailWord_562794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562826 : List Nat := [3, 1, 2, 3, 2, 2, 2, 1, 3, 3]
def baseStart_562826 : Nat := 118140960795 + 562826 * 2 ^ 59
def prefixEnd_562826 : Nat := 4983230072969 + 3 ^ 40 * 562826 * 2
def baseEnd_562826 : Nat := 192666841898346782924411

theorem tailTrace_562826 : CollatzResearch.WordTrace tailWord_562826 prefixEnd_562826 192666841898346782924411 := by
  unfold tailWord_562826
  simp only [CollatzResearch.WordTrace]
  refine ⟨5131987664746249968291083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13685300439323333248776221 5131987664746249968291083)
  ·
    refine ⟨7697981497119374952436625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5131987664746249968291083 7697981497119374952436625)
    ·
      refine ⟨5773486122839531214327469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7697981497119374952436625 5773486122839531214327469)
      ·
        refine ⟨2165057296064824205372801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5773486122839531214327469 2165057296064824205372801)
        ·
          refine ⟨1623792972048618154029601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2165057296064824205372801 1623792972048618154029601)
          ·
            refine ⟨1217844729036463615522201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1623792972048618154029601 1217844729036463615522201)
            ·
              refine ⟨913383546777347711641651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1217844729036463615522201 913383546777347711641651)
              ·
                refine ⟨1370075320166021567462477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 913383546777347711641651 1370075320166021567462477)
                ·
                  refine ⟨513778245062258087798429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1370075320166021567462477 513778245062258087798429)
                  ·
                    refine ⟨192666841898346782924411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 513778245062258087798429 192666841898346782924411)
                    ·
                      rfl

theorem cell22_562826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 3, 3].length) (baseStart_562826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_562826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_562826 prefixEnd_562826 := by exact prefixLift 562826
  have htrace : WordTrace (prefixWord ++ tailWord_562826) baseStart_562826 baseEnd_562826 := by
    simpa [prefixWord, tailWord_562826, baseEnd_562826] using wordTrace_append hprefix tailTrace_562826
  have hstable : (prefixWord ++ tailWord_562826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562826).length < 2 ^ (prefixWord ++ tailWord_562826).sum := by decide
  have hdescent : baseEnd_562826 < baseStart_562826 := by decide
  rcases family_descends (prefixWord ++ tailWord_562826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562912 : List Nat := [2, 1, 1, 3, 1, 2, 4, 8]
def baseStart_562912 : Nat := 118140960795 + 562912 * 2 ^ 59
def prefixEnd_562912 : Nat := 4983230072969 + 3 ^ 40 * 562912 * 2
def baseEnd_562912 : Nat := 21410697939541247252683

theorem tailTrace_562912 : CollatzResearch.WordTrace tailWord_562912 prefixEnd_562912 21410697939541247252683 := by
  unfold tailWord_562912
  simp only [CollatzResearch.WordTrace]
  refine ⟨10265543668336718280397495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13687391557782291040529993 10265543668336718280397495)
  ·
    refine ⟨15398315502505077420596243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10265543668336718280397495 15398315502505077420596243)
    ·
      refine ⟨23097473253757616130894365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15398315502505077420596243 23097473253757616130894365)
      ·
        refine ⟨8661552470159106049085387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23097473253757616130894365 8661552470159106049085387)
        ·
          refine ⟨12992328705238659073628081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8661552470159106049085387 12992328705238659073628081)
          ·
            refine ⟨9744246528928994305221061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12992328705238659073628081 9744246528928994305221061)
            ·
              refine ⟨1827046224174186432228949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9744246528928994305221061 1827046224174186432228949)
              ·
                refine ⟨21410697939541247252683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1827046224174186432228949 21410697939541247252683)
                ·
                  rfl

theorem cell22_562912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 8].length) (baseStart_562912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_562912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_562912 prefixEnd_562912 := by exact prefixLift 562912
  have htrace : WordTrace (prefixWord ++ tailWord_562912) baseStart_562912 baseEnd_562912 := by
    simpa [prefixWord, tailWord_562912, baseEnd_562912] using wordTrace_append hprefix tailTrace_562912
  have hstable : (prefixWord ++ tailWord_562912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562912).length < 2 ^ (prefixWord ++ tailWord_562912).sum := by decide
  have hdescent : baseEnd_562912 < baseStart_562912 := by decide
  rcases family_descends (prefixWord ++ tailWord_562912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562987 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 1, 10]
def baseStart_562987 : Nat := 118140960795 + 562987 * 2 ^ 59
def prefixEnd_562987 : Nat := 4983230072969 + 3 ^ 40 * 562987 * 2
def baseEnd_562987 : Nat := 192721955488596029648917

theorem tailTrace_562987 : CollatzResearch.WordTrace tailWord_562987 prefixEnd_562987 192721955488596029648917 := by
  unfold tailWord_562987
  simp only [CollatzResearch.WordTrace]
  refine ⟨20533822811401724369775215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13689215207601149579850143 20533822811401724369775215)
  ·
    refine ⟨30800734217102586554662823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20533822811401724369775215 30800734217102586554662823)
    ·
      refine ⟨46201101325653879831994235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30800734217102586554662823 46201101325653879831994235)
      ·
        refine ⟨69301651988480819747991353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46201101325653879831994235 69301651988480819747991353)
        ·
          refine ⟨51976238991360614810993515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69301651988480819747991353 51976238991360614810993515)
          ·
            refine ⟨77964358487040922216490273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51976238991360614810993515 77964358487040922216490273)
            ·
              refine ⟨58473268865280691662367705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77964358487040922216490273 58473268865280691662367705)
              ·
                refine ⟨43854951648960518746775779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58473268865280691662367705 43854951648960518746775779)
                ·
                  refine ⟨65782427473440778120163669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43854951648960518746775779 65782427473440778120163669)
                  ·
                    refine ⟨192721955488596029648917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 65782427473440778120163669 192721955488596029648917)
                    ·
                      rfl

theorem cell22_562987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 10].length) (baseStart_562987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_562987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_562987 prefixEnd_562987 := by exact prefixLift 562987
  have htrace : WordTrace (prefixWord ++ tailWord_562987) baseStart_562987 baseEnd_562987 := by
    simpa [prefixWord, tailWord_562987, baseEnd_562987] using wordTrace_append hprefix tailTrace_562987
  have hstable : (prefixWord ++ tailWord_562987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562987).length < 2 ^ (prefixWord ++ tailWord_562987).sum := by decide
  have hdescent : baseEnd_562987 < baseStart_562987 := by decide
  rcases family_descends (prefixWord ++ tailWord_562987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563004 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 5, 4]
def baseStart_563004 : Nat := 118140960795 + 563004 * 2 ^ 59
def prefixEnd_563004 : Nat := 4983230072969 + 3 ^ 40 * 563004 * 2
def baseEnd_563004 : Nat := 192727774936013651973865

theorem tailTrace_563004 : CollatzResearch.WordTrace tailWord_563004 prefixEnd_563004 192727774936013651973865 := by
  unfold tailWord_563004
  simp only [CollatzResearch.WordTrace]
  refine ⟨10267221426170068136572033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13689628568226757515429377 10267221426170068136572033)
  ·
    refine ⟨7700416069627551102429025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10267221426170068136572033 7700416069627551102429025)
    ·
      refine ⟨5775312052220663326821769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7700416069627551102429025 5775312052220663326821769)
      ·
        refine ⟨4331484039165497495116327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5775312052220663326821769 4331484039165497495116327)
        ·
          refine ⟨6497226058748246242674491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4331484039165497495116327 6497226058748246242674491)
          ·
            refine ⟨9745839088122369364011737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6497226058748246242674491 9745839088122369364011737)
            ·
              refine ⟨7309379316091777023008803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9745839088122369364011737 7309379316091777023008803)
              ·
                refine ⟨10964068974137665534513205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7309379316091777023008803 10964068974137665534513205)
                ·
                  refine ⟨1027881466325406143860613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10964068974137665534513205 1027881466325406143860613)
                  ·
                    refine ⟨192727774936013651973865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1027881466325406143860613 192727774936013651973865)
                    ·
                      rfl

theorem cell22_563004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_563004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_563004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_563004 prefixEnd_563004 := by exact prefixLift 563004
  have htrace : WordTrace (prefixWord ++ tailWord_563004) baseStart_563004 baseEnd_563004 := by
    simpa [prefixWord, tailWord_563004, baseEnd_563004] using wordTrace_append hprefix tailTrace_563004
  have hstable : (prefixWord ++ tailWord_563004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563004).length < 2 ^ (prefixWord ++ tailWord_563004).sum := by decide
  have hdescent : baseEnd_563004 < baseStart_563004 := by decide
  rcases family_descends (prefixWord ++ tailWord_563004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563006 : List Nat := [4, 2, 1, 2, 2, 1, 2, 1, 2, 5]
def baseStart_563006 : Nat := 118140960795 + 563006 * 2 ^ 59
def prefixEnd_563006 : Nat := 4983230072969 + 3 ^ 40 * 563006 * 2
def baseEnd_563006 : Nat := 192728459576886313423859

theorem tailTrace_563006 : CollatzResearch.WordTrace tailWord_563006 prefixEnd_563006 192728459576886313423859 := by
  unfold tailWord_563006
  simp only [CollatzResearch.WordTrace]
  refine ⟨2566814474791611326839609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13689677198888593743144581 2566814474791611326839609)
  ·
    refine ⟨1925110856093708495129707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2566814474791611326839609 1925110856093708495129707)
    ·
      refine ⟨2887666284140562742694561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1925110856093708495129707 2887666284140562742694561)
      ·
        refine ⟨2165749713105422057020921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2887666284140562742694561 2165749713105422057020921)
        ·
          refine ⟨1624312284829066542765691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2165749713105422057020921 1624312284829066542765691)
          ·
            refine ⟨2436468427243599814148537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1624312284829066542765691 2436468427243599814148537)
            ·
              refine ⟨1827351320432699860611403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2436468427243599814148537 1827351320432699860611403)
              ·
                refine ⟨2741026980649049790917105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1827351320432699860611403 2741026980649049790917105)
                ·
                  refine ⟨2055770235486787343187829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2741026980649049790917105 2055770235486787343187829)
                  ·
                    refine ⟨192728459576886313423859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2055770235486787343187829 192728459576886313423859)
                    ·
                      rfl

theorem cell22_563006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_563006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_563006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_563006 prefixEnd_563006 := by exact prefixLift 563006
  have htrace : WordTrace (prefixWord ++ tailWord_563006) baseStart_563006 baseEnd_563006 := by
    simpa [prefixWord, tailWord_563006, baseEnd_563006] using wordTrace_append hprefix tailTrace_563006
  have hstable : (prefixWord ++ tailWord_563006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563006).length < 2 ^ (prefixWord ++ tailWord_563006).sum := by decide
  have hdescent : baseEnd_563006 < baseStart_563006 := by decide
  rcases family_descends (prefixWord ++ tailWord_563006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563034 : List Nat := [3, 1, 1, 2, 1, 3, 2, 1, 3, 5]
def baseStart_563034 : Nat := 118140960795 + 563034 * 2 ^ 59
def prefixEnd_563034 : Nat := 4983230072969 + 3 ^ 40 * 563034 * 2
def baseEnd_563034 : Nat := 192738044549103573723773

theorem tailTrace_563034 : CollatzResearch.WordTrace tailWord_563034 prefixEnd_563034 192738044549103573723773 := by
  unfold tailWord_563034
  simp only [CollatzResearch.WordTrace]
  refine ⟨5133884260557862849184039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13690358028154300931157437 5133884260557862849184039)
  ·
    refine ⟨7700826390836794273776059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5133884260557862849184039 7700826390836794273776059)
    ·
      refine ⟨11551239586255191410664089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7700826390836794273776059 11551239586255191410664089)
      ·
        refine ⟨8663429689691393557998067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11551239586255191410664089 8663429689691393557998067)
        ·
          refine ⟨12995144534537090336997101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8663429689691393557998067 12995144534537090336997101)
          ·
            refine ⟨4873179200451408876373913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12995144534537090336997101 4873179200451408876373913)
            ·
              refine ⟨3654884400338556657280435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4873179200451408876373913 3654884400338556657280435)
              ·
                refine ⟨5482326600507834985920653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3654884400338556657280435 5482326600507834985920653)
                ·
                  refine ⟨2055872475190438119720245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5482326600507834985920653 2055872475190438119720245)
                  ·
                    refine ⟨192738044549103573723773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2055872475190438119720245 192738044549103573723773)
                    ·
                      rfl

theorem cell22_563034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_563034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_563034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_563034 prefixEnd_563034 := by exact prefixLift 563034
  have htrace : WordTrace (prefixWord ++ tailWord_563034) baseStart_563034 baseEnd_563034 := by
    simpa [prefixWord, tailWord_563034, baseEnd_563034] using wordTrace_append hprefix tailTrace_563034
  have hstable : (prefixWord ++ tailWord_563034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563034).length < 2 ^ (prefixWord ++ tailWord_563034).sum := by decide
  have hdescent : baseEnd_563034 < baseStart_563034 := by decide
  rcases family_descends (prefixWord ++ tailWord_563034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563051 : List Nat := [1, 1, 1, 1, 2, 2, 3, 6, 2, 3]
def baseStart_563051 : Nat := 118140960795 + 563051 * 2 ^ 59
def prefixEnd_563051 : Nat := 4983230072969 + 3 ^ 40 * 563051 * 2
def baseEnd_563051 : Nat := 192743863996521196048721

theorem tailTrace_563051 : CollatzResearch.WordTrace tailWord_563051 prefixEnd_563051 192743863996521196048721 := by
  unfold tailWord_563051
  simp only [CollatzResearch.WordTrace]
  refine ⟨20536157083169863300105007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13690771388779908866736671 20536157083169863300105007)
  ·
    refine ⟨30804235624754794950157511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20536157083169863300105007 30804235624754794950157511)
    ·
      refine ⟨46206353437132192425236267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30804235624754794950157511 46206353437132192425236267)
      ·
        refine ⟨69309530155698288637854401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46206353437132192425236267 69309530155698288637854401)
        ·
          refine ⟨51982147616773716478390801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69309530155698288637854401 51982147616773716478390801)
          ·
            refine ⟨38986610712580287358793101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51982147616773716478390801 38986610712580287358793101)
            ·
              refine ⟨14619979017217607759547413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38986610712580287358793101 14619979017217607759547413)
              ·
                refine ⟨685311516432075363728785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14619979017217607759547413 685311516432075363728785)
                ·
                  refine ⟨513983637324056522796589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 685311516432075363728785 513983637324056522796589)
                  ·
                    refine ⟨192743863996521196048721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 513983637324056522796589 192743863996521196048721)
                    ·
                      rfl

theorem cell22_563051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 6, 2, 3].length) (baseStart_563051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_563051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_563051 prefixEnd_563051 := by exact prefixLift 563051
  have htrace : WordTrace (prefixWord ++ tailWord_563051) baseStart_563051 baseEnd_563051 := by
    simpa [prefixWord, tailWord_563051, baseEnd_563051] using wordTrace_append hprefix tailTrace_563051
  have hstable : (prefixWord ++ tailWord_563051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563051).length < 2 ^ (prefixWord ++ tailWord_563051).sum := by decide
  have hdescent : baseEnd_563051 < baseStart_563051 := by decide
  rcases family_descends (prefixWord ++ tailWord_563051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563109 : List Nat := [1, 3, 1, 2, 1, 1, 1, 5, 7]
def baseStart_563109 : Nat := 118140960795 + 563109 * 2 ^ 59
def prefixEnd_563109 : Nat := 4983230072969 + 3 ^ 40 * 563109 * 2
def baseEnd_563109 : Nat := 64254572860609459366181

theorem tailTrace_563109 : CollatzResearch.WordTrace tailWord_563109 prefixEnd_563109 64254572860609459366181 := by
  unfold tailWord_563109
  simp only [CollatzResearch.WordTrace]
  refine ⟨20538272516959739205716381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13692181677973159470477587 20538272516959739205716381)
  ·
    refine ⟨7701852193859902202143643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20538272516959739205716381 7701852193859902202143643)
    ·
      refine ⟨11552778290789853303215465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7701852193859902202143643 11552778290789853303215465)
      ·
        refine ⟨8664583718092389977411599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11552778290789853303215465 8664583718092389977411599)
        ·
          refine ⟨12996875577138584966117399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8664583718092389977411599 12996875577138584966117399)
          ·
            refine ⟨19495313365707877449176099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12996875577138584966117399 19495313365707877449176099)
            ·
              refine ⟨29242970048561816173764149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19495313365707877449176099 29242970048561816173764149)
              ·
                refine ⟨2741528442052670266290389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29242970048561816173764149 2741528442052670266290389)
                ·
                  refine ⟨64254572860609459366181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2741528442052670266290389 64254572860609459366181)
                  ·
                    rfl

theorem cell22_563109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 7].length) (baseStart_563109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_563109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_563109 prefixEnd_563109 := by exact prefixLift 563109
  have htrace : WordTrace (prefixWord ++ tailWord_563109) baseStart_563109 baseEnd_563109 := by
    simpa [prefixWord, tailWord_563109, baseEnd_563109] using wordTrace_append hprefix tailTrace_563109
  have hstable : (prefixWord ++ tailWord_563109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563109).length < 2 ^ (prefixWord ++ tailWord_563109).sum := by decide
  have hdescent : baseEnd_563109 < baseStart_563109 := by decide
  rcases family_descends (prefixWord ++ tailWord_563109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563111 : List Nat := [1, 1, 6, 1, 2, 1, 1, 1, 2, 6]
def baseStart_563111 : Nat := 118140960795 + 563111 * 2 ^ 59
def prefixEnd_563111 : Nat := 4983230072969 + 3 ^ 40 * 563111 * 2
def baseEnd_563111 : Nat := 192764403222701039548537

theorem tailTrace_563111 : CollatzResearch.WordTrace tailWord_563111 prefixEnd_563111 192764403222701039548537 := by
  unfold tailWord_563111
  simp only [CollatzResearch.WordTrace]
  refine ⟨20538345462952493547289187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13692230308634995698192791 20538345462952493547289187)
  ·
    refine ⟨30807518194428740320933781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20538345462952493547289187 30807518194428740320933781)
    ·
      refine ⟨1444102415363847202543771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 30807518194428740320933781 1444102415363847202543771)
      ·
        refine ⟨2166153623045770803815657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1444102415363847202543771 2166153623045770803815657)
        ·
          refine ⟨1624615217284328102861743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2166153623045770803815657 1624615217284328102861743)
          ·
            refine ⟨2436922825926492154292615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1624615217284328102861743 2436922825926492154292615)
            ·
              refine ⟨3655384238889738231438923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2436922825926492154292615 3655384238889738231438923)
              ·
                refine ⟨5483076358334607347158385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3655384238889738231438923 5483076358334607347158385)
                ·
                  refine ⟨4112307268750955510368789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5483076358334607347158385 4112307268750955510368789)
                  ·
                    refine ⟨192764403222701039548537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4112307268750955510368789 192764403222701039548537)
                    ·
                      rfl

theorem cell22_563111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_563111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_563111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_563111 prefixEnd_563111 := by exact prefixLift 563111
  have htrace : WordTrace (prefixWord ++ tailWord_563111) baseStart_563111 baseEnd_563111 := by
    simpa [prefixWord, tailWord_563111, baseEnd_563111] using wordTrace_append hprefix tailTrace_563111
  have hstable : (prefixWord ++ tailWord_563111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563111).length < 2 ^ (prefixWord ++ tailWord_563111).sum := by decide
  have hdescent : baseEnd_563111 < baseStart_563111 := by decide
  rcases family_descends (prefixWord ++ tailWord_563111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563164 : List Nat := [2, 2, 6, 1, 1, 1, 2, 1, 3, 3]
def baseStart_563164 : Nat := 118140960795 + 563164 * 2 ^ 59
def prefixEnd_563164 : Nat := 4983230072969 + 3 ^ 40 * 563164 * 2
def baseEnd_563164 : Nat := 192782546205826567973375

theorem tailTrace_563164 : CollatzResearch.WordTrace tailWord_563164 prefixEnd_563164 192782546205826567973375 := by
  unfold tailWord_563164
  simp only [CollatzResearch.WordTrace]
  refine ⟨10270139265880241799484273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13693519021173655732645697 10270139265880241799484273)
  ·
    refine ⟨7702604449410181349613205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10270139265880241799484273 7702604449410181349613205)
    ·
      refine ⟨361059583566102250763119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7702604449410181349613205 361059583566102250763119)
      ·
        refine ⟨541589375349153376144679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361059583566102250763119 541589375349153376144679)
        ·
          refine ⟨812384063023730064217019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 541589375349153376144679 812384063023730064217019)
          ·
            refine ⟨1218576094535595096325529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 812384063023730064217019 1218576094535595096325529)
            ·
              refine ⟨913932070901696322244147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1218576094535595096325529 913932070901696322244147)
              ·
                refine ⟨1370898106352544483366221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 913932070901696322244147 1370898106352544483366221)
                ·
                  refine ⟨514086789882204181262333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1370898106352544483366221 514086789882204181262333)
                  ·
                    refine ⟨192782546205826567973375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 514086789882204181262333 192782546205826567973375)
                    ·
                      rfl

theorem cell22_563164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_563164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_563164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_563164 prefixEnd_563164 := by exact prefixLift 563164
  have htrace : WordTrace (prefixWord ++ tailWord_563164) baseStart_563164 baseEnd_563164 := by
    simpa [prefixWord, tailWord_563164, baseEnd_563164] using wordTrace_append hprefix tailTrace_563164
  have hstable : (prefixWord ++ tailWord_563164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563164).length < 2 ^ (prefixWord ++ tailWord_563164).sum := by decide
  have hdescent : baseEnd_563164 < baseStart_563164 := by decide
  rcases family_descends (prefixWord ++ tailWord_563164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563171 : List Nat := [1, 1, 1, 6, 1, 2, 1, 3, 6]
def baseStart_563171 : Nat := 118140960795 + 563171 * 2 ^ 59
def prefixEnd_563171 : Nat := 4983230072969 + 3 ^ 40 * 563171 * 2
def baseEnd_563171 : Nat := 64261647482960294349451

theorem tailTrace_563171 : CollatzResearch.WordTrace tailWord_563171 prefixEnd_563171 64261647482960294349451 := by
  unfold tailWord_563171
  simp only [CollatzResearch.WordTrace]
  refine ⟨20540533842735123794473367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13693689228490082529648911 20540533842735123794473367)
  ·
    refine ⟨30810800764102685691710051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20540533842735123794473367 30810800764102685691710051)
    ·
      refine ⟨46216201146154028537565077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30810800764102685691710051 46216201146154028537565077)
      ·
        refine ⟨2166384428725970087698363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 46216201146154028537565077 2166384428725970087698363)
        ·
          refine ⟨3249576643088955131547545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2166384428725970087698363 3249576643088955131547545)
          ·
            refine ⟨2437182482316716348660659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3249576643088955131547545 2437182482316716348660659)
            ·
              refine ⟨3655773723475074522990989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2437182482316716348660659 3655773723475074522990989)
              ·
                refine ⟨1370915146303152946121621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3655773723475074522990989 1370915146303152946121621)
                ·
                  refine ⟨64261647482960294349451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1370915146303152946121621 64261647482960294349451)
                  ·
                    rfl

theorem cell22_563171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 6].length) (baseStart_563171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_563171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_563171 prefixEnd_563171 := by exact prefixLift 563171
  have htrace : WordTrace (prefixWord ++ tailWord_563171) baseStart_563171 baseEnd_563171 := by
    simpa [prefixWord, tailWord_563171, baseEnd_563171] using wordTrace_append hprefix tailTrace_563171
  have hstable : (prefixWord ++ tailWord_563171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563171).length < 2 ^ (prefixWord ++ tailWord_563171).sum := by decide
  have hdescent : baseEnd_563171 < baseStart_563171 := by decide
  rcases family_descends (prefixWord ++ tailWord_563171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563201 : List Nat := [1, 2, 4, 1, 2, 1, 1, 3, 1, 6]
def baseStart_563201 : Nat := 118140960795 + 563201 * 2 ^ 59
def prefixEnd_563201 : Nat := 4983230072969 + 3 ^ 40 * 563201 * 2
def baseEnd_563201 : Nat := 192795212061970804798261

theorem tailTrace_563201 : CollatzResearch.WordTrace tailWord_563201 prefixEnd_563201 192795212061970804798261 := by
  unfold tailWord_563201
  simp only [CollatzResearch.WordTrace]
  refine ⟨20541628032626438918065457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13694418688417625945376971 20541628032626438918065457)
  ·
    refine ⟨15406221024469829188549093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20541628032626438918065457 15406221024469829188549093)
    ·
      refine ⟨2888666442088092972852955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15406221024469829188549093 2888666442088092972852955)
      ·
        refine ⟨4332999663132139459279433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2888666442088092972852955 4332999663132139459279433)
        ·
          refine ⟨3249749747349104594459575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4332999663132139459279433 3249749747349104594459575)
          ·
            refine ⟨4874624621023656891689363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3249749747349104594459575 4874624621023656891689363)
            ·
              refine ⟨7311936931535485337534045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4874624621023656891689363 7311936931535485337534045)
              ·
                refine ⟨2741976349325807001575267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7311936931535485337534045 2741976349325807001575267)
                ·
                  refine ⟨4112964523988710502362901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2741976349325807001575267 4112964523988710502362901)
                  ·
                    refine ⟨192795212061970804798261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4112964523988710502362901 192795212061970804798261)
                    ·
                      rfl

theorem cell22_563201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_563201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_563201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_563201 prefixEnd_563201 := by exact prefixLift 563201
  have htrace : WordTrace (prefixWord ++ tailWord_563201) baseStart_563201 baseEnd_563201 := by
    simpa [prefixWord, tailWord_563201, baseEnd_563201] using wordTrace_append hprefix tailTrace_563201
  have hstable : (prefixWord ++ tailWord_563201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563201).length < 2 ^ (prefixWord ++ tailWord_563201).sum := by decide
  have hdescent : baseEnd_563201 < baseStart_563201 := by decide
  rcases family_descends (prefixWord ++ tailWord_563201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563205 : List Nat := [1, 3, 1, 1, 2, 6, 1, 3, 4]
def baseStart_563205 : Nat := 118140960795 + 563205 * 2 ^ 59
def prefixEnd_563205 : Nat := 4983230072969 + 3 ^ 40 * 563205 * 2
def baseEnd_563205 : Nat := 64265527114572042566083

theorem tailTrace_563205 : CollatzResearch.WordTrace tailWord_563205 prefixEnd_563205 64265527114572042566083 := by
  unfold tailWord_563205
  simp only [CollatzResearch.WordTrace]
  refine ⟨20541773924611947601211069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13694515949741298400807379 20541773924611947601211069)
  ·
    refine ⟨7703165221729480350454151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20541773924611947601211069 7703165221729480350454151)
    ·
      refine ⟨11554747832594220525681227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7703165221729480350454151 11554747832594220525681227)
      ·
        refine ⟨17332121748891330788521841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11554747832594220525681227 17332121748891330788521841)
        ·
          refine ⟨12999091311668498091391381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17332121748891330788521841 12999091311668498091391381)
          ·
            refine ⟨609332405234460848033971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12999091311668498091391381 609332405234460848033971)
            ·
              refine ⟨913998607851691272050957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 609332405234460848033971 913998607851691272050957)
              ·
                refine ⟨342749477944384227019109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 913998607851691272050957 342749477944384227019109)
                ·
                  refine ⟨64265527114572042566083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 342749477944384227019109 64265527114572042566083)
                  ·
                    rfl

theorem cell22_563205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 3, 4].length) (baseStart_563205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_563205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_563205 prefixEnd_563205 := by exact prefixLift 563205
  have htrace : WordTrace (prefixWord ++ tailWord_563205) baseStart_563205 baseEnd_563205 := by
    simpa [prefixWord, tailWord_563205, baseEnd_563205] using wordTrace_append hprefix tailTrace_563205
  have hstable : (prefixWord ++ tailWord_563205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563205).length < 2 ^ (prefixWord ++ tailWord_563205).sum := by decide
  have hdescent : baseEnd_563205 < baseStart_563205 := by decide
  rcases family_descends (prefixWord ++ tailWord_563205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563233 : List Nat := [1, 2, 3, 2, 4, 1, 2, 7]
def baseStart_563233 : Nat := 118140960795 + 563233 * 2 ^ 59
def prefixEnd_563233 : Nat := 4983230072969 + 3 ^ 40 * 563233 * 2
def baseEnd_563233 : Nat := 21422907368437043110907

theorem tailTrace_563233 : CollatzResearch.WordTrace tailWord_563233 prefixEnd_563233 21422907368437043110907 := by
  unfold tailWord_563233
  simp only [CollatzResearch.WordTrace]
  refine ⟨20542795168510508383230353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13695196779007005588820235 20542795168510508383230353)
  ·
    refine ⟨15407096376382881287422765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20542795168510508383230353 15407096376382881287422765)
    ·
      refine ⟨5777661141143580482783537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15407096376382881287422765 5777661141143580482783537)
      ·
        refine ⟨4333245855857685362087653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5777661141143580482783537 4333245855857685362087653)
        ·
          refine ⟨812483597973316005391435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4333245855857685362087653 812483597973316005391435)
          ·
            refine ⟨1218725396959974008087153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 812483597973316005391435 1218725396959974008087153)
            ·
              refine ⟨914044047719980506065365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1218725396959974008087153 914044047719980506065365)
              ·
                refine ⟨21422907368437043110907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 914044047719980506065365 21422907368437043110907)
                ·
                  rfl

theorem cell22_563233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 7].length) (baseStart_563233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_563233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_563233 prefixEnd_563233 := by exact prefixLift 563233
  have htrace : WordTrace (prefixWord ++ tailWord_563233) baseStart_563233 baseEnd_563233 := by
    simpa [prefixWord, tailWord_563233, baseEnd_563233] using wordTrace_append hprefix tailTrace_563233
  have hstable : (prefixWord ++ tailWord_563233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563233).length < 2 ^ (prefixWord ++ tailWord_563233).sum := by decide
  have hdescent : baseEnd_563233 < baseStart_563233 := by decide
  rcases family_descends (prefixWord ++ tailWord_563233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563237 : List Nat := [1, 3, 1, 2, 2, 5, 2, 1, 2, 3]
def baseStart_563237 : Nat := 118140960795 + 563237 * 2 ^ 59
def prefixEnd_563237 : Nat := 4983230072969 + 3 ^ 40 * 563237 * 2
def baseEnd_563237 : Nat := 192807535597678710898151

theorem tailTrace_563237 : CollatzResearch.WordTrace tailWord_563237 prefixEnd_563237 192807535597678710898151 := by
  unfold tailWord_563237
  simp only [CollatzResearch.WordTrace]
  refine ⟨20542941060496017066375965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13695294040330678044250643 20542941060496017066375965)
  ·
    refine ⟨7703602897686006399890987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20542941060496017066375965 7703602897686006399890987)
    ·
      refine ⟨11555404346529009599836481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7703602897686006399890987 11555404346529009599836481)
      ·
        refine ⟨8666553259896757199877361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11555404346529009599836481 8666553259896757199877361)
        ·
          refine ⟨6499914944922567899908021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8666553259896757199877361 6499914944922567899908021)
          ·
            refine ⟨609367026086490740616377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6499914944922567899908021 609367026086490740616377)
            ·
              refine ⟨457025269564868055462283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 609367026086490740616377 457025269564868055462283)
              ·
                refine ⟨685537904347302083193425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 457025269564868055462283 685537904347302083193425)
                ·
                  refine ⟨514153428260476562395069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 685537904347302083193425 514153428260476562395069)
                  ·
                    refine ⟨192807535597678710898151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 514153428260476562395069 192807535597678710898151)
                    ·
                      rfl

theorem cell22_563237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 1, 2, 3].length) (baseStart_563237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_563237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_563237 prefixEnd_563237 := by exact prefixLift 563237
  have htrace : WordTrace (prefixWord ++ tailWord_563237) baseStart_563237 baseEnd_563237 := by
    simpa [prefixWord, tailWord_563237, baseEnd_563237] using wordTrace_append hprefix tailTrace_563237
  have hstable : (prefixWord ++ tailWord_563237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563237).length < 2 ^ (prefixWord ++ tailWord_563237).sum := by decide
  have hdescent : baseEnd_563237 < baseStart_563237 := by decide
  rcases family_descends (prefixWord ++ tailWord_563237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563252 : List Nat := [2, 5, 1, 2, 2, 1, 2, 1, 2, 4]
def baseStart_563252 : Nat := 118140960795 + 563252 * 2 ^ 59
def prefixEnd_563252 : Nat := 4983230072969 + 3 ^ 40 * 563252 * 2
def baseEnd_563252 : Nat := 192812670404223671773105

theorem tailTrace_563252 : CollatzResearch.WordTrace tailWord_563252 prefixEnd_563252 192812670404223671773105 := by
  unfold tailWord_563252
  simp only [CollatzResearch.WordTrace]
  refine ⟨10271744077720837314086005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13695658770294449752114673 10271744077720837314086005)
  ·
    refine ⟨962976007286328498195563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10271744077720837314086005 962976007286328498195563)
    ·
      refine ⟨1444464010929492747293345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 962976007286328498195563 1444464010929492747293345)
      ·
        refine ⟨1083348008197119560470009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1444464010929492747293345 1083348008197119560470009)
        ·
          refine ⟨812511006147839670352507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1083348008197119560470009 812511006147839670352507)
          ·
            refine ⟨1218766509221759505528761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 812511006147839670352507 1218766509221759505528761)
            ·
              refine ⟨914074881916319629146571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1218766509221759505528761 914074881916319629146571)
              ·
                refine ⟨1371112322874479443719857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 914074881916319629146571 1371112322874479443719857)
                ·
                  refine ⟨1028334242155859582789893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1371112322874479443719857 1028334242155859582789893)
                  ·
                    refine ⟨192812670404223671773105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1028334242155859582789893 192812670404223671773105)
                    ·
                      rfl

theorem cell22_563252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_563252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_563252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_563252 prefixEnd_563252 := by exact prefixLift 563252
  have htrace : WordTrace (prefixWord ++ tailWord_563252) baseStart_563252 baseEnd_563252 := by
    simpa [prefixWord, tailWord_563252, baseEnd_563252] using wordTrace_append hprefix tailTrace_563252
  have hstable : (prefixWord ++ tailWord_563252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563252).length < 2 ^ (prefixWord ++ tailWord_563252).sum := by decide
  have hdescent : baseEnd_563252 < baseStart_563252 := by decide
  rcases family_descends (prefixWord ++ tailWord_563252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563278 : List Nat := [4, 1, 1, 1, 1, 4, 1, 4, 5]
def baseStart_563278 : Nat := 118140960795 + 563278 * 2 ^ 59
def prefixEnd_563278 : Nat := 4983230072969 + 3 ^ 40 * 563278 * 2
def baseEnd_563278 : Nat := 64273856911856090207675

theorem tailTrace_563278 : CollatzResearch.WordTrace tailWord_563278 prefixEnd_563278 64273856911856090207675 := by
  unfold tailWord_563278
  simp only [CollatzResearch.WordTrace]
  refine ⟨2568054556668435133577311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13696290968898320712412325 2568054556668435133577311)
  ·
    refine ⟨3852081835002652700365967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2568054556668435133577311 3852081835002652700365967)
    ·
      refine ⟨5778122752503979050548951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3852081835002652700365967 5778122752503979050548951)
      ·
        refine ⟨8667184128755968575823427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5778122752503979050548951 8667184128755968575823427)
        ·
          refine ⟨13000776193133952863735141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8667184128755968575823427 13000776193133952863735141)
          ·
            refine ⟨2437645536212616161950339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13000776193133952863735141 2437645536212616161950339)
            ·
              refine ⟨3656468304318924242925509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2437645536212616161950339 3656468304318924242925509)
              ·
                refine ⟨685587807059798295548533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3656468304318924242925509 685587807059798295548533)
                ·
                  refine ⟨64273856911856090207675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 685587807059798295548533 64273856911856090207675)
                  ·
                    rfl

theorem cell22_563278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_563278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_563278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_563278 prefixEnd_563278 := by exact prefixLift 563278
  have htrace : WordTrace (prefixWord ++ tailWord_563278) baseStart_563278 baseEnd_563278 := by
    simpa [prefixWord, tailWord_563278, baseEnd_563278] using wordTrace_append hprefix tailTrace_563278
  have hstable : (prefixWord ++ tailWord_563278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563278).length < 2 ^ (prefixWord ++ tailWord_563278).sum := by decide
  have hdescent : baseEnd_563278 < baseStart_563278 := by decide
  rcases family_descends (prefixWord ++ tailWord_563278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563308 : List Nat := [2, 2, 1, 1, 3, 3, 2, 1, 3, 4]
def baseStart_563308 : Nat := 118140960795 + 563308 * 2 ^ 59
def prefixEnd_563308 : Nat := 4983230072969 + 3 ^ 40 * 563308 * 2
def baseEnd_563308 : Nat := 192831840348658192372933

theorem tailTrace_563308 : CollatzResearch.WordTrace tailWord_563308 prefixEnd_563308 192831840348658192372933 := by
  unfold tailWord_563308
  simp only [CollatzResearch.WordTrace]
  refine ⟨10272765321619398096105289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13697020428825864128140385 10272765321619398096105289)
  ·
    refine ⟨7704573991214548572078967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10272765321619398096105289 7704573991214548572078967)
    ·
      refine ⟨11556860986821822858118451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7704573991214548572078967 11556860986821822858118451)
      ·
        refine ⟨17335291480232734287177677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11556860986821822858118451 17335291480232734287177677)
        ·
          refine ⟨6500734305087275357691629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17335291480232734287177677 6500734305087275357691629)
          ·
            refine ⟨2437775364407728259134361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6500734305087275357691629 2437775364407728259134361)
            ·
              refine ⟨1828331523305796194350771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2437775364407728259134361 1828331523305796194350771)
              ·
                refine ⟨2742497284958694291526157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1828331523305796194350771 2742497284958694291526157)
                ·
                  refine ⟨1028436481859510359322309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2742497284958694291526157 1028436481859510359322309)
                  ·
                    refine ⟨192831840348658192372933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1028436481859510359322309 192831840348658192372933)
                    ·
                      rfl

theorem cell22_563308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 4].length) (baseStart_563308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_563308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_563308 prefixEnd_563308 := by exact prefixLift 563308
  have htrace : WordTrace (prefixWord ++ tailWord_563308) baseStart_563308 baseEnd_563308 := by
    simpa [prefixWord, tailWord_563308, baseEnd_563308] using wordTrace_append hprefix tailTrace_563308
  have hstable : (prefixWord ++ tailWord_563308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563308).length < 2 ^ (prefixWord ++ tailWord_563308).sum := by decide
  have hdescent : baseEnd_563308 < baseStart_563308 := by decide
  rcases family_descends (prefixWord ++ tailWord_563308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563325 : List Nat := [1, 4, 1, 1, 3, 3, 1, 3, 1, 4]
def baseStart_563325 : Nat := 118140960795 + 563325 * 2 ^ 59
def prefixEnd_563325 : Nat := 4983230072969 + 3 ^ 40 * 563325 * 2
def baseEnd_563325 : Nat := 192837659796075814697881

theorem tailTrace_563325 : CollatzResearch.WordTrace tailWord_563325 prefixEnd_563325 192837659796075814697881 := by
  unfold tailWord_563325
  simp only [CollatzResearch.WordTrace]
  refine ⟨20546150684177208095579429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13697433789451472063719619 20546150684177208095579429)
  ·
    refine ⟨3852403253283226517921143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20546150684177208095579429 3852403253283226517921143)
    ·
      refine ⟨5778604879924839776881715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3852403253283226517921143 5778604879924839776881715)
      ·
        refine ⟨8667907319887259665322573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5778604879924839776881715 8667907319887259665322573)
        ·
          refine ⟨3250465244957722374495965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8667907319887259665322573 3250465244957722374495965)
          ·
            refine ⟨1218924466859145890435987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3250465244957722374495965 1218924466859145890435987)
            ·
              refine ⟨1828386700288718835653981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1218924466859145890435987 1828386700288718835653981)
              ·
                refine ⟨685645012608269563370243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1828386700288718835653981 685645012608269563370243)
                ·
                  refine ⟨1028467518912404345055365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 685645012608269563370243 1028467518912404345055365)
                  ·
                    refine ⟨192837659796075814697881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1028467518912404345055365 192837659796075814697881)
                    ·
                      rfl

theorem cell22_563325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_563325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_563325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_563325 prefixEnd_563325 := by exact prefixLift 563325
  have htrace : WordTrace (prefixWord ++ tailWord_563325) baseStart_563325 baseEnd_563325 := by
    simpa [prefixWord, tailWord_563325, baseEnd_563325] using wordTrace_append hprefix tailTrace_563325
  have hstable : (prefixWord ++ tailWord_563325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563325).length < 2 ^ (prefixWord ++ tailWord_563325).sum := by decide
  have hdescent : baseEnd_563325 < baseStart_563325 := by decide
  rcases family_descends (prefixWord ++ tailWord_563325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563428 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 4, 5]
def baseStart_563428 : Nat := 118140960795 + 563428 * 2 ^ 59
def prefixEnd_563428 : Nat := 4983230072969 + 3 ^ 40 * 563428 * 2
def baseEnd_563428 : Nat := 192872918801017879372565

theorem tailTrace_563428 : CollatzResearch.WordTrace tailWord_563428 prefixEnd_563428 192872918801017879372565 := by
  unfold tailWord_563428
  simp only [CollatzResearch.WordTrace]
  refine ⟨10274953701402028343289469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13699938268536037791052625 10274953701402028343289469)
  ·
    refine ⟨3853107638025760628733551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10274953701402028343289469 3853107638025760628733551)
    ·
      refine ⟨5779661457038640943100327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3853107638025760628733551 5779661457038640943100327)
      ·
        refine ⟨8669492185557961414650491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5779661457038640943100327 8669492185557961414650491)
        ·
          refine ⟨13004238278336942121975737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8669492185557961414650491 13004238278336942121975737)
          ·
            refine ⟨9753178708752706591481803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13004238278336942121975737 9753178708752706591481803)
            ·
              refine ⟨14629768063129059887222705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9753178708752706591481803 14629768063129059887222705)
              ·
                refine ⟨10972326047346794915417029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14629768063129059887222705 10972326047346794915417029)
                ·
                  refine ⟨2057311133877524046640693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10972326047346794915417029 2057311133877524046640693)
                  ·
                    refine ⟨192872918801017879372565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2057311133877524046640693 192872918801017879372565)
                    ·
                      rfl

theorem cell22_563428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_563428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_563428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_563428 prefixEnd_563428 := by exact prefixLift 563428
  have htrace : WordTrace (prefixWord ++ tailWord_563428) baseStart_563428 baseEnd_563428 := by
    simpa [prefixWord, tailWord_563428, baseEnd_563428] using wordTrace_append hprefix tailTrace_563428
  have hstable : (prefixWord ++ tailWord_563428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563428).length < 2 ^ (prefixWord ++ tailWord_563428).sum := by decide
  have hdescent : baseEnd_563428 < baseStart_563428 := by decide
  rcases family_descends (prefixWord ++ tailWord_563428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563492 : List Nat := [2, 3, 1, 3, 1, 2, 1, 5, 4]
def baseStart_563492 : Nat := 118140960795 + 563492 * 2 ^ 59
def prefixEnd_563492 : Nat := 4983230072969 + 3 ^ 40 * 563492 * 2
def baseEnd_563492 : Nat := 64298275769647681924123

theorem tailTrace_563492 : CollatzResearch.WordTrace tailWord_563492 prefixEnd_563492 64298275769647681924123 := by
  unfold tailWord_563492
  simp only [CollatzResearch.WordTrace]
  refine ⟨10276120837286097808454365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13701494449714797077939153 10276120837286097808454365)
  ·
    refine ⟨3853545313982286678170387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10276120837286097808454365 3853545313982286678170387)
    ·
      refine ⟨5780317970973430017255581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3853545313982286678170387 5780317970973430017255581)
      ·
        refine ⟨2167619239115036256470843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5780317970973430017255581 2167619239115036256470843)
        ·
          refine ⟨3251428858672554384706265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2167619239115036256470843 3251428858672554384706265)
          ·
            refine ⟨2438571644004415788529699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3251428858672554384706265 2438571644004415788529699)
            ·
              refine ⟨3657857466006623682794549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2438571644004415788529699 3657857466006623682794549)
              ·
                refine ⟨342924137438120970261989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3657857466006623682794549 342924137438120970261989)
                ·
                  refine ⟨64298275769647681924123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 342924137438120970261989 64298275769647681924123)
                  ·
                    rfl

theorem cell22_563492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 5, 4].length) (baseStart_563492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_563492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_563492 prefixEnd_563492 := by exact prefixLift 563492
  have htrace : WordTrace (prefixWord ++ tailWord_563492) baseStart_563492 baseEnd_563492 := by
    simpa [prefixWord, tailWord_563492, baseEnd_563492] using wordTrace_append hprefix tailTrace_563492
  have hstable : (prefixWord ++ tailWord_563492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563492).length < 2 ^ (prefixWord ++ tailWord_563492).sum := by decide
  have hdescent : baseEnd_563492 < baseStart_563492 := by decide
  rcases family_descends (prefixWord ++ tailWord_563492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563535 : List Nat := [1, 1, 2, 1, 1, 2, 1, 5, 5, 3]
def baseStart_563535 : Nat := 118140960795 + 563535 * 2 ^ 59
def prefixEnd_563535 : Nat := 4983230072969 + 3 ^ 40 * 563535 * 2
def baseEnd_563535 : Nat := 192909547087705266947237

theorem tailTrace_563535 : CollatzResearch.WordTrace tailWord_563535 prefixEnd_563535 192909547087705266947237 := by
  unfold tailWord_563535
  simp only [CollatzResearch.WordTrace]
  refine ⟨20553810013416413960724059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13702540008944275973816039 20553810013416413960724059)
  ·
    refine ⟨30830715020124620941086089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20553810013416413960724059 30830715020124620941086089)
    ·
      refine ⟨23123036265093465705814567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30830715020124620941086089 23123036265093465705814567)
      ·
        refine ⟨34684554397640198558721851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23123036265093465705814567 34684554397640198558721851)
        ·
          refine ⟨52026831596460297838082777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34684554397640198558721851 52026831596460297838082777)
          ·
            refine ⟨39020123697345223378562083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52026831596460297838082777 39020123697345223378562083)
            ·
              refine ⟨58530185546017835067843125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39020123697345223378562083 58530185546017835067843125)
              ·
                refine ⟨5487204894939172037610293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58530185546017835067843125 5487204894939172037610293)
                ·
                  refine ⟨514425458900547378525965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5487204894939172037610293 514425458900547378525965)
                  ·
                    refine ⟨192909547087705266947237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 514425458900547378525965 192909547087705266947237)
                    ·
                      rfl

theorem cell22_563535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 5, 3].length) (baseStart_563535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_563535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_563535 prefixEnd_563535 := by exact prefixLift 563535
  have htrace : WordTrace (prefixWord ++ tailWord_563535) baseStart_563535 baseEnd_563535 := by
    simpa [prefixWord, tailWord_563535, baseEnd_563535] using wordTrace_append hprefix tailTrace_563535
  have hstable : (prefixWord ++ tailWord_563535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563535).length < 2 ^ (prefixWord ++ tailWord_563535).sum := by decide
  have hdescent : baseEnd_563535 < baseStart_563535 := by decide
  rcases family_descends (prefixWord ++ tailWord_563535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563537 : List Nat := [1, 2, 2, 1, 4, 4, 2, 6]
def baseStart_563537 : Nat := 118140960795 + 563537 * 2 ^ 59
def prefixEnd_563537 : Nat := 4983230072969 + 3 ^ 40 * 563537 * 2
def baseEnd_563537 : Nat := 21434470192064214266359

theorem tailTrace_563537 : CollatzResearch.WordTrace tailWord_563537 prefixEnd_563537 21434470192064214266359 := by
  unfold tailWord_563537
  simp only [CollatzResearch.WordTrace]
  refine ⟨20553882959409168302296865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13702588639606112201531243 20553882959409168302296865)
  ·
    refine ⟨15415412219556876226722649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20553882959409168302296865 15415412219556876226722649)
    ·
      refine ⟨11561559164667657170041987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15415412219556876226722649 11561559164667657170041987)
      ·
        refine ⟨17342338747001485755062981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11561559164667657170041987 17342338747001485755062981)
        ·
          refine ⟨3251688515062778579074309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17342338747001485755062981 3251688515062778579074309)
          ·
            refine ⟨609691596574270983576433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3251688515062778579074309 609691596574270983576433)
            ·
              refine ⟨457268697430703237682325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 609691596574270983576433 457268697430703237682325)
              ·
                refine ⟨21434470192064214266359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 457268697430703237682325 21434470192064214266359)
                ·
                  rfl

theorem cell22_563537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 6].length) (baseStart_563537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_563537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_563537 prefixEnd_563537 := by exact prefixLift 563537
  have htrace : WordTrace (prefixWord ++ tailWord_563537) baseStart_563537 baseEnd_563537 := by
    simpa [prefixWord, tailWord_563537, baseEnd_563537] using wordTrace_append hprefix tailTrace_563537
  have hstable : (prefixWord ++ tailWord_563537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563537).length < 2 ^ (prefixWord ++ tailWord_563537).sum := by decide
  have hdescent : baseEnd_563537 < baseStart_563537 := by decide
  rcases family_descends (prefixWord ++ tailWord_563537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563565 : List Nat := [1, 5, 1, 1, 1, 2, 1, 3, 7]
def baseStart_563565 : Nat := 118140960795 + 563565 * 2 ^ 59
def prefixEnd_563565 : Nat := 4983230072969 + 3 ^ 40 * 563565 * 2
def baseEnd_563565 : Nat := 64306605566931729565715

theorem tailTrace_563565 : CollatzResearch.WordTrace tailWord_563565 prefixEnd_563565 64306605566931729565715 := by
  unfold tailWord_563565
  simp only [CollatzResearch.WordTrace]
  refine ⟨20554904203307729084316149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13703269468871819389544099 20554904203307729084316149)
  ·
    refine ⟨1927022269060099601654639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20554904203307729084316149 1927022269060099601654639)
    ·
      refine ⟨2890533403590149402481959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1927022269060099601654639 2890533403590149402481959)
      ·
        refine ⟨4335800105385224103722939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2890533403590149402481959 4335800105385224103722939)
        ·
          refine ⟨6503700158077836155584409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4335800105385224103722939 6503700158077836155584409)
          ·
            refine ⟨4877775118558377116688307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6503700158077836155584409 4877775118558377116688307)
            ·
              refine ⟨7316662677837565675032461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4877775118558377116688307 7316662677837565675032461)
              ·
                refine ⟨2743748504189087128137173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7316662677837565675032461 2743748504189087128137173)
                ·
                  refine ⟨64306605566931729565715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2743748504189087128137173 64306605566931729565715)
                  ·
                    rfl

theorem cell22_563565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_563565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_563565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_563565 prefixEnd_563565 := by exact prefixLift 563565
  have htrace : WordTrace (prefixWord ++ tailWord_563565) baseStart_563565 baseEnd_563565 := by
    simpa [prefixWord, tailWord_563565, baseEnd_563565] using wordTrace_append hprefix tailTrace_563565
  have hstable : (prefixWord ++ tailWord_563565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563565).length < 2 ^ (prefixWord ++ tailWord_563565).sum := by decide
  have hdescent : baseEnd_563565 < baseStart_563565 := by decide
  rcases family_descends (prefixWord ++ tailWord_563565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563640 : List Nat := [2, 1, 2, 1, 2, 2, 1, 4, 1, 6]
def baseStart_563640 : Nat := 118140960795 + 563640 * 2 ^ 59
def prefixEnd_563640 : Nat := 4983230072969 + 3 ^ 40 * 563640 * 2
def baseEnd_563640 : Nat := 192945490733519993071915

theorem tailTrace_563640 : CollatzResearch.WordTrace tailWord_563640 prefixEnd_563640 192945490733519993071915 := by
  unfold tailWord_563640
  simp only [CollatzResearch.WordTrace]
  refine ⟨10278819839018008446648187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13705093118690677928864249 10278819839018008446648187)
  ·
    refine ⟨15418229758527012669972281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10278819839018008446648187 15418229758527012669972281)
    ·
      refine ⟨11563672318895259502479211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15418229758527012669972281 11563672318895259502479211)
      ·
        refine ⟨17345508478342889253718817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11563672318895259502479211 17345508478342889253718817)
        ·
          refine ⟨13009131358757166940289113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17345508478342889253718817 13009131358757166940289113)
          ·
            refine ⟨9756848519067875205216835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13009131358757166940289113 9756848519067875205216835)
            ·
              refine ⟨14635272778601812807825253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9756848519067875205216835 14635272778601812807825253)
              ·
                refine ⟨2744113645987839901467235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14635272778601812807825253 2744113645987839901467235)
                ·
                  refine ⟨4116170468981759852200853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2744113645987839901467235 4116170468981759852200853)
                  ·
                    refine ⟨192945490733519993071915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4116170468981759852200853 192945490733519993071915)
                    ·
                      rfl

theorem cell22_563640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_563640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_563640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_563640 prefixEnd_563640 := by exact prefixLift 563640
  have htrace : WordTrace (prefixWord ++ tailWord_563640) baseStart_563640 baseEnd_563640 := by
    simpa [prefixWord, tailWord_563640, baseEnd_563640] using wordTrace_append hprefix tailTrace_563640
  have hstable : (prefixWord ++ tailWord_563640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563640).length < 2 ^ (prefixWord ++ tailWord_563640).sum := by decide
  have hdescent : baseEnd_563640 < baseStart_563640 := by decide
  rcases family_descends (prefixWord ++ tailWord_563640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563657 : List Nat := [1, 2, 1, 1, 2, 1, 7, 1, 2, 4]
def baseStart_563657 : Nat := 118140960795 + 563657 * 2 ^ 59
def prefixEnd_563657 : Nat := 4983230072969 + 3 ^ 40 * 563657 * 2
def baseEnd_563657 : Nat := 192951310180937615396863

theorem tailTrace_563657 : CollatzResearch.WordTrace tailWord_563657 prefixEnd_563657 192951310180937615396863 := by
  unfold tailWord_563657
  simp only [CollatzResearch.WordTrace]
  refine ⟨20558259718974428796665225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13705506479316285864443483 20558259718974428796665225)
  ·
    refine ⟨15418694789230821597498919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20558259718974428796665225 15418694789230821597498919)
    ·
      refine ⟨23128042183846232396248379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15418694789230821597498919 23128042183846232396248379)
      ·
        refine ⟨34692063275769348594372569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23128042183846232396248379 34692063275769348594372569)
        ·
          refine ⟨26019047456827011445779427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34692063275769348594372569 26019047456827011445779427)
          ·
            refine ⟨39028571185240517168669141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26019047456827011445779427 39028571185240517168669141)
            ·
              refine ⟨914732137154074621140683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 39028571185240517168669141 914732137154074621140683)
              ·
                refine ⟨1372098205731111931711025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 914732137154074621140683 1372098205731111931711025)
                ·
                  refine ⟨1029073654298333948783269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1372098205731111931711025 1029073654298333948783269)
                  ·
                    refine ⟨192951310180937615396863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1029073654298333948783269 192951310180937615396863)
                    ·
                      rfl

theorem cell22_563657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 2, 4].length) (baseStart_563657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_563657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_563657 prefixEnd_563657 := by exact prefixLift 563657
  have htrace : WordTrace (prefixWord ++ tailWord_563657) baseStart_563657 baseEnd_563657 := by
    simpa [prefixWord, tailWord_563657, baseEnd_563657] using wordTrace_append hprefix tailTrace_563657
  have hstable : (prefixWord ++ tailWord_563657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563657).length < 2 ^ (prefixWord ++ tailWord_563657).sum := by decide
  have hdescent : baseEnd_563657 < baseStart_563657 := by decide
  rcases family_descends (prefixWord ++ tailWord_563657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563693 : List Nat := [1, 5, 1, 3, 1, 2, 3, 1, 2, 3]
def baseStart_563693 : Nat := 118140960795 + 563693 * 2 ^ 59
def prefixEnd_563693 : Nat := 4983230072969 + 3 ^ 40 * 563693 * 2
def baseEnd_563693 : Nat := 192963633716645521496753

theorem tailTrace_563693 : CollatzResearch.WordTrace tailWord_563693 prefixEnd_563693 192963633716645521496753 := by
  unfold tailWord_563693
  simp only [CollatzResearch.WordTrace]
  refine ⟨20559572746844006944975733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13706381831229337963317155 20559572746844006944975733)
  ·
    refine ⟨1927459945016625651091475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20559572746844006944975733 1927459945016625651091475)
    ·
      refine ⟨2891189917524938476637213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1927459945016625651091475 2891189917524938476637213)
      ·
        refine ⟨1084196219071851928738955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2891189917524938476637213 1084196219071851928738955)
        ·
          refine ⟨1626294328607777893108433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1084196219071851928738955 1626294328607777893108433)
          ·
            refine ⟨1219720746455833419831325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1626294328607777893108433 1219720746455833419831325)
            ·
              refine ⟨457395279920937532436747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1219720746455833419831325 457395279920937532436747)
              ·
                refine ⟨686092919881406298655121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 457395279920937532436747 686092919881406298655121)
                ·
                  refine ⟨514569689911054723991341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 686092919881406298655121 514569689911054723991341)
                  ·
                    refine ⟨192963633716645521496753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 514569689911054723991341 192963633716645521496753)
                    ·
                      rfl

theorem cell22_563693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_563693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_563693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_563693 prefixEnd_563693 := by exact prefixLift 563693
  have htrace : WordTrace (prefixWord ++ tailWord_563693) baseStart_563693 baseEnd_563693 := by
    simpa [prefixWord, tailWord_563693, baseEnd_563693] using wordTrace_append hprefix tailTrace_563693
  have hstable : (prefixWord ++ tailWord_563693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563693).length < 2 ^ (prefixWord ++ tailWord_563693).sum := by decide
  have hdescent : baseEnd_563693 < baseStart_563693 := by decide
  rcases family_descends (prefixWord ++ tailWord_563693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563762 : List Nat := [3, 2, 1, 1, 2, 1, 2, 4, 6]
def baseStart_563762 : Nat := 118140960795 + 563762 * 2 ^ 59
def prefixEnd_563762 : Nat := 4983230072969 + 3 ^ 40 * 563762 * 2
def baseEnd_563762 : Nat := 64329084608917447173847

theorem tailTrace_563762 : CollatzResearch.WordTrace tailWord_563762 prefixEnd_563762 64329084608917447173847 := by
  unfold tailWord_563762
  simp only [CollatzResearch.WordTrace]
  refine ⟨5140522345898507932309385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13708059589062687819491693 5140522345898507932309385)
  ·
    refine ⟨3855391759423880949232039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5140522345898507932309385 3855391759423880949232039)
    ·
      refine ⟨5783087639135821423848059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3855391759423880949232039 5783087639135821423848059)
      ·
        refine ⟨8674631458703732135772089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5783087639135821423848059 8674631458703732135772089)
        ·
          refine ⟨6505973594027799101829067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8674631458703732135772089 6505973594027799101829067)
          ·
            refine ⟨9758960391041698652743601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6505973594027799101829067 9758960391041698652743601)
            ·
              refine ⟨7319220293281273989557701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9758960391041698652743601 7319220293281273989557701)
              ·
                refine ⟨1372353804990238873042069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7319220293281273989557701 1372353804990238873042069)
                ·
                  refine ⟨64329084608917447173847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1372353804990238873042069 64329084608917447173847)
                  ·
                    rfl

theorem cell22_563762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_563762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_563762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_563762 prefixEnd_563762 := by exact prefixLift 563762
  have htrace : WordTrace (prefixWord ++ tailWord_563762) baseStart_563762 baseEnd_563762 := by
    simpa [prefixWord, tailWord_563762, baseEnd_563762] using wordTrace_append hprefix tailTrace_563762
  have hstable : (prefixWord ++ tailWord_563762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563762).length < 2 ^ (prefixWord ++ tailWord_563762).sum := by decide
  have hdescent : baseEnd_563762 < baseStart_563762 := by decide
  rcases family_descends (prefixWord ++ tailWord_563762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563781 : List Nat := [1, 3, 1, 1, 1, 6, 3, 1, 1, 4]
def baseStart_563781 : Nat := 118140960795 + 563781 * 2 ^ 59
def prefixEnd_563781 : Nat := 4983230072969 + 3 ^ 40 * 563781 * 2
def baseEnd_563781 : Nat := 192993757915042625296483

theorem tailTrace_563781 : CollatzResearch.WordTrace tailWord_563781 prefixEnd_563781 192993757915042625296483 := by
  unfold tailWord_563781
  simp only [CollatzResearch.WordTrace]
  refine ⟨20562782370525197974179197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13708521580350131982786131 20562782370525197974179197)
  ·
    refine ⟨7711043388946949240317199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20562782370525197974179197 7711043388946949240317199)
    ·
      refine ⟨11566565083420423860475799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7711043388946949240317199 11566565083420423860475799)
      ·
        refine ⟨17349847625130635790713699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11566565083420423860475799 17349847625130635790713699)
        ·
          refine ⟨26024771437695953686070549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17349847625130635790713699 26024771437695953686070549)
          ·
            refine ⟨1219911161141997829034557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 26024771437695953686070549 1219911161141997829034557)
            ·
              refine ⟨457466685428249185887959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1219911161141997829034557 457466685428249185887959)
              ·
                refine ⟨686200028142373778831939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 457466685428249185887959 686200028142373778831939)
                ·
                  refine ⟨1029300042213560668247909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 686200028142373778831939 1029300042213560668247909)
                  ·
                    refine ⟨192993757915042625296483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1029300042213560668247909 192993757915042625296483)
                    ·
                      rfl

theorem cell22_563781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 1, 1, 4].length) (baseStart_563781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_563781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_563781 prefixEnd_563781 := by exact prefixLift 563781
  have htrace : WordTrace (prefixWord ++ tailWord_563781) baseStart_563781 baseEnd_563781 := by
    simpa [prefixWord, tailWord_563781, baseEnd_563781] using wordTrace_append hprefix tailTrace_563781
  have hstable : (prefixWord ++ tailWord_563781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563781).length < 2 ^ (prefixWord ++ tailWord_563781).sum := by decide
  have hdescent : baseEnd_563781 < baseStart_563781 := by decide
  rcases family_descends (prefixWord ++ tailWord_563781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563792 : List Nat := [2, 1, 1, 1, 1, 3, 2, 3, 4, 4]
def baseStart_563792 : Nat := 118140960795 + 563792 * 2 ^ 59
def prefixEnd_563792 : Nat := 4983230072969 + 3 ^ 40 * 563792 * 2
def baseEnd_563792 : Nat := 192997523439842263271449

theorem tailTrace_563792 : CollatzResearch.WordTrace tailWord_563792 prefixEnd_563792 192997523439842263271449 := by
  unfold tailWord_563792
  simp only [CollatzResearch.WordTrace]
  refine ⟨10281591786742673426414815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13708789048990231235219753 10281591786742673426414815)
  ·
    refine ⟨15422387680114010139622223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10281591786742673426414815 15422387680114010139622223)
    ·
      refine ⟨23133581520171015209433335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15422387680114010139622223 23133581520171015209433335)
      ·
        refine ⟨34700372280256522814150003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23133581520171015209433335 34700372280256522814150003)
        ·
          refine ⟨52050558420384784221225005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34700372280256522814150003 52050558420384784221225005)
          ·
            refine ⟨19518959407644294082959377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52050558420384784221225005 19518959407644294082959377)
            ·
              refine ⟨14639219555733220562219533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19518959407644294082959377 14639219555733220562219533)
              ·
                refine ⟨5489707333399957710832325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14639219555733220562219533 5489707333399957710832325)
                ·
                  refine ⟨1029320125012492070781061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5489707333399957710832325 1029320125012492070781061)
                  ·
                    refine ⟨192997523439842263271449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1029320125012492070781061 192997523439842263271449)
                    ·
                      rfl

theorem cell22_563792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 4, 4].length) (baseStart_563792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_563792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_563792 prefixEnd_563792 := by exact prefixLift 563792
  have htrace : WordTrace (prefixWord ++ tailWord_563792) baseStart_563792 baseEnd_563792 := by
    simpa [prefixWord, tailWord_563792, baseEnd_563792] using wordTrace_append hprefix tailTrace_563792
  have hstable : (prefixWord ++ tailWord_563792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563792).length < 2 ^ (prefixWord ++ tailWord_563792).sum := by decide
  have hdescent : baseEnd_563792 < baseStart_563792 := by decide
  rcases family_descends (prefixWord ++ tailWord_563792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563796 : List Nat := [2, 4, 1, 1, 1, 4, 1, 4, 4]
def baseStart_563796 : Nat := 118140960795 + 563796 * 2 ^ 59
def prefixEnd_563796 : Nat := 4983230072969 + 3 ^ 40 * 563796 * 2
def baseEnd_563796 : Nat := 64332964240529195390479

theorem tailTrace_563796 : CollatzResearch.WordTrace tailWord_563796 prefixEnd_563796 64332964240529195390479 := by
  unfold tailWord_563796
  simp only [CollatzResearch.WordTrace]
  refine ⟨10281664732735427767987621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13708886310313903690650161 10281664732735427767987621)
  ·
    refine ⟨1927812137387892706497679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10281664732735427767987621 1927812137387892706497679)
    ·
      refine ⟨2891718206081839059746519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1927812137387892706497679 2891718206081839059746519)
      ·
        refine ⟨4337577309122758589619779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2891718206081839059746519 4337577309122758589619779)
        ·
          refine ⟨6506365963684137884429669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4337577309122758589619779 6506365963684137884429669)
          ·
            refine ⟨1219943618190775853330563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6506365963684137884429669 1219943618190775853330563)
            ·
              refine ⟨1829915427286163779995845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1219943618190775853330563 1829915427286163779995845)
              ·
                refine ⟨343109142616155708749221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1829915427286163779995845 343109142616155708749221)
                ·
                  refine ⟨64332964240529195390479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 343109142616155708749221 64332964240529195390479)
                  ·
                    rfl

theorem cell22_563796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_563796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_563796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_563796 prefixEnd_563796 := by exact prefixLift 563796
  have htrace : WordTrace (prefixWord ++ tailWord_563796) baseStart_563796 baseEnd_563796 := by
    simpa [prefixWord, tailWord_563796, baseEnd_563796] using wordTrace_append hprefix tailTrace_563796
  have hstable : (prefixWord ++ tailWord_563796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563796).length < 2 ^ (prefixWord ++ tailWord_563796).sum := by decide
  have hdescent : baseEnd_563796 < baseStart_563796 := by decide
  rcases family_descends (prefixWord ++ tailWord_563796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563869 : List Nat := [1, 4, 2, 1, 1, 1, 2, 5, 5]
def baseStart_563869 : Nat := 118140960795 + 563869 * 2 ^ 59
def prefixEnd_563869 : Nat := 4983230072969 + 3 ^ 40 * 563869 * 2
def baseEnd_563869 : Nat := 64341294037813243032071

theorem tailTrace_563869 : CollatzResearch.WordTrace tailWord_563869 prefixEnd_563869 64341294037813243032071 := by
  unfold tailWord_563869
  simp only [CollatzResearch.WordTrace]
  refine ⟨20565991994206389003382661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13710661329470926002255107 20565991994206389003382661)
  ·
    refine ⟨3856123498913697938134249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20565991994206389003382661 3856123498913697938134249)
    ·
      refine ⟨2892092624185273453600687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3856123498913697938134249 2892092624185273453600687)
      ·
        refine ⟨4338138936277910180401031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2892092624185273453600687 4338138936277910180401031)
        ·
          refine ⟨6507208404416865270601547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4338138936277910180401031 6507208404416865270601547)
          ·
            refine ⟨9760812606625297905902321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6507208404416865270601547 9760812606625297905902321)
            ·
              refine ⟨7320609454968973429426741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9760812606625297905902321 7320609454968973429426741)
              ·
                refine ⟨686307136403341259008757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7320609454968973429426741 686307136403341259008757)
                ·
                  refine ⟨64341294037813243032071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 686307136403341259008757 64341294037813243032071)
                  ·
                    rfl

theorem cell22_563869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_563869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_563869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_563869 prefixEnd_563869 := by exact prefixLift 563869
  have htrace : WordTrace (prefixWord ++ tailWord_563869) baseStart_563869 baseEnd_563869 := by
    simpa [prefixWord, tailWord_563869, baseEnd_563869] using wordTrace_append hprefix tailTrace_563869
  have hstable : (prefixWord ++ tailWord_563869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563869).length < 2 ^ (prefixWord ++ tailWord_563869).sum := by decide
  have hdescent : baseEnd_563869 < baseStart_563869 := by decide
  rcases family_descends (prefixWord ++ tailWord_563869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563886 : List Nat := [4, 1, 4, 1, 1, 1, 1, 2, 7]
def baseStart_563886 : Nat := 118140960795 + 563886 * 2 ^ 59
def prefixEnd_563886 : Nat := 4983230072969 + 3 ^ 40 * 563886 * 2
def baseEnd_563886 : Nat := 64343233853619117140387

theorem tailTrace_563886 : CollatzResearch.WordTrace tailWord_563886 prefixEnd_563886 64343233853619117140387 := by
  unfold tailWord_563886
  simp only [CollatzResearch.WordTrace]
  refine ⟨2570826504393100113343939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13711074690096533937834341 2570826504393100113343939)
  ·
    refine ⟨3856239756589650170015909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2570826504393100113343939 3856239756589650170015909)
    ·
      refine ⟨723044954360559406877983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3856239756589650170015909 723044954360559406877983)
      ·
        refine ⟨1084567431540839110316975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 723044954360559406877983 1084567431540839110316975)
        ·
          refine ⟨1626851147311258665475463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1084567431540839110316975 1626851147311258665475463)
          ·
            refine ⟨2440276720966887998213195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1626851147311258665475463 2440276720966887998213195)
            ·
              refine ⟨3660415081450331997319793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2440276720966887998213195 3660415081450331997319793)
              ·
                refine ⟨2745311311087748997989845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3660415081450331997319793 2745311311087748997989845)
                ·
                  refine ⟨64343233853619117140387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2745311311087748997989845 64343233853619117140387)
                  ·
                    rfl

theorem cell22_563886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_563886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_563886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_563886 prefixEnd_563886 := by exact prefixLift 563886
  have htrace : WordTrace (prefixWord ++ tailWord_563886) baseStart_563886 baseEnd_563886 := by
    simpa [prefixWord, tailWord_563886, baseEnd_563886] using wordTrace_append hprefix tailTrace_563886
  have hstable : (prefixWord ++ tailWord_563886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563886).length < 2 ^ (prefixWord ++ tailWord_563886).sum := by decide
  have hdescent : baseEnd_563886 < baseStart_563886 := by decide
  rcases family_descends (prefixWord ++ tailWord_563886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563929 : List Nat := [1, 2, 1, 2, 3, 2, 2, 3, 1, 5]
def baseStart_563929 : Nat := 118140960795 + 563929 * 2 ^ 59
def prefixEnd_563929 : Nat := 4983230072969 + 3 ^ 40 * 563929 * 2
def baseEnd_563929 : Nat := 193044421339619572596029

theorem tailTrace_563929 : CollatzResearch.WordTrace tailWord_563929 prefixEnd_563929 193044421339619572596029 := by
  unfold tailWord_563929
  simp only [CollatzResearch.WordTrace]
  refine ⟨20568180373989019250566841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13712120249326012833711227 20568180373989019250566841)
  ·
    refine ⟨15426135280491764437925131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20568180373989019250566841 15426135280491764437925131)
    ·
      refine ⟨23139202920737646656887697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15426135280491764437925131 23139202920737646656887697)
      ·
        refine ⟨17354402190553234992665773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23139202920737646656887697 17354402190553234992665773)
        ·
          refine ⟨6507900821457463122249665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17354402190553234992665773 6507900821457463122249665)
          ·
            refine ⟨4880925616093097341687249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6507900821457463122249665 4880925616093097341687249)
            ·
              refine ⟨3660694212069823006265437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4880925616093097341687249 3660694212069823006265437)
              ·
                refine ⟨1372760329526183627349539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3660694212069823006265437 1372760329526183627349539)
                ·
                  refine ⟨2059140494289275441024309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1372760329526183627349539 2059140494289275441024309)
                  ·
                    refine ⟨193044421339619572596029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2059140494289275441024309 193044421339619572596029)
                    ·
                      rfl

theorem cell22_563929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 5].length) (baseStart_563929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_563929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_563929 prefixEnd_563929 := by exact prefixLift 563929
  have htrace : WordTrace (prefixWord ++ tailWord_563929) baseStart_563929 baseEnd_563929 := by
    simpa [prefixWord, tailWord_563929, baseEnd_563929] using wordTrace_append hprefix tailTrace_563929
  have hstable : (prefixWord ++ tailWord_563929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563929).length < 2 ^ (prefixWord ++ tailWord_563929).sum := by decide
  have hdescent : baseEnd_563929 < baseStart_563929 := by decide
  rcases family_descends (prefixWord ++ tailWord_563929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563976 : List Nat := [2, 1, 3, 2, 2, 4, 1, 7]
def baseStart_563976 : Nat := 118140960795 + 563976 * 2 ^ 59
def prefixEnd_563976 : Nat := 4983230072969 + 3 ^ 40 * 563976 * 2
def baseEnd_563976 : Nat := 21451167822236346296765

theorem tailTrace_563976 : CollatzResearch.WordTrace tailWord_563976 prefixEnd_563976 21451167822236346296765 := by
  unfold tailWord_563976
  simp only [CollatzResearch.WordTrace]
  refine ⟨10284947302409373138763891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13713263069879164185018521 10284947302409373138763891)
  ·
    refine ⟨15427420953614059708145837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10284947302409373138763891 15427420953614059708145837)
    ·
      refine ⟨5785282857605272390554689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15427420953614059708145837 5785282857605272390554689)
      ·
        refine ⟨4338962143203954292916017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5785282857605272390554689 4338962143203954292916017)
        ·
          refine ⟨3254221607402965719687013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4338962143203954292916017 3254221607402965719687013)
          ·
            refine ⟨610166551388056072441315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3254221607402965719687013 610166551388056072441315)
            ·
              refine ⟨915249827082084108661973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 610166551388056072441315 915249827082084108661973)
              ·
                refine ⟨21451167822236346296765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 915249827082084108661973 21451167822236346296765)
                ·
                  rfl

theorem cell22_563976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 7].length) (baseStart_563976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_563976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_563976 prefixEnd_563976 := by exact prefixLift 563976
  have htrace : WordTrace (prefixWord ++ tailWord_563976) baseStart_563976 baseEnd_563976 := by
    simpa [prefixWord, tailWord_563976, baseEnd_563976] using wordTrace_append hprefix tailTrace_563976
  have hstable : (prefixWord ++ tailWord_563976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563976).length < 2 ^ (prefixWord ++ tailWord_563976).sum := by decide
  have hdescent : baseEnd_563976 < baseStart_563976 := by decide
  rcases family_descends (prefixWord ++ tailWord_563976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563989 : List Nat := [1, 3, 2, 1, 2, 2, 1, 2, 2, 6]
def baseStart_563989 : Nat := 118140960795 + 563989 * 2 ^ 59
def prefixEnd_563989 : Nat := 4983230072969 + 3 ^ 40 * 563989 * 2
def baseEnd_563989 : Nat := 193064960565799416095845

theorem tailTrace_563989 : CollatzResearch.WordTrace tailWord_563989 prefixEnd_563989 193064960565799416095845 := by
  unfold tailWord_563989
  simp only [CollatzResearch.WordTrace]
  refine ⟨20570368753771649497751021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13713579169181099665167347 20570368753771649497751021)
  ·
    refine ⟨7713888282664368561656633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20570368753771649497751021 7713888282664368561656633)
    ·
      refine ⟨5785416211998276421242475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7713888282664368561656633 5785416211998276421242475)
      ·
        refine ⟨8678124317997414631863713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5785416211998276421242475 8678124317997414631863713)
        ·
          refine ⟨6508593238498060973897785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8678124317997414631863713 6508593238498060973897785)
          ·
            refine ⟨4881444928873545730423339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6508593238498060973897785 4881444928873545730423339)
            ·
              refine ⟨7322167393310318595635009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4881444928873545730423339 7322167393310318595635009)
              ·
                refine ⟨5491625544982738946726257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7322167393310318595635009 5491625544982738946726257)
                ·
                  refine ⟨4118719158737054210044693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5491625544982738946726257 4118719158737054210044693)
                  ·
                    refine ⟨193064960565799416095845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4118719158737054210044693 193064960565799416095845)
                    ·
                      rfl

theorem cell22_563989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_563989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_563989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_563989 prefixEnd_563989 := by exact prefixLift 563989
  have htrace : WordTrace (prefixWord ++ tailWord_563989) baseStart_563989 baseEnd_563989 := by
    simpa [prefixWord, tailWord_563989, baseEnd_563989] using wordTrace_append hprefix tailTrace_563989
  have hstable : (prefixWord ++ tailWord_563989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563989).length < 2 ^ (prefixWord ++ tailWord_563989).sum := by decide
  have hdescent : baseEnd_563989 < baseStart_563989 := by decide
  rcases family_descends (prefixWord ++ tailWord_563989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564021 : List Nat := [1, 3, 3, 1, 3, 2, 1, 1, 7]
def baseStart_564021 : Nat := 118140960795 + 564021 * 2 ^ 59
def prefixEnd_564021 : Nat := 4983230072969 + 3 ^ 40 * 564021 * 2
def baseEnd_564021 : Nat := 64358638273253999765249

theorem tailTrace_564021 : CollatzResearch.WordTrace tailWord_564021 prefixEnd_564021 64358638273253999765249 := by
  unfold tailWord_564021
  simp only [CollatzResearch.WordTrace]
  refine ⟨20571535889655718962915917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13714357259770479308610611 20571535889655718962915917)
  ·
    refine ⟨7714325958620894611093469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20571535889655718962915917 7714325958620894611093469)
    ·
      refine ⟨2892872234482835479160051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7714325958620894611093469 2892872234482835479160051)
      ·
        refine ⟨4339308351724253218740077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2892872234482835479160051 4339308351724253218740077)
        ·
          refine ⟨1627240631896594957027529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4339308351724253218740077 1627240631896594957027529)
          ·
            refine ⟨1220430473922446217770647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1627240631896594957027529 1220430473922446217770647)
            ·
              refine ⟨1830645710883669326655971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1220430473922446217770647 1830645710883669326655971)
              ·
                refine ⟨2745968566325503989983957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1830645710883669326655971 2745968566325503989983957)
                ·
                  refine ⟨64358638273253999765249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2745968566325503989983957 64358638273253999765249)
                  ·
                    rfl

theorem cell22_564021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 7].length) (baseStart_564021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_564021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_564021 prefixEnd_564021 := by exact prefixLift 564021
  have htrace : WordTrace (prefixWord ++ tailWord_564021) baseStart_564021 baseEnd_564021 := by
    simpa [prefixWord, tailWord_564021, baseEnd_564021] using wordTrace_append hprefix tailTrace_564021
  have hstable : (prefixWord ++ tailWord_564021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564021).length < 2 ^ (prefixWord ++ tailWord_564021).sum := by decide
  have hdescent : baseEnd_564021 < baseStart_564021 := by decide
  rcases family_descends (prefixWord ++ tailWord_564021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564068 : List Nat := [2, 3, 1, 1, 4, 1, 2, 3, 1, 4]
def baseStart_564068 : Nat := 118140960795 + 564068 * 2 ^ 59
def prefixEnd_564068 : Nat := 4983230072969 + 3 ^ 40 * 564068 * 2
def baseEnd_564068 : Nat := 193092003880269543370603

theorem tailTrace_564068 : CollatzResearch.WordTrace tailWord_564068 prefixEnd_564068 193092003880269543370603 := by
  unfold tailWord_564068
  simp only [CollatzResearch.WordTrace]
  refine ⟨10286625060242722994938429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13715500080323630659917905 10286625060242722994938429)
  ·
    refine ⟨3857484397591021123101911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10286625060242722994938429 3857484397591021123101911)
    ·
      refine ⟨5786226596386531684652867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3857484397591021123101911 5786226596386531684652867)
      ·
        refine ⟨8679339894579797526979301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5786226596386531684652867 8679339894579797526979301)
        ·
          refine ⟨1627376230233712036308619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8679339894579797526979301 1627376230233712036308619)
          ·
            refine ⟨2441064345350568054462929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1627376230233712036308619 2441064345350568054462929)
            ·
              refine ⟨1830798259012926040847197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2441064345350568054462929 1830798259012926040847197)
              ·
                refine ⟨686549347129847265317699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1830798259012926040847197 686549347129847265317699)
                ·
                  refine ⟨1029824020694770897976549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 686549347129847265317699 1029824020694770897976549)
                  ·
                    refine ⟨193092003880269543370603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1029824020694770897976549 193092003880269543370603)
                    ·
                      rfl

theorem cell22_564068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_564068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_564068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_564068 prefixEnd_564068 := by exact prefixLift 564068
  have htrace : WordTrace (prefixWord ++ tailWord_564068) baseStart_564068 baseEnd_564068 := by
    simpa [prefixWord, tailWord_564068, baseEnd_564068] using wordTrace_append hprefix tailTrace_564068
  have hstable : (prefixWord ++ tailWord_564068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564068).length < 2 ^ (prefixWord ++ tailWord_564068).sum := by decide
  have hdescent : baseEnd_564068 < baseStart_564068 := by decide
  rcases family_descends (prefixWord ++ tailWord_564068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564145 : List Nat := [1, 2, 2, 4, 4, 1, 1, 7]
def baseStart_564145 : Nat := 118140960795 + 564145 * 2 ^ 59
def prefixEnd_564145 : Nat := 4983230072969 + 3 ^ 40 * 564145 * 2
def baseEnd_564145 : Nat := 21457595839318556577263

theorem tailTrace_564145 : CollatzResearch.WordTrace tailWord_564145 prefixEnd_564145 21457595839318556577263 := by
  unfold tailWord_564145
  simp only [CollatzResearch.WordTrace]
  refine ⟨20576058541206488140429889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13717372360804325426953259 20576058541206488140429889)
  ·
    refine ⟨15432043905904866105322417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20576058541206488140429889 15432043905904866105322417)
    ·
      refine ⟨11574032929428649578991813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15432043905904866105322417 11574032929428649578991813)
      ·
        refine ⟨2170131174267871796060965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11574032929428649578991813 2170131174267871796060965)
        ·
          refine ⟨406899595175225961761431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2170131174267871796060965 406899595175225961761431)
          ·
            refine ⟨610349392762838942642147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 406899595175225961761431 610349392762838942642147)
            ·
              refine ⟨915524089144258413963221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 610349392762838942642147 915524089144258413963221)
              ·
                refine ⟨21457595839318556577263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 915524089144258413963221 21457595839318556577263)
                ·
                  rfl

theorem cell22_564145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 7].length) (baseStart_564145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_564145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_564145 prefixEnd_564145 := by exact prefixLift 564145
  have htrace : WordTrace (prefixWord ++ tailWord_564145) baseStart_564145 baseEnd_564145 := by
    simpa [prefixWord, tailWord_564145, baseEnd_564145] using wordTrace_append hprefix tailTrace_564145
  have hstable : (prefixWord ++ tailWord_564145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564145).length < 2 ^ (prefixWord ++ tailWord_564145).sum := by decide
  have hdescent : baseEnd_564145 < baseStart_564145 := by decide
  rcases family_descends (prefixWord ++ tailWord_564145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564164 : List Nat := [2, 3, 3, 3, 2, 1, 1, 1, 2, 4]
def baseStart_564164 : Nat := 118140960795 + 564164 * 2 ^ 59
def prefixEnd_564164 : Nat := 4983230072969 + 3 ^ 40 * 564164 * 2
def baseEnd_564164 : Nat := 193124866642157292970309

theorem tailTrace_564164 : CollatzResearch.WordTrace tailWord_564164 prefixEnd_564164 193124866642157292970309 := by
  unfold tailWord_564164
  simp only [CollatzResearch.WordTrace]
  refine ⟨10288375764068827192685773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13717834352091769590247697 10288375764068827192685773)
  ·
    refine ⟨3858140911525810197257165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10288375764068827192685773 3858140911525810197257165)
    ·
      refine ⟨1446802841822178823971437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3858140911525810197257165 1446802841822178823971437)
      ·
        refine ⟨542551065683317058989289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1446802841822178823971437 542551065683317058989289)
        ·
          refine ⟨406913299262487794241967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 542551065683317058989289 406913299262487794241967)
          ·
            refine ⟨610369948893731691362951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 406913299262487794241967 610369948893731691362951)
            ·
              refine ⟨915554923340597537044427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 610369948893731691362951 915554923340597537044427)
              ·
                refine ⟨1373332385010896305566641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 915554923340597537044427 1373332385010896305566641)
                ·
                  refine ⟨1029999288758172229174981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1373332385010896305566641 1029999288758172229174981)
                  ·
                    refine ⟨193124866642157292970309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1029999288758172229174981 193124866642157292970309)
                    ·
                      rfl

theorem cell22_564164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_564164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_564164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_564164 prefixEnd_564164 := by exact prefixLift 564164
  have htrace : WordTrace (prefixWord ++ tailWord_564164) baseStart_564164 baseEnd_564164 := by
    simpa [prefixWord, tailWord_564164, baseEnd_564164] using wordTrace_append hprefix tailTrace_564164
  have hstable : (prefixWord ++ tailWord_564164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564164).length < 2 ^ (prefixWord ++ tailWord_564164).sum := by decide
  have hdescent : baseEnd_564164 < baseStart_564164 := by decide
  rcases family_descends (prefixWord ++ tailWord_564164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564194 : List Nat := [3, 3, 3, 1, 1, 1, 2, 4, 1, 3]
def baseStart_564194 : Nat := 118140960795 + 564194 * 2 ^ 59
def prefixEnd_564194 : Nat := 4983230072969 + 3 ^ 40 * 564194 * 2
def baseEnd_564194 : Nat := 193135136255247214720217

theorem tailTrace_564194 : CollatzResearch.WordTrace tailWord_564194 prefixEnd_564194 193135136255247214720217 := by
  unfold tailWord_564194
  simp only [CollatzResearch.WordTrace]
  refine ⟨5144461429507242377240909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13718563812019313005975757 5144461429507242377240909)
  ·
    refine ⟨1929173036065215891465341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5144461429507242377240909 1929173036065215891465341)
    ·
      refine ⟨723439888524455959299503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1929173036065215891465341 723439888524455959299503)
      ·
        refine ⟨1085159832786683938949255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 723439888524455959299503 1085159832786683938949255)
        ·
          refine ⟨1627739749180025908423883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1085159832786683938949255 1627739749180025908423883)
          ·
            refine ⟨2441609623770038862635825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1627739749180025908423883 2441609623770038862635825)
            ·
              refine ⟨1831207217827529146976869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2441609623770038862635825 1831207217827529146976869)
              ·
                refine ⟨343351353342661715058163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1831207217827529146976869 343351353342661715058163)
                ·
                  refine ⟨515027030013992572587245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 343351353342661715058163 515027030013992572587245)
                  ·
                    refine ⟨193135136255247214720217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 515027030013992572587245 193135136255247214720217)
                    ·
                      rfl

theorem cell22_564194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_564194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_564194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_564194 prefixEnd_564194 := by exact prefixLift 564194
  have htrace : WordTrace (prefixWord ++ tailWord_564194) baseStart_564194 baseEnd_564194 := by
    simpa [prefixWord, tailWord_564194, baseEnd_564194] using wordTrace_append hprefix tailTrace_564194
  have hstable : (prefixWord ++ tailWord_564194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564194).length < 2 ^ (prefixWord ++ tailWord_564194).sum := by decide
  have hdescent : baseEnd_564194 < baseStart_564194 := by decide
  rcases family_descends (prefixWord ++ tailWord_564194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564220 : List Nat := [2, 2, 2, 1, 2, 4, 2, 2, 1, 4]
def baseStart_564220 : Nat := 118140960795 + 564220 * 2 ^ 59
def prefixEnd_564220 : Nat := 4983230072969 + 3 ^ 40 * 564220 * 2
def baseEnd_564220 : Nat := 193144036586591813570137

theorem tailTrace_564220 : CollatzResearch.WordTrace tailWord_564220 prefixEnd_564220 193144036586591813570137 := by
  unfold tailWord_564220
  simp only [CollatzResearch.WordTrace]
  refine ⟨10289397007967387974705057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13719196010623183966273409 10289397007967387974705057)
  ·
    refine ⟨7717047755975540981028793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10289397007967387974705057 7717047755975540981028793)
    ·
      refine ⟨5787785816981655735771595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7717047755975540981028793 5787785816981655735771595)
      ·
        refine ⟨8681678725472483603657393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5787785816981655735771595 8681678725472483603657393)
        ·
          refine ⟨6511259044104362702743045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8681678725472483603657393 6511259044104362702743045)
          ·
            refine ⟨1220861070769568006764321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6511259044104362702743045 1220861070769568006764321)
            ·
              refine ⟨915645803077176005073241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1220861070769568006764321 915645803077176005073241)
              ·
                refine ⟨686734352307882003804931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 915645803077176005073241 686734352307882003804931)
                ·
                  refine ⟨1030101528461823005707397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 686734352307882003804931 1030101528461823005707397)
                  ·
                    refine ⟨193144036586591813570137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1030101528461823005707397 193144036586591813570137)
                    ·
                      rfl

theorem cell22_564220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_564220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_564220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_564220 prefixEnd_564220 := by exact prefixLift 564220
  have htrace : WordTrace (prefixWord ++ tailWord_564220) baseStart_564220 baseEnd_564220 := by
    simpa [prefixWord, tailWord_564220, baseEnd_564220] using wordTrace_append hprefix tailTrace_564220
  have hstable : (prefixWord ++ tailWord_564220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564220).length < 2 ^ (prefixWord ++ tailWord_564220).sum := by decide
  have hdescent : baseEnd_564220 < baseStart_564220 := by decide
  rcases family_descends (prefixWord ++ tailWord_564220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564235 : List Nat := [1, 1, 1, 1, 6, 2, 3, 3, 4]
def baseStart_564235 : Nat := 118140960795 + 564235 * 2 ^ 59
def prefixEnd_564235 : Nat := 4983230072969 + 3 ^ 40 * 564235 * 2
def baseEnd_564235 : Nat := 64383057131045591481697

theorem tailTrace_564235 : CollatzResearch.WordTrace tailWord_564235 prefixEnd_564235 64383057131045591481697 := by
  unfold tailWord_564235
  simp only [CollatzResearch.WordTrace]
  refine ⟨20579341110880433511206159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13719560740586955674137439 20579341110880433511206159)
  ·
    refine ⟨30869011666320650266809239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20579341110880433511206159 30869011666320650266809239)
    ·
      refine ⟨46303517499480975400213859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30869011666320650266809239 46303517499480975400213859)
      ·
        refine ⟨69455276249221463100320789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46303517499480975400213859 69455276249221463100320789)
        ·
          refine ⟨3255716074182256082827537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 69455276249221463100320789 3255716074182256082827537)
          ·
            refine ⟨2441787055636692062120653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3255716074182256082827537 2441787055636692062120653)
            ·
              refine ⟨915670145863759523295245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2441787055636692062120653 915670145863759523295245)
              ·
                refine ⟨343376304698909821235717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 915670145863759523295245 343376304698909821235717)
                ·
                  refine ⟨64383057131045591481697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 343376304698909821235717 64383057131045591481697)
                  ·
                    rfl

theorem cell22_564235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 3, 4].length) (baseStart_564235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_564235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_564235 prefixEnd_564235 := by exact prefixLift 564235
  have htrace : WordTrace (prefixWord ++ tailWord_564235) baseStart_564235 baseEnd_564235 := by
    simpa [prefixWord, tailWord_564235, baseEnd_564235] using wordTrace_append hprefix tailTrace_564235
  have hstable : (prefixWord ++ tailWord_564235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564235).length < 2 ^ (prefixWord ++ tailWord_564235).sum := by decide
  have hdescent : baseEnd_564235 < baseStart_564235 := by decide
  rcases family_descends (prefixWord ++ tailWord_564235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564248 : List Nat := [2, 1, 2, 3, 2, 2, 1, 1, 4, 4]
def baseStart_564248 : Nat := 118140960795 + 564248 * 2 ^ 59
def prefixEnd_564248 : Nat := 4983230072969 + 3 ^ 40 * 564248 * 2
def baseEnd_564248 : Nat := 193153621558809073870051

theorem tailTrace_564248 : CollatzResearch.WordTrace tailWord_564248 prefixEnd_564248 193153621558809073870051 := by
  unfold tailWord_564248
  simp only [CollatzResearch.WordTrace]
  refine ⟨10289907629916668365714699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13719876839888891154286265 10289907629916668365714699)
  ·
    refine ⟨15434861444875002548572049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10289907629916668365714699 15434861444875002548572049)
    ·
      refine ⟨11576146083656251911429037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15434861444875002548572049 11576146083656251911429037)
      ·
        refine ⟨4341054781371094466785889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11576146083656251911429037 4341054781371094466785889)
        ·
          refine ⟨3255791086028320850089417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4341054781371094466785889 3255791086028320850089417)
          ·
            refine ⟨2441843314521240637567063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3255791086028320850089417 2441843314521240637567063)
            ·
              refine ⟨3662764971781860956350595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2441843314521240637567063 3662764971781860956350595)
              ·
                refine ⟨5494147457672791434525893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3662764971781860956350595 5494147457672791434525893)
                ·
                  refine ⟨1030152648313648393973605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5494147457672791434525893 1030152648313648393973605)
                  ·
                    refine ⟨193153621558809073870051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1030152648313648393973605 193153621558809073870051)
                    ·
                      rfl

theorem cell22_564248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 4, 4].length) (baseStart_564248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_564248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_564248 prefixEnd_564248 := by exact prefixLift 564248
  have htrace : WordTrace (prefixWord ++ tailWord_564248) baseStart_564248 baseEnd_564248 := by
    simpa [prefixWord, tailWord_564248, baseEnd_564248] using wordTrace_append hprefix tailTrace_564248
  have hstable : (prefixWord ++ tailWord_564248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564248).length < 2 ^ (prefixWord ++ tailWord_564248).sum := by decide
  have hdescent : baseEnd_564248 < baseStart_564248 := by decide
  rcases family_descends (prefixWord ++ tailWord_564248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564250 : List Nat := [3, 1, 1, 3, 1, 2, 2, 4, 2, 3]
def baseStart_564250 : Nat := 118140960795 + 564250 * 2 ^ 59
def prefixEnd_564250 : Nat := 4983230072969 + 3 ^ 40 * 564250 * 2
def baseEnd_564250 : Nat := 193154306199681735320045

theorem tailTrace_564250 : CollatzResearch.WordTrace tailWord_564250 prefixEnd_564250 193154306199681735320045 := by
  unfold tailWord_564250
  simp only [CollatzResearch.WordTrace]
  refine ⟨5144972051456522768250551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13719925470550727382001469 5144972051456522768250551)
  ·
    refine ⟨7717458077184784152375827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5144972051456522768250551 7717458077184784152375827)
    ·
      refine ⟨11576187115777176228563741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7717458077184784152375827 11576187115777176228563741)
      ·
        refine ⟨4341070168416441085711403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11576187115777176228563741 4341070168416441085711403)
        ·
          refine ⟨6511605252624661628567105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4341070168416441085711403 6511605252624661628567105)
          ·
            refine ⟨4883703939468496221425329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6511605252624661628567105 4883703939468496221425329)
            ·
              refine ⟨3662777954601372166068997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4883703939468496221425329 3662777954601372166068997)
              ·
                refine ⟨686770866487757281137937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3662777954601372166068997 686770866487757281137937)
                ·
                  refine ⟨515078149865817960853453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 686770866487757281137937 515078149865817960853453)
                  ·
                    refine ⟨193154306199681735320045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 515078149865817960853453 193154306199681735320045)
                    ·
                      rfl

theorem cell22_564250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 4, 2, 3].length) (baseStart_564250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_564250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_564250 prefixEnd_564250 := by exact prefixLift 564250
  have htrace : WordTrace (prefixWord ++ tailWord_564250) baseStart_564250 baseEnd_564250 := by
    simpa [prefixWord, tailWord_564250, baseEnd_564250] using wordTrace_append hprefix tailTrace_564250
  have hstable : (prefixWord ++ tailWord_564250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564250).length < 2 ^ (prefixWord ++ tailWord_564250).sum := by decide
  have hdescent : baseEnd_564250 < baseStart_564250 := by decide
  rcases family_descends (prefixWord ++ tailWord_564250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564252 : List Nat := [2, 2, 3, 1, 5, 1, 1, 1, 6]
def baseStart_564252 : Nat := 118140960795 + 564252 * 2 ^ 59
def prefixEnd_564252 : Nat := 4983230072969 + 3 ^ 40 * 564252 * 2
def baseEnd_564252 : Nat := 64384996946851465590013

theorem tailTrace_564252 : CollatzResearch.WordTrace tailWord_564252 prefixEnd_564252 64384996946851465590013 := by
  unfold tailWord_564252
  simp only [CollatzResearch.WordTrace]
  refine ⟨10289980575909422707287505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13719974101212563609716673 10289980575909422707287505)
  ·
    refine ⟨7717485431932067030465629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10289980575909422707287505 7717485431932067030465629)
    ·
      refine ⟨2894057036974525136424611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7717485431932067030465629 2894057036974525136424611)
      ·
        refine ⟨4341085555461787704636917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2894057036974525136424611 4341085555461787704636917)
        ·
          refine ⟨406976770824542597309711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4341085555461787704636917 406976770824542597309711)
          ·
            refine ⟨610465156236813895964567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 406976770824542597309711 610465156236813895964567)
            ·
              refine ⟨915697734355220843946851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 610465156236813895964567 915697734355220843946851)
              ·
                refine ⟨1373546601532831265920277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 915697734355220843946851 1373546601532831265920277)
                ·
                  refine ⟨64384996946851465590013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1373546601532831265920277 64384996946851465590013)
                  ·
                    rfl

theorem cell22_564252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 6].length) (baseStart_564252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_564252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_564252 prefixEnd_564252 := by exact prefixLift 564252
  have htrace : WordTrace (prefixWord ++ tailWord_564252) baseStart_564252 baseEnd_564252 := by
    simpa [prefixWord, tailWord_564252, baseEnd_564252] using wordTrace_append hprefix tailTrace_564252
  have hstable : (prefixWord ++ tailWord_564252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564252).length < 2 ^ (prefixWord ++ tailWord_564252).sum := by decide
  have hdescent : baseEnd_564252 < baseStart_564252 := by decide
  rcases family_descends (prefixWord ++ tailWord_564252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564308 : List Nat := [2, 4, 1, 1, 1, 1, 2, 3, 7]
def baseStart_564308 : Nat := 118140960795 + 564308 * 2 ^ 59
def prefixEnd_564308 : Nat := 4983230072969 + 3 ^ 40 * 564308 * 2
def baseEnd_564308 : Nat := 64391386928329639123289

theorem tailTrace_564308 : CollatzResearch.WordTrace tailWord_564308 prefixEnd_564308 64391386928329639123289 := by
  unfold tailWord_564308
  simp only [CollatzResearch.WordTrace]
  refine ⟨10291001819807983489306789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13721335759743977985742385 10291001819807983489306789)
  ·
    refine ⟨1929562841213996904245023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10291001819807983489306789 1929562841213996904245023)
    ·
      refine ⟨2894344261820995356367535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1929562841213996904245023 2894344261820995356367535)
      ·
        refine ⟨4341516392731493034551303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2894344261820995356367535 4341516392731493034551303)
        ·
          refine ⟨6512274589097239551826955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4341516392731493034551303 6512274589097239551826955)
          ·
            refine ⟨9768411883645859327740433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6512274589097239551826955 9768411883645859327740433)
            ·
              refine ⟨7326308912734394495805325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9768411883645859327740433 7326308912734394495805325)
              ·
                refine ⟨2747365842275397935926997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7326308912734394495805325 2747365842275397935926997)
                ·
                  refine ⟨64391386928329639123289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2747365842275397935926997 64391386928329639123289)
                  ·
                    rfl

theorem cell22_564308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_564308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_564308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_564308 prefixEnd_564308 := by exact prefixLift 564308
  have htrace : WordTrace (prefixWord ++ tailWord_564308) baseStart_564308 baseEnd_564308 := by
    simpa [prefixWord, tailWord_564308, baseEnd_564308] using wordTrace_append hprefix tailTrace_564308
  have hstable : (prefixWord ++ tailWord_564308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564308).length < 2 ^ (prefixWord ++ tailWord_564308).sum := by decide
  have hdescent : baseEnd_564308 < baseStart_564308 := by decide
  rcases family_descends (prefixWord ++ tailWord_564308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564312 : List Nat := [2, 1, 2, 2, 1, 3, 3, 4, 1, 3]
def baseStart_564312 : Nat := 118140960795 + 564312 * 2 ^ 59
def prefixEnd_564312 : Nat := 4983230072969 + 3 ^ 40 * 564312 * 2
def baseEnd_564312 : Nat := 193175530066734240269855

theorem tailTrace_564312 : CollatzResearch.WordTrace tailWord_564312 prefixEnd_564312 193175530066734240269855 := by
  unfold tailWord_564312
  simp only [CollatzResearch.WordTrace]
  refine ⟨10291074765800737830879595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13721433021067650441172793 10291074765800737830879595)
  ·
    refine ⟨15436612148701106746319393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10291074765800737830879595 15436612148701106746319393)
    ·
      refine ⟨11577459111525830059739545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15436612148701106746319393 11577459111525830059739545)
      ·
        refine ⟨8683094333644372544804659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11577459111525830059739545 8683094333644372544804659)
        ·
          refine ⟨13024641500466558817206989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8683094333644372544804659 13024641500466558817206989)
          ·
            refine ⟨4884240562674959556452621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13024641500466558817206989 4884240562674959556452621)
            ·
              refine ⟨1831590211003109833669733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4884240562674959556452621 1831590211003109833669733)
              ·
                refine ⟨343423164563083093813075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1831590211003109833669733 343423164563083093813075)
                ·
                  refine ⟨515134746844624640719613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 343423164563083093813075 515134746844624640719613)
                  ·
                    refine ⟨193175530066734240269855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 515134746844624640719613 193175530066734240269855)
                    ·
                      rfl

theorem cell22_564312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 4, 1, 3].length) (baseStart_564312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_564312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_564312 prefixEnd_564312 := by exact prefixLift 564312
  have htrace : WordTrace (prefixWord ++ tailWord_564312) baseStart_564312 baseEnd_564312 := by
    simpa [prefixWord, tailWord_564312, baseEnd_564312] using wordTrace_append hprefix tailTrace_564312
  have hstable : (prefixWord ++ tailWord_564312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564312).length < 2 ^ (prefixWord ++ tailWord_564312).sum := by decide
  have hdescent : baseEnd_564312 < baseStart_564312 := by decide
  rcases family_descends (prefixWord ++ tailWord_564312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564355 : List Nat := [1, 1, 1, 3, 3, 2, 3, 3, 1, 4]
def baseStart_564355 : Nat := 118140960795 + 564355 * 2 ^ 59
def prefixEnd_564355 : Nat := 4983230072969 + 3 ^ 40 * 564355 * 2
def baseEnd_564355 : Nat := 193190249845496461444723

theorem tailTrace_564355 : CollatzResearch.WordTrace tailWord_564355 prefixEnd_564355 193190249845496461444723 := by
  unfold tailWord_564355
  simp only [CollatzResearch.WordTrace]
  refine ⟨20583717870445694005574519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13722478580297129337049679 20583717870445694005574519)
  ·
    refine ⟨30875576805668541008361779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20583717870445694005574519 30875576805668541008361779)
    ·
      refine ⟨46313365208502811512542669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30875576805668541008361779 46313365208502811512542669)
      ·
        refine ⟨17367511953188554317203501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46313365208502811512542669 17367511953188554317203501)
        ·
          refine ⟨6512816982445707868951313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17367511953188554317203501 6512816982445707868951313)
          ·
            refine ⟨4884612736834280901713485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6512816982445707868951313 4884612736834280901713485)
            ·
              refine ⟨1831729776312855338142557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4884612736834280901713485 1831729776312855338142557)
              ·
                refine ⟨686898666117320751803459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1831729776312855338142557 686898666117320751803459)
                ·
                  refine ⟨1030347999175981127705189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 686898666117320751803459 1030347999175981127705189)
                  ·
                    refine ⟨193190249845496461444723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1030347999175981127705189 193190249845496461444723)
                    ·
                      rfl

theorem cell22_564355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 3, 1, 4].length) (baseStart_564355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_564355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_564355 prefixEnd_564355 := by exact prefixLift 564355
  have htrace : WordTrace (prefixWord ++ tailWord_564355) baseStart_564355 baseEnd_564355 := by
    simpa [prefixWord, tailWord_564355, baseEnd_564355] using wordTrace_append hprefix tailTrace_564355
  have hstable : (prefixWord ++ tailWord_564355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564355).length < 2 ^ (prefixWord ++ tailWord_564355).sum := by decide
  have hdescent : baseEnd_564355 < baseStart_564355 := by decide
  rcases family_descends (prefixWord ++ tailWord_564355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564370 : List Nat := [3, 2, 3, 1, 1, 2, 1, 3, 6]
def baseStart_564370 : Nat := 118140960795 + 564370 * 2 ^ 59
def prefixEnd_564370 : Nat := 4983230072969 + 3 ^ 40 * 564370 * 2
def baseEnd_564370 : Nat := 64398461550680474106559

theorem tailTrace_564370 : CollatzResearch.WordTrace tailWord_564370 prefixEnd_564370 64398461550680474106559 := by
  unfold tailWord_564370
  simp only [CollatzResearch.WordTrace]
  refine ⟨5146066241347837891842641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13722843310260901044913709 5146066241347837891842641)
  ·
    refine ⟨3859549681010878418881981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5146066241347837891842641 3859549681010878418881981)
    ·
      refine ⟨1447331130379079407080743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3859549681010878418881981 1447331130379079407080743)
      ·
        refine ⟨2170996695568619110621115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1447331130379079407080743 2170996695568619110621115)
        ·
          refine ⟨3256495043352928665931673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2170996695568619110621115 3256495043352928665931673)
          ·
            refine ⟨2442371282514696499448755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3256495043352928665931673 2442371282514696499448755)
            ·
              refine ⟨3663556923772044749173133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2442371282514696499448755 3663556923772044749173133)
              ·
                refine ⟨1373833846414516780939925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3663556923772044749173133 1373833846414516780939925)
                ·
                  refine ⟨64398461550680474106559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1373833846414516780939925 64398461550680474106559)
                  ·
                    rfl

theorem cell22_564370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_564370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_564370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_564370 prefixEnd_564370 := by exact prefixLift 564370
  have htrace : WordTrace (prefixWord ++ tailWord_564370) baseStart_564370 baseEnd_564370 := by
    simpa [prefixWord, tailWord_564370, baseEnd_564370] using wordTrace_append hprefix tailTrace_564370
  have hstable : (prefixWord ++ tailWord_564370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564370).length < 2 ^ (prefixWord ++ tailWord_564370).sum := by decide
  have hdescent : baseEnd_564370 < baseStart_564370 := by decide
  rcases family_descends (prefixWord ++ tailWord_564370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564417 : List Nat := [1, 2, 6, 1, 1, 1, 1, 1, 4, 4]
def baseStart_564417 : Nat := 118140960795 + 564417 * 2 ^ 59
def prefixEnd_564417 : Nat := 4983230072969 + 3 ^ 40 * 564417 * 2
def baseEnd_564417 : Nat := 193211473712548966394533

theorem tailTrace_564417 : CollatzResearch.WordTrace tailWord_564417 prefixEnd_564417 193211473712548966394533 := by
  unfold tailWord_564417
  simp only [CollatzResearch.WordTrace]
  refine ⟨20585979196221078594331505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13723986130814052396221003 20585979196221078594331505)
  ·
    refine ⟨15439484397165808945748629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20585979196221078594331505 15439484397165808945748629)
    ·
      refine ⟨723725831117147294331967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15439484397165808945748629 723725831117147294331967)
      ·
        refine ⟨1085588746675720941497951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 723725831117147294331967 1085588746675720941497951)
        ·
          refine ⟨1628383120013581412246927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1085588746675720941497951 1628383120013581412246927)
          ·
            refine ⟨2442574680020372118370391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1628383120013581412246927 2442574680020372118370391)
            ·
              refine ⟨3663862020030558177555587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2442574680020372118370391 3663862020030558177555587)
              ·
                refine ⟨5495793030045837266333381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3663862020030558177555587 5495793030045837266333381)
                ·
                  refine ⟨1030461193133594487437509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5495793030045837266333381 1030461193133594487437509)
                  ·
                    refine ⟨193211473712548966394533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1030461193133594487437509 193211473712548966394533)
                    ·
                      rfl

theorem cell22_564417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_564417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_564417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_564417 prefixEnd_564417 := by exact prefixLift 564417
  have htrace : WordTrace (prefixWord ++ tailWord_564417) baseStart_564417 baseEnd_564417 := by
    simpa [prefixWord, tailWord_564417, baseEnd_564417] using wordTrace_append hprefix tailTrace_564417
  have hstable : (prefixWord ++ tailWord_564417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564417).length < 2 ^ (prefixWord ++ tailWord_564417).sum := by decide
  have hdescent : baseEnd_564417 < baseStart_564417 := by decide
  rcases family_descends (prefixWord ++ tailWord_564417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564436 : List Nat := [2, 4, 1, 4, 1, 1, 1, 3, 2, 3]
def baseStart_564436 : Nat := 118140960795 + 564436 * 2 ^ 59
def prefixEnd_564436 : Nat := 4983230072969 + 3 ^ 40 * 564436 * 2
def baseEnd_564436 : Nat := 193217977800839250169475

theorem tailTrace_564436 : CollatzResearch.WordTrace tailWord_564436 prefixEnd_564436 193217977800839250169475 := by
  unfold tailWord_564436
  simp only [CollatzResearch.WordTrace]
  refine ⟨10293336091576122419636581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13724448122101496559515441 10293336091576122419636581)
  ·
    refine ⟨1930000517170522953681859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10293336091576122419636581 1930000517170522953681859)
    ·
      refine ⟨2895000775755784430522789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1930000517170522953681859 2895000775755784430522789)
      ·
        refine ⟨542812645454209580723023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2895000775755784430522789 542812645454209580723023)
        ·
          refine ⟨814218968181314371084535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 542812645454209580723023 814218968181314371084535)
          ·
            refine ⟨1221328452271971556626803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 814218968181314371084535 1221328452271971556626803)
            ·
              refine ⟨1831992678407957334940205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1221328452271971556626803 1831992678407957334940205)
              ·
                refine ⟨686997254402984000602577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1831992678407957334940205 686997254402984000602577)
                ·
                  refine ⟨515247940802238000451933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 686997254402984000602577 515247940802238000451933)
                  ·
                    refine ⟨193217977800839250169475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 515247940802238000451933 193217977800839250169475)
                    ·
                      rfl

theorem cell22_564436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_564436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_564436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_564436 prefixEnd_564436 := by exact prefixLift 564436
  have htrace : WordTrace (prefixWord ++ tailWord_564436) baseStart_564436 baseEnd_564436 := by
    simpa [prefixWord, tailWord_564436, baseEnd_564436] using wordTrace_append hprefix tailTrace_564436
  have hstable : (prefixWord ++ tailWord_564436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564436).length < 2 ^ (prefixWord ++ tailWord_564436).sum := by decide
  have hdescent : baseEnd_564436 < baseStart_564436 := by decide
  rcases family_descends (prefixWord ++ tailWord_564436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564481 : List Nat := [1, 2, 4, 1, 1, 3, 4, 2, 1, 3]
def baseStart_564481 : Nat := 118140960795 + 564481 * 2 ^ 59
def prefixEnd_564481 : Nat := 4983230072969 + 3 ^ 40 * 564481 * 2
def baseEnd_564481 : Nat := 193233382220474132794337

theorem tailTrace_564481 : CollatzResearch.WordTrace tailWord_564481 prefixEnd_564481 193233382220474132794337 := by
  unfold tailWord_564481
  simp only [CollatzResearch.WordTrace]
  refine ⟨20588313467989217524661297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13725542311992811683107531 20588313467989217524661297)
  ·
    refine ⟨15441235100991913143495973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20588313467989217524661297 15441235100991913143495973)
    ·
      refine ⟨2895231581435983714405495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15441235100991913143495973 2895231581435983714405495)
      ·
        refine ⟨4342847372153975571608243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2895231581435983714405495 4342847372153975571608243)
        ·
          refine ⟨6514271058230963357412365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4342847372153975571608243 6514271058230963357412365)
          ·
            refine ⟨2442851646836611259029637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6514271058230963357412365 2442851646836611259029637)
            ·
              refine ⟨458034683781864611068057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2442851646836611259029637 458034683781864611068057)
              ·
                refine ⟨343526012836398458301043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 458034683781864611068057 343526012836398458301043)
                ·
                  refine ⟨515289019254597687451565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 343526012836398458301043 515289019254597687451565)
                  ·
                    refine ⟨193233382220474132794337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 515289019254597687451565 193233382220474132794337)
                    ·
                      rfl

theorem cell22_564481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_564481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_564481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_564481 prefixEnd_564481 := by exact prefixLift 564481
  have htrace : WordTrace (prefixWord ++ tailWord_564481) baseStart_564481 baseEnd_564481 := by
    simpa [prefixWord, tailWord_564481, baseEnd_564481] using wordTrace_append hprefix tailTrace_564481
  have hstable : (prefixWord ++ tailWord_564481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564481).length < 2 ^ (prefixWord ++ tailWord_564481).sum := by decide
  have hdescent : baseEnd_564481 < baseStart_564481 := by decide
  rcases family_descends (prefixWord ++ tailWord_564481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564567 : List Nat := [1, 1, 3, 2, 3, 2, 4, 6]
def baseStart_564567 : Nat := 118140960795 + 564567 * 2 ^ 59
def prefixEnd_564567 : Nat := 4983230072969 + 3 ^ 40 * 564567 * 2
def baseEnd_564567 : Nat := 21473646864222063904897

theorem tailTrace_564567 : CollatzResearch.WordTrace tailWord_564567 prefixEnd_564567 21473646864222063904897 := by
  unfold tailWord_564567
  simp only [CollatzResearch.WordTrace]
  refine ⟨20591450145677654212291955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13727633430451769474861303 20591450145677654212291955)
  ·
    refine ⟨30887175218516481318437933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20591450145677654212291955 30887175218516481318437933)
    ·
      refine ⟨11582690706943680494414225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30887175218516481318437933 11582690706943680494414225)
      ·
        refine ⟨8687018030207760370810669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11582690706943680494414225 8687018030207760370810669)
        ·
          refine ⟨3257631761327910139054001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8687018030207760370810669 3257631761327910139054001)
          ·
            refine ⟨2443223820995932604290501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3257631761327910139054001 2443223820995932604290501)
            ·
              refine ⟨458104466436737363304469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2443223820995932604290501 458104466436737363304469)
              ·
                refine ⟨21473646864222063904897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 458104466436737363304469 21473646864222063904897)
                ·
                  rfl

theorem cell22_564567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 6].length) (baseStart_564567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_564567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_564567 prefixEnd_564567 := by exact prefixLift 564567
  have htrace : WordTrace (prefixWord ++ tailWord_564567) baseStart_564567 baseEnd_564567 := by
    simpa [prefixWord, tailWord_564567, baseEnd_564567] using wordTrace_append hprefix tailTrace_564567
  have hstable : (prefixWord ++ tailWord_564567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564567).length < 2 ^ (prefixWord ++ tailWord_564567).sum := by decide
  have hdescent : baseEnd_564567 < baseStart_564567 := by decide
  rcases family_descends (prefixWord ++ tailWord_564567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564584 : List Nat := [2, 1, 4, 2, 4, 1, 8]
def baseStart_564584 : Nat := 118140960795 + 564584 * 2 ^ 59
def prefixEnd_564584 : Nat := 4983230072969 + 3 ^ 40 * 564584 * 2
def baseEnd_564584 : Nat := 7158097823163562869223

theorem tailTrace_564584 : CollatzResearch.WordTrace tailWord_564584 prefixEnd_564584 7158097823163562869223 := by
  unfold tailWord_564584
  simp only [CollatzResearch.WordTrace]
  refine ⟨10296035093308033057830403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13728046791077377410440537 10296035093308033057830403)
  ·
    refine ⟨15444052639962049586745605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10296035093308033057830403 15444052639962049586745605)
    ·
      refine ⟨2895759869992884297514801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15444052639962049586745605 2895759869992884297514801)
      ·
        refine ⟨2171819902494663223136101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2895759869992884297514801 2171819902494663223136101)
        ·
          refine ⟨407216231717749354338019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2171819902494663223136101 407216231717749354338019)
          ·
            refine ⟨610824347576624031507029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407216231717749354338019 610824347576624031507029)
            ·
              refine ⟨7158097823163562869223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 610824347576624031507029 7158097823163562869223)
              ·
                rfl

theorem cell22_564584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 8].length) (baseStart_564584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_564584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_564584 prefixEnd_564584 := by exact prefixLift 564584
  have htrace : WordTrace (prefixWord ++ tailWord_564584) baseStart_564584 baseEnd_564584 := by
    simpa [prefixWord, tailWord_564584, baseEnd_564584] using wordTrace_append hprefix tailTrace_564584
  have hstable : (prefixWord ++ tailWord_564584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564584).length < 2 ^ (prefixWord ++ tailWord_564584).sum := by decide
  have hdescent : baseEnd_564584 < baseStart_564584 := by decide
  rcases family_descends (prefixWord ++ tailWord_564584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564625 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 2, 8]
def baseStart_564625 : Nat := 118140960795 + 564625 * 2 ^ 59
def prefixEnd_564625 : Nat := 4983230072969 + 3 ^ 40 * 564625 * 2
def baseEnd_564625 : Nat := 193282676363305757193895

theorem tailTrace_564625 : CollatzResearch.WordTrace tailWord_564625 prefixEnd_564625 193282676363305757193895 := by
  unfold tailWord_564625
  simp only [CollatzResearch.WordTrace]
  refine ⟨20593565579467530117903329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13729043719645020078602219 20593565579467530117903329)
  ·
    refine ⟨15445174184600647588427497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20593565579467530117903329 15445174184600647588427497)
    ·
      refine ⟨11583880638450485691320623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15445174184600647588427497 11583880638450485691320623)
      ·
        refine ⟨17375820957675728536980935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11583880638450485691320623 17375820957675728536980935)
        ·
          refine ⟨26063731436513592805471403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17375820957675728536980935 26063731436513592805471403)
          ·
            refine ⟨39095597154770389208207105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26063731436513592805471403 39095597154770389208207105)
            ·
              refine ⟨29321697866077791906155329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39095597154770389208207105 29321697866077791906155329)
              ·
                refine ⟨21991273399558343929616497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29321697866077791906155329 21991273399558343929616497)
                ·
                  refine ⟨16493455049668757947212373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21991273399558343929616497 16493455049668757947212373)
                  ·
                    refine ⟨193282676363305757193895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 16493455049668757947212373 193282676363305757193895)
                    ·
                      rfl

theorem cell22_564625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_564625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_564625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_564625 prefixEnd_564625 := by exact prefixLift 564625
  have htrace : WordTrace (prefixWord ++ tailWord_564625) baseStart_564625 baseEnd_564625 := by
    simpa [prefixWord, tailWord_564625, baseEnd_564625] using wordTrace_append hprefix tailTrace_564625
  have hstable : (prefixWord ++ tailWord_564625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564625).length < 2 ^ (prefixWord ++ tailWord_564625).sum := by decide
  have hdescent : baseEnd_564625 < baseStart_564625 := by decide
  rcases family_descends (prefixWord ++ tailWord_564625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564657 : List Nat := [1, 2, 2, 4, 1, 1, 2, 3, 6]
def baseStart_564657 : Nat := 118140960795 + 564657 * 2 ^ 59
def prefixEnd_564657 : Nat := 4983230072969 + 3 ^ 40 * 564657 * 2
def baseEnd_564657 : Nat := 64431210205756113464599

theorem tailTrace_564657 : CollatzResearch.WordTrace tailWord_564657 prefixEnd_564657 64431210205756113464599 := by
  unfold tailWord_564657
  simp only [CollatzResearch.WordTrace]
  refine ⟨20594732715351599583068225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13729821810234399722045483 20594732715351599583068225)
  ·
    refine ⟨15446049536513699687301169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20594732715351599583068225 15446049536513699687301169)
    ·
      refine ⟨11584537152385274765475877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15446049536513699687301169 11584537152385274765475877)
      ·
        refine ⟨2172100716072239018526727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11584537152385274765475877 2172100716072239018526727)
        ·
          refine ⟨3258151074108358527790091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2172100716072239018526727 3258151074108358527790091)
          ·
            refine ⟨4887226611162537791685137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3258151074108358527790091 4887226611162537791685137)
            ·
              refine ⟨3665419958371903343763853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4887226611162537791685137 3665419958371903343763853)
              ·
                refine ⟨1374532484389463753911445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3665419958371903343763853 1374532484389463753911445)
                ·
                  refine ⟨64431210205756113464599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1374532484389463753911445 64431210205756113464599)
                  ·
                    rfl

theorem cell22_564657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 6].length) (baseStart_564657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_564657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_564657 prefixEnd_564657 := by exact prefixLift 564657
  have htrace : WordTrace (prefixWord ++ tailWord_564657) baseStart_564657 baseEnd_564657 := by
    simpa [prefixWord, tailWord_564657, baseEnd_564657] using wordTrace_append hprefix tailTrace_564657
  have hstable : (prefixWord ++ tailWord_564657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564657).length < 2 ^ (prefixWord ++ tailWord_564657).sum := by decide
  have hdescent : baseEnd_564657 < baseStart_564657 := by decide
  rcases family_descends (prefixWord ++ tailWord_564657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564672 : List Nat := [2, 1, 1, 2, 3, 1, 3, 3, 1, 5]
def baseStart_564672 : Nat := 118140960795 + 564672 * 2 ^ 59
def prefixEnd_564672 : Nat := 4983230072969 + 3 ^ 40 * 564672 * 2
def baseEnd_564672 : Nat := 193298765423813301268751

theorem tailTrace_564672 : CollatzResearch.WordTrace tailWord_564672 prefixEnd_564672 193298765423813301268751 := by
  unfold tailWord_564672
  simp only [CollatzResearch.WordTrace]
  refine ⟨10297639905148628572432135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13730186540198171429909513 10297639905148628572432135)
  ·
    refine ⟨15446459857722942858648203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10297639905148628572432135 15446459857722942858648203)
    ·
      refine ⟨23169689786584414287972305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15446459857722942858648203 23169689786584414287972305)
      ·
        refine ⟨17377267339938310715979229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23169689786584414287972305 17377267339938310715979229)
        ·
          refine ⟨6516475252476866518492211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17377267339938310715979229 6516475252476866518492211)
          ·
            refine ⟨9774712878715299777738317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6516475252476866518492211 9774712878715299777738317)
            ·
              refine ⟨3665517329518237416651869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9774712878715299777738317 3665517329518237416651869)
              ·
                refine ⟨1374568998569339031244451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3665517329518237416651869 1374568998569339031244451)
                ·
                  refine ⟨2061853497854008546866677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1374568998569339031244451 2061853497854008546866677)
                  ·
                    refine ⟨193298765423813301268751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2061853497854008546866677 193298765423813301268751)
                    ·
                      rfl

theorem cell22_564672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 1, 5].length) (baseStart_564672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_564672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_564672 prefixEnd_564672 := by exact prefixLift 564672
  have htrace : WordTrace (prefixWord ++ tailWord_564672) baseStart_564672 baseEnd_564672 := by
    simpa [prefixWord, tailWord_564672, baseEnd_564672] using wordTrace_append hprefix tailTrace_564672
  have hstable : (prefixWord ++ tailWord_564672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564672).length < 2 ^ (prefixWord ++ tailWord_564672).sum := by decide
  have hdescent : baseEnd_564672 < baseStart_564672 := by decide
  rcases family_descends (prefixWord ++ tailWord_564672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564732 : List Nat := [2, 2, 2, 1, 2, 1, 2, 2, 2, 6]
def baseStart_564732 : Nat := 118140960795 + 564732 * 2 ^ 59
def prefixEnd_564732 : Nat := 4983230072969 + 3 ^ 40 * 564732 * 2
def baseEnd_564732 : Nat := 193319304649993144768567

theorem tailTrace_564732 : CollatzResearch.WordTrace tailWord_564732 prefixEnd_564732 193319304649993144768567 := by
  unfold tailWord_564732
  simp only [CollatzResearch.WordTrace]
  refine ⟨10298734095039943696024225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13731645460053258261365633 10298734095039943696024225)
  ·
    refine ⟨7724050571279957772018169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10298734095039943696024225 7724050571279957772018169)
    ·
      refine ⟨5793037928459968329013627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7724050571279957772018169 5793037928459968329013627)
      ·
        refine ⟨8689556892689952493520441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5793037928459968329013627 8689556892689952493520441)
        ·
          refine ⟨6517167669517464370140331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8689556892689952493520441 6517167669517464370140331)
          ·
            refine ⟨9775751504276196555210497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6517167669517464370140331 9775751504276196555210497)
            ·
              refine ⟨7331813628207147416407873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9775751504276196555210497 7331813628207147416407873)
              ·
                refine ⟨5498860221155360562305905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7331813628207147416407873 5498860221155360562305905)
                ·
                  refine ⟨4124145165866520421729429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5498860221155360562305905 4124145165866520421729429)
                  ·
                    refine ⟨193319304649993144768567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4124145165866520421729429 193319304649993144768567)
                    ·
                      rfl

theorem cell22_564732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_564732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_564732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_564732 prefixEnd_564732 := by exact prefixLift 564732
  have htrace : WordTrace (prefixWord ++ tailWord_564732) baseStart_564732 baseEnd_564732 := by
    simpa [prefixWord, tailWord_564732, baseEnd_564732] using wordTrace_append hprefix tailTrace_564732
  have hstable : (prefixWord ++ tailWord_564732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564732).length < 2 ^ (prefixWord ++ tailWord_564732).sum := by decide
  have hdescent : baseEnd_564732 < baseStart_564732 := by decide
  rcases family_descends (prefixWord ++ tailWord_564732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564764 : List Nat := [2, 2, 3, 1, 2, 1, 2, 4, 5]
def baseStart_564764 : Nat := 118140960795 + 564764 * 2 ^ 59
def prefixEnd_564764 : Nat := 4983230072969 + 3 ^ 40 * 564764 * 2
def baseEnd_564764 : Nat := 64443419634651909322823

theorem tailTrace_564764 : CollatzResearch.WordTrace tailWord_564764 prefixEnd_564764 64443419634651909322823 := by
  unfold tailWord_564764
  simp only [CollatzResearch.WordTrace]
  refine ⟨10299317662981978428606673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13732423550642637904808897 10299317662981978428606673)
  ·
    refine ⟨7724488247236483821455005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10299317662981978428606673 7724488247236483821455005)
    ·
      refine ⟨2896683092713681433045627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7724488247236483821455005 2896683092713681433045627)
      ·
        refine ⟨4345024639070522149568441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2896683092713681433045627 4345024639070522149568441)
        ·
          refine ⟨3258768479302891612176331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4345024639070522149568441 3258768479302891612176331)
          ·
            refine ⟨4888152718954337418264497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3258768479302891612176331 4888152718954337418264497)
            ·
              refine ⟨3666114539215753063698373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4888152718954337418264497 3666114539215753063698373)
              ·
                refine ⟨687396476102953699443445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3666114539215753063698373 687396476102953699443445)
                ·
                  refine ⟨64443419634651909322823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 687396476102953699443445 64443419634651909322823)
                  ·
                    rfl

theorem cell22_564764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 4, 5].length) (baseStart_564764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_564764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_564764 prefixEnd_564764 := by exact prefixLift 564764
  have htrace : WordTrace (prefixWord ++ tailWord_564764) baseStart_564764 baseEnd_564764 := by
    simpa [prefixWord, tailWord_564764, baseEnd_564764] using wordTrace_append hprefix tailTrace_564764
  have hstable : (prefixWord ++ tailWord_564764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564764).length < 2 ^ (prefixWord ++ tailWord_564764).sum := by decide
  have hdescent : baseEnd_564764 < baseStart_564764 := by decide
  rcases family_descends (prefixWord ++ tailWord_564764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564768 : List Nat := [2, 1, 1, 6, 1, 3, 1, 1, 3, 3]
def baseStart_564768 : Nat := 118140960795 + 564768 * 2 ^ 59
def prefixEnd_564768 : Nat := 4983230072969 + 3 ^ 40 * 564768 * 2
def baseEnd_564768 : Nat := 193331628185701050868457

theorem tailTrace_564768 : CollatzResearch.WordTrace tailWord_564768 prefixEnd_564768 193331628185701050868457 := by
  unfold tailWord_564768
  simp only [CollatzResearch.WordTrace]
  refine ⟨10299390608974732770179479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13732520811966310360239305 10299390608974732770179479)
  ·
    refine ⟨15449085913462099155269219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10299390608974732770179479 15449085913462099155269219)
    ·
      refine ⟨23173628870193148732903829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15449085913462099155269219 23173628870193148732903829)
      ·
        refine ⟨1086263853290303846854867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 23173628870193148732903829 1086263853290303846854867)
        ·
          refine ⟨1629395779935455770282301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1086263853290303846854867 1629395779935455770282301)
          ·
            refine ⟨611023417475795913855863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1629395779935455770282301 611023417475795913855863)
            ·
              refine ⟨916535126213693870783795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 611023417475795913855863 916535126213693870783795)
              ·
                refine ⟨1374802689320540806175693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 916535126213693870783795 1374802689320540806175693)
                ·
                  refine ⟨515551008495202802315885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1374802689320540806175693 515551008495202802315885)
                  ·
                    refine ⟨193331628185701050868457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 515551008495202802315885 193331628185701050868457)
                    ·
                      rfl

theorem cell22_564768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 3, 3].length) (baseStart_564768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_564768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_564768 prefixEnd_564768 := by exact prefixLift 564768
  have htrace : WordTrace (prefixWord ++ tailWord_564768) baseStart_564768 baseEnd_564768 := by
    simpa [prefixWord, tailWord_564768, baseEnd_564768] using wordTrace_append hprefix tailTrace_564768
  have hstable : (prefixWord ++ tailWord_564768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564768).length < 2 ^ (prefixWord ++ tailWord_564768).sum := by decide
  have hdescent : baseEnd_564768 < baseStart_564768 := by decide
  rcases family_descends (prefixWord ++ tailWord_564768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564794 : List Nat := [3, 1, 1, 1, 3, 2, 3, 1, 3, 4]
def baseStart_564794 : Nat := 118140960795 + 564794 * 2 ^ 59
def prefixEnd_564794 : Nat := 4983230072969 + 3 ^ 40 * 564794 * 2
def baseEnd_564794 : Nat := 193340528517045649718377

theorem tailTrace_564794 : CollatzResearch.WordTrace tailWord_564794 prefixEnd_564794 193340528517045649718377 := by
  unfold tailWord_564794
  simp only [CollatzResearch.WordTrace]
  refine ⟨5149932378963817995201359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13733153010570181320536957 5149932378963817995201359)
  ·
    refine ⟨7724898568445726992802039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5149932378963817995201359 7724898568445726992802039)
    ·
      refine ⟨11587347852668590489203059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7724898568445726992802039 11587347852668590489203059)
      ·
        refine ⟨17381021779002885733804589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11587347852668590489203059 17381021779002885733804589)
        ·
          refine ⟨6517883167126082150176721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17381021779002885733804589 6517883167126082150176721)
          ·
            refine ⟨4888412375344561612632541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6517883167126082150176721 4888412375344561612632541)
            ·
              refine ⟨1833154640754210604737203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4888412375344561612632541 1833154640754210604737203)
              ·
                refine ⟨2749731961131315907105805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1833154640754210604737203 2749731961131315907105805)
                ·
                  refine ⟨1031149485424243465164677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2749731961131315907105805 1031149485424243465164677)
                  ·
                    refine ⟨193340528517045649718377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1031149485424243465164677 193340528517045649718377)
                    ·
                      rfl

theorem cell22_564794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 3, 4].length) (baseStart_564794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_564794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_564794 prefixEnd_564794 := by exact prefixLift 564794
  have htrace : WordTrace (prefixWord ++ tailWord_564794) baseStart_564794 baseEnd_564794 := by
    simpa [prefixWord, tailWord_564794, baseEnd_564794] using wordTrace_append hprefix tailTrace_564794
  have hstable : (prefixWord ++ tailWord_564794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564794).length < 2 ^ (prefixWord ++ tailWord_564794).sum := by decide
  have hdescent : baseEnd_564794 < baseStart_564794 := by decide
  rcases family_descends (prefixWord ++ tailWord_564794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564839 : List Nat := [1, 1, 5, 1, 1, 1, 2, 2, 4, 4]
def baseStart_564839 : Nat := 118140960795 + 564839 * 2 ^ 59
def prefixEnd_564839 : Nat := 4983230072969 + 3 ^ 40 * 564839 * 2
def baseEnd_564839 : Nat := 193355932936680532343239

theorem tailTrace_564839 : CollatzResearch.WordTrace tailWord_564839 prefixEnd_564839 193355932936680532343239 := by
  unfold tailWord_564839
  simp only [CollatzResearch.WordTrace]
  refine ⟨20601370800692244666193571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13734247200461496444129047 20601370800692244666193571)
  ·
    refine ⟨30902056201038366999290357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20601370800692244666193571 30902056201038366999290357)
    ·
      refine ⟨2897067768847346906183471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30902056201038366999290357 2897067768847346906183471)
      ·
        refine ⟨4345601653271020359275207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2897067768847346906183471 4345601653271020359275207)
        ·
          refine ⟨6518402479906530538912811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4345601653271020359275207 6518402479906530538912811)
          ·
            refine ⟨9777603719859795808369217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6518402479906530538912811 9777603719859795808369217)
            ·
              refine ⟨7333202789894846856276913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9777603719859795808369217 7333202789894846856276913)
              ·
                refine ⟨5499902092421135142207685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7333202789894846856276913 5499902092421135142207685)
                ·
                  refine ⟨1031231642328962839163941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5499902092421135142207685 1031231642328962839163941)
                  ·
                    refine ⟨193355932936680532343239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1031231642328962839163941 193355932936680532343239)
                    ·
                      rfl

theorem cell22_564839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_564839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_564839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_564839 prefixEnd_564839 := by exact prefixLift 564839
  have htrace : WordTrace (prefixWord ++ tailWord_564839) baseStart_564839 baseEnd_564839 := by
    simpa [prefixWord, tailWord_564839, baseEnd_564839] using wordTrace_append hprefix tailTrace_564839
  have hstable : (prefixWord ++ tailWord_564839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564839).length < 2 ^ (prefixWord ++ tailWord_564839).sum := by decide
  have hdescent : baseEnd_564839 < baseStart_564839 := by decide
  rcases family_descends (prefixWord ++ tailWord_564839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564841 : List Nat := [1, 2, 1, 1, 1, 4, 4, 3, 2, 3]
def baseStart_564841 : Nat := 118140960795 + 564841 * 2 ^ 59
def prefixEnd_564841 : Nat := 4983230072969 + 3 ^ 40 * 564841 * 2
def baseEnd_564841 : Nat := 193356617577553193793233

theorem tailTrace_564841 : CollatzResearch.WordTrace tailWord_564841 prefixEnd_564841 193356617577553193793233 := by
  unfold tailWord_564841
  simp only [CollatzResearch.WordTrace]
  refine ⟨20601443746684999007766377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13734295831123332671844251 20601443746684999007766377)
  ·
    refine ⟨15451082810013749255824783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20601443746684999007766377 15451082810013749255824783)
    ·
      refine ⟨23176624215020623883737175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15451082810013749255824783 23176624215020623883737175)
      ·
        refine ⟨34764936322530935825605763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23176624215020623883737175 34764936322530935825605763)
        ·
          refine ⟨52147404483796403738408645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34764936322530935825605763 52147404483796403738408645)
          ·
            refine ⟨9777638340711825700951621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52147404483796403738408645 9777638340711825700951621)
            ·
              refine ⟨1833307188883467318928429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9777638340711825700951621 1833307188883467318928429)
              ·
                refine ⟨687490195831300244598161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1833307188883467318928429 687490195831300244598161)
                ·
                  refine ⟨515617646873475183448621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 687490195831300244598161 515617646873475183448621)
                  ·
                    refine ⟨193356617577553193793233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 515617646873475183448621 193356617577553193793233)
                    ·
                      rfl

theorem cell22_564841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 3, 2, 3].length) (baseStart_564841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_564841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_564841 prefixEnd_564841 := by exact prefixLift 564841
  have htrace : WordTrace (prefixWord ++ tailWord_564841) baseStart_564841 baseEnd_564841 := by
    simpa [prefixWord, tailWord_564841, baseEnd_564841] using wordTrace_append hprefix tailTrace_564841
  have hstable : (prefixWord ++ tailWord_564841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564841).length < 2 ^ (prefixWord ++ tailWord_564841).sum := by decide
  have hdescent : baseEnd_564841 < baseStart_564841 := by decide
  rcases family_descends (prefixWord ++ tailWord_564841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564914 : List Nat := [3, 2, 1, 1, 1, 2, 2, 2, 1, 7]
def baseStart_564914 : Nat := 118140960795 + 564914 * 2 ^ 59
def prefixEnd_564914 : Nat := 4983230072969 + 3 ^ 40 * 564914 * 2
def baseEnd_564914 : Nat := 193381606969405336718009

theorem tailTrace_564914 : CollatzResearch.WordTrace tailWord_564914 prefixEnd_564914 193381606969405336718009 := by
  unfold tailWord_564914
  simp only [CollatzResearch.WordTrace]
  refine ⟨5151026568855133118793449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13736070850280354983449197 5151026568855133118793449)
  ·
    refine ⟨3863269926641349839095087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5151026568855133118793449 3863269926641349839095087)
    ·
      refine ⟨5794904889962024758642631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3863269926641349839095087 5794904889962024758642631)
      ·
        refine ⟨8692357334943037137963947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5794904889962024758642631 8692357334943037137963947)
        ·
          refine ⟨13038536002414555706945921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8692357334943037137963947 13038536002414555706945921)
          ·
            refine ⟨9778902001810916780209441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13038536002414555706945921 9778902001810916780209441)
            ·
              refine ⟨7334176501358187585157081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9778902001810916780209441 7334176501358187585157081)
              ·
                refine ⟨5500632376018640688867811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7334176501358187585157081 5500632376018640688867811)
                ·
                  refine ⟨8250948564027961033301717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5500632376018640688867811 8250948564027961033301717)
                  ·
                    refine ⟨193381606969405336718009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8250948564027961033301717 193381606969405336718009)
                    ·
                      rfl

theorem cell22_564914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_564914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_564914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_564914 prefixEnd_564914 := by exact prefixLift 564914
  have htrace : WordTrace (prefixWord ++ tailWord_564914) baseStart_564914 baseEnd_564914 := by
    simpa [prefixWord, tailWord_564914, baseEnd_564914] using wordTrace_append hprefix tailTrace_564914
  have hstable : (prefixWord ++ tailWord_564914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564914).length < 2 ^ (prefixWord ++ tailWord_564914).sum := by decide
  have hdescent : baseEnd_564914 < baseStart_564914 := by decide
  rcases family_descends (prefixWord ++ tailWord_564914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564944 : List Nat := [2, 1, 1, 1, 1, 2, 1, 7, 6]
def baseStart_564944 : Nat := 118140960795 + 564944 * 2 ^ 59
def prefixEnd_564944 : Nat := 4983230072969 + 3 ^ 40 * 564944 * 2
def baseEnd_564944 : Nat := 64463958860831752822639

theorem tailTrace_564944 : CollatzResearch.WordTrace tailWord_564944 prefixEnd_564944 64463958860831752822639 := by
  unfold tailWord_564944
  simp only [CollatzResearch.WordTrace]
  refine ⟨10302600232655923799382943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13736800310207898399177257 10302600232655923799382943)
  ·
    refine ⟨15453900348983885699074415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10302600232655923799382943 15453900348983885699074415)
    ·
      refine ⟨23180850523475828548611623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15453900348983885699074415 23180850523475828548611623)
      ·
        refine ⟨34771275785213742822917435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23180850523475828548611623 34771275785213742822917435)
        ·
          refine ⟨52156913677820614234376153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34771275785213742822917435 52156913677820614234376153)
          ·
            refine ⟨39117685258365460675782115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52156913677820614234376153 39117685258365460675782115)
            ·
              refine ⟨58676527887548191013673173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39117685258365460675782115 58676527887548191013673173)
              ·
                refine ⟨1375231122364410726882965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 58676527887548191013673173 1375231122364410726882965)
                ·
                  refine ⟨64463958860831752822639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1375231122364410726882965 64463958860831752822639)
                  ·
                    rfl

theorem cell22_564944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 6].length) (baseStart_564944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_564944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_564944 prefixEnd_564944 := by exact prefixLift 564944
  have htrace : WordTrace (prefixWord ++ tailWord_564944) baseStart_564944 baseEnd_564944 := by
    simpa [prefixWord, tailWord_564944, baseEnd_564944] using wordTrace_append hprefix tailTrace_564944
  have hstable : (prefixWord ++ tailWord_564944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564944).length < 2 ^ (prefixWord ++ tailWord_564944).sum := by decide
  have hdescent : baseEnd_564944 < baseStart_564944 := by decide
  rcases family_descends (prefixWord ++ tailWord_564944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564963 : List Nat := [1, 1, 1, 7, 2, 1, 1, 1, 3, 4]
def baseStart_564963 : Nat := 118140960795 + 564963 * 2 ^ 59
def prefixEnd_564963 : Nat := 4983230072969 + 3 ^ 40 * 564963 * 2
def baseEnd_564963 : Nat := 193398380670785542242859

theorem tailTrace_564963 : CollatzResearch.WordTrace tailWord_564963 prefixEnd_564963 193398380670785542242859 := by
  unfold tailWord_564963
  simp only [CollatzResearch.WordTrace]
  refine ⟨20605893452243013843707543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13737262301495342562471695 20605893452243013843707543)
  ·
    refine ⟨30908840178364520765561315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20605893452243013843707543 30908840178364520765561315)
    ·
      refine ⟨46363260267546781148341973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30908840178364520765561315 46363260267546781148341973)
      ·
        refine ⟨1086638912520627683164265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 46363260267546781148341973 1086638912520627683164265)
        ·
          refine ⟨814979184390470762373199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1086638912520627683164265 814979184390470762373199)
          ·
            refine ⟨1222468776585706143559799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 814979184390470762373199 1222468776585706143559799)
            ·
              refine ⟨1833703164878559215339699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1222468776585706143559799 1833703164878559215339699)
              ·
                refine ⟨2750554747317838823009549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1833703164878559215339699 2750554747317838823009549)
                ·
                  refine ⟨1031458030244189558628581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2750554747317838823009549 1031458030244189558628581)
                  ·
                    refine ⟨193398380670785542242859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1031458030244189558628581 193398380670785542242859)
                    ·
                      rfl

theorem cell22_564963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 3, 4].length) (baseStart_564963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_564963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_564963 prefixEnd_564963 := by exact prefixLift 564963
  have htrace : WordTrace (prefixWord ++ tailWord_564963) baseStart_564963 baseEnd_564963 := by
    simpa [prefixWord, tailWord_564963, baseEnd_564963] using wordTrace_append hprefix tailTrace_564963
  have hstable : (prefixWord ++ tailWord_564963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564963).length < 2 ^ (prefixWord ++ tailWord_564963).sum := by decide
  have hdescent : baseEnd_564963 < baseStart_564963 := by decide
  rcases family_descends (prefixWord ++ tailWord_564963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564976 : List Nat := [2, 1, 1, 1, 3, 1, 2, 4, 4, 3]
def baseStart_564976 : Nat := 118140960795 + 564976 * 2 ^ 59
def prefixEnd_564976 : Nat := 4983230072969 + 3 ^ 40 * 564976 * 2
def baseEnd_564976 : Nat := 193402830836457841667819

theorem tailTrace_564976 : CollatzResearch.WordTrace tailWord_564976 prefixEnd_564976 193402830836457841667819 := by
  unfold tailWord_564976
  simp only [CollatzResearch.WordTrace]
  refine ⟨10303183800597958531965391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13737578400797278042620521 10303183800597958531965391)
  ·
    refine ⟨15454775700896937797948087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10303183800597958531965391 15454775700896937797948087)
    ·
      refine ⟨23182163551345406696922131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15454775700896937797948087 23182163551345406696922131)
      ·
        refine ⟨34773245327018110045383197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23182163551345406696922131 34773245327018110045383197)
        ·
          refine ⟨13039966997631791267018699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34773245327018110045383197 13039966997631791267018699)
          ·
            refine ⟨19559950496447686900528049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13039966997631791267018699 19559950496447686900528049)
            ·
              refine ⟨14669962872335765175396037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19559950496447686900528049 14669962872335765175396037)
              ·
                refine ⟨2750618038562955970386757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14669962872335765175396037 2750618038562955970386757)
                ·
                  refine ⟨515740882230554244447517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2750618038562955970386757 515740882230554244447517)
                  ·
                    refine ⟨193402830836457841667819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 515740882230554244447517 193402830836457841667819)
                    ·
                      rfl

theorem cell22_564976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 4, 3].length) (baseStart_564976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_564976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_564976 prefixEnd_564976 := by exact prefixLift 564976
  have htrace : WordTrace (prefixWord ++ tailWord_564976) baseStart_564976 baseEnd_564976 := by
    simpa [prefixWord, tailWord_564976, baseEnd_564976] using wordTrace_append hprefix tailTrace_564976
  have hstable : (prefixWord ++ tailWord_564976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564976).length < 2 ^ (prefixWord ++ tailWord_564976).sum := by decide
  have hdescent : baseEnd_564976 < baseStart_564976 := by decide
  rcases family_descends (prefixWord ++ tailWord_564976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564978 : List Nat := [3, 2, 1, 3, 1, 1, 2, 5, 4]
def baseStart_564978 : Nat := 118140960795 + 564978 * 2 ^ 59
def prefixEnd_564978 : Nat := 4983230072969 + 3 ^ 40 * 564978 * 2
def baseEnd_564978 : Nat := 64467838492443501039271

theorem tailTrace_564978 : CollatzResearch.WordTrace tailWord_564978 prefixEnd_564978 64467838492443501039271 := by
  unfold tailWord_564978
  simp only [CollatzResearch.WordTrace]
  refine ⟨5151610136797167851375897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13737627031459114270335725 5151610136797167851375897)
  ·
    refine ⟨3863707602597875888531923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5151610136797167851375897 3863707602597875888531923)
    ·
      refine ⟨5795561403896813832797885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3863707602597875888531923 5795561403896813832797885)
      ·
        refine ⟨2173335526461305187299207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5795561403896813832797885 2173335526461305187299207)
        ·
          refine ⟨3260003289691957780948811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2173335526461305187299207 3260003289691957780948811)
          ·
            refine ⟨4890004934537936671423217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3260003289691957780948811 4890004934537936671423217)
            ·
              refine ⟨3667503700903452503567413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4890004934537936671423217 3667503700903452503567413)
              ·
                refine ⟨343828471959698672209445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3667503700903452503567413 343828471959698672209445)
                ·
                  refine ⟨64467838492443501039271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 343828471959698672209445 64467838492443501039271)
                  ·
                    rfl

theorem cell22_564978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 5, 4].length) (baseStart_564978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_564978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_564978 prefixEnd_564978 := by exact prefixLift 564978
  have htrace : WordTrace (prefixWord ++ tailWord_564978) baseStart_564978 baseEnd_564978 := by
    simpa [prefixWord, tailWord_564978, baseEnd_564978] using wordTrace_append hprefix tailTrace_564978
  have hstable : (prefixWord ++ tailWord_564978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564978).length < 2 ^ (prefixWord ++ tailWord_564978).sum := by decide
  have hdescent : baseEnd_564978 < baseStart_564978 := by decide
  rcases family_descends (prefixWord ++ tailWord_564978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564991 : List Nat := [1, 1, 2, 2, 1, 3, 4, 2, 2, 4]
def baseStart_564991 : Nat := 118140960795 + 564991 * 2 ^ 59
def prefixEnd_564991 : Nat := 4983230072969 + 3 ^ 40 * 564991 * 2
def baseEnd_564991 : Nat := 193407965643002802542773

theorem tailTrace_564991 : CollatzResearch.WordTrace tailWord_564991 prefixEnd_564991 193407965643002802542773 := by
  unfold tailWord_564991
  simp only [CollatzResearch.WordTrace]
  refine ⟨20606914696141574625726827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13737943130761049750484551 20606914696141574625726827)
  ·
    refine ⟨30910372044212361938590241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20606914696141574625726827 30910372044212361938590241)
    ·
      refine ⟨23182779033159271453942681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30910372044212361938590241 23182779033159271453942681)
      ·
        refine ⟨17387084274869453590457011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23182779033159271453942681 17387084274869453590457011)
        ·
          refine ⟨26080626412304180385685517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17387084274869453590457011 26080626412304180385685517)
          ·
            refine ⟨9780234904614067644632069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26080626412304180385685517 9780234904614067644632069)
            ·
              refine ⟨1833794044615137683368513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9780234904614067644632069 1833794044615137683368513)
              ·
                refine ⟨1375345533461353262526385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1833794044615137683368513 1375345533461353262526385)
                ·
                  refine ⟨1031509150096014946894789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1375345533461353262526385 1031509150096014946894789)
                  ·
                    refine ⟨193407965643002802542773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1031509150096014946894789 193407965643002802542773)
                    ·
                      rfl

theorem cell22_564991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 2, 4].length) (baseStart_564991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_564991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_564991 prefixEnd_564991 := by exact prefixLift 564991
  have htrace : WordTrace (prefixWord ++ tailWord_564991) baseStart_564991 baseEnd_564991 := by
    simpa [prefixWord, tailWord_564991, baseEnd_564991] using wordTrace_append hprefix tailTrace_564991
  have hstable : (prefixWord ++ tailWord_564991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564991).length < 2 ^ (prefixWord ++ tailWord_564991).sum := by decide
  have hdescent : baseEnd_564991 < baseStart_564991 := by decide
  rcases family_descends (prefixWord ++ tailWord_564991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564993 : List Nat := [1, 2, 4, 1, 1, 1, 3, 4, 2, 3]
def baseStart_564993 : Nat := 118140960795 + 564993 * 2 ^ 59
def prefixEnd_564993 : Nat := 4983230072969 + 3 ^ 40 * 564993 * 2
def baseEnd_564993 : Nat := 193408650283875463992767

theorem tailTrace_564993 : CollatzResearch.WordTrace tailWord_564993 prefixEnd_564993 193408650283875463992767 := by
  unfold tailWord_564993
  simp only [CollatzResearch.WordTrace]
  refine ⟨20606987642134328967299633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13737991761422885978199755 20606987642134328967299633)
  ·
    refine ⟨15455240731600746725474725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20606987642134328967299633 15455240731600746725474725)
    ·
      refine ⟨2897857637175140011026511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15455240731600746725474725 2897857637175140011026511)
      ·
        refine ⟨4346786455762710016539767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2897857637175140011026511 4346786455762710016539767)
        ·
          refine ⟨6520179683644065024809651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4346786455762710016539767 6520179683644065024809651)
          ·
            refine ⟨9780269525466097537214477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6520179683644065024809651 9780269525466097537214477)
            ·
              refine ⟨3667601072049786576455429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9780269525466097537214477 3667601072049786576455429)
              ·
                refine ⟨687675201009334983085393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3667601072049786576455429 687675201009334983085393)
                ·
                  refine ⟨515756400757001237314045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 687675201009334983085393 515756400757001237314045)
                  ·
                    refine ⟨193408650283875463992767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 515756400757001237314045 193408650283875463992767)
                    ·
                      rfl

theorem cell22_564993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_564993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_564993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_564993 prefixEnd_564993 := by exact prefixLift 564993
  have htrace : WordTrace (prefixWord ++ tailWord_564993) baseStart_564993 baseEnd_564993 := by
    simpa [prefixWord, tailWord_564993, baseEnd_564993] using wordTrace_append hprefix tailTrace_564993
  have hstable : (prefixWord ++ tailWord_564993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564993).length < 2 ^ (prefixWord ++ tailWord_564993).sum := by decide
  have hdescent : baseEnd_564993 < baseStart_564993 := by decide
  rcases family_descends (prefixWord ++ tailWord_564993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565006 : List Nat := [4, 1, 1, 2, 1, 1, 5, 7]
def baseStart_565006 : Nat := 118140960795 + 565006 * 2 ^ 59
def prefixEnd_565006 : Nat := 4983230072969 + 3 ^ 40 * 565006 * 2
def baseEnd_565006 : Nat := 21490344494394195935303

theorem tailTrace_565006 : CollatzResearch.WordTrace tailWord_565006 prefixEnd_565006 21490344494394195935303 := by
  unfold tailWord_565006
  simp only [CollatzResearch.WordTrace]
  refine ⟨2575932723885904023440359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13738307860724821458348581 2575932723885904023440359)
  ·
    refine ⟨3863899085828856035160539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2575932723885904023440359 3863899085828856035160539)
    ·
      refine ⟨5795848628743284052740809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3863899085828856035160539 5795848628743284052740809)
      ·
        refine ⟨4346886471557463039555607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5795848628743284052740809 4346886471557463039555607)
        ·
          refine ⟨6520329707336194559333411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4346886471557463039555607 6520329707336194559333411)
          ·
            refine ⟨9780494561004291839000117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6520329707336194559333411 9780494561004291839000117)
            ·
              refine ⟨916921365094152359906261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9780494561004291839000117 916921365094152359906261)
              ·
                refine ⟨21490344494394195935303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 916921365094152359906261 21490344494394195935303)
                ·
                  rfl

theorem cell22_565006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 7].length) (baseStart_565006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_565006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_565006 prefixEnd_565006 := by exact prefixLift 565006
  have htrace : WordTrace (prefixWord ++ tailWord_565006) baseStart_565006 baseEnd_565006 := by
    simpa [prefixWord, tailWord_565006, baseEnd_565006] using wordTrace_append hprefix tailTrace_565006
  have hstable : (prefixWord ++ tailWord_565006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565006).length < 2 ^ (prefixWord ++ tailWord_565006).sum := by decide
  have hdescent : baseEnd_565006 < baseStart_565006 := by decide
  rcases family_descends (prefixWord ++ tailWord_565006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565010 : List Nat := [3, 2, 4, 1, 1, 2, 2, 1, 1, 5]
def baseStart_565010 : Nat := 118140960795 + 565010 * 2 ^ 59
def prefixEnd_565010 : Nat := 4983230072969 + 3 ^ 40 * 565010 * 2
def baseEnd_565010 : Nat := 193414469731293086317715

theorem tailTrace_565010 : CollatzResearch.WordTrace tailWord_565010 prefixEnd_565010 193414469731293086317715 := by
  unfold tailWord_565010
  simp only [CollatzResearch.WordTrace]
  refine ⟨5151901920768185217667121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13738405122048493913778989 5151901920768185217667121)
  ·
    refine ⟨3863926440576138913250341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5151901920768185217667121 3863926440576138913250341)
    ·
      refine ⟨724486207608026046234439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3863926440576138913250341 724486207608026046234439)
      ·
        refine ⟨1086729311412039069351659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 724486207608026046234439 1086729311412039069351659)
        ·
          refine ⟨1630093967118058604027489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1086729311412039069351659 1630093967118058604027489)
          ·
            refine ⟨1222570475338543953020617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1630093967118058604027489 1222570475338543953020617)
            ·
              refine ⟨916927856503907964765463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1222570475338543953020617 916927856503907964765463)
              ·
                refine ⟨1375391784755861947148195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 916927856503907964765463 1375391784755861947148195)
                ·
                  refine ⟨2063087677133792920722293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1375391784755861947148195 2063087677133792920722293)
                  ·
                    refine ⟨193414469731293086317715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2063087677133792920722293 193414469731293086317715)
                    ·
                      rfl

theorem cell22_565010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_565010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_565010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_565010 prefixEnd_565010 := by exact prefixLift 565010
  have htrace : WordTrace (prefixWord ++ tailWord_565010) baseStart_565010 baseEnd_565010 := by
    simpa [prefixWord, tailWord_565010, baseEnd_565010] using wordTrace_append hprefix tailTrace_565010
  have hstable : (prefixWord ++ tailWord_565010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565010).length < 2 ^ (prefixWord ++ tailWord_565010).sum := by decide
  have hdescent : baseEnd_565010 < baseStart_565010 := by decide
  rcases family_descends (prefixWord ++ tailWord_565010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565012 : List Nat := [2, 4, 4, 1, 1, 1, 1, 2, 6]
def baseStart_565012 : Nat := 118140960795 + 565012 * 2 ^ 59
def prefixEnd_565012 : Nat := 4983230072969 + 3 ^ 40 * 565012 * 2
def baseEnd_565012 : Nat := 64471718124055249255903

theorem tailTrace_565012 : CollatzResearch.WordTrace tailWord_565012 prefixEnd_565012 64471718124055249255903 := by
  unfold tailWord_565012
  simp only [CollatzResearch.WordTrace]
  refine ⟨10303840314532747606120645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13738453752710330141494193 10303840314532747606120645)
  ·
    refine ⟨1931970058974890176147621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10303840314532747606120645 1931970058974890176147621)
    ·
      refine ⟨362244386057791908027679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1931970058974890176147621 362244386057791908027679)
      ·
        refine ⟨543366579086687862041519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 362244386057791908027679 543366579086687862041519)
        ·
          refine ⟨815049868630031793062279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 543366579086687862041519 815049868630031793062279)
          ·
            refine ⟨1222574802945047689593419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 815049868630031793062279 1222574802945047689593419)
            ·
              refine ⟨1833862204417571534390129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1222574802945047689593419 1833862204417571534390129)
              ·
                refine ⟨1375396653313178650792597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1833862204417571534390129 1375396653313178650792597)
                ·
                  refine ⟨64471718124055249255903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1375396653313178650792597 64471718124055249255903)
                  ·
                    rfl

theorem cell22_565012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_565012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_565012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_565012 prefixEnd_565012 := by exact prefixLift 565012
  have htrace : WordTrace (prefixWord ++ tailWord_565012) baseStart_565012 baseEnd_565012 := by
    simpa [prefixWord, tailWord_565012, baseEnd_565012] using wordTrace_append hprefix tailTrace_565012
  have hstable : (prefixWord ++ tailWord_565012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565012).length < 2 ^ (prefixWord ++ tailWord_565012).sum := by decide
  have hdescent : baseEnd_565012 < baseStart_565012 := by decide
  rcases family_descends (prefixWord ++ tailWord_565012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565055 : List Nat := [1, 1, 2, 2, 6, 1, 2, 1, 3, 3]
def baseStart_565055 : Nat := 118140960795 + 565055 * 2 ^ 59
def prefixEnd_565055 : Nat := 4983230072969 + 3 ^ 40 * 565055 * 2
def baseEnd_565055 : Nat := 193429874150927968942577

theorem tailTrace_565055 : CollatzResearch.WordTrace tailWord_565055 prefixEnd_565055 193429874150927968942577 := by
  unfold tailWord_565055
  simp only [CollatzResearch.WordTrace]
  refine ⟨20609248967909713556056619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13739499311939809037371079 20609248967909713556056619)
  ·
    refine ⟨30913873451864570334084929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20609248967909713556056619 30913873451864570334084929)
    ·
      refine ⟨23185405088898427750563697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30913873451864570334084929 23185405088898427750563697)
      ·
        refine ⟨17389053816673820812922773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23185405088898427750563697 17389053816673820812922773)
        ·
          refine ⟨815111897656585350605755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17389053816673820812922773 815111897656585350605755)
          ·
            refine ⟨1222667846484878025908633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 815111897656585350605755 1222667846484878025908633)
            ·
              refine ⟨917000884863658519431475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1222667846484878025908633 917000884863658519431475)
              ·
                refine ⟨1375501327295487779147213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 917000884863658519431475 1375501327295487779147213)
                ·
                  refine ⟨515812997735807917180205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1375501327295487779147213 515812997735807917180205)
                  ·
                    refine ⟨193429874150927968942577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 515812997735807917180205 193429874150927968942577)
                    ·
                      rfl

theorem cell22_565055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 3, 3].length) (baseStart_565055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_565055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_565055 prefixEnd_565055 := by exact prefixLift 565055
  have htrace : WordTrace (prefixWord ++ tailWord_565055) baseStart_565055 baseEnd_565055 := by
    simpa [prefixWord, tailWord_565055, baseEnd_565055] using wordTrace_append hprefix tailTrace_565055
  have hstable : (prefixWord ++ tailWord_565055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565055).length < 2 ^ (prefixWord ++ tailWord_565055).sum := by decide
  have hdescent : baseEnd_565055 < baseStart_565055 := by decide
  rcases family_descends (prefixWord ++ tailWord_565055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565066 : List Nat := [3, 1, 2, 1, 1, 1, 3, 3, 2, 5]
def baseStart_565066 : Nat := 118140960795 + 565066 * 2 ^ 59
def prefixEnd_565066 : Nat := 4983230072969 + 3 ^ 40 * 565066 * 2
def baseEnd_565066 : Nat := 193433639675727606917543

theorem tailTrace_565066 : CollatzResearch.WordTrace tailWord_565066 prefixEnd_565066 193433639675727606917543 := by
  unfold tailWord_565066
  simp only [CollatzResearch.WordTrace]
  refine ⟨5152412542717465608676763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13739766780579908289804701 5152412542717465608676763)
  ·
    refine ⟨7728618814076198413015145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5152412542717465608676763 7728618814076198413015145)
    ·
      refine ⟨5796464110557148809761359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7728618814076198413015145 5796464110557148809761359)
      ·
        refine ⟨8694696165835723214642039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5796464110557148809761359 8694696165835723214642039)
        ·
          refine ⟨13042044248753584821963059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8694696165835723214642039 13042044248753584821963059)
          ·
            refine ⟨19563066373130377232944589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13042044248753584821963059 19563066373130377232944589)
            ·
              refine ⟨7336149889923891462354221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19563066373130377232944589 7336149889923891462354221)
              ·
                refine ⟨2751056208721459298382833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7336149889923891462354221 2751056208721459298382833)
                ·
                  refine ⟨2063292156541094473787125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2751056208721459298382833 2063292156541094473787125)
                  ·
                    refine ⟨193433639675727606917543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2063292156541094473787125 193433639675727606917543)
                    ·
                      rfl

theorem cell22_565066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_565066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_565066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_565066 prefixEnd_565066 := by exact prefixLift 565066
  have htrace : WordTrace (prefixWord ++ tailWord_565066) baseStart_565066 baseEnd_565066 := by
    simpa [prefixWord, tailWord_565066, baseEnd_565066] using wordTrace_append hprefix tailTrace_565066
  have hstable : (prefixWord ++ tailWord_565066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565066).length < 2 ^ (prefixWord ++ tailWord_565066).sum := by decide
  have hdescent : baseEnd_565066 < baseStart_565066 := by decide
  rcases family_descends (prefixWord ++ tailWord_565066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565141 : List Nat := [1, 3, 2, 1, 1, 3, 1, 10]
def baseStart_565141 : Nat := 118140960795 + 565141 * 2 ^ 59
def prefixEnd_565141 : Nat := 4983230072969 + 3 ^ 40 * 565141 * 2
def baseEnd_565141 : Nat := 21495479300939156810257

theorem tailTrace_565141 : CollatzResearch.WordTrace tailWord_565141 prefixEnd_565141 21495479300939156810257 := by
  unfold tailWord_565141
  simp only [CollatzResearch.WordTrace]
  refine ⟨20612385645598150243687277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13741590430398766829124851 20612385645598150243687277)
  ·
    refine ⟨7729644617099306341382729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20612385645598150243687277 7729644617099306341382729)
    ·
      refine ⟨5797233462824479756037047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7729644617099306341382729 5797233462824479756037047)
      ·
        refine ⟨8695850194236719634055571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5797233462824479756037047 8695850194236719634055571)
        ·
          refine ⟨13043775291355079451083357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8695850194236719634055571 13043775291355079451083357)
          ·
            refine ⟨4891415734258154794156259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13043775291355079451083357 4891415734258154794156259)
            ·
              refine ⟨7337123601387232191234389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4891415734258154794156259 7337123601387232191234389)
              ·
                refine ⟨21495479300939156810257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 7337123601387232191234389 21495479300939156810257)
                ·
                  rfl

theorem cell22_565141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 10].length) (baseStart_565141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_565141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_565141 prefixEnd_565141 := by exact prefixLift 565141
  have htrace : WordTrace (prefixWord ++ tailWord_565141) baseStart_565141 baseEnd_565141 := by
    simpa [prefixWord, tailWord_565141, baseEnd_565141] using wordTrace_append hprefix tailTrace_565141
  have hstable : (prefixWord ++ tailWord_565141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565141).length < 2 ^ (prefixWord ++ tailWord_565141).sum := by decide
  have hdescent : baseEnd_565141 < baseStart_565141 := by decide
  rcases family_descends (prefixWord ++ tailWord_565141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565143 : List Nat := [1, 1, 3, 3, 1, 3, 1, 3, 2, 4]
def baseStart_565143 : Nat := 118140960795 + 565143 * 2 ^ 59
def prefixEnd_565143 : Nat := 4983230072969 + 3 ^ 40 * 565143 * 2
def baseEnd_565143 : Nat := 193459998349325072742307

theorem tailTrace_565143 : CollatzResearch.WordTrace tailWord_565143 prefixEnd_565143 193459998349325072742307 := by
  unfold tailWord_565143
  simp only [CollatzResearch.WordTrace]
  refine ⟨20612458591590904585260083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13741639061060603056840055 20612458591590904585260083)
  ·
    refine ⟨30918687887386356877890125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20612458591590904585260083 30918687887386356877890125)
    ·
      refine ⟨11594507957769883829208797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30918687887386356877890125 11594507957769883829208797)
      ·
        refine ⟨4347940484163706435953299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11594507957769883829208797 4347940484163706435953299)
        ·
          refine ⟨6521910726245559653929949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4347940484163706435953299 6521910726245559653929949)
          ·
            refine ⟨2445716522342084870223731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6521910726245559653929949 2445716522342084870223731)
            ·
              refine ⟨3668574783513127305335597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2445716522342084870223731 3668574783513127305335597)
              ·
                refine ⟨1375715543817422739500849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3668574783513127305335597 1375715543817422739500849)
                ·
                  refine ⟨1031786657863067054625637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1375715543817422739500849 1031786657863067054625637)
                  ·
                    refine ⟨193459998349325072742307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1031786657863067054625637 193459998349325072742307)
                    ·
                      rfl

theorem cell22_565143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 2, 4].length) (baseStart_565143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_565143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_565143 prefixEnd_565143 := by exact prefixLift 565143
  have htrace : WordTrace (prefixWord ++ tailWord_565143) baseStart_565143 baseEnd_565143 := by
    simpa [prefixWord, tailWord_565143, baseEnd_565143] using wordTrace_append hprefix tailTrace_565143
  have hstable : (prefixWord ++ tailWord_565143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565143).length < 2 ^ (prefixWord ++ tailWord_565143).sum := by decide
  have hdescent : baseEnd_565143 < baseStart_565143 := by decide
  rcases family_descends (prefixWord ++ tailWord_565143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565171 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 1, 8]
def baseStart_565171 : Nat := 118140960795 + 565171 * 2 ^ 59
def prefixEnd_565171 : Nat := 4983230072969 + 3 ^ 40 * 565171 * 2
def baseEnd_565171 : Nat := 193469583321542333042221

theorem tailTrace_565171 : CollatzResearch.WordTrace tailWord_565171 prefixEnd_565171 193469583321542333042221 := by
  unfold tailWord_565171
  simp only [CollatzResearch.WordTrace]
  refine ⟨20613479835489465367279367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13742319890326310244852911 20613479835489465367279367)
  ·
    refine ⟨30920219753234198050919051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20613479835489465367279367 30920219753234198050919051)
    ·
      refine ⟨46380329629851297076378577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30920219753234198050919051 46380329629851297076378577)
      ·
        refine ⟨34785247222388472807283933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46380329629851297076378577 34785247222388472807283933)
        ·
          refine ⟨13044467708395677302731475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34785247222388472807283933 13044467708395677302731475)
          ·
            refine ⟨19566701562593515954097213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13044467708395677302731475 19566701562593515954097213)
            ·
              refine ⟨7337513085972568482786455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19566701562593515954097213 7337513085972568482786455)
              ·
                refine ⟨11006269628958852724179683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7337513085972568482786455 11006269628958852724179683)
                ·
                  refine ⟨16509404443438279086269525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11006269628958852724179683 16509404443438279086269525)
                  ·
                    refine ⟨193469583321542333042221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 16509404443438279086269525 193469583321542333042221)
                    ·
                      rfl

theorem cell22_565171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 8].length) (baseStart_565171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_565171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_565171 prefixEnd_565171 := by exact prefixLift 565171
  have htrace : WordTrace (prefixWord ++ tailWord_565171) baseStart_565171 baseEnd_565171 := by
    simpa [prefixWord, tailWord_565171, baseEnd_565171] using wordTrace_append hprefix tailTrace_565171
  have hstable : (prefixWord ++ tailWord_565171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565171).length < 2 ^ (prefixWord ++ tailWord_565171).sum := by decide
  have hdescent : baseEnd_565171 < baseStart_565171 := by decide
  rcases family_descends (prefixWord ++ tailWord_565171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565207 : List Nat := [1, 1, 3, 2, 1, 1, 6, 3, 1, 3]
def baseStart_565207 : Nat := 118140960795 + 565207 * 2 ^ 59
def prefixEnd_565207 : Nat := 4983230072969 + 3 ^ 40 * 565207 * 2
def baseEnd_565207 : Nat := 193481906857250239142111

theorem tailTrace_565207 : CollatzResearch.WordTrace tailWord_565207 prefixEnd_565207 193481906857250239142111 := by
  unfold tailWord_565207
  simp only [CollatzResearch.WordTrace]
  refine ⟨20614792863359043515589875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13743195242239362343726583 20614792863359043515589875)
  ·
    refine ⟨30922189295038565273384813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20614792863359043515589875 30922189295038565273384813)
    ·
      refine ⟨11595820985639461977519305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30922189295038565273384813 11595820985639461977519305)
      ·
        refine ⟨8696865739229596483139479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11595820985639461977519305 8696865739229596483139479)
        ·
          refine ⟨13045298608844394724709219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8696865739229596483139479 13045298608844394724709219)
          ·
            refine ⟨19567947913266592087063829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13045298608844394724709219 19567947913266592087063829)
            ·
              refine ⟨917247558434371504081117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19567947913266592087063829 917247558434371504081117)
              ·
                refine ⟨343967834412889314030419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 917247558434371504081117 343967834412889314030419)
                ·
                  refine ⟨515951751619333971045629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 343967834412889314030419 515951751619333971045629)
                  ·
                    refine ⟨193481906857250239142111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 515951751619333971045629 193481906857250239142111)
                    ·
                      rfl

theorem cell22_565207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 3, 1, 3].length) (baseStart_565207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_565207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_565207 prefixEnd_565207 := by exact prefixLift 565207
  have htrace : WordTrace (prefixWord ++ tailWord_565207) baseStart_565207 baseEnd_565207 := by
    simpa [prefixWord, tailWord_565207, baseEnd_565207] using wordTrace_append hprefix tailTrace_565207
  have hstable : (prefixWord ++ tailWord_565207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565207).length < 2 ^ (prefixWord ++ tailWord_565207).sum := by decide
  have hdescent : baseEnd_565207 < baseStart_565207 := by decide
  rcases family_descends (prefixWord ++ tailWord_565207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565297 : List Nat := [1, 2, 2, 3, 1, 4, 1, 3, 2, 3]
def baseStart_565297 : Nat := 118140960795 + 565297 * 2 ^ 59
def prefixEnd_565297 : Nat := 4983230072969 + 3 ^ 40 * 565297 * 2
def baseEnd_565297 : Nat := 193512715696520004391835

theorem tailTrace_565297 : CollatzResearch.WordTrace tailWord_565297 prefixEnd_565297 193512715696520004391835 := by
  unfold tailWord_565297
  simp only [CollatzResearch.WordTrace]
  refine ⟨20618075433032988886366145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13745383622021992590910763 20618075433032988886366145)
  ·
    refine ⟨15463556574774741664774609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20618075433032988886366145 15463556574774741664774609)
    ·
      refine ⟨11597667431081056248580957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15463556574774741664774609 11597667431081056248580957)
      ·
        refine ⟨4349125286655396093217859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11597667431081056248580957 4349125286655396093217859)
        ·
          refine ⟨6523687929983094139826789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4349125286655396093217859 6523687929983094139826789)
          ·
            refine ⟨1223191486871830151217523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6523687929983094139826789 1223191486871830151217523)
            ·
              refine ⟨1834787230307745226826285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1223191486871830151217523 1834787230307745226826285)
              ·
                refine ⟨688045211365404460059857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1834787230307745226826285 688045211365404460059857)
                ·
                  refine ⟨516033908524053345044893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 688045211365404460059857 516033908524053345044893)
                  ·
                    refine ⟨193512715696520004391835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 516033908524053345044893 193512715696520004391835)
                    ·
                      rfl

theorem cell22_565297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 3, 2, 3].length) (baseStart_565297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_565297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_565297 prefixEnd_565297 := by exact prefixLift 565297
  have htrace : WordTrace (prefixWord ++ tailWord_565297) baseStart_565297 baseEnd_565297 := by
    simpa [prefixWord, tailWord_565297, baseEnd_565297] using wordTrace_append hprefix tailTrace_565297
  have hstable : (prefixWord ++ tailWord_565297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565297).length < 2 ^ (prefixWord ++ tailWord_565297).sum := by decide
  have hdescent : baseEnd_565297 < baseStart_565297 := by decide
  rcases family_descends (prefixWord ++ tailWord_565297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565340 : List Nat := [2, 2, 4, 1, 1, 2, 1, 1, 2, 6]
def baseStart_565340 : Nat := 118140960795 + 565340 * 2 ^ 59
def prefixEnd_565340 : Nat := 4983230072969 + 3 ^ 40 * 565340 * 2
def baseEnd_565340 : Nat := 193527435475282225566703

theorem tailTrace_565340 : CollatzResearch.WordTrace tailWord_565340 prefixEnd_565340 193527435475282225566703 := by
  unfold tailWord_565340
  simp only [CollatzResearch.WordTrace]
  refine ⟨10309821885938603615090737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13746429181251471486787649 10309821885938603615090737)
  ·
    refine ⟨7732366414453952711318053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10309821885938603615090737 7732366414453952711318053)
    ·
      refine ⟨1449818702710116133372135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7732366414453952711318053 1449818702710116133372135)
      ·
        refine ⟨2174728054065174200058203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1449818702710116133372135 2174728054065174200058203)
        ·
          refine ⟨3262092081097761300087305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2174728054065174200058203 3262092081097761300087305)
          ·
            refine ⟨2446569060823320975065479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3262092081097761300087305 2446569060823320975065479)
            ·
              refine ⟨3669853591234981462598219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2446569060823320975065479 3669853591234981462598219)
              ·
                refine ⟨5504780386852472193897329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3669853591234981462598219 5504780386852472193897329)
                ·
                  refine ⟨4128585290139354145422997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5504780386852472193897329 4128585290139354145422997)
                  ·
                    refine ⟨193527435475282225566703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4128585290139354145422997 193527435475282225566703)
                    ·
                      rfl

theorem cell22_565340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_565340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_565340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_565340 prefixEnd_565340 := by exact prefixLift 565340
  have htrace : WordTrace (prefixWord ++ tailWord_565340) baseStart_565340 baseEnd_565340 := by
    simpa [prefixWord, tailWord_565340, baseEnd_565340] using wordTrace_append hprefix tailTrace_565340
  have hstable : (prefixWord ++ tailWord_565340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565340).length < 2 ^ (prefixWord ++ tailWord_565340).sum := by decide
  have hdescent : baseEnd_565340 < baseStart_565340 := by decide
  rcases family_descends (prefixWord ++ tailWord_565340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565406 : List Nat := [4, 3, 1, 1, 3, 1, 3, 1, 5]
def baseStart_565406 : Nat := 118140960795 + 565406 * 2 ^ 59
def prefixEnd_565406 : Nat := 4983230072969 + 3 ^ 40 * 565406 * 2
def baseEnd_565406 : Nat := 64516676208026684472167

theorem tailTrace_565406 : CollatzResearch.WordTrace tailWord_565406 prefixEnd_565406 64516676208026684472167 := by
  unfold tailWord_565406
  simp only [CollatzResearch.WordTrace]
  refine ⟨2577756373704762562760509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13748033993092067001389381 2577756373704762562760509)
  ·
    refine ⟨966658640139285961035191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2577756373704762562760509 966658640139285961035191)
    ·
      refine ⟨1449987960208928941552787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 966658640139285961035191 1449987960208928941552787)
      ·
        refine ⟨2174981940313393412329181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1449987960208928941552787 2174981940313393412329181)
        ·
          refine ⟨815618227617522529623443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2174981940313393412329181 815618227617522529623443)
          ·
            refine ⟨1223427341426283794435165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 815618227617522529623443 1223427341426283794435165)
            ·
              refine ⟨458785253034856422913187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1223427341426283794435165 458785253034856422913187)
              ·
                refine ⟨688177879552284634369781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 458785253034856422913187 688177879552284634369781)
                ·
                  refine ⟨64516676208026684472167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 688177879552284634369781 64516676208026684472167)
                  ·
                    rfl

theorem cell22_565406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_565406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_565406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_565406 prefixEnd_565406 := by exact prefixLift 565406
  have htrace : WordTrace (prefixWord ++ tailWord_565406) baseStart_565406 baseEnd_565406 := by
    simpa [prefixWord, tailWord_565406, baseEnd_565406] using wordTrace_append hprefix tailTrace_565406
  have hstable : (prefixWord ++ tailWord_565406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565406).length < 2 ^ (prefixWord ++ tailWord_565406).sum := by decide
  have hdescent : baseEnd_565406 < baseStart_565406 := by decide
  rcases family_descends (prefixWord ++ tailWord_565406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565507 : List Nat := [1, 1, 1, 3, 2, 3, 4, 2, 5]
def baseStart_565507 : Nat := 118140960795 + 565507 * 2 ^ 59
def prefixEnd_565507 : Nat := 4983230072969 + 3 ^ 40 * 565507 * 2
def baseEnd_565507 : Nat := 64528200996049818880397

theorem tailTrace_565507 : CollatzResearch.WordTrace tailWord_565507 prefixEnd_565507 64528200996049818880397 := by
  unfold tailWord_565507
  simp only [CollatzResearch.WordTrace]
  refine ⟨20625734762272194751510775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13750489841514796501007183 20625734762272194751510775)
  ·
    refine ⟨30938602143408292127266163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20625734762272194751510775 30938602143408292127266163)
    ·
      refine ⟨46407903215112438190899245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30938602143408292127266163 46407903215112438190899245)
      ·
        refine ⟨17402963705667164321587217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46407903215112438190899245 17402963705667164321587217)
        ·
          refine ⟨13052222779250373241190413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17402963705667164321587217 13052222779250373241190413)
          ·
            refine ⟨4894583542218889965446405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13052222779250373241190413 4894583542218889965446405)
            ·
              refine ⟨917734414166041868521201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4894583542218889965446405 917734414166041868521201)
              ·
                refine ⟨688300810624531401390901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 917734414166041868521201 688300810624531401390901)
                ·
                  refine ⟨64528200996049818880397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 688300810624531401390901 64528200996049818880397)
                  ·
                    rfl

theorem cell22_565507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 2, 5].length) (baseStart_565507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_565507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_565507 prefixEnd_565507 := by exact prefixLift 565507
  have htrace : WordTrace (prefixWord ++ tailWord_565507) baseStart_565507 baseEnd_565507 := by
    simpa [prefixWord, tailWord_565507, baseEnd_565507] using wordTrace_append hprefix tailTrace_565507
  have hstable : (prefixWord ++ tailWord_565507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565507).length < 2 ^ (prefixWord ++ tailWord_565507).sum := by decide
  have hdescent : baseEnd_565507 < baseStart_565507 := by decide
  rcases family_descends (prefixWord ++ tailWord_565507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565537 : List Nat := [1, 2, 3, 2, 1, 1, 4, 1, 3, 4]
def baseStart_565537 : Nat := 118140960795 + 565537 * 2 ^ 59
def prefixEnd_565537 : Nat := 4983230072969 + 3 ^ 40 * 565537 * 2
def baseEnd_565537 : Nat := 193594872601239378391099

theorem tailTrace_565537 : CollatzResearch.WordTrace tailWord_565537 prefixEnd_565537 193594872601239378391099 := by
  unfold tailWord_565537
  simp only [CollatzResearch.WordTrace]
  refine ⟨20626828952163509875102865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13751219301442339916735243 20626828952163509875102865)
  ·
    refine ⟨15470121714122632406327149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20626828952163509875102865 15470121714122632406327149)
    ·
      refine ⟨5801295642795987152372681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15470121714122632406327149 5801295642795987152372681)
      ·
        refine ⟨4350971732096990364279511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5801295642795987152372681 4350971732096990364279511)
        ·
          refine ⟨6526457598145485546419267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4350971732096990364279511 6526457598145485546419267)
          ·
            refine ⟨9789686397218228319628901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6526457598145485546419267 9789686397218228319628901)
            ·
              refine ⟨1835566199478417809930419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9789686397218228319628901 1835566199478417809930419)
              ·
                refine ⟨2753349299217626714895629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1835566199478417809930419 2753349299217626714895629)
                ·
                  refine ⟨1032505987206610018085861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2753349299217626714895629 1032505987206610018085861)
                  ·
                    refine ⟨193594872601239378391099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1032505987206610018085861 193594872601239378391099)
                    ·
                      rfl

theorem cell22_565537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_565537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_565537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_565537 prefixEnd_565537 := by exact prefixLift 565537
  have htrace : WordTrace (prefixWord ++ tailWord_565537) baseStart_565537 baseEnd_565537 := by
    simpa [prefixWord, tailWord_565537, baseEnd_565537] using wordTrace_append hprefix tailTrace_565537
  have hstable : (prefixWord ++ tailWord_565537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565537).length < 2 ^ (prefixWord ++ tailWord_565537).sum := by decide
  have hdescent : baseEnd_565537 < baseStart_565537 := by decide
  rcases family_descends (prefixWord ++ tailWord_565537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565582 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 6, 4]
def baseStart_565582 : Nat := 118140960795 + 565582 * 2 ^ 59
def prefixEnd_565582 : Nat := 4983230072969 + 3 ^ 40 * 565582 * 2
def baseEnd_565582 : Nat := 193610277020874261015961

theorem tailTrace_565582 : CollatzResearch.WordTrace tailWord_565582 prefixEnd_565582 193610277020874261015961 := by
  unfold tailWord_565582
  simp only [CollatzResearch.WordTrace]
  refine ⟨2578558779625060320061375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13752313491333655040327333 2578558779625060320061375)
  ·
    refine ⟨3867838169437590480092063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2578558779625060320061375 3867838169437590480092063)
    ·
      refine ⟨5801757254156385720138095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3867838169437590480092063 5801757254156385720138095)
      ·
        refine ⟨8702635881234578580207143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5801757254156385720138095 8702635881234578580207143)
        ·
          refine ⟨13053953821851867870310715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8702635881234578580207143 13053953821851867870310715)
          ·
            refine ⟨19580930732777801805466073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13053953821851867870310715 19580930732777801805466073)
            ·
              refine ⟨14685698049583351354099555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19580930732777801805466073 14685698049583351354099555)
              ·
                refine ⟨22028547074375027031149333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14685698049583351354099555 22028547074375027031149333)
                ·
                  refine ⟨1032588144111329392085125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 22028547074375027031149333 1032588144111329392085125)
                  ·
                    refine ⟨193610277020874261015961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1032588144111329392085125 193610277020874261015961)
                    ·
                      rfl

theorem cell22_565582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_565582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_565582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_565582 prefixEnd_565582 := by exact prefixLift 565582
  have htrace : WordTrace (prefixWord ++ tailWord_565582) baseStart_565582 baseEnd_565582 := by
    simpa [prefixWord, tailWord_565582, baseEnd_565582] using wordTrace_append hprefix tailTrace_565582
  have hstable : (prefixWord ++ tailWord_565582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565582).length < 2 ^ (prefixWord ++ tailWord_565582).sum := by decide
  have hdescent : baseEnd_565582 < baseStart_565582 := by decide
  rcases family_descends (prefixWord ++ tailWord_565582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565584 : List Nat := [2, 1, 1, 1, 1, 8, 1, 1, 1, 5]
def baseStart_565584 : Nat := 118140960795 + 565584 * 2 ^ 59
def prefixEnd_565584 : Nat := 4983230072969 + 3 ^ 40 * 565584 * 2
def baseEnd_565584 : Nat := 193610961661746922465955

theorem tailTrace_565584 : CollatzResearch.WordTrace tailWord_565584 prefixEnd_565584 193610961661746922465955 := by
  unfold tailWord_565584
  simp only [CollatzResearch.WordTrace]
  refine ⟨10314271591496618451031903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13752362121995491268042537 10314271591496618451031903)
  ·
    refine ⟨15471407387244927676547855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10314271591496618451031903 15471407387244927676547855)
    ·
      refine ⟨23207111080867391514821783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15471407387244927676547855 23207111080867391514821783)
      ·
        refine ⟨34810666621301087272232675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23207111080867391514821783 34810666621301087272232675)
        ·
          refine ⟨52215999931951630908349013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34810666621301087272232675 52215999931951630908349013)
          ·
            refine ⟨611906249202558174707215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 52215999931951630908349013 611906249202558174707215)
            ·
              refine ⟨917859373803837262060823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 611906249202558174707215 917859373803837262060823)
              ·
                refine ⟨1376789060705755893091235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 917859373803837262060823 1376789060705755893091235)
                ·
                  refine ⟨2065183591058633839636853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1376789060705755893091235 2065183591058633839636853)
                  ·
                    refine ⟨193610961661746922465955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2065183591058633839636853 193610961661746922465955)
                    ·
                      rfl

theorem cell22_565584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 1, 5].length) (baseStart_565584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_565584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_565584 prefixEnd_565584 := by exact prefixLift 565584
  have htrace : WordTrace (prefixWord ++ tailWord_565584) baseStart_565584 baseEnd_565584 := by
    simpa [prefixWord, tailWord_565584, baseEnd_565584] using wordTrace_append hprefix tailTrace_565584
  have hstable : (prefixWord ++ tailWord_565584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565584).length < 2 ^ (prefixWord ++ tailWord_565584).sum := by decide
  have hdescent : baseEnd_565584 < baseStart_565584 := by decide
  rcases family_descends (prefixWord ++ tailWord_565584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565635 : List Nat := [1, 1, 1, 3, 7, 1, 2, 1, 2, 3]
def baseStart_565635 : Nat := 118140960795 + 565635 * 2 ^ 59
def prefixEnd_565635 : Nat := 4983230072969 + 3 ^ 40 * 565635 * 2
def baseEnd_565635 : Nat := 193628420003999789440799

theorem tailTrace_565635 : CollatzResearch.WordTrace tailWord_565635 prefixEnd_565635 193628420003999789440799 := by
  unfold tailWord_565635
  simp only [CollatzResearch.WordTrace]
  refine ⟨20630403305808472612170359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13753602203872315074780239 20630403305808472612170359)
  ·
    refine ⟨30945604958712708918255539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20630403305808472612170359 30945604958712708918255539)
    ·
      refine ⟨46418407438069063377383309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30945604958712708918255539 46418407438069063377383309)
      ·
        refine ⟨17406902789275898766518741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46418407438069063377383309 17406902789275898766518741)
        ·
          refine ⟨407974284123653877340283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 17406902789275898766518741 407974284123653877340283)
          ·
            refine ⟨611961426185480816010425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407974284123653877340283 611961426185480816010425)
            ·
              refine ⟨458971069639110612007819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 611961426185480816010425 458971069639110612007819)
              ·
                refine ⟨688456604458665918011729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 458971069639110612007819 688456604458665918011729)
                ·
                  refine ⟨516342453343999438508797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 688456604458665918011729 516342453343999438508797)
                  ·
                    refine ⟨193628420003999789440799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 516342453343999438508797 193628420003999789440799)
                    ·
                      rfl

theorem cell22_565635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 1, 2, 3].length) (baseStart_565635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_565635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_565635 prefixEnd_565635 := by exact prefixLift 565635
  have htrace : WordTrace (prefixWord ++ tailWord_565635) baseStart_565635 baseEnd_565635 := by
    simpa [prefixWord, tailWord_565635, baseEnd_565635] using wordTrace_append hprefix tailTrace_565635
  have hstable : (prefixWord ++ tailWord_565635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565635).length < 2 ^ (prefixWord ++ tailWord_565635).sum := by decide
  have hdescent : baseEnd_565635 < baseStart_565635 := by decide
  rcases family_descends (prefixWord ++ tailWord_565635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565689 : List Nat := [1, 2, 1, 4, 3, 1, 1, 2, 3, 4]
def baseStart_565689 : Nat := 118140960795 + 565689 * 2 ^ 59
def prefixEnd_565689 : Nat := 4983230072969 + 3 ^ 40 * 565689 * 2
def baseEnd_565689 : Nat := 193646905307561648590633

theorem tailTrace_565689 : CollatzResearch.WordTrace tailWord_565689 prefixEnd_565689 193646905307561648590633 := by
  unfold tailWord_565689
  simp only [CollatzResearch.WordTrace]
  refine ⟨20632372847612839834636121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13754915231741893223090747 20632372847612839834636121)
  ·
    refine ⟨15474279635709629875977091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20632372847612839834636121 15474279635709629875977091)
    ·
      refine ⟨23211419453564444813965637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15474279635709629875977091 23211419453564444813965637)
      ·
        refine ⟨4352141147543333402618557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23211419453564444813965637 4352141147543333402618557)
        ·
          refine ⟨1632052930328750025981959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4352141147543333402618557 1632052930328750025981959)
          ·
            refine ⟨2448079395493125038972939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1632052930328750025981959 2448079395493125038972939)
            ·
              refine ⟨3672119093239687558459409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2448079395493125038972939 3672119093239687558459409)
              ·
                refine ⟨2754089319929765668844557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3672119093239687558459409 2754089319929765668844557)
                ·
                  refine ⟨1032783494973662125816709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2754089319929765668844557 1032783494973662125816709)
                  ·
                    refine ⟨193646905307561648590633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1032783494973662125816709 193646905307561648590633)
                    ·
                      rfl

theorem cell22_565689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 3, 4].length) (baseStart_565689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_565689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_565689 prefixEnd_565689 := by exact prefixLift 565689
  have htrace : WordTrace (prefixWord ++ tailWord_565689) baseStart_565689 baseEnd_565689 := by
    simpa [prefixWord, tailWord_565689, baseEnd_565689] using wordTrace_append hprefix tailTrace_565689
  have hstable : (prefixWord ++ tailWord_565689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565689).length < 2 ^ (prefixWord ++ tailWord_565689).sum := by decide
  have hdescent : baseEnd_565689 < baseStart_565689 := by decide
  rcases family_descends (prefixWord ++ tailWord_565689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565704 : List Nat := [2, 1, 3, 1, 3, 3, 1, 2, 6]
def baseStart_565704 : Nat := 118140960795 + 565704 * 2 ^ 59
def prefixEnd_565704 : Nat := 4983230072969 + 3 ^ 40 * 565704 * 2
def baseEnd_565704 : Nat := 64550680038035536488529

theorem tailTrace_565704 : CollatzResearch.WordTrace tailWord_565704 prefixEnd_565704 64550680038035536488529 := by
  unfold tailWord_565704
  simp only [CollatzResearch.WordTrace]
  refine ⟨10316459971279248698216083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13755279961705664930954777 10316459971279248698216083)
  ·
    refine ⟨15474689956918873047324125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10316459971279248698216083 15474689956918873047324125)
    ·
      refine ⟨5803008733844577392746547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15474689956918873047324125 5803008733844577392746547)
      ·
        refine ⟨8704513100766866089119821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5803008733844577392746547 8704513100766866089119821)
        ·
          refine ⟨3264192412787574783419933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8704513100766866089119821 3264192412787574783419933)
          ·
            refine ⟨1224072154795340543782475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3264192412787574783419933 1224072154795340543782475)
            ·
              refine ⟨1836108232193010815673713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1224072154795340543782475 1836108232193010815673713)
              ·
                refine ⟨1377081174144758111755285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1836108232193010815673713 1377081174144758111755285)
                ·
                  refine ⟨64550680038035536488529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1377081174144758111755285 64550680038035536488529)
                  ·
                    rfl

theorem cell22_565704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 6].length) (baseStart_565704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_565704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_565704 prefixEnd_565704 := by exact prefixLift 565704
  have htrace : WordTrace (prefixWord ++ tailWord_565704) baseStart_565704 baseEnd_565704 := by
    simpa [prefixWord, tailWord_565704, baseEnd_565704] using wordTrace_append hprefix tailTrace_565704
  have hstable : (prefixWord ++ tailWord_565704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565704).length < 2 ^ (prefixWord ++ tailWord_565704).sum := by decide
  have hdescent : baseEnd_565704 < baseStart_565704 := by decide
  rcases family_descends (prefixWord ++ tailWord_565704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565721 : List Nat := [1, 2, 1, 2, 4, 1, 4, 3, 4]
def baseStart_565721 : Nat := 118140960795 + 565721 * 2 ^ 59
def prefixEnd_565721 : Nat := 4983230072969 + 3 ^ 40 * 565721 * 2
def baseEnd_565721 : Nat := 64552619853841410596845

theorem tailTrace_565721 : CollatzResearch.WordTrace tailWord_565721 prefixEnd_565721 64552619853841410596845 := by
  unfold tailWord_565721
  simp only [CollatzResearch.WordTrace]
  refine ⟨20633539983496909299801017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13755693322331272866534011 20633539983496909299801017)
  ·
    refine ⟨15475154987622681974850763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20633539983496909299801017 15475154987622681974850763)
    ·
      refine ⟨23212732481434022962276145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15475154987622681974850763 23212732481434022962276145)
      ·
        refine ⟨17409549361075517221707109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23212732481434022962276145 17409549361075517221707109)
        ·
          refine ⟨3264290505201659479070083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17409549361075517221707109 3264290505201659479070083)
          ·
            refine ⟨4896435757802489218605125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3264290505201659479070083 4896435757802489218605125)
            ·
              refine ⟨918081704587966728488461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4896435757802489218605125 918081704587966728488461)
              ·
                refine ⟨344280639220487523183173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 918081704587966728488461 344280639220487523183173)
                ·
                  refine ⟨64552619853841410596845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 344280639220487523183173 64552619853841410596845)
                  ·
                    rfl

theorem cell22_565721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 3, 4].length) (baseStart_565721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_565721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_565721 prefixEnd_565721 := by exact prefixLift 565721
  have htrace : WordTrace (prefixWord ++ tailWord_565721) baseStart_565721 baseEnd_565721 := by
    simpa [prefixWord, tailWord_565721, baseEnd_565721] using wordTrace_append hprefix tailTrace_565721
  have hstable : (prefixWord ++ tailWord_565721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565721).length < 2 ^ (prefixWord ++ tailWord_565721).sum := by decide
  have hdescent : baseEnd_565721 < baseStart_565721 := by decide
  rcases family_descends (prefixWord ++ tailWord_565721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565736 : List Nat := [2, 1, 4, 1, 1, 4, 1, 1, 4, 3]
def baseStart_565736 : Nat := 118140960795 + 565736 * 2 ^ 59
def prefixEnd_565736 : Nat := 4983230072969 + 3 ^ 40 * 565736 * 2
def baseEnd_565736 : Nat := 193662994368069192665489

theorem tailTrace_565736 : CollatzResearch.WordTrace tailWord_565736 prefixEnd_565736 193662994368069192665489 := by
  unfold tailWord_565736
  simp only [CollatzResearch.WordTrace]
  refine ⟨10317043539221283430798531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13756058052295044574398041 10317043539221283430798531)
  ·
    refine ⟨15475565308831925146197797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10317043539221283430798531 15475565308831925146197797)
    ·
      refine ⟨2901668495405985964912087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15475565308831925146197797 2901668495405985964912087)
      ·
        refine ⟨4352502743108978947368131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2901668495405985964912087 4352502743108978947368131)
        ·
          refine ⟨6528754114663468421052197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4352502743108978947368131 6528754114663468421052197)
          ·
            refine ⟨1224141396499400328947287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6528754114663468421052197 1224141396499400328947287)
            ·
              refine ⟨1836212094749100493420931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1224141396499400328947287 1836212094749100493420931)
              ·
                refine ⟨2754318142123650740131397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1836212094749100493420931 2754318142123650740131397)
                ·
                  refine ⟨516434651648184513774637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2754318142123650740131397 516434651648184513774637)
                  ·
                    refine ⟨193662994368069192665489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 516434651648184513774637 193662994368069192665489)
                    ·
                      rfl

theorem cell22_565736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_565736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_565736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_565736 prefixEnd_565736 := by exact prefixLift 565736
  have htrace : WordTrace (prefixWord ++ tailWord_565736) baseStart_565736 baseEnd_565736 := by
    simpa [prefixWord, tailWord_565736, baseEnd_565736] using wordTrace_append hprefix tailTrace_565736
  have hstable : (prefixWord ++ tailWord_565736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565736).length < 2 ^ (prefixWord ++ tailWord_565736).sum := by decide
  have hdescent : baseEnd_565736 < baseStart_565736 := by decide
  rcases family_descends (prefixWord ++ tailWord_565736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565783 : List Nat := [1, 1, 3, 6, 2, 1, 8]
def baseStart_565783 : Nat := 118140960795 + 565783 * 2 ^ 59
def prefixEnd_565783 : Nat := 4983230072969 + 3 ^ 40 * 565783 * 2
def baseEnd_565783 : Nat := 7173299386243582842235

theorem tailTrace_565783 : CollatzResearch.WordTrace tailWord_565783 prefixEnd_565783 7173299386243582842235 := by
  unfold tailWord_565783
  simp only [CollatzResearch.WordTrace]
  refine ⟨20635801309272293888558003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13757200872848195925705335 20635801309272293888558003)
  ·
    refine ⟨30953701963908440832837005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20635801309272293888558003 30953701963908440832837005)
    ·
      refine ⟨11607638236465665312313877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30953701963908440832837005 11607638236465665312313877)
      ·
        refine ⟨544108042334328061514713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11607638236465665312313877 544108042334328061514713)
        ·
          refine ⟨408081031750746046136035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 544108042334328061514713 408081031750746046136035)
          ·
            refine ⟨612121547626119069204053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408081031750746046136035 612121547626119069204053)
            ·
              refine ⟨7173299386243582842235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 612121547626119069204053 7173299386243582842235)
              ·
                rfl

theorem cell22_565783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 8].length) (baseStart_565783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_565783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_565783 prefixEnd_565783 := by exact prefixLift 565783
  have htrace : WordTrace (prefixWord ++ tailWord_565783) baseStart_565783 baseEnd_565783 := by
    simpa [prefixWord, tailWord_565783, baseEnd_565783] using wordTrace_append hprefix tailTrace_565783
  have hstable : (prefixWord ++ tailWord_565783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565783).length < 2 ^ (prefixWord ++ tailWord_565783).sum := by decide
  have hdescent : baseEnd_565783 < baseStart_565783 := by decide
  rcases family_descends (prefixWord ++ tailWord_565783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565809 : List Nat := [1, 2, 2, 3, 1, 1, 2, 3, 2, 5]
def baseStart_565809 : Nat := 118140960795 + 565809 * 2 ^ 59
def prefixEnd_565809 : Nat := 4983230072969 + 3 ^ 40 * 565809 * 2
def baseEnd_565809 : Nat := 193687983759921335590265

theorem tailTrace_565809 : CollatzResearch.WordTrace tailWord_565809 prefixEnd_565809 193687983759921335590265 := by
  unfold tailWord_565809
  simp only [CollatzResearch.WordTrace]
  refine ⟨20636749607178100329004481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13757833071452066886002987 20636749607178100329004481)
  ·
    refine ⟨15477562205383575246753361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20636749607178100329004481 15477562205383575246753361)
    ·
      refine ⟨11608171654037681435065021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15477562205383575246753361 11608171654037681435065021)
      ·
        refine ⟨4353064370264130538149383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11608171654037681435065021 4353064370264130538149383)
        ·
          refine ⟨6529596555396195807224075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4353064370264130538149383 6529596555396195807224075)
          ·
            refine ⟨9794394833094293710836113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6529596555396195807224075 9794394833094293710836113)
            ·
              refine ⟨7345796124820720283127085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9794394833094293710836113 7345796124820720283127085)
              ·
                refine ⟨2754673546807770106172657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7345796124820720283127085 2754673546807770106172657)
                ·
                  refine ⟨2066005160105827579629493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2754673546807770106172657 2066005160105827579629493)
                  ·
                    refine ⟨193687983759921335590265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2066005160105827579629493 193687983759921335590265)
                    ·
                      rfl

theorem cell22_565809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_565809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_565809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_565809 prefixEnd_565809 := by exact prefixLift 565809
  have htrace : WordTrace (prefixWord ++ tailWord_565809) baseStart_565809 baseEnd_565809 := by
    simpa [prefixWord, tailWord_565809, baseEnd_565809] using wordTrace_append hprefix tailTrace_565809
  have hstable : (prefixWord ++ tailWord_565809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565809).length < 2 ^ (prefixWord ++ tailWord_565809).sum := by decide
  have hdescent : baseEnd_565809 < baseStart_565809 := by decide
  rcases family_descends (prefixWord ++ tailWord_565809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565884 : List Nat := [2, 2, 2, 1, 1, 2, 2, 10]
def baseStart_565884 : Nat := 118140960795 + 565884 * 2 ^ 59
def prefixEnd_565884 : Nat := 4983230072969 + 3 ^ 40 * 565884 * 2
def baseEnd_565884 : Nat := 21523739754738459996115

theorem tailTrace_565884 : CollatzResearch.WordTrace tailWord_565884 prefixEnd_565884 21523739754738459996115 := by
  unfold tailWord_565884
  simp only [CollatzResearch.WordTrace]
  refine ⟨10319742540953194068992353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13759656721270925425323137 10319742540953194068992353)
  ·
    refine ⟨7739806905714895551744265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10319742540953194068992353 7739806905714895551744265)
    ·
      refine ⟨5804855179286171663808199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7739806905714895551744265 5804855179286171663808199)
      ·
        refine ⟨8707282768929257495712299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5804855179286171663808199 8707282768929257495712299)
        ·
          refine ⟨13060924153393886243568449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8707282768929257495712299 13060924153393886243568449)
          ·
            refine ⟨9795693115045414682676337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13060924153393886243568449 9795693115045414682676337)
            ·
              refine ⟨7346769836284061012007253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9795693115045414682676337 7346769836284061012007253)
              ·
                refine ⟨21523739754738459996115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 7346769836284061012007253 21523739754738459996115)
                ·
                  rfl

theorem cell22_565884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 10].length) (baseStart_565884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_565884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_565884 prefixEnd_565884 := by exact prefixLift 565884
  have htrace : WordTrace (prefixWord ++ tailWord_565884) baseStart_565884 baseEnd_565884 := by
    simpa [prefixWord, tailWord_565884, baseEnd_565884] using wordTrace_append hprefix tailTrace_565884
  have hstable : (prefixWord ++ tailWord_565884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565884).length < 2 ^ (prefixWord ++ tailWord_565884).sum := by decide
  have hdescent : baseEnd_565884 < baseStart_565884 := by decide
  rcases family_descends (prefixWord ++ tailWord_565884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565929 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 9]
def baseStart_565929 : Nat := 118140960795 + 565929 * 2 ^ 59
def prefixEnd_565929 : Nat := 4983230072969 + 3 ^ 40 * 565929 * 2
def baseEnd_565929 : Nat := 64576354070760340863299

theorem tailTrace_565929 : CollatzResearch.WordTrace tailWord_565929 prefixEnd_565929 64576354070760340863299 := by
  unfold tailWord_565929
  simp only [CollatzResearch.WordTrace]
  refine ⟨20641126366743360823372841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13760750911162240548915227 20641126366743360823372841)
  ·
    refine ⟨15480844775057520617529631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20641126366743360823372841 15480844775057520617529631)
    ·
      refine ⟨23221267162586280926294447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15480844775057520617529631 23221267162586280926294447)
      ·
        refine ⟨34831900743879421389441671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23221267162586280926294447 34831900743879421389441671)
        ·
          refine ⟨52247851115819132084162507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34831900743879421389441671 52247851115819132084162507)
          ·
            refine ⟨78371776673728698126243761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52247851115819132084162507 78371776673728698126243761)
            ·
              refine ⟨58778832505296523594682821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78371776673728698126243761 58778832505296523594682821)
              ·
                refine ⟨11021031094743098174003029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58778832505296523594682821 11021031094743098174003029)
                ·
                  refine ⟨64576354070760340863299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 11021031094743098174003029 64576354070760340863299)
                  ·
                    rfl

theorem cell22_565929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 9].length) (baseStart_565929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_565929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_565929 prefixEnd_565929 := by exact prefixLift 565929
  have htrace : WordTrace (prefixWord ++ tailWord_565929) baseStart_565929 baseEnd_565929 := by
    simpa [prefixWord, tailWord_565929, baseEnd_565929] using wordTrace_append hprefix tailTrace_565929
  have hstable : (prefixWord ++ tailWord_565929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565929).length < 2 ^ (prefixWord ++ tailWord_565929).sum := by decide
  have hdescent : baseEnd_565929 < baseStart_565929 := by decide
  rcases family_descends (prefixWord ++ tailWord_565929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565980 : List Nat := [2, 2, 5, 1, 1, 2, 1, 3, 5]
def baseStart_565980 : Nat := 118140960795 + 565980 * 2 ^ 59
def prefixEnd_565980 : Nat := 4983230072969 + 3 ^ 40 * 565980 * 2
def baseEnd_565980 : Nat := 64582173518177963188247

theorem tailTrace_565980 : CollatzResearch.WordTrace tailWord_565980 prefixEnd_565980 64582173518177963188247 := by
  unfold tailWord_565980
  simp only [CollatzResearch.WordTrace]
  refine ⟨10321493244779298266739697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13761990993039064355652929 10321493244779298266739697)
  ·
    refine ⟨7741119933584473700054773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10321493244779298266739697 7741119933584473700054773)
    ·
      refine ⟨725729993773544409380135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7741119933584473700054773 725729993773544409380135)
      ·
        refine ⟨1088594990660316614070203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 725729993773544409380135 1088594990660316614070203)
        ·
          refine ⟨1632892485990474921105305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1088594990660316614070203 1632892485990474921105305)
          ·
            refine ⟨1224669364492856190828979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1632892485990474921105305 1224669364492856190828979)
            ·
              refine ⟨1837004046739284286243469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1224669364492856190828979 1837004046739284286243469)
              ·
                refine ⟨688876517527231607341301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1837004046739284286243469 688876517527231607341301)
                ·
                  refine ⟨64582173518177963188247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 688876517527231607341301 64582173518177963188247)
                  ·
                    rfl

theorem cell22_565980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 3, 5].length) (baseStart_565980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_565980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_565980 prefixEnd_565980 := by exact prefixLift 565980
  have htrace : WordTrace (prefixWord ++ tailWord_565980) baseStart_565980 baseEnd_565980 := by
    simpa [prefixWord, tailWord_565980, baseEnd_565980] using wordTrace_append hprefix tailTrace_565980
  have hstable : (prefixWord ++ tailWord_565980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565980).length < 2 ^ (prefixWord ++ tailWord_565980).sum := by decide
  have hdescent : baseEnd_565980 < baseStart_565980 := by decide
  rcases family_descends (prefixWord ++ tailWord_565980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565993 : List Nat := [1, 2, 1, 1, 1, 2, 7, 2, 1, 4]
def baseStart_565993 : Nat := 118140960795 + 565993 * 2 ^ 59
def prefixEnd_565993 : Nat := 4983230072969 + 3 ^ 40 * 565993 * 2
def baseEnd_565993 : Nat := 193750970720206188989701

theorem tailTrace_565993 : CollatzResearch.WordTrace tailWord_565993 prefixEnd_565993 193750970720206188989701 := by
  unfold tailWord_565993
  simp only [CollatzResearch.WordTrace]
  refine ⟨20643460638511499753702633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13762307092340999835801755 20643460638511499753702633)
  ·
    refine ⟨15482595478883624815276975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20643460638511499753702633 15482595478883624815276975)
    ·
      refine ⟨23223893218325437222915463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15482595478883624815276975 23223893218325437222915463)
      ·
        refine ⟨34835839827488155834373195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23223893218325437222915463 34835839827488155834373195)
        ·
          refine ⟨52253759741232233751559793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34835839827488155834373195 52253759741232233751559793)
          ·
            refine ⟨39190319805924175313669845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52253759741232233751559793 39190319805924175313669845)
            ·
              refine ⟨918523120451347858914137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 39190319805924175313669845 918523120451347858914137)
              ·
                refine ⟨688892340338510894185603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 918523120451347858914137 688892340338510894185603)
                ·
                  refine ⟨1033338510507766341278405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 688892340338510894185603 1033338510507766341278405)
                  ·
                    refine ⟨193750970720206188989701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1033338510507766341278405 193750970720206188989701)
                    ·
                      rfl

theorem cell22_565993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 2, 1, 4].length) (baseStart_565993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_565993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_565993 prefixEnd_565993 := by exact prefixLift 565993
  have htrace : WordTrace (prefixWord ++ tailWord_565993) baseStart_565993 baseEnd_565993 := by
    simpa [prefixWord, tailWord_565993, baseEnd_565993] using wordTrace_append hprefix tailTrace_565993
  have hstable : (prefixWord ++ tailWord_565993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565993).length < 2 ^ (prefixWord ++ tailWord_565993).sum := by decide
  have hdescent : baseEnd_565993 < baseStart_565993 := by decide
  rcases family_descends (prefixWord ++ tailWord_565993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566008 : List Nat := [2, 1, 2, 1, 1, 2, 4, 5, 4]
def baseStart_566008 : Nat := 118140960795 + 566008 * 2 ^ 59
def prefixEnd_566008 : Nat := 4983230072969 + 3 ^ 40 * 566008 * 2
def baseEnd_566008 : Nat := 64585368508917049954885

theorem tailTrace_566008 : CollatzResearch.WordTrace tailWord_566008 prefixEnd_566008 64585368508917049954885 := by
  unfold tailWord_566008
  simp only [CollatzResearch.WordTrace]
  refine ⟨10322003866728578657749339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13762671822304771543665785 10322003866728578657749339)
  ·
    refine ⟨15483005800092867986624009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10322003866728578657749339 15483005800092867986624009)
    ·
      refine ⟨11612254350069650989968007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15483005800092867986624009 11612254350069650989968007)
      ·
        refine ⟨17418381525104476484952011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11612254350069650989968007 17418381525104476484952011)
        ·
          refine ⟨26127572287656714727428017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17418381525104476484952011 26127572287656714727428017)
          ·
            refine ⟨19595679215742536045571013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26127572287656714727428017 19595679215742536045571013)
            ·
              refine ⟨3674189852951725508544565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19595679215742536045571013 3674189852951725508544565)
              ·
                refine ⟨344455298714224266426053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3674189852951725508544565 344455298714224266426053)
                ·
                  refine ⟨64585368508917049954885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 344455298714224266426053 64585368508917049954885)
                  ·
                    rfl

theorem cell22_566008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 5, 4].length) (baseStart_566008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_566008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_566008 prefixEnd_566008 := by exact prefixLift 566008
  have htrace : WordTrace (prefixWord ++ tailWord_566008) baseStart_566008 baseEnd_566008 := by
    simpa [prefixWord, tailWord_566008, baseEnd_566008] using wordTrace_append hprefix tailTrace_566008
  have hstable : (prefixWord ++ tailWord_566008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566008).length < 2 ^ (prefixWord ++ tailWord_566008).sum := by decide
  have hdescent : baseEnd_566008 < baseStart_566008 := by decide
  rcases family_descends (prefixWord ++ tailWord_566008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566025 : List Nat := [1, 2, 1, 1, 3, 2, 6, 2, 4]
def baseStart_566025 : Nat := 118140960795 + 566025 * 2 ^ 59
def prefixEnd_566025 : Nat := 4983230072969 + 3 ^ 40 * 566025 * 2
def baseEnd_566025 : Nat := 64587308324722924063201

theorem tailTrace_566025 : CollatzResearch.WordTrace tailWord_566025 prefixEnd_566025 64587308324722924063201 := by
  unfold tailWord_566025
  simp only [CollatzResearch.WordTrace]
  refine ⟨20644627774395569218867529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13763085182930379479245019 20644627774395569218867529)
  ·
    refine ⟨15483470830796676914150647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20644627774395569218867529 15483470830796676914150647)
    ·
      refine ⟨23225206246195015371225971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15483470830796676914150647 23225206246195015371225971)
      ·
        refine ⟨34837809369292523056838957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23225206246195015371225971 34837809369292523056838957)
        ·
          refine ⟨13064178513484696146314609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34837809369292523056838957 13064178513484696146314609)
          ·
            refine ⟨9798133885113522109735957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13064178513484696146314609 9798133885113522109735957)
            ·
              refine ⟨459287525864696348893873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9798133885113522109735957 459287525864696348893873)
              ·
                refine ⟨344465644398522261670405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 459287525864696348893873 344465644398522261670405)
                ·
                  refine ⟨64587308324722924063201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 344465644398522261670405 64587308324722924063201)
                  ·
                    rfl

theorem cell22_566025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 2, 4].length) (baseStart_566025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_566025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_566025 prefixEnd_566025 := by exact prefixLift 566025
  have htrace : WordTrace (prefixWord ++ tailWord_566025) baseStart_566025 baseEnd_566025 := by
    simpa [prefixWord, tailWord_566025, baseEnd_566025] using wordTrace_append hprefix tailTrace_566025
  have hstable : (prefixWord ++ tailWord_566025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566025).length < 2 ^ (prefixWord ++ tailWord_566025).sum := by decide
  have hdescent : baseEnd_566025 < baseStart_566025 := by decide
  rcases family_descends (prefixWord ++ tailWord_566025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566053 : List Nat := [1, 3, 1, 2, 3, 1, 5, 6]
def baseStart_566053 : Nat := 118140960795 + 566053 * 2 ^ 59
def prefixEnd_566053 : Nat := 4983230072969 + 3 ^ 40 * 566053 * 2
def baseEnd_566053 : Nat := 21530167771820670276613

theorem tailTrace_566053 : CollatzResearch.WordTrace tailWord_566053 prefixEnd_566053 21530167771820670276613 := by
  unfold tailWord_566053
  simp only [CollatzResearch.WordTrace]
  refine ⟨20645649018294130000886813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13763766012196086667257875 20645649018294130000886813)
  ·
    refine ⟨7742118381860298750332555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20645649018294130000886813 7742118381860298750332555)
    ·
      refine ⟨11613177572790448125498833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7742118381860298750332555 11613177572790448125498833)
      ·
        refine ⟨8709883179592836094124125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11613177572790448125498833 8709883179592836094124125)
        ·
          refine ⟨3266206192347313535296547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8709883179592836094124125 3266206192347313535296547)
          ·
            refine ⟨4899309288520970302944821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3266206192347313535296547 4899309288520970302944821)
            ·
              refine ⟨459310245798840965901077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4899309288520970302944821 459310245798840965901077)
              ·
                refine ⟨21530167771820670276613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 459310245798840965901077 21530167771820670276613)
                ·
                  rfl

theorem cell22_566053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 6].length) (baseStart_566053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_566053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_566053 prefixEnd_566053 := by exact prefixLift 566053
  have htrace : WordTrace (prefixWord ++ tailWord_566053) baseStart_566053 baseEnd_566053 := by
    simpa [prefixWord, tailWord_566053, baseEnd_566053] using wordTrace_append hprefix tailTrace_566053
  have hstable : (prefixWord ++ tailWord_566053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566053).length < 2 ^ (prefixWord ++ tailWord_566053).sum := by decide
  have hdescent : baseEnd_566053 < baseStart_566053 := by decide
  rcases family_descends (prefixWord ++ tailWord_566053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566061 : List Nat := [1, 5, 3, 2, 1, 2, 2, 1, 1, 4]
def baseStart_566061 : Nat := 118140960795 + 566061 * 2 ^ 59
def prefixEnd_566061 : Nat := 4983230072969 + 3 ^ 40 * 566061 * 2
def baseEnd_566061 : Nat := 193774248509876678289493

theorem tailTrace_566061 : CollatzResearch.WordTrace tailWord_566061 prefixEnd_566061 193774248509876678289493 := by
  unfold tailWord_566061
  simp only [CollatzResearch.WordTrace]
  refine ⟨20645940802265147367178037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13763960534843431578118691 20645940802265147367178037)
  ·
    refine ⟨1935556950212357565672941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20645940802265147367178037 1935556950212357565672941)
    ·
      refine ⟨725833856329634087127353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1935556950212357565672941 725833856329634087127353)
      ·
        refine ⟨544375392247225565345515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 725833856329634087127353 544375392247225565345515)
        ·
          refine ⟨816563088370838348018273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 544375392247225565345515 816563088370838348018273)
          ·
            refine ⟨612422316278128761013705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 816563088370838348018273 612422316278128761013705)
            ·
              refine ⟨459316737208596570760279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 612422316278128761013705 459316737208596570760279)
              ·
                refine ⟨688975105812894856140419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 459316737208596570760279 688975105812894856140419)
                ·
                  refine ⟨1033462658719342284210629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 688975105812894856140419 1033462658719342284210629)
                  ·
                    refine ⟨193774248509876678289493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1033462658719342284210629 193774248509876678289493)
                    ·
                      rfl

theorem cell22_566061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_566061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_566061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_566061 prefixEnd_566061 := by exact prefixLift 566061
  have htrace : WordTrace (prefixWord ++ tailWord_566061) baseStart_566061 baseEnd_566061 := by
    simpa [prefixWord, tailWord_566061, baseEnd_566061] using wordTrace_append hprefix tailTrace_566061
  have hstable : (prefixWord ++ tailWord_566061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566061).length < 2 ^ (prefixWord ++ tailWord_566061).sum := by decide
  have hdescent : baseEnd_566061 < baseStart_566061 := by decide
  rcases family_descends (prefixWord ++ tailWord_566061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566070 : List Nat := [5, 1, 2, 2, 2, 1, 9]
def baseStart_566070 : Nat := 118140960795 + 566070 * 2 ^ 59
def prefixEnd_566070 : Nat := 4983230072969 + 3 ^ 40 * 566070 * 2
def baseEnd_566070 : Nat := 7176938125696431659795

theorem tailTrace_566070 : CollatzResearch.WordTrace tailWord_566070 prefixEnd_566070 7176938125696431659795 := by
  unfold tailWord_566070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1290391816202033869015979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13764179372821694602837109 1290391816202033869015979)
  ·
    refine ⟨1935587724303050803523969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1290391816202033869015979 1935587724303050803523969)
    ·
      refine ⟨1451690793227288102642977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1935587724303050803523969 1451690793227288102642977)
      ·
        refine ⟨1088768094920466076982233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1451690793227288102642977 1088768094920466076982233)
        ·
          refine ⟨816576071190349557736675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1088768094920466076982233 816576071190349557736675)
          ·
            refine ⟨1224864106785524336605013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 816576071190349557736675 1224864106785524336605013)
            ·
              refine ⟨7176938125696431659795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1224864106785524336605013 7176938125696431659795)
              ·
                rfl

theorem cell22_566070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 9].length) (baseStart_566070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_566070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_566070 prefixEnd_566070 := by exact prefixLift 566070
  have htrace : WordTrace (prefixWord ++ tailWord_566070) baseStart_566070 baseEnd_566070 := by
    simpa [prefixWord, tailWord_566070, baseEnd_566070] using wordTrace_append hprefix tailTrace_566070
  have hstable : (prefixWord ++ tailWord_566070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566070).length < 2 ^ (prefixWord ++ tailWord_566070).sum := by decide
  have hdescent : baseEnd_566070 < baseStart_566070 := by decide
  rcases family_descends (prefixWord ++ tailWord_566070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566074 : List Nat := [3, 1, 1, 1, 7, 1, 1, 2, 2, 3]
def baseStart_566074 : Nat := 118140960795 + 566074 * 2 ^ 59
def prefixEnd_566074 : Nat := 4983230072969 + 3 ^ 40 * 566074 * 2
def baseEnd_566074 : Nat := 193778698675548977714453

theorem tailTrace_566074 : CollatzResearch.WordTrace tailWord_566074 prefixEnd_566074 193778698675548977714453 := by
  unfold tailWord_566074
  simp only [CollatzResearch.WordTrace]
  refine ⟨5161603737804512646850319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13764276634145367058267517 5161603737804512646850319)
  ·
    refine ⟨7742405606706768970275479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5161603737804512646850319 7742405606706768970275479)
    ·
      refine ⟨11613608410060153455413219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7742405606706768970275479 11613608410060153455413219)
      ·
        refine ⟨17420412615090230183119829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11613608410060153455413219 17420412615090230183119829)
        ·
          refine ⟨408290920666177269916871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 17420412615090230183119829 408290920666177269916871)
          ·
            refine ⟨612436380999265904875307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408290920666177269916871 612436380999265904875307)
            ·
              refine ⟨918654571498898857312961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 612436380999265904875307 918654571498898857312961)
              ·
                refine ⟨688990928624174142984721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 918654571498898857312961 688990928624174142984721)
                ·
                  refine ⟨516743196468130607238541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 688990928624174142984721 516743196468130607238541)
                  ·
                    refine ⟨193778698675548977714453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 516743196468130607238541 193778698675548977714453)
                    ·
                      rfl

theorem cell22_566074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 2, 2, 3].length) (baseStart_566074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_566074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_566074 prefixEnd_566074 := by exact prefixLift 566074
  have htrace : WordTrace (prefixWord ++ tailWord_566074) baseStart_566074 baseEnd_566074 := by
    simpa [prefixWord, tailWord_566074, baseEnd_566074] using wordTrace_append hprefix tailTrace_566074
  have hstable : (prefixWord ++ tailWord_566074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566074).length < 2 ^ (prefixWord ++ tailWord_566074).sum := by decide
  have hdescent : baseEnd_566074 < baseStart_566074 := by decide
  rcases family_descends (prefixWord ++ tailWord_566074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566119 : List Nat := [1, 1, 5, 1, 2, 4, 1, 3, 1, 3]
def baseStart_566119 : Nat := 118140960795 + 566119 * 2 ^ 59
def prefixEnd_566119 : Nat := 4983230072969 + 3 ^ 40 * 566119 * 2
def baseEnd_566119 : Nat := 193794103095183860339315

theorem tailTrace_566119 : CollatzResearch.WordTrace tailWord_566119 prefixEnd_566119 193794103095183860339315 := by
  unfold tailWord_566119
  simp only [CollatzResearch.WordTrace]
  refine ⟨20648056236055023272789411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13765370824036682181859607 20648056236055023272789411)
  ·
    refine ⟨30972084354082534909184117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20648056236055023272789411 30972084354082534909184117)
    ·
      refine ⟨2903632908195237647736011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30972084354082534909184117 2903632908195237647736011)
      ·
        refine ⟨4355449362292856471604017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2903632908195237647736011 4355449362292856471604017)
        ·
          refine ⟨3266587021719642353703013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4355449362292856471604017 3266587021719642353703013)
          ·
            refine ⟨612485066572432941319315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3266587021719642353703013 612485066572432941319315)
            ·
              refine ⟨918727599858649411978973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 612485066572432941319315 918727599858649411978973)
              ·
                refine ⟨344522849946993529492115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 918727599858649411978973 344522849946993529492115)
                ·
                  refine ⟨516784274920490294238173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 344522849946993529492115 516784274920490294238173)
                  ·
                    refine ⟨193794103095183860339315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 516784274920490294238173 193794103095183860339315)
                    ·
                      rfl

theorem cell22_566119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_566119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_566119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_566119 prefixEnd_566119 := by exact prefixLift 566119
  have htrace : WordTrace (prefixWord ++ tailWord_566119) baseStart_566119 baseEnd_566119 := by
    simpa [prefixWord, tailWord_566119, baseEnd_566119] using wordTrace_append hprefix tailTrace_566119
  have hstable : (prefixWord ++ tailWord_566119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566119).length < 2 ^ (prefixWord ++ tailWord_566119).sum := by decide
  have hdescent : baseEnd_566119 < baseStart_566119 := by decide
  rcases family_descends (prefixWord ++ tailWord_566119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566143 : List Nat := [1, 1, 2, 2, 1, 1, 7, 1, 6]
def baseStart_566143 : Nat := 118140960795 + 566143 * 2 ^ 59
def prefixEnd_566143 : Nat := 4983230072969 + 3 ^ 40 * 566143 * 2
def baseEnd_566143 : Nat := 64600772928551932579747

theorem tailTrace_566143 : CollatzResearch.WordTrace tailWord_566143 prefixEnd_566143 64600772928551932579747 := by
  unfold tailWord_566143
  simp only [CollatzResearch.WordTrace]
  refine ⟨20648931587968075371663083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13765954391978716914442055 20648931587968075371663083)
  ·
    refine ⟨30973397381952113057494625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20648931587968075371663083 30973397381952113057494625)
    ·
      refine ⟨23230048036464084793120969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30973397381952113057494625 23230048036464084793120969)
      ·
        refine ⟨17422536027348063594840727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23230048036464084793120969 17422536027348063594840727)
        ·
          refine ⟨26133804041022095392261091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17422536027348063594840727 26133804041022095392261091)
          ·
            refine ⟨39200706061533143088391637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26133804041022095392261091 39200706061533143088391637)
            ·
              refine ⟨918766548317183041134179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 39200706061533143088391637 918766548317183041134179)
              ·
                refine ⟨1378149822475774561701269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 918766548317183041134179 1378149822475774561701269)
                ·
                  refine ⟨64600772928551932579747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1378149822475774561701269 64600772928551932579747)
                  ·
                    rfl

theorem cell22_566143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 6].length) (baseStart_566143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_566143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_566143 prefixEnd_566143 := by exact prefixLift 566143
  have htrace : WordTrace (prefixWord ++ tailWord_566143) baseStart_566143 baseEnd_566143 := by
    simpa [prefixWord, tailWord_566143, baseEnd_566143] using wordTrace_append hprefix tailTrace_566143
  have hstable : (prefixWord ++ tailWord_566143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566143).length < 2 ^ (prefixWord ++ tailWord_566143).sum := by decide
  have hdescent : baseEnd_566143 < baseStart_566143 := by decide
  rcases family_descends (prefixWord ++ tailWord_566143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566162 : List Nat := [3, 2, 3, 2, 2, 1, 1, 1, 3, 4]
def baseStart_566162 : Nat := 118140960795 + 566162 * 2 ^ 59
def prefixEnd_566162 : Nat := 4983230072969 + 3 ^ 40 * 566162 * 2
def baseEnd_566162 : Nat := 193808822873946081514183

theorem tailTrace_566162 : CollatzResearch.WordTrace tailWord_566162 prefixEnd_566162 193808822873946081514183 := by
  unfold tailWord_566162
  simp only [CollatzResearch.WordTrace]
  refine ⟨5162406143724810404151185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13766416383266161077736493 5162406143724810404151185)
  ·
    refine ⟨3871804607793607803113389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5162406143724810404151185 3871804607793607803113389)
    ·
      refine ⟨1451926727922602926167521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3871804607793607803113389 1451926727922602926167521)
      ·
        refine ⟨1088945045941952194625641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1451926727922602926167521 1088945045941952194625641)
        ·
          refine ⟨816708784456464145969231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1088945045941952194625641 816708784456464145969231)
          ·
            refine ⟨1225063176684696218953847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 816708784456464145969231 1225063176684696218953847)
            ·
              refine ⟨1837594765027044328430771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1225063176684696218953847 1837594765027044328430771)
              ·
                refine ⟨2756392147540566492646157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1837594765027044328430771 2756392147540566492646157)
                ·
                  refine ⟨1033647055327712434742309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2756392147540566492646157 1033647055327712434742309)
                  ·
                    refine ⟨193808822873946081514183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1033647055327712434742309 193808822873946081514183)
                    ·
                      rfl

theorem cell22_566162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_566162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_566162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_566162 prefixEnd_566162 := by exact prefixLift 566162
  have htrace : WordTrace (prefixWord ++ tailWord_566162) baseStart_566162 baseEnd_566162 := by
    simpa [prefixWord, tailWord_566162, baseEnd_566162] using wordTrace_append hprefix tailTrace_566162
  have hstable : (prefixWord ++ tailWord_566162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566162).length < 2 ^ (prefixWord ++ tailWord_566162).sum := by decide
  have hdescent : baseEnd_566162 < baseStart_566162 := by decide
  rcases family_descends (prefixWord ++ tailWord_566162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566175 : List Nat := [1, 1, 2, 5, 2, 2, 1, 2, 1, 5]
def baseStart_566175 : Nat := 118140960795 + 566175 * 2 ^ 59
def prefixEnd_566175 : Nat := 4983230072969 + 3 ^ 40 * 566175 * 2
def baseEnd_566175 : Nat := 193813273039618380939143

theorem tailTrace_566175 : CollatzResearch.WordTrace tailWord_566175 prefixEnd_566175 193813273039618380939143 := by
  unfold tailWord_566175
  simp only [CollatzResearch.WordTrace]
  refine ⟨20650098723852144836827979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13766732482568096557885319 20650098723852144836827979)
  ·
    refine ⟨30975148085778217255241969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20650098723852144836827979 30975148085778217255241969)
    ·
      refine ⟨23231361064333662941431477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30975148085778217255241969 23231361064333662941431477)
      ·
        refine ⟨2177940099781280900759201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23231361064333662941431477 2177940099781280900759201)
        ·
          refine ⟨1633455074835960675569401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2177940099781280900759201 1633455074835960675569401)
          ·
            refine ⟨1225091306126970506677051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1633455074835960675569401 1225091306126970506677051)
            ·
              refine ⟨1837636959190455760015577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1225091306126970506677051 1837636959190455760015577)
              ·
                refine ⟨1378227719392841820011683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1837636959190455760015577 1378227719392841820011683)
                ·
                  refine ⟨2067341579089262730017525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1378227719392841820011683 2067341579089262730017525)
                  ·
                    refine ⟨193813273039618380939143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2067341579089262730017525 193813273039618380939143)
                    ·
                      rfl

theorem cell22_566175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 5].length) (baseStart_566175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_566175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_566175 prefixEnd_566175 := by exact prefixLift 566175
  have htrace : WordTrace (prefixWord ++ tailWord_566175) baseStart_566175 baseEnd_566175 := by
    simpa [prefixWord, tailWord_566175, baseEnd_566175] using wordTrace_append hprefix tailTrace_566175
  have hstable : (prefixWord ++ tailWord_566175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566175).length < 2 ^ (prefixWord ++ tailWord_566175).sum := by decide
  have hdescent : baseEnd_566175 < baseStart_566175 := by decide
  rcases family_descends (prefixWord ++ tailWord_566175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566218 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 4, 6]
def baseStart_566218 : Nat := 118140960795 + 566218 * 2 ^ 59
def prefixEnd_566218 : Nat := 4983230072969 + 3 ^ 40 * 566218 * 2
def baseEnd_566218 : Nat := 193827992818380602114011

theorem tailTrace_566218 : CollatzResearch.WordTrace tailWord_566218 prefixEnd_566218 193827992818380602114011 := by
  unfold tailWord_566218
  simp only [CollatzResearch.WordTrace]
  refine ⟨5162916765674090795160827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13767778041797575453762205 5162916765674090795160827)
  ·
    refine ⟨7744375148511136192741241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5162916765674090795160827 7744375148511136192741241)
    ·
      refine ⟨5808281361383352144555931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7744375148511136192741241 5808281361383352144555931)
      ·
        refine ⟨8712422042075028216833897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5808281361383352144555931 8712422042075028216833897)
        ·
          refine ⟨6534316531556271162625423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8712422042075028216833897 6534316531556271162625423)
          ·
            refine ⟨9801474797334406743938135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6534316531556271162625423 9801474797334406743938135)
            ·
              refine ⟨14702212196001610115907203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9801474797334406743938135 14702212196001610115907203)
              ·
                refine ⟨22053318294002415173860805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14702212196001610115907203 22053318294002415173860805)
                ·
                  refine ⟨4134997180125452845098901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22053318294002415173860805 4134997180125452845098901)
                  ·
                    refine ⟨193827992818380602114011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4134997180125452845098901 193827992818380602114011)
                    ·
                      rfl

theorem cell22_566218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_566218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_566218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_566218 prefixEnd_566218 := by exact prefixLift 566218
  have htrace : WordTrace (prefixWord ++ tailWord_566218) baseStart_566218 baseEnd_566218 := by
    simpa [prefixWord, tailWord_566218, baseEnd_566218] using wordTrace_append hprefix tailTrace_566218
  have hstable : (prefixWord ++ tailWord_566218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566218).length < 2 ^ (prefixWord ++ tailWord_566218).sum := by decide
  have hdescent : baseEnd_566218 < baseStart_566218 := by decide
  rcases family_descends (prefixWord ++ tailWord_566218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
