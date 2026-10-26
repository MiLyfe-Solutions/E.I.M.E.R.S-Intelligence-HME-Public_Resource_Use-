import V185TrunkScan23Chunk0220

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1307573 : List Nat := [1, 3, 3, 2, 1, 1, 2, 2, 8]
def baseStart_1307573 : Nat := 118140960795 + 1307573 * 2 ^ 59
def prefixEnd_1307573 : Nat := 4983230072969 + 3 ^ 40 * 1307573 * 2
def baseEnd_1307573 : Nat := 74601493315724205369343

theorem tailTrace_1307573 : CollatzResearch.WordTrace tailWord_1307573 prefixEnd_1307573 74601493315724205369343 := by
  unfold tailWord_1307573
  simp only [CollatzResearch.WordTrace]
  refine ⟨47691105291893811534439373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31794070194595874356292915 47691105291893811534439373)
  ·
    refine ⟨17884164484460179325414765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47691105291893811534439373 17884164484460179325414765)
    ·
      refine ⟨6706561681672567247030537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17884164484460179325414765 6706561681672567247030537)
      ·
        refine ⟨5029921261254425435272903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6706561681672567247030537 5029921261254425435272903)
        ·
          refine ⟨7544881891881638152909355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5029921261254425435272903 7544881891881638152909355)
          ·
            refine ⟨11317322837822457229364033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7544881891881638152909355 11317322837822457229364033)
            ·
              refine ⟨8487992128366842922023025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11317322837822457229364033 8487992128366842922023025)
              ·
                refine ⟨6365994096275132191517269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8487992128366842922023025 6365994096275132191517269)
                ·
                  refine ⟨74601493315724205369343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6365994096275132191517269 74601493315724205369343)
                  ·
                    rfl

theorem cell23_1307573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 8].length) (baseStart_1307573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307573 prefixEnd_1307573 := by exact prefixLift 1307573
  have htrace : WordTrace (prefixWord ++ tailWord_1307573) baseStart_1307573 baseEnd_1307573 := by
    simpa [prefixWord, tailWord_1307573, baseEnd_1307573] using wordTrace_append hprefix tailTrace_1307573
  have hstable : (prefixWord ++ tailWord_1307573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307573).length < 2 ^ (prefixWord ++ tailWord_1307573).sum := by decide
  have hdescent : baseEnd_1307573 < baseStart_1307573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307577 : List Nat := [1, 2, 1, 4, 2, 2, 1, 5, 1, 4]
def baseStart_1307577 : Nat := 118140960795 + 1307577 * 2 ^ 59
def prefixEnd_1307577 : Nat := 4983230072969 + 3 ^ 40 * 1307577 * 2
def baseEnd_1307577 : Nat := 223805164588045277558023

theorem tailTrace_1307577 : CollatzResearch.WordTrace tailWord_1307577 prefixEnd_1307577 223805164588045277558023 := by
  unfold tailWord_1307577
  simp only [CollatzResearch.WordTrace]
  refine ⟨47691251183879320217584985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31794167455919546811723323 47691251183879320217584985)
  ·
    refine ⟨35768438387909490163188739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47691251183879320217584985 35768438387909490163188739)
    ·
      refine ⟨53652657581864235244783109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35768438387909490163188739 53652657581864235244783109)
      ·
        refine ⟨10059873296599544108396833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53652657581864235244783109 10059873296599544108396833)
        ·
          refine ⟨7544904972449658081297625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10059873296599544108396833 7544904972449658081297625)
          ·
            refine ⟨5658678729337243560973219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7544904972449658081297625 5658678729337243560973219)
            ·
              refine ⟨8488018094005865341459829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5658678729337243560973219 8488018094005865341459829)
              ·
                refine ⟨795751696313049875761859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8488018094005865341459829 795751696313049875761859)
                ·
                  refine ⟨1193627544469574813642789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 795751696313049875761859 1193627544469574813642789)
                  ·
                    refine ⟨223805164588045277558023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1193627544469574813642789 223805164588045277558023)
                    ·
                      rfl

theorem cell23_1307577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 5, 1, 4].length) (baseStart_1307577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307577 prefixEnd_1307577 := by exact prefixLift 1307577
  have htrace : WordTrace (prefixWord ++ tailWord_1307577) baseStart_1307577 baseEnd_1307577 := by
    simpa [prefixWord, tailWord_1307577, baseEnd_1307577] using wordTrace_append hprefix tailTrace_1307577
  have hstable : (prefixWord ++ tailWord_1307577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307577).length < 2 ^ (prefixWord ++ tailWord_1307577).sum := by decide
  have hdescent : baseEnd_1307577 < baseStart_1307577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307653 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 3, 1, 6]
def baseStart_1307653 : Nat := 118140960795 + 1307653 * 2 ^ 59
def prefixEnd_1307653 : Nat := 4983230072969 + 3 ^ 40 * 1307653 * 2
def baseEnd_1307653 : Nat := 671454518293877535323719

theorem tailTrace_1307653 : CollatzResearch.WordTrace tailWord_1307653 prefixEnd_1307653 671454518293877535323719 := by
  unfold tailWord_1307653
  simp only [CollatzResearch.WordTrace]
  refine ⟨47694023131603985197351613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31796015421069323464901075 47694023131603985197351613)
  ·
    refine ⟨17885258674351494449006855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47694023131603985197351613 17885258674351494449006855)
    ·
      refine ⟨26827888011527241673510283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17885258674351494449006855 26827888011527241673510283)
      ·
        refine ⟨40241832017290862510265425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26827888011527241673510283 40241832017290862510265425)
        ·
          refine ⟨30181374012968146882699069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40241832017290862510265425 30181374012968146882699069)
          ·
            refine ⟨11318015254863055081012151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30181374012968146882699069 11318015254863055081012151)
            ·
              refine ⟨16977022882294582621518227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11318015254863055081012151 16977022882294582621518227)
              ·
                refine ⟨25465534323441873932277341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16977022882294582621518227 25465534323441873932277341)
                ·
                  refine ⟨9549575371290702724604003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25465534323441873932277341 9549575371290702724604003)
                  ·
                    refine ⟨14324363056936054086906005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9549575371290702724604003 14324363056936054086906005)
                    ·
                      refine ⟨671454518293877535323719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14324363056936054086906005 671454518293877535323719)
                      ·
                        rfl

theorem cell23_1307653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_1307653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307653 prefixEnd_1307653 := by exact prefixLift 1307653
  have htrace : WordTrace (prefixWord ++ tailWord_1307653) baseStart_1307653 baseEnd_1307653 := by
    simpa [prefixWord, tailWord_1307653, baseEnd_1307653] using wordTrace_append hprefix tailTrace_1307653
  have hstable : (prefixWord ++ tailWord_1307653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307653).length < 2 ^ (prefixWord ++ tailWord_1307653).sum := by decide
  have hdescent : baseEnd_1307653 < baseStart_1307653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307660 : List Nat := [2, 2, 1, 2, 3, 2, 2, 2, 1, 1, 5]
def baseStart_1307660 : Nat := 118140960795 + 1307660 * 2 ^ 59
def prefixEnd_1307660 : Nat := 4983230072969 + 3 ^ 40 * 1307660 * 2
def baseEnd_1307660 : Nat := 671458112658459007936187

theorem tailTrace_1307660 : CollatzResearch.WordTrace tailWord_1307660 prefixEnd_1307660 671458112658459007936187 := by
  unfold tailWord_1307660
  simp only [CollatzResearch.WordTrace]
  refine ⟨23847139221289312696428217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31796185628385750261904289 23847139221289312696428217)
  ·
    refine ⟨17885354415966984522321163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23847139221289312696428217 17885354415966984522321163)
    ·
      refine ⟨26828031623950476783481745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17885354415966984522321163 26828031623950476783481745)
      ·
        refine ⟨20121023717962857587611309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26828031623950476783481745 20121023717962857587611309)
        ·
          refine ⟨7545383894236071595354241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20121023717962857587611309 7545383894236071595354241)
          ·
            refine ⟨5659037920677053696515681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7545383894236071595354241 5659037920677053696515681)
            ·
              refine ⟨4244278440507790272386761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5659037920677053696515681 4244278440507790272386761)
              ·
                refine ⟨3183208830380842704290071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4244278440507790272386761 3183208830380842704290071)
                ·
                  refine ⟨4774813245571264056435107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3183208830380842704290071 4774813245571264056435107)
                  ·
                    refine ⟨7162219868356896084652661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4774813245571264056435107 7162219868356896084652661)
                    ·
                      refine ⟨671458112658459007936187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7162219868356896084652661 671458112658459007936187)
                      ·
                        rfl

theorem cell23_1307660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_1307660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307660 prefixEnd_1307660 := by exact prefixLift 1307660
  have htrace : WordTrace (prefixWord ++ tailWord_1307660) baseStart_1307660 baseEnd_1307660 := by
    simpa [prefixWord, tailWord_1307660, baseEnd_1307660] using wordTrace_append hprefix tailTrace_1307660
  have hstable : (prefixWord ++ tailWord_1307660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307660).length < 2 ^ (prefixWord ++ tailWord_1307660).sum := by decide
  have hdescent : baseEnd_1307660 < baseStart_1307660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307687 : List Nat := [1, 1, 7, 1, 1, 1, 1, 1, 3, 2, 4]
def baseStart_1307687 : Nat := 118140960795 + 1307687 * 2 ^ 59
def prefixEnd_1307687 : Nat := 4983230072969 + 3 ^ 40 * 1307687 * 2
def baseEnd_1307687 : Nat := 671471976636130402298563

theorem tailTrace_1307687 : CollatzResearch.WordTrace tailWord_1307687 prefixEnd_1307687 671471976636130402298563 := by
  unfold tailWord_1307687
  simp only [CollatzResearch.WordTrace]
  refine ⟨47695263213480809004089315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31796842142320539336059543 47695263213480809004089315)
  ·
    refine ⟨71542894820221213506133973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47695263213480809004089315 71542894820221213506133973)
    ·
      refine ⟨1676786597348934691550015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 71542894820221213506133973 1676786597348934691550015)
      ·
        refine ⟨2515179896023402037325023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1676786597348934691550015 2515179896023402037325023)
        ·
          refine ⟨3772769844035103055987535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2515179896023402037325023 3772769844035103055987535)
          ·
            refine ⟨5659154766052654583981303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3772769844035103055987535 5659154766052654583981303)
            ·
              refine ⟨8488732149078981875971955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5659154766052654583981303 8488732149078981875971955)
              ·
                refine ⟨12733098223618472813957933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8488732149078981875971955 12733098223618472813957933)
                ·
                  refine ⟨4774911833856927305234225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12733098223618472813957933 4774911833856927305234225)
                  ·
                    refine ⟨3581183875392695478925669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4774911833856927305234225 3581183875392695478925669)
                    ·
                      refine ⟨671471976636130402298563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3581183875392695478925669 671471976636130402298563)
                      ·
                        rfl

theorem cell23_1307687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_1307687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307687 prefixEnd_1307687 := by exact prefixLift 1307687
  have htrace : WordTrace (prefixWord ++ tailWord_1307687) baseStart_1307687 baseEnd_1307687 := by
    simpa [prefixWord, tailWord_1307687, baseEnd_1307687] using wordTrace_append hprefix tailTrace_1307687
  have hstable : (prefixWord ++ tailWord_1307687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307687).length < 2 ^ (prefixWord ++ tailWord_1307687).sum := by decide
  have hdescent : baseEnd_1307687 < baseStart_1307687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307708 : List Nat := [2, 2, 2, 2, 2, 2, 4, 2, 1, 2, 2]
def baseStart_1307708 : Nat := 118140960795 + 1307708 * 2 ^ 59
def prefixEnd_1307708 : Nat := 4983230072969 + 3 ^ 40 * 1307708 * 2
def baseEnd_1307708 : Nat := 671482759729874820135967

theorem tailTrace_1307708 : CollatzResearch.WordTrace tailWord_1307708 prefixEnd_1307708 671482759729874820135967 := by
  unfold tailWord_1307708
  simp only [CollatzResearch.WordTrace]
  refine ⟨23848014573202364795301889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31797352764269819727069185 23848014573202364795301889)
  ·
    refine ⟨17886010929901773596476417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23848014573202364795301889 17886010929901773596476417)
    ·
      refine ⟨13414508197426330197357313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17886010929901773596476417 13414508197426330197357313)
      ·
        refine ⟨10060881148069747648017985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13414508197426330197357313 10060881148069747648017985)
        ·
          refine ⟨7545660861052310736013489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10060881148069747648017985 7545660861052310736013489)
          ·
            refine ⟨5659245645789233052010117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7545660861052310736013489 5659245645789233052010117)
            ·
              refine ⟨1061108558585481197251897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5659245645789233052010117 1061108558585481197251897)
              ·
                refine ⟨795831418939110897938923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1061108558585481197251897 795831418939110897938923)
                ·
                  refine ⟨1193747128408666346908385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 795831418939110897938923 1193747128408666346908385)
                  ·
                    refine ⟨895310346306499760181289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1193747128408666346908385 895310346306499760181289)
                    ·
                      refine ⟨671482759729874820135967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 895310346306499760181289 671482759729874820135967)
                      ·
                        rfl

theorem cell23_1307708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 2, 1, 2, 2].length) (baseStart_1307708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307708 prefixEnd_1307708 := by exact prefixLift 1307708
  have htrace : WordTrace (prefixWord ++ tailWord_1307708) baseStart_1307708 baseEnd_1307708 := by
    simpa [prefixWord, tailWord_1307708, baseEnd_1307708] using wordTrace_append hprefix tailTrace_1307708
  have hstable : (prefixWord ++ tailWord_1307708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307708).length < 2 ^ (prefixWord ++ tailWord_1307708).sum := by decide
  have hdescent : baseEnd_1307708 < baseStart_1307708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307717 : List Nat := [1, 3, 1, 1, 1, 3, 3, 2, 3, 3, 2]
def baseStart_1307717 : Nat := 118140960795 + 1307717 * 2 ^ 59
def prefixEnd_1307717 : Nat := 4983230072969 + 3 ^ 40 * 1307717 * 2
def baseEnd_1307717 : Nat := 671487381055765284923425

theorem tailTrace_1307717 : CollatzResearch.WordTrace tailWord_1307717 prefixEnd_1307717 671487381055765284923425 := by
  unfold tailWord_1307717
  simp only [CollatzResearch.WordTrace]
  refine ⟨47696357403372124127681405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31797571602248082751787603 47696357403372124127681405)
  ·
    refine ⟨17886134026264546547880527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47696357403372124127681405 17886134026264546547880527)
    ·
      refine ⟨26829201039396819821820791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17886134026264546547880527 26829201039396819821820791)
      ·
        refine ⟨40243801559095229732731187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26829201039396819821820791 40243801559095229732731187)
        ·
          refine ⟨60365702338642844599096781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40243801559095229732731187 60365702338642844599096781)
          ·
            refine ⟨22637138376991066724661293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60365702338642844599096781 22637138376991066724661293)
            ·
              refine ⟨8488926891371650021747985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22637138376991066724661293 8488926891371650021747985)
              ·
                refine ⟨6366695168528737516310989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8488926891371650021747985 6366695168528737516310989)
                ·
                  refine ⟨2387510688198276568616621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6366695168528737516310989 2387510688198276568616621)
                  ·
                    refine ⟨895316508074353713231233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2387510688198276568616621 895316508074353713231233)
                    ·
                      refine ⟨671487381055765284923425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 895316508074353713231233 671487381055765284923425)
                      ·
                        rfl

theorem cell23_1307717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 3, 3, 2].length) (baseStart_1307717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307717 prefixEnd_1307717 := by exact prefixLift 1307717
  have htrace : WordTrace (prefixWord ++ tailWord_1307717) baseStart_1307717 baseEnd_1307717 := by
    simpa [prefixWord, tailWord_1307717, baseEnd_1307717] using wordTrace_append hprefix tailTrace_1307717
  have hstable : (prefixWord ++ tailWord_1307717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307717).length < 2 ^ (prefixWord ++ tailWord_1307717).sum := by decide
  have hdescent : baseEnd_1307717 < baseStart_1307717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307740 : List Nat := [2, 2, 4, 1, 1, 1, 1, 2, 1, 8]
def baseStart_1307740 : Nat := 118140960795 + 1307740 * 2 ^ 59
def prefixEnd_1307740 : Nat := 4983230072969 + 3 ^ 40 * 1307740 * 2
def baseEnd_1307740 : Nat := 223833063703606231645273

theorem tailTrace_1307740 : CollatzResearch.WordTrace tailWord_1307740 prefixEnd_1307740 223833063703606231645273 := by
  unfold tailWord_1307740
  simp only [CollatzResearch.WordTrace]
  refine ⟨23848598141144399527884337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31798130854859199370512449 23848598141144399527884337)
  ·
    refine ⟨17886448605858299645913253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23848598141144399527884337 17886448605858299645913253)
    ·
      refine ⟨3353709113598431183608735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17886448605858299645913253 3353709113598431183608735)
      ·
        refine ⟨5030563670397646775413103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3353709113598431183608735 5030563670397646775413103)
        ·
          refine ⟨7545845505596470163119655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5030563670397646775413103 7545845505596470163119655)
          ·
            refine ⟨11318768258394705244679483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7545845505596470163119655 11318768258394705244679483)
            ·
              refine ⟨16978152387592057867019225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11318768258394705244679483 16978152387592057867019225)
              ·
                refine ⟨12733614290694043400264419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16978152387592057867019225 12733614290694043400264419)
                ·
                  refine ⟨19100421436041065100396629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12733614290694043400264419 19100421436041065100396629)
                  ·
                    refine ⟨223833063703606231645273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 19100421436041065100396629 223833063703606231645273)
                    ·
                      rfl

theorem cell23_1307740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_1307740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307740 prefixEnd_1307740 := by exact prefixLift 1307740
  have htrace : WordTrace (prefixWord ++ tailWord_1307740) baseStart_1307740 baseEnd_1307740 := by
    simpa [prefixWord, tailWord_1307740, baseEnd_1307740] using wordTrace_append hprefix tailTrace_1307740
  have hstable : (prefixWord ++ tailWord_1307740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307740).length < 2 ^ (prefixWord ++ tailWord_1307740).sum := by decide
  have hdescent : baseEnd_1307740 < baseStart_1307740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307742 : List Nat := [4, 4, 1, 1, 1, 2, 2, 3, 1, 2, 2]
def baseStart_1307742 : Nat := 118140960795 + 1307742 * 2 ^ 59
def prefixEnd_1307742 : Nat := 4983230072969 + 3 ^ 40 * 1307742 * 2
def baseEnd_1307742 : Nat := 671500218072127687110811

theorem tailTrace_1307742 : CollatzResearch.WordTrace tailWord_1307742 prefixEnd_1307742 671500218072127687110811 := by
  unfold tailWord_1307742
  simp only [CollatzResearch.WordTrace]
  refine ⟨5962158653535194174667685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31798179485521035598227653 5962158653535194174667685)
  ·
    refine ⟨1117904747537848907750191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5962158653535194174667685 1117904747537848907750191)
    ·
      refine ⟨1676857121306773361625287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1117904747537848907750191 1676857121306773361625287)
      ·
        refine ⟨2515285681960160042437931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1676857121306773361625287 2515285681960160042437931)
        ·
          refine ⟨3772928522940240063656897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2515285681960160042437931 3772928522940240063656897)
          ·
            refine ⟨2829696392205180047742673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3772928522940240063656897 2829696392205180047742673)
            ·
              refine ⟨2122272294153885035807005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2829696392205180047742673 2122272294153885035807005)
              ·
                refine ⟨795852110307706888427627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2122272294153885035807005 795852110307706888427627)
                ·
                  refine ⟨1193778165461560332641441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 795852110307706888427627 1193778165461560332641441)
                  ·
                    refine ⟨895333624096170249481081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1193778165461560332641441 895333624096170249481081)
                    ·
                      refine ⟨671500218072127687110811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 895333624096170249481081 671500218072127687110811)
                      ·
                        rfl

theorem cell23_1307742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_1307742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307742 prefixEnd_1307742 := by exact prefixLift 1307742
  have htrace : WordTrace (prefixWord ++ tailWord_1307742) baseStart_1307742 baseEnd_1307742 := by
    simpa [prefixWord, tailWord_1307742, baseEnd_1307742] using wordTrace_append hprefix tailTrace_1307742
  have hstable : (prefixWord ++ tailWord_1307742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307742).length < 2 ^ (prefixWord ++ tailWord_1307742).sum := by decide
  have hdescent : baseEnd_1307742 < baseStart_1307742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307751 : List Nat := [1, 1, 5, 1, 1, 3, 4, 1, 1, 3, 2]
def baseStart_1307751 : Nat := 118140960795 + 1307751 * 2 ^ 59
def prefixEnd_1307751 : Nat := 4983230072969 + 3 ^ 40 * 1307751 * 2
def baseEnd_1307751 : Nat := 671504839398018151898269

theorem tailTrace_1307751 : CollatzResearch.WordTrace tailWord_1307751 prefixEnd_1307751 671504839398018151898269 := by
  unfold tailWord_1307751
  simp only [CollatzResearch.WordTrace]
  refine ⟨47697597485248947934419107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31798398323499298622946071 47697597485248947934419107)
  ·
    refine ⟨71546396227873421901628661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47697597485248947934419107 71546396227873421901628661)
    ·
      refine ⟨6707474646363133303277687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71546396227873421901628661 6707474646363133303277687)
      ·
        refine ⟨10061211969544699954916531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6707474646363133303277687 10061211969544699954916531)
        ·
          refine ⟨15091817954317049932374797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10061211969544699954916531 15091817954317049932374797)
          ·
            refine ⟨5659431732868893724640549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15091817954317049932374797 5659431732868893724640549)
            ·
              refine ⟨1061143449912917573370103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5659431732868893724640549 1061143449912917573370103)
              ·
                refine ⟨1591715174869376360055155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1061143449912917573370103 1591715174869376360055155)
                ·
                  refine ⟨2387572762304064540082733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1591715174869376360055155 2387572762304064540082733)
                  ·
                    refine ⟨895339785864024202531025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2387572762304064540082733 895339785864024202531025)
                    ·
                      refine ⟨671504839398018151898269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 895339785864024202531025 671504839398018151898269)
                      ·
                        rfl

theorem cell23_1307751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 1, 1, 3, 2].length) (baseStart_1307751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307751 prefixEnd_1307751 := by exact prefixLift 1307751
  have htrace : WordTrace (prefixWord ++ tailWord_1307751) baseStart_1307751 baseEnd_1307751 := by
    simpa [prefixWord, tailWord_1307751, baseEnd_1307751] using wordTrace_append hprefix tailTrace_1307751
  have hstable : (prefixWord ++ tailWord_1307751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307751).length < 2 ^ (prefixWord ++ tailWord_1307751).sum := by decide
  have hdescent : baseEnd_1307751 < baseStart_1307751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307760 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 4]
def baseStart_1307760 : Nat := 118140960795 + 1307760 * 2 ^ 59
def prefixEnd_1307760 : Nat := 4983230072969 + 3 ^ 40 * 1307760 * 2
def baseEnd_1307760 : Nat := 671509460723908616685727

theorem tailTrace_1307760 : CollatzResearch.WordTrace tailWord_1307760 prefixEnd_1307760 671509460723908616685727 := by
  unfold tailWord_1307760
  simp only [CollatzResearch.WordTrace]
  refine ⟨23848962871108171235748367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31798617161477561647664489 23848962871108171235748367)
  ·
    refine ⟨35773444306662256853622551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23848962871108171235748367 35773444306662256853622551)
    ·
      refine ⟨53660166459993385280433827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35773444306662256853622551 53660166459993385280433827)
      ·
        refine ⟨80490249689990077920650741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53660166459993385280433827 80490249689990077920650741)
        ·
          refine ⟨7545960908436569805061007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80490249689990077920650741 7545960908436569805061007)
          ·
            refine ⟨11318941362654854707591511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7545960908436569805061007 11318941362654854707591511)
            ·
              refine ⟨16978412043982282061387267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11318941362654854707591511 16978412043982282061387267)
              ·
                refine ⟨25467618065973423092080901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16978412043982282061387267 25467618065973423092080901)
                ·
                  refine ⟨4775178387370016829765169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25467618065973423092080901 4775178387370016829765169)
                  ·
                    refine ⟨3581383790527512622323877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4775178387370016829765169 3581383790527512622323877)
                    ·
                      refine ⟨671509460723908616685727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3581383790527512622323877 671509460723908616685727)
                      ·
                        rfl

theorem cell23_1307760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 4].length) (baseStart_1307760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307760 prefixEnd_1307760 := by exact prefixLift 1307760
  have htrace : WordTrace (prefixWord ++ tailWord_1307760) baseStart_1307760 baseEnd_1307760 := by
    simpa [prefixWord, tailWord_1307760, baseEnd_1307760] using wordTrace_append hprefix tailTrace_1307760
  have hstable : (prefixWord ++ tailWord_1307760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307760).length < 2 ^ (prefixWord ++ tailWord_1307760).sum := by decide
  have hdescent : baseEnd_1307760 < baseStart_1307760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307777 : List Nat := [1, 2, 4, 2, 2, 1, 2, 1, 2, 2, 4]
def baseStart_1307777 : Nat := 118140960795 + 1307777 * 2 ^ 59
def prefixEnd_1307777 : Nat := 4983230072969 + 3 ^ 40 * 1307777 * 2
def baseEnd_1307777 : Nat := 671518189895035050173149

theorem tailTrace_1307777 : CollatzResearch.WordTrace tailWord_1307777 prefixEnd_1307777 671518189895035050173149 := by
  unfold tailWord_1307777
  simp only [CollatzResearch.WordTrace]
  refine ⟨47698545783154754374865585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31799030522103169583243723 47698545783154754374865585)
  ·
    refine ⟨35773909337366065781149189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47698545783154754374865585 35773909337366065781149189)
    ·
      refine ⟨6707608000756137333965473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35773909337366065781149189 6707608000756137333965473)
      ·
        refine ⟨5030706000567103000474105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6707608000756137333965473 5030706000567103000474105)
        ·
          refine ⟨3773029500425327250355579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5030706000567103000474105 3773029500425327250355579)
          ·
            refine ⟨5659544250637990875533369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3773029500425327250355579 5659544250637990875533369)
            ·
              refine ⟨4244658187978493156650027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5659544250637990875533369 4244658187978493156650027)
              ·
                refine ⟨6366987281967739734975041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4244658187978493156650027 6366987281967739734975041)
                ·
                  refine ⟨4775240461475804801231281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6366987281967739734975041 4775240461475804801231281)
                  ·
                    refine ⟨3581430346106853600923461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4775240461475804801231281 3581430346106853600923461)
                    ·
                      refine ⟨671518189895035050173149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3581430346106853600923461 671518189895035050173149)
                      ·
                        rfl

theorem cell23_1307777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_1307777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307777 prefixEnd_1307777 := by exact prefixLift 1307777
  have htrace : WordTrace (prefixWord ++ tailWord_1307777) baseStart_1307777 baseEnd_1307777 := by
    simpa [prefixWord, tailWord_1307777, baseEnd_1307777] using wordTrace_append hprefix tailTrace_1307777
  have hstable : (prefixWord ++ tailWord_1307777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307777).length < 2 ^ (prefixWord ++ tailWord_1307777).sum := by decide
  have hdescent : baseEnd_1307777 < baseStart_1307777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307781 : List Nat := [1, 3, 1, 1, 6, 2, 1, 1, 1, 4, 2]
def baseStart_1307781 : Nat := 118140960795 + 1307781 * 2 ^ 59
def prefixEnd_1307781 : Nat := 4983230072969 + 3 ^ 40 * 1307781 * 2
def baseEnd_1307781 : Nat := 671520243817653034523131

theorem tailTrace_1307781 : CollatzResearch.WordTrace tailWord_1307781 prefixEnd_1307781 671520243817653034523131 := by
  unfold tailWord_1307781
  simp only [CollatzResearch.WordTrace]
  refine ⟨47698691675140263058011197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31799127783426842038674131 47698691675140263058011197)
  ·
    refine ⟨17887009378177598646754199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47698691675140263058011197 17887009378177598646754199)
    ·
      refine ⟨26830514067266397970131299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17887009378177598646754199 26830514067266397970131299)
      ·
        refine ⟨40245771100899596955196949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26830514067266397970131299 40245771100899596955196949)
        ·
          refine ⟨1886520520354668607274857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 40245771100899596955196949 1886520520354668607274857)
          ·
            refine ⟨1414890390266001455456143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1886520520354668607274857 1414890390266001455456143)
            ·
              refine ⟨2122335585399002183184215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1414890390266001455456143 2122335585399002183184215)
              ·
                refine ⟨3183503378098503274776323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2122335585399002183184215 3183503378098503274776323)
                ·
                  refine ⟨4775255067147754912164485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3183503378098503274776323 4775255067147754912164485)
                  ·
                    refine ⟨895360325090204046030841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4775255067147754912164485 895360325090204046030841)
                    ·
                      refine ⟨671520243817653034523131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 895360325090204046030841 671520243817653034523131)
                      ·
                        rfl

theorem cell23_1307781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 4, 2].length) (baseStart_1307781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307781 prefixEnd_1307781 := by exact prefixLift 1307781
  have htrace : WordTrace (prefixWord ++ tailWord_1307781) baseStart_1307781 baseEnd_1307781 := by
    simpa [prefixWord, tailWord_1307781, baseEnd_1307781] using wordTrace_append hprefix tailTrace_1307781
  have hstable : (prefixWord ++ tailWord_1307781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307781).length < 2 ^ (prefixWord ++ tailWord_1307781).sum := by decide
  have hdescent : baseEnd_1307781 < baseStart_1307781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307804 : List Nat := [2, 2, 3, 2, 1, 2, 3, 3, 5]
def baseStart_1307804 : Nat := 118140960795 + 1307804 * 2 ^ 59
def prefixEnd_1307804 : Nat := 4983230072969 + 3 ^ 40 * 1307804 * 2
def baseEnd_1307804 : Nat := 74614672652522938281725

theorem tailTrace_1307804 : CollatzResearch.WordTrace tailWord_1307804 prefixEnd_1307804 74614672652522938281725 := by
  unfold tailWord_1307804
  simp only [CollatzResearch.WordTrace]
  refine ⟨23849765277028468993049233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31799687036037958657398977 23849765277028468993049233)
  ·
    refine ⟨17887323957771351744786925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23849765277028468993049233 17887323957771351744786925)
    ·
      refine ⟨6707746484164256904295097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17887323957771351744786925 6707746484164256904295097)
      ·
        refine ⟨5030809863123192678221323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6707746484164256904295097 5030809863123192678221323)
        ·
          refine ⟨7546214794684789017331985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5030809863123192678221323 7546214794684789017331985)
          ·
            refine ⟨5659661096013591762998989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7546214794684789017331985 5659661096013591762998989)
            ·
              refine ⟨2122372911005096911124621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5659661096013591762998989 2122372911005096911124621)
              ·
                refine ⟨795889841626911341671733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2122372911005096911124621 795889841626911341671733)
                ·
                  refine ⟨74614672652522938281725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 795889841626911341671733 74614672652522938281725)
                  ·
                    rfl

theorem cell23_1307804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 3, 5].length) (baseStart_1307804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307804 prefixEnd_1307804 := by exact prefixLift 1307804
  have htrace : WordTrace (prefixWord ++ tailWord_1307804) baseStart_1307804 baseEnd_1307804 := by
    simpa [prefixWord, tailWord_1307804, baseEnd_1307804] using wordTrace_append hprefix tailTrace_1307804
  have hstable : (prefixWord ++ tailWord_1307804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307804).length < 2 ^ (prefixWord ++ tailWord_1307804).sum := by decide
  have hdescent : baseEnd_1307804 < baseStart_1307804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307820 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 4]
def baseStart_1307820 : Nat := 118140960795 + 1307820 * 2 ^ 59
def prefixEnd_1307820 : Nat := 4983230072969 + 3 ^ 40 * 1307820 * 2
def baseEnd_1307820 : Nat := 671540269563178381935451

theorem tailTrace_1307820 : CollatzResearch.WordTrace tailWord_1307820 prefixEnd_1307820 671540269563178381935451 := by
  unfold tailWord_1307820
  simp only [CollatzResearch.WordTrace]
  refine ⟨23850057060999486359340457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31800076081332648479120609 23850057060999486359340457)
  ·
    refine ⟨17887542795749614769505343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23850057060999486359340457 17887542795749614769505343)
    ·
      refine ⟨26831314193624422154258015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17887542795749614769505343 26831314193624422154258015)
      ·
        refine ⟨40246971290436633231387023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26831314193624422154258015 40246971290436633231387023)
        ·
          refine ⟨60370456935654949847080535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40246971290436633231387023 60370456935654949847080535)
          ·
            refine ⟨90555685403482424770620803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60370456935654949847080535 90555685403482424770620803)
            ·
              refine ⟨135833528105223637155931205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90555685403482424770620803 135833528105223637155931205)
              ·
                refine ⟨25468786519729431966737101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 135833528105223637155931205 25468786519729431966737101)
                ·
                  refine ⟨9550794944898536987526413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25468786519729431966737101 9550794944898536987526413)
                  ·
                    refine ⟨3581548104336951370322405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9550794944898536987526413 3581548104336951370322405)
                    ·
                      refine ⟨671540269563178381935451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3581548104336951370322405 671540269563178381935451)
                      ·
                        rfl

theorem cell23_1307820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 4].length) (baseStart_1307820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307820 prefixEnd_1307820 := by exact prefixLift 1307820
  have htrace : WordTrace (prefixWord ++ tailWord_1307820) baseStart_1307820 baseEnd_1307820 := by
    simpa [prefixWord, tailWord_1307820, baseEnd_1307820] using wordTrace_append hprefix tailTrace_1307820
  have hstable : (prefixWord ++ tailWord_1307820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307820).length < 2 ^ (prefixWord ++ tailWord_1307820).sum := by decide
  have hdescent : baseEnd_1307820 < baseStart_1307820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307821 : List Nat := [1, 5, 2, 1, 4, 1, 1, 1, 7]
def baseStart_1307821 : Nat := 118140960795 + 1307821 * 2 ^ 59
def prefixEnd_1307821 : Nat := 4983230072969 + 3 ^ 40 * 1307821 * 2
def baseEnd_1307821 : Nat := 74615642560425875335883

theorem tailTrace_1307821 : CollatzResearch.WordTrace tailWord_1307821 prefixEnd_1307821 74615642560425875335883 := by
  unfold tailWord_1307821
  simp only [CollatzResearch.WordTrace]
  refine ⟨47700150594995349889467317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31800100396663566592978211 47700150594995349889467317)
  ·
    refine ⟨4471889118280814052137561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47700150594995349889467317 4471889118280814052137561)
    ·
      refine ⟨3353916838710610539103171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4471889118280814052137561 3353916838710610539103171)
      ·
        refine ⟨5030875258065915808654757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3353916838710610539103171 5030875258065915808654757)
        ·
          refine ⟨943289110887359214122767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5030875258065915808654757 943289110887359214122767)
          ·
            refine ⟨1414933666331038821184151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 943289110887359214122767 1414933666331038821184151)
            ·
              refine ⟨2122400499496558231776227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1414933666331038821184151 2122400499496558231776227)
              ·
                refine ⟨3183600749244837347664341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2122400499496558231776227 3183600749244837347664341)
                ·
                  refine ⟨74615642560425875335883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3183600749244837347664341 74615642560425875335883)
                  ·
                    rfl

theorem cell23_1307821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_1307821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307821 prefixEnd_1307821 := by exact prefixLift 1307821
  have htrace : WordTrace (prefixWord ++ tailWord_1307821) baseStart_1307821 baseEnd_1307821 := by
    simpa [prefixWord, tailWord_1307821, baseEnd_1307821] using wordTrace_append hprefix tailTrace_1307821
  have hstable : (prefixWord ++ tailWord_1307821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307821).length < 2 ^ (prefixWord ++ tailWord_1307821).sum := by decide
  have hdescent : baseEnd_1307821 < baseStart_1307821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307847 : List Nat := [1, 1, 4, 1, 1, 1, 1, 6, 3, 4]
def baseStart_1307847 : Nat := 118140960795 + 1307847 * 2 ^ 59
def prefixEnd_1307847 : Nat := 4983230072969 + 3 ^ 40 * 1307847 * 2
def baseEnd_1307847 : Nat := 223851377846949925432609

theorem tailTrace_1307847 : CollatzResearch.WordTrace tailWord_1307847 prefixEnd_1307847 223851377846949925432609 := by
  unfold tailWord_1307847
  simp only [CollatzResearch.WordTrace]
  refine ⟨47701098892901156329913795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31800732595267437553275863 47701098892901156329913795)
  ·
    refine ⟨71551648339351734494870693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47701098892901156329913795 71551648339351734494870693)
    ·
      refine ⟨13415934063628450217788255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71551648339351734494870693 13415934063628450217788255)
      ·
        refine ⟨20123901095442675326682383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13415934063628450217788255 20123901095442675326682383)
        ·
          refine ⟨30185851643164012990023575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20123901095442675326682383 30185851643164012990023575)
          ·
            refine ⟨45278777464746019485035363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30185851643164012990023575 45278777464746019485035363)
            ·
              refine ⟨67918166197119029227553045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45278777464746019485035363 67918166197119029227553045)
              ·
                refine ⟨3183664040489954495041549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67918166197119029227553045 3183664040489954495041549)
                ·
                  refine ⟨1193874015183732935640581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3183664040489954495041549 1193874015183732935640581)
                  ·
                    refine ⟨223851377846949925432609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1193874015183732935640581 223851377846949925432609)
                    ·
                      rfl

theorem cell23_1307847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 3, 4].length) (baseStart_1307847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307847 prefixEnd_1307847 := by exact prefixLift 1307847
  have htrace : WordTrace (prefixWord ++ tailWord_1307847) baseStart_1307847 baseEnd_1307847 := by
    simpa [prefixWord, tailWord_1307847, baseEnd_1307847] using wordTrace_append hprefix tailTrace_1307847
  have hstable : (prefixWord ++ tailWord_1307847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307847).length < 2 ^ (prefixWord ++ tailWord_1307847).sum := by decide
  have hdescent : baseEnd_1307847 < baseStart_1307847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307907 : List Nat := [1, 1, 1, 3, 2, 4, 2, 1, 3, 5]
def baseStart_1307907 : Nat := 118140960795 + 1307907 * 2 ^ 59
def prefixEnd_1307907 : Nat := 4983230072969 + 3 ^ 40 * 1307907 * 2
def baseEnd_1307907 : Nat := 223861647460039847182517

theorem tailTrace_1307907 : CollatzResearch.WordTrace tailWord_1307907 prefixEnd_1307907 223861647460039847182517 := by
  unfold tailWord_1307907
  simp only [CollatzResearch.WordTrace]
  refine ⟨47703287272683786577097975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31802191515122524384731983 47703287272683786577097975)
  ·
    refine ⟨71554930909025679865646963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47703287272683786577097975 71554930909025679865646963)
    ·
      refine ⟨107332396363538519798470445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71554930909025679865646963 107332396363538519798470445)
      ·
        refine ⟨40249648636326944924426417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107332396363538519798470445 40249648636326944924426417)
        ·
          refine ⟨30187236477245208693319813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40249648636326944924426417 30187236477245208693319813)
          ·
            refine ⟨5660106839483476629997465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30187236477245208693319813 5660106839483476629997465)
            ·
              refine ⟨4245080129612607472498099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5660106839483476629997465 4245080129612607472498099)
              ·
                refine ⟨6367620194418911208747149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4245080129612607472498099 6367620194418911208747149)
                ·
                  refine ⟨2387857572907091703280181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6367620194418911208747149 2387857572907091703280181)
                  ·
                    refine ⟨223861647460039847182517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2387857572907091703280181 223861647460039847182517)
                    ·
                      rfl

theorem cell23_1307907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 3, 5].length) (baseStart_1307907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307907 prefixEnd_1307907 := by exact prefixLift 1307907
  have htrace : WordTrace (prefixWord ++ tailWord_1307907) baseStart_1307907 baseEnd_1307907 := by
    simpa [prefixWord, tailWord_1307907, baseEnd_1307907] using wordTrace_append hprefix tailTrace_1307907
  have hstable : (prefixWord ++ tailWord_1307907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307907).length < 2 ^ (prefixWord ++ tailWord_1307907).sum := by decide
  have hdescent : baseEnd_1307907 < baseStart_1307907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307920 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 4, 10]
def baseStart_1307920 : Nat := 118140960795 + 1307920 * 2 ^ 59
def prefixEnd_1307920 : Nat := 4983230072969 + 3 ^ 40 * 1307920 * 2
def baseEnd_1307920 : Nat := 223863872542875996894997

theorem tailTrace_1307920 : CollatzResearch.WordTrace tailWord_1307920 prefixEnd_1307920 223863872542875996894997 := by
  unfold tailWord_1307920
  simp only [CollatzResearch.WordTrace]
  refine ⟨23851880710818344898660607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31802507614424459864880809 23851880710818344898660607)
  ·
    refine ⟨35777821066227517347990911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23851880710818344898660607 35777821066227517347990911)
    ·
      refine ⟨53666731599341276021986367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35777821066227517347990911 53666731599341276021986367)
      ·
        refine ⟨80500097399011914032979551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53666731599341276021986367 80500097399011914032979551)
        ·
          refine ⟨120750146098517871049469327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80500097399011914032979551 120750146098517871049469327)
          ·
            refine ⟨181125219147776806574203991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120750146098517871049469327 181125219147776806574203991)
            ·
              refine ⟨271687828721665209861305987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181125219147776806574203991 271687828721665209861305987)
              ·
                refine ⟨407531743082497814791958981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 271687828721665209861305987 407531743082497814791958981)
                ·
                  refine ⟨76412201827968340273492309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 407531743082497814791958981 76412201827968340273492309)
                  ·
                    refine ⟨223863872542875996894997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 76412201827968340273492309 223863872542875996894997)
                    ·
                      rfl

theorem cell23_1307920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 4, 10].length) (baseStart_1307920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307920 prefixEnd_1307920 := by exact prefixLift 1307920
  have htrace : WordTrace (prefixWord ++ tailWord_1307920) baseStart_1307920 baseEnd_1307920 := by
    simpa [prefixWord, tailWord_1307920, baseEnd_1307920] using wordTrace_append hprefix tailTrace_1307920
  have hstable : (prefixWord ++ tailWord_1307920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307920).length < 2 ^ (prefixWord ++ tailWord_1307920).sum := by decide
  have hdescent : baseEnd_1307920 < baseStart_1307920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307938 : List Nat := [3, 3, 1, 1, 4, 1, 2, 1, 3, 1, 3]
def baseStart_1307938 : Nat := 118140960795 + 1307938 * 2 ^ 59
def prefixEnd_1307938 : Nat := 4983230072969 + 3 ^ 40 * 1307938 * 2
def baseEnd_1307938 : Nat := 671600860280408920259909

theorem tailTrace_1307938 : CollatzResearch.WordTrace tailWord_1307938 prefixEnd_1307938 671600860280408920259909 := by
  unfold tailWord_1307938
  simp only [CollatzResearch.WordTrace]
  refine ⟨11926104483892869717869117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31802945290380985914317645 11926104483892869717869117)
  ·
    refine ⟨4472289181459826144200919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11926104483892869717869117 4472289181459826144200919)
    ·
      refine ⟨6708433772189739216301379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4472289181459826144200919 6708433772189739216301379)
      ·
        refine ⟨10062650658284608824452069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6708433772189739216301379 10062650658284608824452069)
        ·
          refine ⟨1886746998428364154584763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10062650658284608824452069 1886746998428364154584763)
          ·
            refine ⟨2830120497642546231877145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1886746998428364154584763 2830120497642546231877145)
            ·
              refine ⟨2122590373231909673907859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2830120497642546231877145 2122590373231909673907859)
              ·
                refine ⟨3183885559847864510861789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2122590373231909673907859 3183885559847864510861789)
                ·
                  refine ⟨1193957084942949191573171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3183885559847864510861789 1193957084942949191573171)
                  ·
                    refine ⟨1790935627414423787359757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1193957084942949191573171 1790935627414423787359757)
                    ·
                      refine ⟨671600860280408920259909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1790935627414423787359757 671600860280408920259909)
                      ·
                        rfl

theorem cell23_1307938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_1307938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307938 prefixEnd_1307938 := by exact prefixLift 1307938
  have htrace : WordTrace (prefixWord ++ tailWord_1307938) baseStart_1307938 baseEnd_1307938 := by
    simpa [prefixWord, tailWord_1307938, baseEnd_1307938] using wordTrace_append hprefix tailTrace_1307938
  have hstable : (prefixWord ++ tailWord_1307938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307938).length < 2 ^ (prefixWord ++ tailWord_1307938).sum := by decide
  have hdescent : baseEnd_1307938 < baseStart_1307938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307954 : List Nat := [3, 2, 1, 1, 4, 1, 3, 1, 1, 6]
def baseStart_1307954 : Nat := 118140960795 + 1307954 * 2 ^ 59
def prefixEnd_1307954 : Nat := 4983230072969 + 3 ^ 40 * 1307954 * 2
def baseEnd_1307954 : Nat := 223869691990293619219945

theorem tailTrace_1307954 : CollatzResearch.WordTrace tailWord_1307954 prefixEnd_1307954 223869691990293619219945 := by
  unfold tailWord_1307954
  simp only [CollatzResearch.WordTrace]
  refine ⟨11926250375878378401014729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31803334335675675736039277 11926250375878378401014729)
  ·
    refine ⟨8944687781908783800761047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11926250375878378401014729 8944687781908783800761047)
    ·
      refine ⟨13417031672863175701141571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8944687781908783800761047 13417031672863175701141571)
      ·
        refine ⟨20125547509294763551712357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13417031672863175701141571 20125547509294763551712357)
        ·
          refine ⟨3773540157992768165946067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20125547509294763551712357 3773540157992768165946067)
          ·
            refine ⟨5660310236989152248919101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3773540157992768165946067 5660310236989152248919101)
            ·
              refine ⟨2122616338870932093344663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5660310236989152248919101 2122616338870932093344663)
              ·
                refine ⟨3183924508306398140016995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2122616338870932093344663 3183924508306398140016995)
                ·
                  refine ⟨4775886762459597210025493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3183924508306398140016995 4775886762459597210025493)
                  ·
                    refine ⟨223869691990293619219945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4775886762459597210025493 223869691990293619219945)
                    ·
                      rfl

theorem cell23_1307954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 1, 6].length) (baseStart_1307954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307954 prefixEnd_1307954 := by exact prefixLift 1307954
  have htrace : WordTrace (prefixWord ++ tailWord_1307954) baseStart_1307954 baseEnd_1307954 := by
    simpa [prefixWord, tailWord_1307954, baseEnd_1307954] using wordTrace_append hprefix tailTrace_1307954
  have hstable : (prefixWord ++ tailWord_1307954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307954).length < 2 ^ (prefixWord ++ tailWord_1307954).sum := by decide
  have hdescent : baseEnd_1307954 < baseStart_1307954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307967 : List Nat := [1, 1, 2, 2, 4, 3, 1, 9]
def baseStart_1307967 : Nat := 118140960795 + 1307967 * 2 ^ 59
def prefixEnd_1307967 : Nat := 4983230072969 + 3 ^ 40 * 1307967 * 2
def baseEnd_1307967 : Nat := 24874657452569974325825

theorem tailTrace_1307967 : CollatzResearch.WordTrace tailWord_1307967 prefixEnd_1307967 24874657452569974325825 := by
  unfold tailWord_1307967
  simp only [CollatzResearch.WordTrace]
  refine ⟨47705475652466416824282155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31803650434977611216188103 47705475652466416824282155)
  ·
    refine ⟨71558213478699625236423233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47705475652466416824282155 71558213478699625236423233)
    ·
      refine ⟨53668660109024718927317425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71558213478699625236423233 53668660109024718927317425)
      ·
        refine ⟨40251495081768539195488069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53668660109024718927317425 40251495081768539195488069)
        ·
          refine ⟨7547155327831601099154013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40251495081768539195488069 7547155327831601099154013)
          ·
            refine ⟨2830183247936850412182755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7547155327831601099154013 2830183247936850412182755)
            ·
              refine ⟨4245274871905275618274133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2830183247936850412182755 4245274871905275618274133)
              ·
                refine ⟨24874657452569974325825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4245274871905275618274133 24874657452569974325825)
                ·
                  rfl

theorem cell23_1307967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 9].length) (baseStart_1307967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307967 prefixEnd_1307967 := by exact prefixLift 1307967
  have htrace : WordTrace (prefixWord ++ tailWord_1307967) baseStart_1307967 baseEnd_1307967 := by
    simpa [prefixWord, tailWord_1307967, baseEnd_1307967] using wordTrace_append hprefix tailTrace_1307967
  have hstable : (prefixWord ++ tailWord_1307967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307967).length < 2 ^ (prefixWord ++ tailWord_1307967).sum := by decide
  have hdescent : baseEnd_1307967 < baseStart_1307967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307972 : List Nat := [2, 3, 4, 1, 1, 3, 1, 3, 1, 1, 3]
def baseStart_1307972 : Nat := 118140960795 + 1307972 * 2 ^ 59
def prefixEnd_1307972 : Nat := 4983230072969 + 3 ^ 40 * 1307972 * 2
def baseEnd_1307972 : Nat := 671618318622661787234753

theorem tailTrace_1307972 : CollatzResearch.WordTrace tailWord_1307972 prefixEnd_1307972 671618318622661787234753 := by
  unfold tailWord_1307972
  simp only [CollatzResearch.WordTrace]
  refine ⟨23852829008724151339107085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31803772011632201785476113 23852829008724151339107085)
  ·
    refine ⟨8944810878271556752165157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23852829008724151339107085 8944810878271556752165157)
    ·
      refine ⟨1677152039675916891030967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8944810878271556752165157 1677152039675916891030967)
      ·
        refine ⟨2515728059513875336546451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1677152039675916891030967 2515728059513875336546451)
        ·
          refine ⟨3773592089270813004819677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2515728059513875336546451 3773592089270813004819677)
          ·
            refine ⟨1415097033476554876807379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3773592089270813004819677 1415097033476554876807379)
            ·
              refine ⟨2122645550214832315211069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1415097033476554876807379 2122645550214832315211069)
              ·
                refine ⟨795992081330562118204151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2122645550214832315211069 795992081330562118204151)
                ·
                  refine ⟨1193988121995843177306227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 795992081330562118204151 1193988121995843177306227)
                  ·
                    refine ⟨1790982182993764765959341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1193988121995843177306227 1790982182993764765959341)
                    ·
                      refine ⟨671618318622661787234753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1790982182993764765959341 671618318622661787234753)
                      ·
                        rfl

theorem cell23_1307972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_1307972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307972 prefixEnd_1307972 := by exact prefixLift 1307972
  have htrace : WordTrace (prefixWord ++ tailWord_1307972) baseStart_1307972 baseEnd_1307972 := by
    simpa [prefixWord, tailWord_1307972, baseEnd_1307972] using wordTrace_append hprefix tailTrace_1307972
  have hstable : (prefixWord ++ tailWord_1307972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307972).length < 2 ^ (prefixWord ++ tailWord_1307972).sum := by decide
  have hdescent : baseEnd_1307972 < baseStart_1307972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308046 : List Nat := [4, 1, 1, 4, 3, 1, 2, 2, 1, 2, 2]
def baseStart_1308046 : Nat := 118140960795 + 1308046 * 2 ^ 59
def prefixEnd_1308046 : Nat := 4983230072969 + 3 ^ 40 * 1308046 * 2
def baseEnd_1308046 : Nat := 671656316191094497709413

theorem tailTrace_1308046 : CollatzResearch.WordTrace tailWord_1308046 prefixEnd_1308046 671656316191094497709413 := by
  unfold tailWord_1308046
  simp only [CollatzResearch.WordTrace]
  refine ⟨5963544627397526664550999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31805571346120142210938661 5963544627397526664550999)
  ·
    refine ⟨8945316941096289996826499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5963544627397526664550999 8945316941096289996826499)
    ·
      refine ⟨13417975411644434995239749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8945316941096289996826499 13417975411644434995239749)
      ·
        refine ⟨2515870389683331561607453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13417975411644434995239749 2515870389683331561607453)
        ·
          refine ⟨943451396131249335602795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2515870389683331561607453 943451396131249335602795)
          ·
            refine ⟨1415177094196874003404193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 943451396131249335602795 1415177094196874003404193)
            ·
              refine ⟨1061382820647655502553145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1415177094196874003404193 1061382820647655502553145)
              ·
                refine ⟨796037115485741626914859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1061382820647655502553145 796037115485741626914859)
                ·
                  refine ⟨1194055673228612440372289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 796037115485741626914859 1194055673228612440372289)
                  ·
                    refine ⟨895541754921459330279217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1194055673228612440372289 895541754921459330279217)
                    ·
                      refine ⟨671656316191094497709413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 895541754921459330279217 671656316191094497709413)
                      ·
                        rfl

theorem cell23_1308046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_1308046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1308046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1308046 prefixEnd_1308046 := by exact prefixLift 1308046
  have htrace : WordTrace (prefixWord ++ tailWord_1308046) baseStart_1308046 baseEnd_1308046 := by
    simpa [prefixWord, tailWord_1308046, baseEnd_1308046] using wordTrace_append hprefix tailTrace_1308046
  have hstable : (prefixWord ++ tailWord_1308046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308046).length < 2 ^ (prefixWord ++ tailWord_1308046).sum := by decide
  have hdescent : baseEnd_1308046 < baseStart_1308046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308064 : List Nat := [2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 4]
def baseStart_1308064 : Nat := 118140960795 + 1308064 * 2 ^ 59
def prefixEnd_1308064 : Nat := 4983230072969 + 3 ^ 40 * 1308064 * 2
def baseEnd_1308064 : Nat := 671665558842875427284329

theorem tailTrace_1308064 : CollatzResearch.WordTrace tailWord_1308064 prefixEnd_1308064 671665558842875427284329 := by
  unfold tailWord_1308064
  simp only [CollatzResearch.WordTrace]
  refine ⟨23854506766557501195281623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31806009022076668260375497 23854506766557501195281623)
  ·
    refine ⟨35781760149836251792922435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23854506766557501195281623 35781760149836251792922435)
    ·
      refine ⟨53672640224754377689383653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35781760149836251792922435 53672640224754377689383653)
      ·
        refine ⟨10063620042141445816759435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53672640224754377689383653 10063620042141445816759435)
        ·
          refine ⟨15095430063212168725139153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10063620042141445816759435 15095430063212168725139153)
          ·
            refine ⟨11321572547409126543854365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15095430063212168725139153 11321572547409126543854365)
            ·
              refine ⟨4245589705278422453945387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11321572547409126543854365 4245589705278422453945387)
              ·
                refine ⟨6368384557917633680918081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4245589705278422453945387 6368384557917633680918081)
                ·
                  refine ⟨4776288418438225260688561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6368384557917633680918081 4776288418438225260688561)
                  ·
                    refine ⟨3582216313828668945516421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4776288418438225260688561 3582216313828668945516421)
                    ·
                      refine ⟨671665558842875427284329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3582216313828668945516421 671665558842875427284329)
                      ·
                        rfl

theorem cell23_1308064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_1308064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1308064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1308064 prefixEnd_1308064 := by exact prefixLift 1308064
  have htrace : WordTrace (prefixWord ++ tailWord_1308064) baseStart_1308064 baseEnd_1308064 := by
    simpa [prefixWord, tailWord_1308064, baseEnd_1308064] using wordTrace_append hprefix tailTrace_1308064
  have hstable : (prefixWord ++ tailWord_1308064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308064).length < 2 ^ (prefixWord ++ tailWord_1308064).sum := by decide
  have hdescent : baseEnd_1308064 < baseStart_1308064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308104 : List Nat := [2, 1, 3, 1, 3, 1, 2, 1, 4, 5]
def baseStart_1308104 : Nat := 118140960795 + 1308104 * 2 ^ 59
def prefixEnd_1308104 : Nat := 4983230072969 + 3 ^ 40 * 1308104 * 2
def baseEnd_1308104 : Nat := 223895366023018423594715

theorem tailTrace_1308104 : CollatzResearch.WordTrace tailWord_1308104 prefixEnd_1308104 223895366023018423594715 := by
  unfold tailWord_1308104
  simp only [CollatzResearch.WordTrace]
  refine ⟨23855236226485044611009683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31806981635313392814679577 23855236226485044611009683)
  ·
    refine ⟨35782854339727566916514525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23855236226485044611009683 35782854339727566916514525)
    ·
      refine ⟨13418570377397837593692947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35782854339727566916514525 13418570377397837593692947)
      ·
        refine ⟨20127855566096756390539421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13418570377397837593692947 20127855566096756390539421)
        ·
          refine ⟨7547945837286283646452283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20127855566096756390539421 7547945837286283646452283)
          ·
            refine ⟨11321918755929425469678425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7547945837286283646452283 11321918755929425469678425)
            ·
              refine ⟨8491439066947069102258819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11321918755929425469678425 8491439066947069102258819)
              ·
                refine ⟨12737158600420603653388229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8491439066947069102258819 12737158600420603653388229)
                ·
                  refine ⟨2388217237578863185010293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12737158600420603653388229 2388217237578863185010293)
                  ·
                    refine ⟨223895366023018423594715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2388217237578863185010293 223895366023018423594715)
                    ·
                      rfl

theorem cell23_1308104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_1308104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1308104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1308104 prefixEnd_1308104 := by exact prefixLift 1308104
  have htrace : WordTrace (prefixWord ++ tailWord_1308104) baseStart_1308104 baseEnd_1308104 := by
    simpa [prefixWord, tailWord_1308104, baseEnd_1308104] using wordTrace_append hprefix tailTrace_1308104
  have hstable : (prefixWord ++ tailWord_1308104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308104).length < 2 ^ (prefixWord ++ tailWord_1308104).sum := by decide
  have hdescent : baseEnd_1308104 < baseStart_1308104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308118 : List Nat := [5, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3]
def baseStart_1308118 : Nat := 118140960795 + 1308118 * 2 ^ 59
def prefixEnd_1308118 : Nat := 4983230072969 + 3 ^ 40 * 1308118 * 2
def baseEnd_1308118 : Nat := 671693286798218216009081

theorem tailTrace_1308118 : CollatzResearch.WordTrace tailWord_1308118 prefixEnd_1308118 671693286798218216009081 := by
  unfold tailWord_1308118
  simp only [CollatzResearch.WordTrace]
  refine ⟨2981936442182460600814313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31807322049946246408686005 2981936442182460600814313)
  ·
    refine ⟨2236452331636845450610735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2981936442182460600814313 2236452331636845450610735)
    ·
      refine ⟨3354678497455268175916103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2236452331636845450610735 3354678497455268175916103)
      ·
        refine ⟨5032017746182902263874155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3354678497455268175916103 5032017746182902263874155)
        ·
          refine ⟨7548026619274353395811233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5032017746182902263874155 7548026619274353395811233)
          ·
            refine ⟨5661019964455765046858425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7548026619274353395811233 5661019964455765046858425)
            ·
              refine ⟨4245764973341823785143819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5661019964455765046858425 4245764973341823785143819)
              ·
                refine ⟨6368647460012735677715729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4245764973341823785143819 6368647460012735677715729)
                ·
                  refine ⟨4776485595009551758286797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6368647460012735677715729 4776485595009551758286797)
                  ·
                    refine ⟨1791182098128581909357549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4776485595009551758286797 1791182098128581909357549)
                    ·
                      refine ⟨671693286798218216009081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1791182098128581909357549 671693286798218216009081)
                      ·
                        rfl

theorem cell23_1308118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_1308118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1308118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1308118 prefixEnd_1308118 := by exact prefixLift 1308118
  have htrace : WordTrace (prefixWord ++ tailWord_1308118) baseStart_1308118 baseEnd_1308118 := by
    simpa [prefixWord, tailWord_1308118, baseEnd_1308118] using wordTrace_append hprefix tailTrace_1308118
  have hstable : (prefixWord ++ tailWord_1308118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308118).length < 2 ^ (prefixWord ++ tailWord_1308118).sum := by decide
  have hdescent : baseEnd_1308118 < baseStart_1308118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308168 : List Nat := [2, 1, 3, 2, 1, 1, 2, 6, 1, 4]
def baseStart_1308168 : Nat := 118140960795 + 1308168 * 2 ^ 59
def prefixEnd_1308168 : Nat := 4983230072969 + 3 ^ 40 * 1308168 * 2
def baseEnd_1308168 : Nat := 223906320276981006794617

theorem tailTrace_1308168 : CollatzResearch.WordTrace tailWord_1308168 prefixEnd_1308168 223906320276981006794617 := by
  unfold tailWord_1308168
  simp only [CollatzResearch.WordTrace]
  refine ⟨23856403362369114076174579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31808537816492152101566105 23856403362369114076174579)
  ·
    refine ⟨35784605043553671114261869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23856403362369114076174579 35784605043553671114261869)
    ·
      refine ⟨13419226891332626667848201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35784605043553671114261869 13419226891332626667848201)
      ·
        refine ⟨10064420168499470000886151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13419226891332626667848201 10064420168499470000886151)
        ·
          refine ⟨15096630252749205001329227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10064420168499470000886151 15096630252749205001329227)
          ·
            refine ⟨22644945379123807501993841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15096630252749205001329227 22644945379123807501993841)
            ·
              refine ⟨16983709034342855626495381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22644945379123807501993841 16983709034342855626495381)
              ·
                refine ⟨796111360984821357491971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16983709034342855626495381 796111360984821357491971)
                ·
                  refine ⟨1194167041477232036237957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 796111360984821357491971 1194167041477232036237957)
                  ·
                    refine ⟨223906320276981006794617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1194167041477232036237957 223906320276981006794617)
                    ·
                      rfl

theorem cell23_1308168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 6, 1, 4].length) (baseStart_1308168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1308168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1308168 prefixEnd_1308168 := by exact prefixLift 1308168
  have htrace : WordTrace (prefixWord ++ tailWord_1308168) baseStart_1308168 baseEnd_1308168 := by
    simpa [prefixWord, tailWord_1308168, baseEnd_1308168] using wordTrace_append hprefix tailTrace_1308168
  have hstable : (prefixWord ++ tailWord_1308168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308168).length < 2 ^ (prefixWord ++ tailWord_1308168).sum := by decide
  have hdescent : baseEnd_1308168 < baseStart_1308168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308181 : List Nat := [1, 3, 2, 1, 3, 3, 1, 3, 6]
def baseStart_1308181 : Nat := 118140960795 + 1308181 * 2 ^ 59
def prefixEnd_1308181 : Nat := 4983230072969 + 3 ^ 40 * 1308181 * 2
def baseEnd_1308181 : Nat := 74636181786605718835699

theorem tailTrace_1308181 : CollatzResearch.WordTrace tailWord_1308181 prefixEnd_1308181 74636181786605718835699 := by
  unfold tailWord_1308181
  simp only [CollatzResearch.WordTrace]
  refine ⟨47713280873691131372572397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31808853915794087581714931 47713280873691131372572397)
  ·
    refine ⟨17892480327634174264714649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47713280873691131372572397 17892480327634174264714649)
    ·
      refine ⟨13419360245725630698535987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17892480327634174264714649 13419360245725630698535987)
      ·
        refine ⟨20129040368588446047803981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13419360245725630698535987 20129040368588446047803981)
        ·
          refine ⟨7548390138220667267926493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20129040368588446047803981 7548390138220667267926493)
          ·
            refine ⟨2830646301832750225472435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7548390138220667267926493 2830646301832750225472435)
            ·
              refine ⟨4245969452749125338208653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2830646301832750225472435 4245969452749125338208653)
              ·
                refine ⟨1592238544780922001828245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4245969452749125338208653 1592238544780922001828245)
                ·
                  refine ⟨74636181786605718835699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1592238544780922001828245 74636181786605718835699)
                  ·
                    rfl

theorem cell23_1308181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 3, 6].length) (baseStart_1308181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1308181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1308181 prefixEnd_1308181 := by exact prefixLift 1308181
  have htrace : WordTrace (prefixWord ++ tailWord_1308181) baseStart_1308181 baseEnd_1308181 := by
    simpa [prefixWord, tailWord_1308181, baseEnd_1308181] using wordTrace_append hprefix tailTrace_1308181
  have hstable : (prefixWord ++ tailWord_1308181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308181).length < 2 ^ (prefixWord ++ tailWord_1308181).sum := by decide
  have hdescent : baseEnd_1308181 < baseStart_1308181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308218 : List Nat := [3, 1, 1, 1, 3, 2, 1, 4, 2, 3, 2]
def baseStart_1308218 : Nat := 118140960795 + 1308218 * 2 ^ 59
def prefixEnd_1308218 : Nat := 4983230072969 + 3 ^ 40 * 1308218 * 2
def baseEnd_1308218 : Nat := 671744634863667824758621

theorem tailTrace_1308218 : CollatzResearch.WordTrace tailWord_1308218 prefixEnd_1308218 671744634863667824758621 := by
  unfold tailWord_1308218
  simp only [CollatzResearch.WordTrace]
  refine ⟨11928657593639271672917327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31809753583038057794446205 11928657593639271672917327)
  ·
    refine ⟨17892986390458907509375991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11928657593639271672917327 17892986390458907509375991)
    ·
      refine ⟨26839479585688361264063987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17892986390458907509375991 26839479585688361264063987)
      ·
        refine ⟨40259219378532541896095981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26839479585688361264063987 40259219378532541896095981)
        ·
          refine ⟨15097207266949703211035993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40259219378532541896095981 15097207266949703211035993)
          ·
            refine ⟨11322905450212277408276995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15097207266949703211035993 11322905450212277408276995)
            ·
              refine ⟨16984358175318416112415493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11322905450212277408276995 16984358175318416112415493)
              ·
                refine ⟨3184567157872203021077905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16984358175318416112415493 3184567157872203021077905)
                ·
                  refine ⟨2388425368404152265808429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3184567157872203021077905 2388425368404152265808429)
                  ·
                    refine ⟨895659513151557099678161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2388425368404152265808429 895659513151557099678161)
                    ·
                      refine ⟨671744634863667824758621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 895659513151557099678161 671744634863667824758621)
                      ·
                        rfl

theorem cell23_1308218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 2, 3, 2].length) (baseStart_1308218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1308218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1308218 prefixEnd_1308218 := by exact prefixLift 1308218
  have htrace : WordTrace (prefixWord ++ tailWord_1308218) baseStart_1308218 baseEnd_1308218 := by
    simpa [prefixWord, tailWord_1308218, baseEnd_1308218] using wordTrace_append hprefix tailTrace_1308218
  have hstable : (prefixWord ++ tailWord_1308218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308218).length < 2 ^ (prefixWord ++ tailWord_1308218).sum := by decide
  have hdescent : baseEnd_1308218 < baseStart_1308218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308224 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 5, 6]
def baseStart_1308224 : Nat := 118140960795 + 1308224 * 2 ^ 59
def prefixEnd_1308224 : Nat := 4983230072969 + 3 ^ 40 * 1308224 * 2
def baseEnd_1308224 : Nat := 223915905249198267094531

theorem tailTrace_1308224 : CollatzResearch.WordTrace tailWord_1308224 prefixEnd_1308224 223915905249198267094531 := by
  unfold tailWord_1308224
  simp only [CollatzResearch.WordTrace]
  refine ⟨23857424606267674858193863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31809899475023566477591817 23857424606267674858193863)
  ·
    refine ⟨35786136909401512287290795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23857424606267674858193863 35786136909401512287290795)
    ·
      refine ⟨53679205364102268430936193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35786136909401512287290795 53679205364102268430936193)
      ·
        refine ⟨40259404023076701323202145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53679205364102268430936193 40259404023076701323202145)
        ·
          refine ⟨30194553017307525992401609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40259404023076701323202145 30194553017307525992401609)
          ·
            refine ⟨22645914762980644494301207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30194553017307525992401609 22645914762980644494301207)
            ·
              refine ⟨33968872144470966741451811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22645914762980644494301207 33968872144470966741451811)
              ·
                refine ⟨50953308216706450112177717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33968872144470966741451811 50953308216706450112177717)
                ·
                  refine ⟨4776872645316229698016661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50953308216706450112177717 4776872645316229698016661)
                  ·
                    refine ⟨223915905249198267094531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4776872645316229698016661 223915905249198267094531)
                    ·
                      rfl

theorem cell23_1308224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 5, 6].length) (baseStart_1308224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1308224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1308224 prefixEnd_1308224 := by exact prefixLift 1308224
  have htrace : WordTrace (prefixWord ++ tailWord_1308224) baseStart_1308224 baseEnd_1308224 := by
    simpa [prefixWord, tailWord_1308224, baseEnd_1308224] using wordTrace_append hprefix tailTrace_1308224
  have hstable : (prefixWord ++ tailWord_1308224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308224).length < 2 ^ (prefixWord ++ tailWord_1308224).sum := by decide
  have hdescent : baseEnd_1308224 < baseStart_1308224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308241 : List Nat := [1, 2, 2, 1, 3, 2, 4, 1, 1, 6]
def baseStart_1308241 : Nat := 118140960795 + 1308241 * 2 ^ 59
def prefixEnd_1308241 : Nat := 4983230072969 + 3 ^ 40 * 1308241 * 2
def baseEnd_1308241 : Nat := 223918814972907078257005

theorem tailTrace_1308241 : CollatzResearch.WordTrace tailWord_1308241 prefixEnd_1308241 223918814972907078257005 := by
  unfold tailWord_1308241
  simp only [CollatzResearch.WordTrace]
  refine ⟨47715469253473761619756577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31810312835649174413171051 47715469253473761619756577)
  ·
    refine ⟨35786601940105321214817433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47715469253473761619756577 35786601940105321214817433)
    ·
      refine ⟨26839951455078990911113075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35786601940105321214817433 26839951455078990911113075)
      ·
        refine ⟨40259927182618486366669613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26839951455078990911113075 40259927182618486366669613)
        ·
          refine ⟨15097472693481932387501105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40259927182618486366669613 15097472693481932387501105)
          ·
            refine ⟨11323104520111449290625829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15097472693481932387501105 11323104520111449290625829)
            ·
              refine ⟨2123082097520896741992343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11323104520111449290625829 2123082097520896741992343)
              ·
                refine ⟨3184623146281345112988515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2123082097520896741992343 3184623146281345112988515)
                ·
                  refine ⟨4776934719422017669482773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3184623146281345112988515 4776934719422017669482773)
                  ·
                    refine ⟨223918814972907078257005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4776934719422017669482773 223918814972907078257005)
                    ·
                      rfl

theorem cell23_1308241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 6].length) (baseStart_1308241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1308241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1308241 prefixEnd_1308241 := by exact prefixLift 1308241
  have htrace : WordTrace (prefixWord ++ tailWord_1308241) baseStart_1308241 baseEnd_1308241 := by
    simpa [prefixWord, tailWord_1308241, baseEnd_1308241] using wordTrace_append hprefix tailTrace_1308241
  have hstable : (prefixWord ++ tailWord_1308241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308241).length < 2 ^ (prefixWord ++ tailWord_1308241).sum := by decide
  have hdescent : baseEnd_1308241 < baseStart_1308241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308246 : List Nat := [5, 2, 2, 2, 2, 1, 1, 1, 2, 2, 3]
def baseStart_1308246 : Nat := 118140960795 + 1308246 * 2 ^ 59
def prefixEnd_1308246 : Nat := 4983230072969 + 3 ^ 40 * 1308246 * 2
def baseEnd_1308246 : Nat := 671759012321993715208493

theorem tailTrace_1308246 : CollatzResearch.WordTrace tailWord_1308246 prefixEnd_1308246 671759012321993715208493 := by
  unfold tailWord_1308246
  simp only [CollatzResearch.WordTrace]
  refine ⟨2982228226153477967105537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31810434412303764982459061 2982228226153477967105537)
  ·
    refine ⟨2236671169615108475329153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2982228226153477967105537 2236671169615108475329153)
    ·
      refine ⟨1677503377211331356496865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2236671169615108475329153 1677503377211331356496865)
      ·
        refine ⟨1258127532908498517372649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1677503377211331356496865 1258127532908498517372649)
        ·
          refine ⟨943595649681373888029487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1258127532908498517372649 943595649681373888029487)
          ·
            refine ⟨1415393474522060832044231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 943595649681373888029487 1415393474522060832044231)
            ·
              refine ⟨2123090211783091248066347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1415393474522060832044231 2123090211783091248066347)
              ·
                refine ⟨3184635317674636872099521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2123090211783091248066347 3184635317674636872099521)
                ·
                  refine ⟨2388476488255977654074641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3184635317674636872099521 2388476488255977654074641)
                  ·
                    refine ⟨1791357366191983240555981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2388476488255977654074641 1791357366191983240555981)
                    ·
                      refine ⟨671759012321993715208493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1791357366191983240555981 671759012321993715208493)
                      ·
                        rfl

theorem cell23_1308246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_1308246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1308246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1308246 prefixEnd_1308246 := by exact prefixLift 1308246
  have htrace : WordTrace (prefixWord ++ tailWord_1308246) baseStart_1308246 baseEnd_1308246 := by
    simpa [prefixWord, tailWord_1308246, baseEnd_1308246] using wordTrace_append hprefix tailTrace_1308246
  have hstable : (prefixWord ++ tailWord_1308246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308246).length < 2 ^ (prefixWord ++ tailWord_1308246).sum := by decide
  have hdescent : baseEnd_1308246 < baseStart_1308246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308252 : List Nat := [2, 2, 4, 1, 2, 3, 1, 1, 2, 3, 2]
def baseStart_1308252 : Nat := 118140960795 + 1308252 * 2 ^ 59
def prefixEnd_1308252 : Nat := 4983230072969 + 3 ^ 40 * 1308252 * 2
def baseEnd_1308252 : Nat := 671762093205920691733465

theorem tailTrace_1308252 : CollatzResearch.WordTrace tailWord_1308252 prefixEnd_1308252 671762093205920691733465 := by
  unfold tailWord_1308252
  simp only [CollatzResearch.WordTrace]
  refine ⟨23857935228216955249203505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31810580304289273665604673 23857935228216955249203505)
  ·
    refine ⟨17893451421162716436902629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23857935228216955249203505 17893451421162716436902629)
    ·
      refine ⟨3355022141468009331919243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17893451421162716436902629 3355022141468009331919243)
      ·
        refine ⟨5032533212202013997878865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3355022141468009331919243 5032533212202013997878865)
        ·
          refine ⟨3774399909151510498409149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5032533212202013997878865 3774399909151510498409149)
          ·
            refine ⟨1415399965931816436903431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3774399909151510498409149 1415399965931816436903431)
            ·
              refine ⟨2123099948897724655355147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1415399965931816436903431 2123099948897724655355147)
              ·
                refine ⟨3184649923346586983032721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2123099948897724655355147 3184649923346586983032721)
                ·
                  refine ⟨2388487442509940237274541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3184649923346586983032721 2388487442509940237274541)
                  ·
                    refine ⟨895682790941227588977953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2388487442509940237274541 895682790941227588977953)
                    ·
                      refine ⟨671762093205920691733465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 895682790941227588977953 671762093205920691733465)
                      ·
                        rfl

theorem cell23_1308252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_1308252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1308252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1308252 prefixEnd_1308252 := by exact prefixLift 1308252
  have htrace : WordTrace (prefixWord ++ tailWord_1308252) baseStart_1308252 baseEnd_1308252 := by
    simpa [prefixWord, tailWord_1308252, baseEnd_1308252] using wordTrace_append hprefix tailTrace_1308252
  have hstable : (prefixWord ++ tailWord_1308252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308252).length < 2 ^ (prefixWord ++ tailWord_1308252).sum := by decide
  have hdescent : baseEnd_1308252 < baseStart_1308252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308292 : List Nat := [2, 3, 2, 1, 4, 1, 3, 1, 2, 4]
def baseStart_1308292 : Nat := 118140960795 + 1308292 * 2 ^ 59
def prefixEnd_1308292 : Nat := 4983230072969 + 3 ^ 40 * 1308292 * 2
def baseEnd_1308292 : Nat := 223927544144033511744427

theorem tailTrace_1308292 : CollatzResearch.WordTrace tailWord_1308292 prefixEnd_1308292 223927544144033511744427 := by
  unfold tailWord_1308292
  simp only [CollatzResearch.WordTrace]
  refine ⟨23858664688144498664931565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31811552917525998219908753 23858664688144498664931565)
  ·
    refine ⟨8946999258054186999349337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23858664688144498664931565 8946999258054186999349337)
    ·
      refine ⟨6710249443540640249512003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8946999258054186999349337 6710249443540640249512003)
      ·
        refine ⟨10065374165310960374268005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6710249443540640249512003 10065374165310960374268005)
        ·
          refine ⟨1887257655995805070175251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10065374165310960374268005 1887257655995805070175251)
          ·
            refine ⟨2830886483993707605262877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1887257655995805070175251 2830886483993707605262877)
            ·
              refine ⟨1061582431497640351973579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2830886483993707605262877 1061582431497640351973579)
              ·
                refine ⟨1592373647246460527960369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1061582431497640351973579 1592373647246460527960369)
                ·
                  refine ⟨1194280235434845395970277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1592373647246460527960369 1194280235434845395970277)
                  ·
                    refine ⟨223927544144033511744427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1194280235434845395970277 223927544144033511744427)
                    ·
                      rfl

theorem cell23_1308292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_1308292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1308292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1308292 prefixEnd_1308292 := by exact prefixLift 1308292
  have htrace : WordTrace (prefixWord ++ tailWord_1308292) baseStart_1308292 baseEnd_1308292 := by
    simpa [prefixWord, tailWord_1308292, baseEnd_1308292] using wordTrace_append hprefix tailTrace_1308292
  have hstable : (prefixWord ++ tailWord_1308292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308292).length < 2 ^ (prefixWord ++ tailWord_1308292).sum := by decide
  have hdescent : baseEnd_1308292 < baseStart_1308292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308311 : List Nat := [1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 5]
def baseStart_1308311 : Nat := 118140960795 + 1308311 * 2 ^ 59
def prefixEnd_1308311 : Nat := 4983230072969 + 3 ^ 40 * 1308311 * 2
def baseEnd_1308311 : Nat := 671792388564535960895693

theorem tailTrace_1308311 : CollatzResearch.WordTrace tailWord_1308311 prefixEnd_1308311 671792388564535960895693 := by
  unfold tailWord_1308311
  simp only [CollatzResearch.WordTrace]
  refine ⟨47718022363220163574804787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31812014908813442383203191 47718022363220163574804787)
  ·
    refine ⟨71577033544830245362207181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47718022363220163574804787 71577033544830245362207181)
    ·
      refine ⟨26841387579311342010827693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71577033544830245362207181 26841387579311342010827693)
      ·
        refine ⟨10065520342241753254060385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26841387579311342010827693 10065520342241753254060385)
        ·
          refine ⟨7549140256681314940545289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10065520342241753254060385 7549140256681314940545289)
          ·
            refine ⟨5661855192510986205408967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7549140256681314940545289 5661855192510986205408967)
            ·
              refine ⟨8492782788766479308113451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5661855192510986205408967 8492782788766479308113451)
              ·
                refine ⟨12739174183149718962170177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8492782788766479308113451 12739174183149718962170177)
                ·
                  refine ⟨9554380637362289221627633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12739174183149718962170177 9554380637362289221627633)
                  ·
                    refine ⟨7165785478021716916220725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9554380637362289221627633 7165785478021716916220725)
                    ·
                      refine ⟨671792388564535960895693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7165785478021716916220725 671792388564535960895693)
                      ·
                        rfl

theorem cell23_1308311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_1308311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1308311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1308311 prefixEnd_1308311 := by exact prefixLift 1308311
  have htrace : WordTrace (prefixWord ++ tailWord_1308311) baseStart_1308311 baseEnd_1308311 := by
    simpa [prefixWord, tailWord_1308311, baseEnd_1308311] using wordTrace_append hprefix tailTrace_1308311
  have hstable : (prefixWord ++ tailWord_1308311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308311).length < 2 ^ (prefixWord ++ tailWord_1308311).sum := by decide
  have hdescent : baseEnd_1308311 < baseStart_1308311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308316 : List Nat := [2, 2, 3, 2, 3, 2, 1, 3, 1, 2, 2]
def baseStart_1308316 : Nat := 118140960795 + 1308316 * 2 ^ 59
def prefixEnd_1308316 : Nat := 4983230072969 + 3 ^ 40 * 1308316 * 2
def baseEnd_1308316 : Nat := 671794955967808441333171

theorem tailTrace_1308316 : CollatzResearch.WordTrace tailWord_1308316 prefixEnd_1308316 671794955967808441333171 := by
  unfold tailWord_1308316
  simp only [CollatzResearch.WordTrace]
  refine ⟨23859102364101024714368401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31812136485468032952491201 23859102364101024714368401)
  ·
    refine ⟨17894326773075768535776301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23859102364101024714368401 17894326773075768535776301)
    ·
      refine ⟨6710372539903413200916113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17894326773075768535776301 6710372539903413200916113)
      ·
        refine ⟨5032779404927559900687085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6710372539903413200916113 5032779404927559900687085)
        ·
          refine ⟨1887292276847834962757657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5032779404927559900687085 1887292276847834962757657)
          ·
            refine ⟨1415469207635876222068243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1887292276847834962757657 1415469207635876222068243)
            ·
              refine ⟨2123203811453814333102365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1415469207635876222068243 2123203811453814333102365)
              ·
                refine ⟨796201429295180374913387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2123203811453814333102365 796201429295180374913387)
                ·
                  refine ⟨1194302143942770562370081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 796201429295180374913387 1194302143942770562370081)
                  ·
                    refine ⟨895726607957077921777561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1194302143942770562370081 895726607957077921777561)
                    ·
                      refine ⟨671794955967808441333171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 895726607957077921777561 671794955967808441333171)
                      ·
                        rfl

theorem cell23_1308316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_1308316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1308316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1308316 prefixEnd_1308316 := by exact prefixLift 1308316
  have htrace : WordTrace (prefixWord ++ tailWord_1308316) baseStart_1308316 baseEnd_1308316 := by
    simpa [prefixWord, tailWord_1308316, baseEnd_1308316] using wordTrace_append hprefix tailTrace_1308316
  have hstable : (prefixWord ++ tailWord_1308316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308316).length < 2 ^ (prefixWord ++ tailWord_1308316).sum := by decide
  have hdescent : baseEnd_1308316 < baseStart_1308316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308325 : List Nat := [1, 3, 1, 2, 1, 2, 4, 3, 1, 3, 2]
def baseStart_1308325 : Nat := 118140960795 + 1308325 * 2 ^ 59
def prefixEnd_1308325 : Nat := 4983230072969 + 3 ^ 40 * 1308325 * 2
def baseEnd_1308325 : Nat := 671799577293698906120629

theorem tailTrace_1308325 : CollatzResearch.WordTrace tailWord_1308325 prefixEnd_1308325 671799577293698906120629 := by
  unfold tailWord_1308325
  simp only [CollatzResearch.WordTrace]
  refine ⟨47718532985169443965814429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31812355323446295977209619 47718532985169443965814429)
  ·
    refine ⟨17894449869438541487180411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47718532985169443965814429 17894449869438541487180411)
    ·
      refine ⟨26841674804157812230770617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17894449869438541487180411 26841674804157812230770617)
      ·
        refine ⟨20131256103118359173077963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26841674804157812230770617 20131256103118359173077963)
        ·
          refine ⟨30196884154677538759616945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20131256103118359173077963 30196884154677538759616945)
          ·
            refine ⟨22647663116008154069712709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30196884154677538759616945 22647663116008154069712709)
            ·
              refine ⟨4246436834251528888071133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22647663116008154069712709 4246436834251528888071133)
              ·
                refine ⟨1592413812844323333026675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4246436834251528888071133 1592413812844323333026675)
                ·
                  refine ⟨2388620719266484999540013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1592413812844323333026675 2388620719266484999540013)
                  ·
                    refine ⟨895732769724931874827505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2388620719266484999540013 895732769724931874827505)
                    ·
                      refine ⟨671799577293698906120629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 895732769724931874827505 671799577293698906120629)
                      ·
                        rfl

theorem cell23_1308325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 3, 1, 3, 2].length) (baseStart_1308325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1308325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1308325 prefixEnd_1308325 := by exact prefixLift 1308325
  have htrace : WordTrace (prefixWord ++ tailWord_1308325) baseStart_1308325 baseEnd_1308325 := by
    simpa [prefixWord, tailWord_1308325, baseEnd_1308325] using wordTrace_append hprefix tailTrace_1308325
  have hstable : (prefixWord ++ tailWord_1308325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308325).length < 2 ^ (prefixWord ++ tailWord_1308325).sum := by decide
  have hdescent : baseEnd_1308325 < baseStart_1308325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308351 : List Nat := [1, 1, 2, 2, 2, 3, 2, 1, 1, 4, 4]
def baseStart_1308351 : Nat := 118140960795 + 1308351 * 2 ^ 59
def prefixEnd_1308351 : Nat := 4983230072969 + 3 ^ 40 * 1308351 * 2
def baseEnd_1308351 : Nat := 671812927790715804395509

theorem tailTrace_1308351 : CollatzResearch.WordTrace tailWord_1308351 prefixEnd_1308351 671812927790715804395509 := by
  unfold tailWord_1308351
  simp only [CollatzResearch.WordTrace]
  refine ⟨47719481283075250406260907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31812987522050166937507271 47719481283075250406260907)
  ·
    refine ⟨71579221924612875609391361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47719481283075250406260907 71579221924612875609391361)
    ·
      refine ⟨53684416443459656707043521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71579221924612875609391361 53684416443459656707043521)
      ·
        refine ⟨40263312332594742530282641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53684416443459656707043521 40263312332594742530282641)
        ·
          refine ⟨30197484249446056897711981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40263312332594742530282641 30197484249446056897711981)
          ·
            refine ⟨11324056593542271336641993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30197484249446056897711981 11324056593542271336641993)
            ·
              refine ⟨8493042445156703502481495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11324056593542271336641993 8493042445156703502481495)
              ·
                refine ⟨12739563667735055253722243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8493042445156703502481495 12739563667735055253722243)
                ·
                  refine ⟨19109345501602582880583365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12739563667735055253722243 19109345501602582880583365)
                  ·
                    refine ⟨3583002281550484290109381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19109345501602582880583365 3583002281550484290109381)
                    ·
                      refine ⟨671812927790715804395509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3583002281550484290109381 671812927790715804395509)
                      ·
                        rfl

theorem cell23_1308351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 4, 4].length) (baseStart_1308351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1308351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1308351 prefixEnd_1308351 := by exact prefixLift 1308351
  have htrace : WordTrace (prefixWord ++ tailWord_1308351) baseStart_1308351 baseEnd_1308351 := by
    simpa [prefixWord, tailWord_1308351, baseEnd_1308351] using wordTrace_append hprefix tailTrace_1308351
  have hstable : (prefixWord ++ tailWord_1308351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308351).length < 2 ^ (prefixWord ++ tailWord_1308351).sum := by decide
  have hdescent : baseEnd_1308351 < baseStart_1308351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308372 : List Nat := [2, 4, 1, 3, 1, 2, 1, 2, 1, 4, 2]
def baseStart_1308372 : Nat := 118140960795 + 1308372 * 2 ^ 59
def prefixEnd_1308372 : Nat := 4983230072969 + 3 ^ 40 * 1308372 * 2
def baseEnd_1308372 : Nat := 671823710884460222232913

theorem tailTrace_1308372 : CollatzResearch.WordTrace tailWord_1308372 prefixEnd_1308372 671823710884460222232913 := by
  unfold tailWord_1308372
  simp only [CollatzResearch.WordTrace]
  refine ⟨23860123607999585496387685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31813498143999447328516913 23860123607999585496387685)
  ·
    refine ⟨4473773176499922280572691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23860123607999585496387685 4473773176499922280572691)
    ·
      refine ⟨6710659764749883420859037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4473773176499922280572691 6710659764749883420859037)
      ·
        refine ⟨2516497411781206282822139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6710659764749883420859037 2516497411781206282822139)
        ·
          refine ⟨3774746117671809424233209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2516497411781206282822139 3774746117671809424233209)
          ·
            refine ⟨2831059588253857068174907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3774746117671809424233209 2831059588253857068174907)
            ·
              refine ⟨4246589382380785602262361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2831059588253857068174907 4246589382380785602262361)
              ·
                refine ⟨3184942036785589201696771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4246589382380785602262361 3184942036785589201696771)
                ·
                  refine ⟨4777413055178383802545157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3184942036785589201696771 4777413055178383802545157)
                  ·
                    refine ⟨895764947845946962977217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4777413055178383802545157 895764947845946962977217)
                    ·
                      refine ⟨671823710884460222232913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 895764947845946962977217 671823710884460222232913)
                      ·
                        rfl

theorem cell23_1308372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_1308372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1308372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1308372 prefixEnd_1308372 := by exact prefixLift 1308372
  have htrace : WordTrace (prefixWord ++ tailWord_1308372) baseStart_1308372 baseEnd_1308372 := by
    simpa [prefixWord, tailWord_1308372, baseEnd_1308372] using wordTrace_append hprefix tailTrace_1308372
  have hstable : (prefixWord ++ tailWord_1308372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308372).length < 2 ^ (prefixWord ++ tailWord_1308372).sum := by decide
  have hdescent : baseEnd_1308372 < baseStart_1308372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308388 : List Nat := [2, 3, 1, 1, 1, 3, 2, 2, 2, 3, 3]
def baseStart_1308388 : Nat := 118140960795 + 1308388 * 2 ^ 59
def prefixEnd_1308388 : Nat := 4983230072969 + 3 ^ 40 * 1308388 * 2
def baseEnd_1308388 : Nat := 671831926574932159632839

theorem tailTrace_1308388 : CollatzResearch.WordTrace tailWord_1308388 prefixEnd_1308388 671831926574932159632839 := by
  unfold tailWord_1308388
  simp only [CollatzResearch.WordTrace]
  refine ⟨23860415391970602862678909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31813887189294137150238545 23860415391970602862678909)
  ·
    refine ⟨8947655771988976073504591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23860415391970602862678909 8947655771988976073504591)
    ·
      refine ⟨13421483657983464110256887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8947655771988976073504591 13421483657983464110256887)
      ·
        refine ⟨20132225486975196165385331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13421483657983464110256887 20132225486975196165385331)
        ·
          refine ⟨30198338230462794248077997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20132225486975196165385331 30198338230462794248077997)
          ·
            refine ⟨11324376836423547843029249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30198338230462794248077997 11324376836423547843029249)
            ·
              refine ⟨8493282627317660882271937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11324376836423547843029249 8493282627317660882271937)
              ·
                refine ⟨6369961970488245661703953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8493282627317660882271937 6369961970488245661703953)
                ·
                  refine ⟨4777471477866184246277965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6369961970488245661703953 4777471477866184246277965)
                  ·
                    refine ⟨1791551804199819092354237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4777471477866184246277965 1791551804199819092354237)
                    ·
                      refine ⟨671831926574932159632839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1791551804199819092354237 671831926574932159632839)
                      ·
                        rfl

theorem cell23_1308388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 2, 3, 3].length) (baseStart_1308388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1308388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1308388 prefixEnd_1308388 := by exact prefixLift 1308388
  have htrace : WordTrace (prefixWord ++ tailWord_1308388) baseStart_1308388 baseEnd_1308388 := by
    simpa [prefixWord, tailWord_1308388, baseEnd_1308388] using wordTrace_append hprefix tailTrace_1308388
  have hstable : (prefixWord ++ tailWord_1308388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308388).length < 2 ^ (prefixWord ++ tailWord_1308388).sum := by decide
  have hdescent : baseEnd_1308388 < baseStart_1308388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308395 : List Nat := [1, 1, 1, 1, 2, 4, 6, 2, 5]
def baseStart_1308395 : Nat := 118140960795 + 1308395 * 2 ^ 59
def prefixEnd_1308395 : Nat := 4983230072969 + 3 ^ 40 * 1308395 * 2
def baseEnd_1308395 : Nat := 74648391215501514693923

theorem tailTrace_1308395 : CollatzResearch.WordTrace tailWord_1308395 prefixEnd_1308395 74648391215501514693923 := by
  unfold tailWord_1308395
  simp only [CollatzResearch.WordTrace]
  refine ⟨47721086094915845920862639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31814057396610563947241759 47721086094915845920862639)
  ·
    refine ⟨71581629142373768881293959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47721086094915845920862639 71581629142373768881293959)
    ·
      refine ⟨107372443713560653321940939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71581629142373768881293959 107372443713560653321940939)
      ·
        refine ⟨161058665570340979982911409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107372443713560653321940939 161058665570340979982911409)
        ·
          refine ⟨120793999177755734987183557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161058665570340979982911409 120793999177755734987183557)
          ·
            refine ⟨22648874845829200310096917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120793999177755734987183557 22648874845829200310096917)
            ·
              refine ⟨1061666008398243764535793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22648874845829200310096917 1061666008398243764535793)
              ·
                refine ⟨796249506298682823401845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1061666008398243764535793 796249506298682823401845)
                ·
                  refine ⟨74648391215501514693923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 796249506298682823401845 74648391215501514693923)
                  ·
                    rfl

theorem cell23_1308395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 2, 5].length) (baseStart_1308395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1308395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1308395 prefixEnd_1308395 := by exact prefixLift 1308395
  have htrace : WordTrace (prefixWord ++ tailWord_1308395) baseStart_1308395 baseEnd_1308395 := by
    simpa [prefixWord, tailWord_1308395, baseEnd_1308395] using wordTrace_append hprefix tailTrace_1308395
  have hstable : (prefixWord ++ tailWord_1308395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308395).length < 2 ^ (prefixWord ++ tailWord_1308395).sum := by decide
  have hdescent : baseEnd_1308395 < baseStart_1308395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308431 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 5]
def baseStart_1308431 : Nat := 118140960795 + 1308431 * 2 ^ 59
def prefixEnd_1308431 : Nat := 4983230072969 + 3 ^ 40 * 1308431 * 2
def baseEnd_1308431 : Nat := 671854006243075491395141

theorem tailTrace_1308431 : CollatzResearch.WordTrace tailWord_1308431 prefixEnd_1308431 671854006243075491395141 := by
  unfold tailWord_1308431
  simp only [CollatzResearch.WordTrace]
  refine ⟨47722399122785424069173147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31814932748523616046115431 47722399122785424069173147)
  ·
    refine ⟨71583598684178136103759721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47722399122785424069173147 71583598684178136103759721)
    ·
      refine ⟨53687699013133602077819791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71583598684178136103759721 53687699013133602077819791)
      ·
        refine ⟨80531548519700403116729687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53687699013133602077819791 80531548519700403116729687)
        ·
          refine ⟨120797322779550604675094531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80531548519700403116729687 120797322779550604675094531)
          ·
            refine ⟨181195984169325907012641797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120797322779550604675094531 181195984169325907012641797)
            ·
              refine ⟨33974247031748607564870337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 181195984169325907012641797 33974247031748607564870337)
              ·
                refine ⟨25480685273811455673652753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33974247031748607564870337 25480685273811455673652753)
                ·
                  refine ⟨19110513955358591755239565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25480685273811455673652753 19110513955358591755239565)
                  ·
                    refine ⟨7166442733259471908214837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19110513955358591755239565 7166442733259471908214837)
                    ·
                      refine ⟨671854006243075491395141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7166442733259471908214837 671854006243075491395141)
                      ·
                        rfl

theorem cell23_1308431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 5].length) (baseStart_1308431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1308431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1308431 prefixEnd_1308431 := by exact prefixLift 1308431
  have htrace : WordTrace (prefixWord ++ tailWord_1308431) baseStart_1308431 baseEnd_1308431 := by
    simpa [prefixWord, tailWord_1308431, baseEnd_1308431] using wordTrace_append hprefix tailTrace_1308431
  have hstable : (prefixWord ++ tailWord_1308431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308431).length < 2 ^ (prefixWord ++ tailWord_1308431).sum := by decide
  have hdescent : baseEnd_1308431 < baseStart_1308431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308512 : List Nat := [2, 1, 1, 3, 3, 2, 3, 1, 3, 1, 3]
def baseStart_1308512 : Nat := 118140960795 + 1308512 * 2 ^ 59
def prefixEnd_1308512 : Nat := 4983230072969 + 3 ^ 40 * 1308512 * 2
def baseEnd_1308512 : Nat := 671895598176089674482269

theorem tailTrace_1308512 : CollatzResearch.WordTrace tailWord_1308512 prefixEnd_1308512 671895598176089674482269 := by
  unfold tailWord_1308512
  simp only [CollatzResearch.WordTrace]
  refine ⟨23862676717745987451435895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31816902290327983268581193 23862676717745987451435895)
  ·
    refine ⟨35794015076618981177153843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23862676717745987451435895 35794015076618981177153843)
    ·
      refine ⟨53691022614928471765730765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35794015076618981177153843 53691022614928471765730765)
      ·
        refine ⟨20134133480598176912149037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53691022614928471765730765 20134133480598176912149037)
        ·
          refine ⟨7550300055224316342055889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20134133480598176912149037 7550300055224316342055889)
          ·
            refine ⟨5662725041418237256541917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7550300055224316342055889 5662725041418237256541917)
            ·
              refine ⟨2123521890531838971203219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5662725041418237256541917 2123521890531838971203219)
              ·
                refine ⟨3185282835797758456804829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2123521890531838971203219 3185282835797758456804829)
                ·
                  refine ⟨1194481063424159421301811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3185282835797758456804829 1194481063424159421301811)
                  ·
                    refine ⟨1791721595136239131952717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1194481063424159421301811 1791721595136239131952717)
                    ·
                      refine ⟨671895598176089674482269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1791721595136239131952717 671895598176089674482269)
                      ·
                        rfl

theorem cell23_1308512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 3, 1, 3].length) (baseStart_1308512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1308512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1308512 prefixEnd_1308512 := by exact prefixLift 1308512
  have htrace : WordTrace (prefixWord ++ tailWord_1308512) baseStart_1308512 baseEnd_1308512 := by
    simpa [prefixWord, tailWord_1308512, baseEnd_1308512] using wordTrace_append hprefix tailTrace_1308512
  have hstable : (prefixWord ++ tailWord_1308512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308512).length < 2 ^ (prefixWord ++ tailWord_1308512).sum := by decide
  have hdescent : baseEnd_1308512 < baseStart_1308512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308528 : List Nat := [2, 1, 1, 1, 4, 1, 1, 5, 1, 6]
def baseStart_1308528 : Nat := 118140960795 + 1308528 * 2 ^ 59
def prefixEnd_1308528 : Nat := 4983230072969 + 3 ^ 40 * 1308528 * 2
def baseEnd_1308528 : Nat := 223967937955520537294065

theorem tailTrace_1308528 : CollatzResearch.WordTrace tailWord_1308528 prefixEnd_1308528 223967937955520537294065 := by
  unfold tailWord_1308528
  simp only [CollatzResearch.WordTrace]
  refine ⟨23862968501717004817727119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31817291335622673090302825 23862968501717004817727119)
  ·
    refine ⟨35794452752575507226590679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23862968501717004817727119 35794452752575507226590679)
    ·
      refine ⟨53691679128863260839886019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35794452752575507226590679 53691679128863260839886019)
      ·
        refine ⟨80537518693294891259829029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53691679128863260839886019 80537518693294891259829029)
        ·
          refine ⟨15100784754992792111217943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80537518693294891259829029 15100784754992792111217943)
          ·
            refine ⟨22651177132489188166826915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15100784754992792111217943 22651177132489188166826915)
            ·
              refine ⟨33976765698733782250240373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22651177132489188166826915 33976765698733782250240373)
              ·
                refine ⟨3185321784256292085960035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33976765698733782250240373 3185321784256292085960035)
                ·
                  refine ⟨4777982676384438128940053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3185321784256292085960035 4777982676384438128940053)
                  ·
                    refine ⟨223967937955520537294065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4777982676384438128940053 223967937955520537294065)
                    ·
                      rfl

theorem cell23_1308528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 1, 6].length) (baseStart_1308528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1308528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1308528 prefixEnd_1308528 := by exact prefixLift 1308528
  have htrace : WordTrace (prefixWord ++ tailWord_1308528) baseStart_1308528 baseEnd_1308528 := by
    simpa [prefixWord, tailWord_1308528, baseEnd_1308528] using wordTrace_append hprefix tailTrace_1308528
  have hstable : (prefixWord ++ tailWord_1308528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308528).length < 2 ^ (prefixWord ++ tailWord_1308528).sum := by decide
  have hdescent : baseEnd_1308528 < baseStart_1308528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308538 : List Nat := [3, 1, 1, 1, 1, 1, 4, 2, 3, 1, 5]
def baseStart_1308538 : Nat := 118140960795 + 1308538 * 2 ^ 59
def prefixEnd_1308538 : Nat := 4983230072969 + 3 ^ 40 * 1308538 * 2
def baseEnd_1308538 : Nat := 671908948673106572757149

theorem tailTrace_1308538 : CollatzResearch.WordTrace tailWord_1308538 prefixEnd_1308538 671908948673106572757149 := by
  unfold tailWord_1308538
  simp only [CollatzResearch.WordTrace]
  refine ⟨11931575433349445335829567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31817534488931854228878845 11931575433349445335829567)
  ·
    refine ⟨17897363150024168003744351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11931575433349445335829567 17897363150024168003744351)
    ·
      refine ⟨26846044725036252005616527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17897363150024168003744351 26846044725036252005616527)
      ·
        refine ⟨40269067087554378008424791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26846044725036252005616527 40269067087554378008424791)
        ·
          refine ⟨60403600631331567012637187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40269067087554378008424791 60403600631331567012637187)
          ·
            refine ⟨90605400946997350518955781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60403600631331567012637187 90605400946997350518955781)
            ·
              refine ⟨16988512677562003222304209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90605400946997350518955781 16988512677562003222304209)
              ·
                refine ⟨12741384508171502416728157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16988512677562003222304209 12741384508171502416728157)
                ·
                  refine ⟨4778019190564313406273059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12741384508171502416728157 4778019190564313406273059)
                  ·
                    refine ⟨7167028785846470109409589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4778019190564313406273059 7167028785846470109409589)
                    ·
                      refine ⟨671908948673106572757149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7167028785846470109409589 671908948673106572757149)
                      ·
                        rfl

theorem cell23_1308538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 3, 1, 5].length) (baseStart_1308538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1308538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1308538 prefixEnd_1308538 := by exact prefixLift 1308538
  have htrace : WordTrace (prefixWord ++ tailWord_1308538) baseStart_1308538 baseEnd_1308538 := by
    simpa [prefixWord, tailWord_1308538, baseEnd_1308538] using wordTrace_append hprefix tailTrace_1308538
  have hstable : (prefixWord ++ tailWord_1308538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308538).length < 2 ^ (prefixWord ++ tailWord_1308538).sum := by decide
  have hdescent : baseEnd_1308538 < baseStart_1308538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308572 : List Nat := [2, 2, 3, 3, 1, 1, 1, 2, 3, 2, 3]
def baseStart_1308572 : Nat := 118140960795 + 1308572 * 2 ^ 59
def prefixEnd_1308572 : Nat := 4983230072969 + 3 ^ 40 * 1308572 * 2
def baseEnd_1308572 : Nat := 671926407015359439731993

theorem tailTrace_1308572 : CollatzResearch.WordTrace tailWord_1308572 prefixEnd_1308572 671926407015359439731993 := by
  unfold tailWord_1308572
  simp only [CollatzResearch.WordTrace]
  refine ⟨23863770907637302575027985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31818361210183070100037313 23863770907637302575027985)
  ·
    refine ⟨17897828180727976931270989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23863770907637302575027985 17897828180727976931270989)
    ·
      refine ⟨6711685567772991349226621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17897828180727976931270989 6711685567772991349226621)
      ·
        refine ⟨2516882087914871755959983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6711685567772991349226621 2516882087914871755959983)
        ·
          refine ⟨3775323131872307633939975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2516882087914871755959983 3775323131872307633939975)
          ·
            refine ⟨5662984697808461450909963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3775323131872307633939975 5662984697808461450909963)
            ·
              refine ⟨8494477046712692176364945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5662984697808461450909963 8494477046712692176364945)
              ·
                refine ⟨6370857785034519132273709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8494477046712692176364945 6370857785034519132273709)
                ·
                  refine ⟨2389071669387944674602641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6370857785034519132273709 2389071669387944674602641)
                  ·
                    refine ⟨1791803752040958505951981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2389071669387944674602641 1791803752040958505951981)
                    ·
                      refine ⟨671926407015359439731993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1791803752040958505951981 671926407015359439731993)
                      ·
                        rfl

theorem cell23_1308572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_1308572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1308572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1308572 prefixEnd_1308572 := by exact prefixLift 1308572
  have htrace : WordTrace (prefixWord ++ tailWord_1308572) baseStart_1308572 baseEnd_1308572 := by
    simpa [prefixWord, tailWord_1308572, baseEnd_1308572] using wordTrace_append hprefix tailTrace_1308572
  have hstable : (prefixWord ++ tailWord_1308572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308572).length < 2 ^ (prefixWord ++ tailWord_1308572).sum := by decide
  have hdescent : baseEnd_1308572 < baseStart_1308572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308590 : List Nat := [4, 1, 5, 1, 1, 2, 1, 1, 2, 3, 2]
def baseStart_1308590 : Nat := 118140960795 + 1308590 * 2 ^ 59
def prefixEnd_1308590 : Nat := 4983230072969 + 3 ^ 40 * 1308590 * 2
def baseEnd_1308590 : Nat := 671935649667140369306911

theorem tailTrace_1308590 : CollatzResearch.WordTrace tailWord_1308590 prefixEnd_1308590 671935649667140369306911 := by
  unfold tailWord_1308590
  simp only [CollatzResearch.WordTrace]
  refine ⟨5966024791151174278026403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31818798886139596149474149 5966024791151174278026403)
  ·
    refine ⟨8949037186726761417039605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5966024791151174278026403 8949037186726761417039605)
    ·
      refine ⟨838972236255633882847463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8949037186726761417039605 838972236255633882847463)
      ·
        refine ⟨1258458354383450824271195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 838972236255633882847463 1258458354383450824271195)
        ·
          refine ⟨1887687531575176236406793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1258458354383450824271195 1887687531575176236406793)
          ·
            refine ⟨1415765648681382177305095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1887687531575176236406793 1415765648681382177305095)
            ·
              refine ⟨2123648473022073265957643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1415765648681382177305095 2123648473022073265957643)
              ·
                refine ⟨3185472709533109898936465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2123648473022073265957643 3185472709533109898936465)
                ·
                  refine ⟨2389104532149832424202349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3185472709533109898936465 2389104532149832424202349)
                  ·
                    refine ⟨895914199556187159075881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2389104532149832424202349 895914199556187159075881)
                    ·
                      refine ⟨671935649667140369306911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 895914199556187159075881 671935649667140369306911)
                      ·
                        rfl

theorem cell23_1308590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_1308590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1308590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1308590 prefixEnd_1308590 := by exact prefixLift 1308590
  have htrace : WordTrace (prefixWord ++ tailWord_1308590) baseStart_1308590 baseEnd_1308590 := by
    simpa [prefixWord, tailWord_1308590, baseEnd_1308590] using wordTrace_append hprefix tailTrace_1308590
  have hstable : (prefixWord ++ tailWord_1308590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308590).length < 2 ^ (prefixWord ++ tailWord_1308590).sum := by decide
  have hdescent : baseEnd_1308590 < baseStart_1308590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308606 : List Nat := [4, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3]
def baseStart_1308606 : Nat := 118140960795 + 1308606 * 2 ^ 59
def prefixEnd_1308606 : Nat := 4983230072969 + 3 ^ 40 * 1308606 * 2
def baseEnd_1308606 : Nat := 671943865357612306706837

theorem tailTrace_1308606 : CollatzResearch.WordTrace tailWord_1308606 prefixEnd_1308606 671943865357612306706837 := by
  unfold tailWord_1308606
  simp only [CollatzResearch.WordTrace]
  refine ⟨5966097737143928619599209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31819187931434285971195781 5966097737143928619599209)
  ·
    refine ⟨4474573302857946464699407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5966097737143928619599209 4474573302857946464699407)
    ·
      refine ⟨6711859954286919697049111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4474573302857946464699407 6711859954286919697049111)
      ·
        refine ⟨10067789931430379545573667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6711859954286919697049111 10067789931430379545573667)
        ·
          refine ⟨15101684897145569318360501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10067789931430379545573667 15101684897145569318360501)
          ·
            refine ⟨1415782959107397123596297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15101684897145569318360501 1415782959107397123596297)
            ·
              refine ⟨1061837219330547842697223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1415782959107397123596297 1061837219330547842697223)
              ·
                refine ⟨1592755828995821764045835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1061837219330547842697223 1592755828995821764045835)
                ·
                  refine ⟨2389133743493732646068753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1592755828995821764045835 2389133743493732646068753)
                  ·
                    refine ⟨1791850307620299484551565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2389133743493732646068753 1791850307620299484551565)
                    ·
                      refine ⟨671943865357612306706837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1791850307620299484551565 671943865357612306706837)
                      ·
                        rfl

theorem cell23_1308606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3].length) (baseStart_1308606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1308606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1308606 prefixEnd_1308606 := by exact prefixLift 1308606
  have htrace : WordTrace (prefixWord ++ tailWord_1308606) baseStart_1308606 baseEnd_1308606 := by
    simpa [prefixWord, tailWord_1308606, baseEnd_1308606] using wordTrace_append hprefix tailTrace_1308606
  have hstable : (prefixWord ++ tailWord_1308606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308606).length < 2 ^ (prefixWord ++ tailWord_1308606).sum := by decide
  have hdescent : baseEnd_1308606 < baseStart_1308606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308675 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 4, 3, 3]
def baseStart_1308675 : Nat := 118140960795 + 1308675 * 2 ^ 59
def prefixEnd_1308675 : Nat := 4983230072969 + 3 ^ 40 * 1308675 * 2
def baseEnd_1308675 : Nat := 671979295522772536744019

theorem tailTrace_1308675 : CollatzResearch.WordTrace tailWord_1308675 prefixEnd_1308675 671979295522772536744019 := by
  unfold tailWord_1308675
  simp only [CollatzResearch.WordTrace]
  refine ⟨47731298533901453741055479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31820865689267635827370319 47731298533901453741055479)
  ·
    refine ⟨71596947800852180611583219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47731298533901453741055479 71596947800852180611583219)
    ·
      refine ⟨107395421701278270917374829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71596947800852180611583219 107395421701278270917374829)
      ·
        refine ⟨40273283137979351594015561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107395421701278270917374829 40273283137979351594015561)
        ·
          refine ⟨30204962353484513695511671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40273283137979351594015561 30204962353484513695511671)
          ·
            refine ⟨45307443530226770543267507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30204962353484513695511671 45307443530226770543267507)
            ·
              refine ⟨67961165295340155814901261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45307443530226770543267507 67961165295340155814901261)
              ·
                refine ⟨25485436985752558430587973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67961165295340155814901261 25485436985752558430587973)
                ·
                  refine ⟨4778519434828604705735245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25485436985752558430587973 4778519434828604705735245)
                  ·
                    refine ⟨1791944788060726764650717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4778519434828604705735245 1791944788060726764650717)
                    ·
                      refine ⟨671979295522772536744019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1791944788060726764650717 671979295522772536744019)
                      ·
                        rfl

theorem cell23_1308675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 3, 3].length) (baseStart_1308675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1308675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1308675 prefixEnd_1308675 := by exact prefixLift 1308675
  have htrace : WordTrace (prefixWord ++ tailWord_1308675) baseStart_1308675 baseEnd_1308675 := by
    simpa [prefixWord, tailWord_1308675, baseEnd_1308675] using wordTrace_append hprefix tailTrace_1308675
  have hstable : (prefixWord ++ tailWord_1308675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308675).length < 2 ^ (prefixWord ++ tailWord_1308675).sum := by decide
  have hdescent : baseEnd_1308675 < baseStart_1308675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308732 : List Nat := [2, 2, 2, 2, 2, 1, 1, 4, 2, 1, 4]
def baseStart_1308732 : Nat := 118140960795 + 1308732 * 2 ^ 59
def prefixEnd_1308732 : Nat := 4983230072969 + 3 ^ 40 * 1308732 * 2
def baseEnd_1308732 : Nat := 672008563920078813731257

theorem tailTrace_1308732 : CollatzResearch.WordTrace tailWord_1308732 prefixEnd_1308732 672008563920078813731257 := by
  unfold tailWord_1308732
  simp only [CollatzResearch.WordTrace]
  refine ⟨23866688747347476237940225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31822251663129968317253633 23866688747347476237940225)
  ·
    refine ⟨17900016560510607178455169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23866688747347476237940225 17900016560510607178455169)
    ·
      refine ⟨13425012420382955383841377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17900016560510607178455169 13425012420382955383841377)
      ·
        refine ⟨10068759315287216537881033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13425012420382955383841377 10068759315287216537881033)
        ·
          refine ⟨7551569486465412403410775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10068759315287216537881033 7551569486465412403410775)
          ·
            refine ⟨11327354229698118605116163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7551569486465412403410775 11327354229698118605116163)
            ·
              refine ⟨16991031344547177907674245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11327354229698118605116163 16991031344547177907674245)
              ·
                refine ⟨3185818377102595857688921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16991031344547177907674245 3185818377102595857688921)
                ·
                  refine ⟨2389363782826946893266691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3185818377102595857688921 2389363782826946893266691)
                  ·
                    refine ⟨3584045674240420339900037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2389363782826946893266691 3584045674240420339900037)
                    ·
                      refine ⟨672008563920078813731257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3584045674240420339900037 672008563920078813731257)
                      ·
                        rfl

theorem cell23_1308732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_1308732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1308732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1308732 prefixEnd_1308732 := by exact prefixLift 1308732
  have htrace : WordTrace (prefixWord ++ tailWord_1308732) baseStart_1308732 baseEnd_1308732 := by
    simpa [prefixWord, tailWord_1308732, baseEnd_1308732] using wordTrace_append hprefix tailTrace_1308732
  have hstable : (prefixWord ++ tailWord_1308732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308732).length < 2 ^ (prefixWord ++ tailWord_1308732).sum := by decide
  have hdescent : baseEnd_1308732 < baseStart_1308732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308833 : List Nat := [1, 2, 3, 3, 1, 2, 3, 3, 1, 1, 3]
def baseStart_1308833 : Nat := 118140960795 + 1308833 * 2 ^ 59
def prefixEnd_1308833 : Nat := 4983230072969 + 3 ^ 40 * 1308833 * 2
def baseEnd_1308833 : Nat := 672060425466182918568293

theorem tailTrace_1308833 : CollatzResearch.WordTrace tailWord_1308833 prefixEnd_1308833 672060425466182918568293 := by
  unfold tailWord_1308833
  simp only [CollatzResearch.WordTrace]
  refine ⟨47737061267329046725307153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31824707511552697816871435 47737061267329046725307153)
  ·
    refine ⟨35802795950496785043980365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47737061267329046725307153 35802795950496785043980365)
    ·
      refine ⟨13426048481436294391492637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35802795950496785043980365 13426048481436294391492637)
      ·
        refine ⟨5034768180538610396809739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13426048481436294391492637 5034768180538610396809739)
        ·
          refine ⟨7552152270807915595214609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5034768180538610396809739 7552152270807915595214609)
          ·
            refine ⟨5664114203105936696410957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7552152270807915595214609 5664114203105936696410957)
            ·
              refine ⟨2124042826164726261154109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5664114203105936696410957 2124042826164726261154109)
              ·
                refine ⟨796516059811772347932791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2124042826164726261154109 796516059811772347932791)
                ·
                  refine ⟨1194774089717658521899187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 796516059811772347932791 1194774089717658521899187)
                  ·
                    refine ⟨1792161134576487782848781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1194774089717658521899187 1792161134576487782848781)
                    ·
                      refine ⟨672060425466182918568293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1792161134576487782848781 672060425466182918568293)
                      ·
                        rfl

theorem cell23_1308833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_1308833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1308833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1308833 prefixEnd_1308833 := by exact prefixLift 1308833
  have htrace : WordTrace (prefixWord ++ tailWord_1308833) baseStart_1308833 baseEnd_1308833 := by
    simpa [prefixWord, tailWord_1308833, baseEnd_1308833] using wordTrace_append hprefix tailTrace_1308833
  have hstable : (prefixWord ++ tailWord_1308833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308833).length < 2 ^ (prefixWord ++ tailWord_1308833).sum := by decide
  have hdescent : baseEnd_1308833 < baseStart_1308833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308886 : List Nat := [5, 2, 1, 2, 1, 1, 1, 1, 3, 2, 4]
def baseStart_1308886 : Nat := 118140960795 + 1308886 * 2 ^ 59
def prefixEnd_1308886 : Nat := 4983230072969 + 3 ^ 40 * 1308886 * 2
def baseEnd_1308886 : Nat := 672087639940871211205549

theorem tailTrace_1308886 : CollatzResearch.WordTrace tailWord_1308886 prefixEnd_1308886 672087639940871211205549 := by
  unfold tailWord_1308886
  simp only [CollatzResearch.WordTrace]
  refine ⟨2983687146008564798561657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31825996224091357851324341 2983687146008564798561657)
  ·
    refine ⟨2237765359506423598921243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2983687146008564798561657 2237765359506423598921243)
    ·
      refine ⟨3356648039259635398381865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2237765359506423598921243 3356648039259635398381865)
      ·
        refine ⟨2517486029444726548786399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3356648039259635398381865 2517486029444726548786399)
        ·
          refine ⟨3776229044167089823179599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2517486029444726548786399 3776229044167089823179599)
          ·
            refine ⟨5664343566250634734769399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3776229044167089823179599 5664343566250634734769399)
            ·
              refine ⟨8496515349375952102154099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5664343566250634734769399 8496515349375952102154099)
              ·
                refine ⟨12744773024063928153231149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8496515349375952102154099 12744773024063928153231149)
                ·
                  refine ⟨4779289884023973057461681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12744773024063928153231149 4779289884023973057461681)
                  ·
                    refine ⟨3584467413017979793096261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4779289884023973057461681 3584467413017979793096261)
                    ·
                      refine ⟨672087639940871211205549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3584467413017979793096261 672087639940871211205549)
                      ·
                        rfl

theorem cell23_1308886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_1308886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1308886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1308886 prefixEnd_1308886 := by exact prefixLift 1308886
  have htrace : WordTrace (prefixWord ++ tailWord_1308886) baseStart_1308886 baseEnd_1308886 := by
    simpa [prefixWord, tailWord_1308886, baseEnd_1308886] using wordTrace_append hprefix tailTrace_1308886
  have hstable : (prefixWord ++ tailWord_1308886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308886).length < 2 ^ (prefixWord ++ tailWord_1308886).sum := by decide
  have hdescent : baseEnd_1308886 < baseStart_1308886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308889 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 6, 1, 3]
def baseStart_1308889 : Nat := 118140960795 + 1308889 * 2 ^ 59
def prefixEnd_1308889 : Nat := 4983230072969 + 3 ^ 40 * 1308889 * 2
def baseEnd_1308889 : Nat := 672089180382834699468035

theorem tailTrace_1308889 : CollatzResearch.WordTrace tailWord_1308889 prefixEnd_1308889 672089180382834699468035 := by
  unfold tailWord_1308889
  simp only [CollatzResearch.WordTrace]
  refine ⟨47739103755126168289345721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31826069170084112192897147 47739103755126168289345721)
  ·
    refine ⟨35804327816344626217009291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47739103755126168289345721 35804327816344626217009291)
    ·
      refine ⟨53706491724516939325513937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35804327816344626217009291 53706491724516939325513937)
      ·
        refine ⟨40279868793387704494135453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53706491724516939325513937 40279868793387704494135453)
        ·
          refine ⟨15104950797520389185300795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40279868793387704494135453 15104950797520389185300795)
          ·
            refine ⟨22657426196280583777951193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15104950797520389185300795 22657426196280583777951193)
            ·
              refine ⟨16993069647210437833463395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22657426196280583777951193 16993069647210437833463395)
              ·
                refine ⟨25489604470815656750195093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16993069647210437833463395 25489604470815656750195093)
                ·
                  refine ⟨1194825209569483910165395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 25489604470815656750195093 1194825209569483910165395)
                  ·
                    refine ⟨1792237814354225865248093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1194825209569483910165395 1792237814354225865248093)
                    ·
                      refine ⟨672089180382834699468035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1792237814354225865248093 672089180382834699468035)
                      ·
                        rfl

theorem cell23_1308889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 6, 1, 3].length) (baseStart_1308889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1308889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1308889 prefixEnd_1308889 := by exact prefixLift 1308889
  have htrace : WordTrace (prefixWord ++ tailWord_1308889) baseStart_1308889 baseEnd_1308889 := by
    simpa [prefixWord, tailWord_1308889, baseEnd_1308889] using wordTrace_append hprefix tailTrace_1308889
  have hstable : (prefixWord ++ tailWord_1308889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308889).length < 2 ^ (prefixWord ++ tailWord_1308889).sum := by decide
  have hdescent : baseEnd_1308889 < baseStart_1308889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308922 : List Nat := [3, 1, 1, 1, 1, 5, 1, 1, 1, 8]
def baseStart_1308922 : Nat := 118140960795 + 1308922 * 2 ^ 59
def prefixEnd_1308922 : Nat := 4983230072969 + 3 ^ 40 * 1308922 * 2
def baseEnd_1308922 : Nat := 224035375081477690118461

theorem tailTrace_1308922 : CollatzResearch.WordTrace tailWord_1308922 prefixEnd_1308922 224035375081477690118461 := by
  unfold tailWord_1308922
  simp only [CollatzResearch.WordTrace]
  refine ⟨11935076841001653731324255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31826871576004409950198013 11935076841001653731324255)
  ·
    refine ⟨17902615261502480596986383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11935076841001653731324255 17902615261502480596986383)
    ·
      refine ⟨26853922892253720895479575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17902615261502480596986383 26853922892253720895479575)
      ·
        refine ⟨40280884338380581343219363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26853922892253720895479575 40280884338380581343219363)
        ·
          refine ⟨60421326507570872014829045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40280884338380581343219363 60421326507570872014829045)
          ·
            refine ⟨5664499360084769251390223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60421326507570872014829045 5664499360084769251390223)
            ·
              refine ⟨8496749040127153877085335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5664499360084769251390223 8496749040127153877085335)
              ·
                refine ⟨12745123560190730815628003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8496749040127153877085335 12745123560190730815628003)
                ·
                  refine ⟨19117685340286096223442005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12745123560190730815628003 19117685340286096223442005)
                  ·
                    refine ⟨224035375081477690118461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 19117685340286096223442005 224035375081477690118461)
                    ·
                      rfl

theorem cell23_1308922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 1, 8].length) (baseStart_1308922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1308922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1308922 prefixEnd_1308922 := by exact prefixLift 1308922
  have htrace : WordTrace (prefixWord ++ tailWord_1308922) baseStart_1308922 baseEnd_1308922 := by
    simpa [prefixWord, tailWord_1308922, baseEnd_1308922] using wordTrace_append hprefix tailTrace_1308922
  have hstable : (prefixWord ++ tailWord_1308922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308922).length < 2 ^ (prefixWord ++ tailWord_1308922).sum := by decide
  have hdescent : baseEnd_1308922 < baseStart_1308922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308952 : List Nat := [2, 1, 2, 3, 1, 2, 1, 2, 9]
def baseStart_1308952 : Nat := 118140960795 + 1308952 * 2 ^ 59
def prefixEnd_1308952 : Nat := 4983230072969 + 3 ^ 40 * 1308952 * 2
def baseEnd_1308952 : Nat := 74680169962674216997805

theorem tailTrace_1308952 : CollatzResearch.WordTrace tailWord_1308952 prefixEnd_1308952 74680169962674216997805 := by
  unfold tailWord_1308952
  simp only [CollatzResearch.WordTrace]
  refine ⟨23870700776948965024444555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31827601035931953365926073 23870700776948965024444555)
  ·
    refine ⟨35806051165423447536666833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23870700776948965024444555 35806051165423447536666833)
    ·
      refine ⟨26854538374067585652500125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35806051165423447536666833 26854538374067585652500125)
      ·
        refine ⟨10070451890275344619687547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26854538374067585652500125 10070451890275344619687547)
        ·
          refine ⟨15105677835413016929531321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10070451890275344619687547 15105677835413016929531321)
          ·
            refine ⟨11329258376559762697148491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15105677835413016929531321 11329258376559762697148491)
            ·
              refine ⟨16993887564839644045722737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11329258376559762697148491 16993887564839644045722737)
              ·
                refine ⟨12745415673629733034292053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16993887564839644045722737 12745415673629733034292053)
                ·
                  refine ⟨74680169962674216997805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 12745415673629733034292053 74680169962674216997805)
                  ·
                    rfl

theorem cell23_1308952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 9].length) (baseStart_1308952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1308952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1308952 prefixEnd_1308952 := by exact prefixLift 1308952
  have htrace : WordTrace (prefixWord ++ tailWord_1308952) baseStart_1308952 baseEnd_1308952 := by
    simpa [prefixWord, tailWord_1308952, baseEnd_1308952] using wordTrace_append hprefix tailTrace_1308952
  have hstable : (prefixWord ++ tailWord_1308952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308952).length < 2 ^ (prefixWord ++ tailWord_1308952).sum := by decide
  have hdescent : baseEnd_1308952 < baseStart_1308952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308957 : List Nat := [1, 4, 2, 3, 3, 1, 1, 2, 2, 1, 3]
def baseStart_1308957 : Nat := 118140960795 + 1308957 * 2 ^ 59
def prefixEnd_1308957 : Nat := 4983230072969 + 3 ^ 40 * 1308957 * 2
def baseEnd_1308957 : Nat := 672124097067340433417723

theorem tailTrace_1308957 : CollatzResearch.WordTrace tailWord_1308957 prefixEnd_1308957 672124097067340433417723 := by
  unfold tailWord_1308957
  simp only [CollatzResearch.WordTrace]
  refine ⟨47741583918879815902821125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31827722612586543935214083 47741583918879815902821125)
  ·
    refine ⟨8951546984789965481778961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47741583918879815902821125 8951546984789965481778961)
    ·
      refine ⟨6713660238592474111334221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8951546984789965481778961 6713660238592474111334221)
      ·
        refine ⟨2517622589472177791750333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6713660238592474111334221 2517622589472177791750333)
        ·
          refine ⟨944108471052066671906375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2517622589472177791750333 944108471052066671906375)
          ·
            refine ⟨1416162706578100007859563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 944108471052066671906375 1416162706578100007859563)
            ·
              refine ⟨2124244059867150011789345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1416162706578100007859563 2124244059867150011789345)
              ·
                refine ⟨1593183044900362508842009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2124244059867150011789345 1593183044900362508842009)
                ·
                  refine ⟨1194887283675271881631507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1593183044900362508842009 1194887283675271881631507)
                  ·
                    refine ⟨1792330925512907822447261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1194887283675271881631507 1792330925512907822447261)
                    ·
                      refine ⟨672124097067340433417723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1792330925512907822447261 672124097067340433417723)
                      ·
                        rfl

theorem cell23_1308957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_1308957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1308957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1308957 prefixEnd_1308957 := by exact prefixLift 1308957
  have htrace : WordTrace (prefixWord ++ tailWord_1308957) baseStart_1308957 baseEnd_1308957 := by
    simpa [prefixWord, tailWord_1308957, baseEnd_1308957] using wordTrace_append hprefix tailTrace_1308957
  have hstable : (prefixWord ++ tailWord_1308957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308957).length < 2 ^ (prefixWord ++ tailWord_1308957).sum := by decide
  have hdescent : baseEnd_1308957 < baseStart_1308957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308959 : List Nat := [1, 1, 2, 4, 3, 1, 1, 2, 2, 2, 4]
def baseStart_1308959 : Nat := 118140960795 + 1308959 * 2 ^ 59
def prefixEnd_1308959 : Nat := 4983230072969 + 3 ^ 40 * 1308959 * 2
def baseEnd_1308959 : Nat := 672125124028649425592713

theorem tailTrace_1308959 : CollatzResearch.WordTrace tailWord_1308959 prefixEnd_1308959 672125124028649425592713 := by
  unfold tailWord_1308959
  simp only [CollatzResearch.WordTrace]
  refine ⟨47741656864872570244393931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31827771243248380162929287 47741656864872570244393931)
  ·
    refine ⟨71612485297308855366590897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47741656864872570244393931 71612485297308855366590897)
    ·
      refine ⟨53709363972981641524943173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71612485297308855366590897 53709363972981641524943173)
      ·
        refine ⟨10070505744934057785926845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53709363972981641524943173 10070505744934057785926845)
        ·
          refine ⟨3776439654350271669722567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10070505744934057785926845 3776439654350271669722567)
          ·
            refine ⟨5664659481525407504583851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3776439654350271669722567 5664659481525407504583851)
            ·
              refine ⟨8496989222288111256875777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5664659481525407504583851 8496989222288111256875777)
              ·
                refine ⟨6372741916716083442656833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8496989222288111256875777 6372741916716083442656833)
                ·
                  refine ⟨4779556437537062581992625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6372741916716083442656833 4779556437537062581992625)
                  ·
                    refine ⟨3584667328152796936494469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4779556437537062581992625 3584667328152796936494469)
                    ·
                      refine ⟨672125124028649425592713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3584667328152796936494469 672125124028649425592713)
                      ·
                        rfl

theorem cell23_1308959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_1308959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1308959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1308959 prefixEnd_1308959 := by exact prefixLift 1308959
  have htrace : WordTrace (prefixWord ++ tailWord_1308959) baseStart_1308959 baseEnd_1308959 := by
    simpa [prefixWord, tailWord_1308959, baseEnd_1308959] using wordTrace_append hprefix tailTrace_1308959
  have hstable : (prefixWord ++ tailWord_1308959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308959).length < 2 ^ (prefixWord ++ tailWord_1308959).sum := by decide
  have hdescent : baseEnd_1308959 < baseStart_1308959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308979 : List Nat := [1, 1, 1, 2, 5, 1, 1, 3, 2, 3, 3]
def baseStart_1308979 : Nat := 118140960795 + 1308979 * 2 ^ 59
def prefixEnd_1308979 : Nat := 4983230072969 + 3 ^ 40 * 1308979 * 2
def baseEnd_1308979 : Nat := 672135393641739347342621

theorem tailTrace_1308979 : CollatzResearch.WordTrace tailWord_1308979 prefixEnd_1308979 672135393641739347342621 := by
  unfold tailWord_1308979
  simp only [CollatzResearch.WordTrace]
  refine ⟨47742386324800113660121991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31828257549866742440081327 47742386324800113660121991)
  ·
    refine ⟨71613579487200170490182987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47742386324800113660121991 71613579487200170490182987)
    ·
      refine ⟨107420369230800255735274481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71613579487200170490182987 107420369230800255735274481)
      ·
        refine ⟨80565276923100191801455861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107420369230800255735274481 80565276923100191801455861)
        ·
          refine ⟨7552994711540642981386487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80565276923100191801455861 7552994711540642981386487)
          ·
            refine ⟨11329492067310964472079731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7552994711540642981386487 11329492067310964472079731)
            ·
              refine ⟨16994238100966446708119597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11329492067310964472079731 16994238100966446708119597)
              ·
                refine ⟨6372839287862417515544849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16994238100966446708119597 6372839287862417515544849)
                ·
                  refine ⟨4779629465896813136658637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6372839287862417515544849 4779629465896813136658637)
                  ·
                    refine ⟨1792361049711304926246989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4779629465896813136658637 1792361049711304926246989)
                    ·
                      refine ⟨672135393641739347342621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1792361049711304926246989 672135393641739347342621)
                      ·
                        rfl

theorem cell23_1308979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 3, 3].length) (baseStart_1308979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1308979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1308979 prefixEnd_1308979 := by exact prefixLift 1308979
  have htrace : WordTrace (prefixWord ++ tailWord_1308979) baseStart_1308979 baseEnd_1308979 := by
    simpa [prefixWord, tailWord_1308979, baseEnd_1308979] using wordTrace_append hprefix tailTrace_1308979
  have hstable : (prefixWord ++ tailWord_1308979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308979).length < 2 ^ (prefixWord ++ tailWord_1308979).sum := by decide
  have hdescent : baseEnd_1308979 < baseStart_1308979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308980 : List Nat := [2, 5, 1, 1, 1, 4, 1, 1, 1, 4, 2]
def baseStart_1308980 : Nat := 118140960795 + 1308980 * 2 ^ 59
def prefixEnd_1308980 : Nat := 4983230072969 + 3 ^ 40 * 1308980 * 2
def baseEnd_1308980 : Nat := 672135907122393843430117

theorem tailTrace_1308980 : CollatzResearch.WordTrace tailWord_1308980 prefixEnd_1308980 672135907122393843430117 := by
  unfold tailWord_1308980
  simp only [CollatzResearch.WordTrace]
  refine ⟨23871211398898245415454197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31828281865197660553938929 23871211398898245415454197)
  ·
    refine ⟨2237926068646710507698831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23871211398898245415454197 2237926068646710507698831)
    ·
      refine ⟨3356889102970065761548247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2237926068646710507698831 3356889102970065761548247)
      ·
        refine ⟨5035333654455098642322371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3356889102970065761548247 5035333654455098642322371)
        ·
          refine ⟨7553000481682647963483557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5035333654455098642322371 7553000481682647963483557)
          ·
            refine ⟨1416187590315496493153167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7553000481682647963483557 1416187590315496493153167)
            ·
              refine ⟨2124281385473244739729751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1416187590315496493153167 2124281385473244739729751)
              ·
                refine ⟨3186422078209867109594627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2124281385473244739729751 3186422078209867109594627)
                ·
                  refine ⟨4779633117314800664391941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3186422078209867109594627 4779633117314800664391941)
                  ·
                    refine ⟨896181209496525124573489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4779633117314800664391941 896181209496525124573489)
                    ·
                      refine ⟨672135907122393843430117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 896181209496525124573489 672135907122393843430117)
                      ·
                        rfl

theorem cell23_1308980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_1308980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1308980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1308980 prefixEnd_1308980 := by exact prefixLift 1308980
  have htrace : WordTrace (prefixWord ++ tailWord_1308980) baseStart_1308980 baseEnd_1308980 := by
    simpa [prefixWord, tailWord_1308980, baseEnd_1308980] using wordTrace_append hprefix tailTrace_1308980
  have hstable : (prefixWord ++ tailWord_1308980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308980).length < 2 ^ (prefixWord ++ tailWord_1308980).sum := by decide
  have hdescent : baseEnd_1308980 < baseStart_1308980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308992 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 7]
def baseStart_1308992 : Nat := 118140960795 + 1308992 * 2 ^ 59
def prefixEnd_1308992 : Nat := 4983230072969 + 3 ^ 40 * 1308992 * 2
def baseEnd_1308992 : Nat := 672142068890247796480061

theorem tailTrace_1308992 : CollatzResearch.WordTrace tailWord_1308992 prefixEnd_1308992 672142068890247796480061 := by
  unfold tailWord_1308992
  simp only [CollatzResearch.WordTrace]
  refine ⟨23871430236876508440172615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31828573649168677920230153 23871430236876508440172615)
  ·
    refine ⟨35807145355314762660258923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23871430236876508440172615 35807145355314762660258923)
    ·
      refine ⟨53710718032972143990388385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35807145355314762660258923 53710718032972143990388385)
      ·
        refine ⟨40283038524729107992791289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53710718032972143990388385 40283038524729107992791289)
        ·
          refine ⟨30212278893546830994593467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40283038524729107992791289 30212278893546830994593467)
          ·
            refine ⟨45318418340320246491890201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30212278893546830994593467 45318418340320246491890201)
            ·
              refine ⟨33988813755240184868917651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45318418340320246491890201 33988813755240184868917651)
              ·
                refine ⟨50983220632860277303376477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33988813755240184868917651 50983220632860277303376477)
                ·
                  refine ⟨19118707737322603988766179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50983220632860277303376477 19118707737322603988766179)
                  ·
                    refine ⟨28678061605983905983149269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19118707737322603988766179 28678061605983905983149269)
                    ·
                      refine ⟨672142068890247796480061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 28678061605983905983149269 672142068890247796480061)
                      ·
                        rfl

theorem cell23_1308992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_1308992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1308992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1308992 prefixEnd_1308992 := by exact prefixLift 1308992
  have htrace : WordTrace (prefixWord ++ tailWord_1308992) baseStart_1308992 baseEnd_1308992 := by
    simpa [prefixWord, tailWord_1308992, baseEnd_1308992] using wordTrace_append hprefix tailTrace_1308992
  have hstable : (prefixWord ++ tailWord_1308992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308992).length < 2 ^ (prefixWord ++ tailWord_1308992).sum := by decide
  have hdescent : baseEnd_1308992 < baseStart_1308992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308999 : List Nat := [1, 1, 4, 1, 2, 2, 2, 3, 2, 5]
def baseStart_1308999 : Nat := 118140960795 + 1308999 * 2 ^ 59
def prefixEnd_1308999 : Nat := 4983230072969 + 3 ^ 40 * 1308999 * 2
def baseEnd_1308999 : Nat := 224048554418276423030843

theorem tailTrace_1308999 : CollatzResearch.WordTrace tailWord_1308999 prefixEnd_1308999 224048554418276423030843 := by
  unfold tailWord_1308999
  simp only [CollatzResearch.WordTrace]
  refine ⟨47743115784727657075850051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31828743856485104717233367 47743115784727657075850051)
  ·
    refine ⟨71614673677091485613775077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47743115784727657075850051 71614673677091485613775077)
    ·
      refine ⟨13427751314454653552582827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71614673677091485613775077 13427751314454653552582827)
      ·
        refine ⟨20141626971681980328874241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13427751314454653552582827 20141626971681980328874241)
        ·
          refine ⟨15106220228761485246655681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20141626971681980328874241 15106220228761485246655681)
          ·
            refine ⟨11329665171571113934991761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15106220228761485246655681 11329665171571113934991761)
            ·
              refine ⟨8497248878678335451243821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11329665171571113934991761 8497248878678335451243821)
              ·
                refine ⟨3186468329504375794216433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8497248878678335451243821 3186468329504375794216433)
                ·
                  refine ⟨2389851247128281845662325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3186468329504375794216433 2389851247128281845662325)
                  ·
                    refine ⟨224048554418276423030843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2389851247128281845662325 224048554418276423030843)
                    ·
                      rfl

theorem cell23_1308999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_1308999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1308999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1308999 prefixEnd_1308999 := by exact prefixLift 1308999
  have htrace : WordTrace (prefixWord ++ tailWord_1308999) baseStart_1308999 baseEnd_1308999 := by
    simpa [prefixWord, tailWord_1308999, baseEnd_1308999] using wordTrace_append hprefix tailTrace_1308999
  have hstable : (prefixWord ++ tailWord_1308999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308999).length < 2 ^ (prefixWord ++ tailWord_1308999).sum := by decide
  have hdescent : baseEnd_1308999 < baseStart_1308999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309020 : List Nat := [2, 2, 4, 3, 2, 1, 1, 1, 7]
def baseStart_1309020 : Nat := 118140960795 + 1309020 * 2 ^ 59
def prefixEnd_1309020 : Nat := 4983230072969 + 3 ^ 40 * 1309020 * 2
def baseEnd_1309020 : Nat := 74684049594285965214437

theorem tailTrace_1309020 : CollatzResearch.WordTrace tailWord_1309020 prefixEnd_1309020 74684049594285965214437 := by
  unfold tailWord_1309020
  simp only [CollatzResearch.WordTrace]
  refine ⟨23871940858825788831182257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31829254478434385108243009 23871940858825788831182257)
  ·
    refine ⟨17903955644119341623386693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23871940858825788831182257 17903955644119341623386693)
    ·
      refine ⟨3356991683272376554385005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17903955644119341623386693 3356991683272376554385005)
      ·
        refine ⟨1258871881227141207894377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3356991683272376554385005 1258871881227141207894377)
        ·
          refine ⟨944153910920355905920783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1258871881227141207894377 944153910920355905920783)
          ·
            refine ⟨1416230866380533858881175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 944153910920355905920783 1416230866380533858881175)
            ·
              refine ⟨2124346299570800788321763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1416230866380533858881175 2124346299570800788321763)
              ·
                refine ⟨3186519449356201182482645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2124346299570800788321763 3186519449356201182482645)
                ·
                  refine ⟨74684049594285965214437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3186519449356201182482645 74684049594285965214437)
                  ·
                    rfl

theorem cell23_1309020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 7].length) (baseStart_1309020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309020 prefixEnd_1309020 := by exact prefixLift 1309020
  have htrace : WordTrace (prefixWord ++ tailWord_1309020) baseStart_1309020 baseEnd_1309020 := by
    simpa [prefixWord, tailWord_1309020, baseEnd_1309020] using wordTrace_append hprefix tailTrace_1309020
  have hstable : (prefixWord ++ tailWord_1309020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309020).length < 2 ^ (prefixWord ++ tailWord_1309020).sum := by decide
  have hdescent : baseEnd_1309020 < baseStart_1309020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309026 : List Nat := [3, 3, 2, 1, 1, 3, 1, 1, 1, 2, 5]
def baseStart_1309026 : Nat := 118140960795 + 1309026 * 2 ^ 59
def prefixEnd_1309026 : Nat := 4983230072969 + 3 ^ 40 * 1309026 * 2
def baseEnd_1309026 : Nat := 672159527232500663454905

theorem tailTrace_1309026 : CollatzResearch.WordTrace tailWord_1309026 prefixEnd_1309026 672159527232500663454905 := by
  unfold tailWord_1309026
  simp only [CollatzResearch.WordTrace]
  refine ⟨11936025138907460171770733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31829400370419893791388621 11936025138907460171770733)
  ·
    refine ⟨4476009427090297564414025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11936025138907460171770733 4476009427090297564414025)
    ·
      refine ⟨3357007070317723173310519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4476009427090297564414025 3357007070317723173310519)
      ·
        refine ⟨5035510605476584759965779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3357007070317723173310519 5035510605476584759965779)
        ·
          refine ⟨7553265908214877139948669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5035510605476584759965779 7553265908214877139948669)
          ·
            refine ⟨2832474715580578927480751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7553265908214877139948669 2832474715580578927480751)
            ·
              refine ⟨4248712073370868391221127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2832474715580578927480751 4248712073370868391221127)
              ·
                refine ⟨6373068110056302586831691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4248712073370868391221127 6373068110056302586831691)
                ·
                  refine ⟨9559602165084453880247537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6373068110056302586831691 9559602165084453880247537)
                  ·
                    refine ⟨7169701623813340410185653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9559602165084453880247537 7169701623813340410185653)
                    ·
                      refine ⟨672159527232500663454905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7169701623813340410185653 672159527232500663454905)
                      ·
                        rfl

theorem cell23_1309026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_1309026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309026 prefixEnd_1309026 := by exact prefixLift 1309026
  have htrace : WordTrace (prefixWord ++ tailWord_1309026) baseStart_1309026 baseEnd_1309026 := by
    simpa [prefixWord, tailWord_1309026, baseEnd_1309026] using wordTrace_append hprefix tailTrace_1309026
  have hstable : (prefixWord ++ tailWord_1309026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309026).length < 2 ^ (prefixWord ++ tailWord_1309026).sum := by decide
  have hdescent : baseEnd_1309026 < baseStart_1309026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309039 : List Nat := [1, 1, 2, 1, 3, 1, 2, 4, 1, 4, 3]
def baseStart_1309039 : Nat := 118140960795 + 1309039 * 2 ^ 59
def prefixEnd_1309039 : Nat := 4983230072969 + 3 ^ 40 * 1309039 * 2
def baseEnd_1309039 : Nat := 672166202481009112592345

theorem tailTrace_1309039 : CollatzResearch.WordTrace tailWord_1309039 prefixEnd_1309039 672166202481009112592345 := by
  unfold tailWord_1309039
  simp only [CollatzResearch.WordTrace]
  refine ⟨47744574704582743907306171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31829716469721829271537447 47744574704582743907306171)
  ·
    refine ⟨71616862056874115860959257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47744574704582743907306171 71616862056874115860959257)
    ·
      refine ⟨53712646542655586895719443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71616862056874115860959257 53712646542655586895719443)
      ·
        refine ⟨80568969813983380343579165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53712646542655586895719443 80568969813983380343579165)
        ·
          refine ⟨30213363680243767628842187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80568969813983380343579165 30213363680243767628842187)
          ·
            refine ⟨45320045520365651443263281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30213363680243767628842187 45320045520365651443263281)
            ·
              refine ⟨33990034140274238582447461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45320045520365651443263281 33990034140274238582447461)
              ·
                refine ⟨6373131401301419734208899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33990034140274238582447461 6373131401301419734208899)
                ·
                  refine ⟨9559697101952129601313349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6373131401301419734208899 9559697101952129601313349)
                  ·
                    refine ⟨1792443206616024300246253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9559697101952129601313349 1792443206616024300246253)
                    ·
                      refine ⟨672166202481009112592345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1792443206616024300246253 672166202481009112592345)
                      ·
                        rfl

theorem cell23_1309039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 4, 3].length) (baseStart_1309039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309039 prefixEnd_1309039 := by exact prefixLift 1309039
  have htrace : WordTrace (prefixWord ++ tailWord_1309039) baseStart_1309039 baseEnd_1309039 := by
    simpa [prefixWord, tailWord_1309039, baseEnd_1309039] using wordTrace_append hprefix tailTrace_1309039
  have hstable : (prefixWord ++ tailWord_1309039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309039).length < 2 ^ (prefixWord ++ tailWord_1309039).sum := by decide
  have hdescent : baseEnd_1309039 < baseStart_1309039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309063 : List Nat := [1, 1, 4, 2, 2, 1, 2, 5, 1, 4]
def baseStart_1309063 : Nat := 118140960795 + 1309063 * 2 ^ 59
def prefixEnd_1309063 : Nat := 4983230072969 + 3 ^ 40 * 1309063 * 2
def baseEnd_1309063 : Nat := 224059508672239006230745

theorem tailTrace_1309063 : CollatzResearch.WordTrace tailWord_1309063 prefixEnd_1309063 224059508672239006230745 := by
  unfold tailWord_1309063
  simp only [CollatzResearch.WordTrace]
  refine ⟨47745450056495796006179843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31830300037663864004119895 47745450056495796006179843)
  ·
    refine ⟨71618175084743694009269765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47745450056495796006179843 71618175084743694009269765)
    ·
      refine ⟨13428407828389442626738081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71618175084743694009269765 13428407828389442626738081)
      ·
        refine ⟨10071305871292081970053561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13428407828389442626738081 10071305871292081970053561)
        ·
          refine ⟨7553479403469061477540171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10071305871292081970053561 7553479403469061477540171)
          ·
            refine ⟨11330219105203592216310257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7553479403469061477540171 11330219105203592216310257)
            ·
              refine ⟨8497664328902694162232693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11330219105203592216310257 8497664328902694162232693)
              ·
                refine ⟨796656030834627577709315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8497664328902694162232693 796656030834627577709315)
                ·
                  refine ⟨1194984046251941366563973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 796656030834627577709315 1194984046251941366563973)
                  ·
                    refine ⟨224059508672239006230745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1194984046251941366563973 224059508672239006230745)
                    ·
                      rfl

theorem cell23_1309063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 5, 1, 4].length) (baseStart_1309063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309063 prefixEnd_1309063 := by exact prefixLift 1309063
  have htrace : WordTrace (prefixWord ++ tailWord_1309063) baseStart_1309063 baseEnd_1309063 := by
    simpa [prefixWord, tailWord_1309063, baseEnd_1309063] using wordTrace_append hprefix tailTrace_1309063
  have hstable : (prefixWord ++ tailWord_1309063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309063).length < 2 ^ (prefixWord ++ tailWord_1309063).sum := by decide
  have hdescent : baseEnd_1309063 < baseStart_1309063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309080 : List Nat := [2, 1, 2, 5, 1, 2, 1, 4, 1, 4]
def baseStart_1309080 : Nat := 118140960795 + 1309080 * 2 ^ 59
def prefixEnd_1309080 : Nat := 4983230072969 + 3 ^ 40 * 1309080 * 2
def baseEnd_1309080 : Nat := 224062418395947817393219

theorem tailTrace_1309080 : CollatzResearch.WordTrace tailWord_1309080 prefixEnd_1309080 224062418395947817393219 := by
  unfold tailWord_1309080
  simp only [CollatzResearch.WordTrace]
  refine ⟨23873035048717103954774347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31830713398289471939699129 23873035048717103954774347)
  ·
    refine ⟨35809552573075655932161521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23873035048717103954774347 35809552573075655932161521)
    ·
      refine ⟨26857164429806741949121141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35809552573075655932161521 26857164429806741949121141)
      ·
        refine ⟨2517859165294382057730107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26857164429806741949121141 2517859165294382057730107)
        ·
          refine ⟨3776788747941573086595161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2517859165294382057730107 3776788747941573086595161)
          ·
            refine ⟨2832591560956179814946371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3776788747941573086595161 2832591560956179814946371)
            ·
              refine ⟨4248887341434269722419557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2832591560956179814946371 4248887341434269722419557)
              ·
                refine ⟨796666376518925572953667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4248887341434269722419557 796666376518925572953667)
                ·
                  refine ⟨1194999564778388359430501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 796666376518925572953667 1194999564778388359430501)
                  ·
                    refine ⟨224062418395947817393219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1194999564778388359430501 224062418395947817393219)
                    ·
                      rfl

theorem cell23_1309080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 4, 1, 4].length) (baseStart_1309080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309080 prefixEnd_1309080 := by exact prefixLift 1309080
  have htrace : WordTrace (prefixWord ++ tailWord_1309080) baseStart_1309080 baseEnd_1309080 := by
    simpa [prefixWord, tailWord_1309080, baseEnd_1309080] using wordTrace_append hprefix tailTrace_1309080
  have hstable : (prefixWord ++ tailWord_1309080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309080).length < 2 ^ (prefixWord ++ tailWord_1309080).sum := by decide
  have hdescent : baseEnd_1309080 < baseStart_1309080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309106 : List Nat := [3, 2, 1, 1, 1, 1, 4, 4, 1, 5]
def baseStart_1309106 : Nat := 118140960795 + 1309106 * 2 ^ 59
def prefixEnd_1309106 : Nat := 4983230072969 + 3 ^ 40 * 1309106 * 2
def baseEnd_1309106 : Nat := 224066868561620116818179

theorem tailTrace_1309106 : CollatzResearch.WordTrace tailWord_1309106 prefixEnd_1309106 224066868561620116818179 := by
  unfold tailWord_1309106
  simp only [CollatzResearch.WordTrace]
  refine ⟨11936754598835003587498793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31831345596893342899996781 11936754598835003587498793)
  ·
    refine ⟨8952565949126252690624095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11936754598835003587498793 8952565949126252690624095)
    ·
      refine ⟨13428848923689379035936143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8952565949126252690624095 13428848923689379035936143)
      ·
        refine ⟨20143273385534068553904215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13428848923689379035936143 20143273385534068553904215)
        ·
          refine ⟨30214910078301102830856323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20143273385534068553904215 30214910078301102830856323)
          ·
            refine ⟨45322365117451654246284485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30214910078301102830856323 45322365117451654246284485)
            ·
              refine ⟨8497943459522185171178341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45322365117451654246284485 8497943459522185171178341)
              ·
                refine ⟨1593364398660409719595939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8497943459522185171178341 1593364398660409719595939)
                ·
                  refine ⟨2390046597990614579393909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1593364398660409719595939 2390046597990614579393909)
                  ·
                    refine ⟨224066868561620116818179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2390046597990614579393909 224066868561620116818179)
                    ·
                      rfl

theorem cell23_1309106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 4, 1, 5].length) (baseStart_1309106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309106 prefixEnd_1309106 := by exact prefixLift 1309106
  have htrace : WordTrace (prefixWord ++ tailWord_1309106) baseStart_1309106 baseEnd_1309106 := by
    simpa [prefixWord, tailWord_1309106, baseEnd_1309106] using wordTrace_append hprefix tailTrace_1309106
  have hstable : (prefixWord ++ tailWord_1309106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309106).length < 2 ^ (prefixWord ++ tailWord_1309106).sum := by decide
  have hdescent : baseEnd_1309106 < baseStart_1309106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309113 : List Nat := [1, 2, 1, 4, 3, 2, 1, 1, 1, 5, 2]
def baseStart_1309113 : Nat := 118140960795 + 1309113 * 2 ^ 59
def prefixEnd_1309113 : Nat := 4983230072969 + 3 ^ 40 * 1309113 * 2
def baseEnd_1309113 : Nat := 672204200049441823067005

theorem tailTrace_1309113 : CollatzResearch.WordTrace tailWord_1309113 prefixEnd_1309113 672204200049441823067005 := by
  unfold tailWord_1309113
  simp only [CollatzResearch.WordTrace]
  refine ⟨47747273706314654545499993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31831515804209769696999995 47747273706314654545499993)
  ·
    refine ⟨35810455279735990909124995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47747273706314654545499993 35810455279735990909124995)
    ·
      refine ⟨53715682919603986363687493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35810455279735990909124995 53715682919603986363687493)
      ·
        refine ⟨10071690547425747443191405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53715682919603986363687493 10071690547425747443191405)
        ·
          refine ⟨3776883955284655291196777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10071690547425747443191405 3776883955284655291196777)
          ·
            refine ⟨2832662966463491468397583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3776883955284655291196777 2832662966463491468397583)
            ·
              refine ⟨4248994449695237202596375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2832662966463491468397583 4248994449695237202596375)
              ·
                refine ⟨6373491674542855803894563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4248994449695237202596375 6373491674542855803894563)
                ·
                  refine ⟨9560237511814283705841845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6373491674542855803894563 9560237511814283705841845)
                  ·
                    refine ⟨896272266732589097422673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9560237511814283705841845 896272266732589097422673)
                    ·
                      refine ⟨672204200049441823067005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 896272266732589097422673 672204200049441823067005)
                      ·
                        rfl

theorem cell23_1309113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 5, 2].length) (baseStart_1309113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309113 prefixEnd_1309113 := by exact prefixLift 1309113
  have htrace : WordTrace (prefixWord ++ tailWord_1309113) baseStart_1309113 baseEnd_1309113 := by
    simpa [prefixWord, tailWord_1309113, baseEnd_1309113] using wordTrace_append hprefix tailTrace_1309113
  have hstable : (prefixWord ++ tailWord_1309113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309113).length < 2 ^ (prefixWord ++ tailWord_1309113).sum := by decide
  have hdescent : baseEnd_1309113 < baseStart_1309113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309146 : List Nat := [3, 1, 1, 2, 3, 1, 3, 2, 1, 1, 5]
def baseStart_1309146 : Nat := 118140960795 + 1309146 * 2 ^ 59
def prefixEnd_1309146 : Nat := 4983230072969 + 3 ^ 40 * 1309146 * 2
def baseEnd_1309146 : Nat := 672221144911040193954353

theorem tailTrace_1309146 : CollatzResearch.WordTrace tailWord_1309146 prefixEnd_1309146 672221144911040193954353 := by
  unfold tailWord_1309146
  simp only [CollatzResearch.WordTrace]
  refine ⟨11937119328798775295362823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31832318210130067454300861 11937119328798775295362823)
  ·
    refine ⟨17905678993198162943044235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11937119328798775295362823 17905678993198162943044235)
    ·
      refine ⟨26858518489797244414566353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17905678993198162943044235 26858518489797244414566353)
      ·
        refine ⟨20143888867347933310924765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26858518489797244414566353 20143888867347933310924765)
        ·
          refine ⟨7553958325255474991596787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20143888867347933310924765 7553958325255474991596787)
          ·
            refine ⟨11330937487883212487395181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7553958325255474991596787 11330937487883212487395181)
            ·
              refine ⟨4249101557956204682773193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11330937487883212487395181 4249101557956204682773193)
              ·
                refine ⟨3186826168467153512079895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4249101557956204682773193 3186826168467153512079895)
                ·
                  refine ⟨4780239252700730268119843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3186826168467153512079895 4780239252700730268119843)
                  ·
                    refine ⟨7170358879051095402179765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4780239252700730268119843 7170358879051095402179765)
                    ·
                      refine ⟨672221144911040193954353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7170358879051095402179765 672221144911040193954353)
                      ·
                        rfl

theorem cell23_1309146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_1309146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309146 prefixEnd_1309146 := by exact prefixLift 1309146
  have htrace : WordTrace (prefixWord ++ tailWord_1309146) baseStart_1309146 baseEnd_1309146 := by
    simpa [prefixWord, tailWord_1309146, baseEnd_1309146] using wordTrace_append hprefix tailTrace_1309146
  have hstable : (prefixWord ++ tailWord_1309146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309146).length < 2 ^ (prefixWord ++ tailWord_1309146).sum := by decide
  have hdescent : baseEnd_1309146 < baseStart_1309146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309160 : List Nat := [2, 1, 4, 1, 1, 3, 2, 2, 3, 2, 2]
def baseStart_1309160 : Nat := 118140960795 + 1309160 * 2 ^ 59
def prefixEnd_1309160 : Nat := 4983230072969 + 3 ^ 40 * 1309160 * 2
def baseEnd_1309160 : Nat := 672228333640203139179289

theorem tailTrace_1309160 : CollatzResearch.WordTrace tailWord_1309160 prefixEnd_1309160 672228333640203139179289 := by
  unfold tailWord_1309160
  simp only [CollatzResearch.WordTrace]
  refine ⟨23874493968572190786230467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31832658624762921048307289 23874493968572190786230467)
  ·
    refine ⟨35811740952858286179345701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23874493968572190786230467 35811740952858286179345701)
    ·
      refine ⟨6714701428660928658627319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35811740952858286179345701 6714701428660928658627319)
      ·
        refine ⟨10072052142991392987940979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6714701428660928658627319 10072052142991392987940979)
        ·
          refine ⟨15108078214487089481911469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10072052142991392987940979 15108078214487089481911469)
          ·
            refine ⟨5665529330432658555716801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15108078214487089481911469 5665529330432658555716801)
            ·
              refine ⟨4249146997824493916787601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5665529330432658555716801 4249146997824493916787601)
              ·
                refine ⟨3186860248368370437590701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4249146997824493916787601 3186860248368370437590701)
                ·
                  refine ⟨1195072593138138914096513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3186860248368370437590701 1195072593138138914096513)
                  ·
                    refine ⟨896304444853604185572385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1195072593138138914096513 896304444853604185572385)
                    ·
                      refine ⟨672228333640203139179289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 896304444853604185572385 672228333640203139179289)
                      ·
                        rfl

theorem cell23_1309160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 3, 2, 2].length) (baseStart_1309160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309160 prefixEnd_1309160 := by exact prefixLift 1309160
  have htrace : WordTrace (prefixWord ++ tailWord_1309160) baseStart_1309160 baseEnd_1309160 := by
    simpa [prefixWord, tailWord_1309160, baseEnd_1309160] using wordTrace_append hprefix tailTrace_1309160
  have hstable : (prefixWord ++ tailWord_1309160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309160).length < 2 ^ (prefixWord ++ tailWord_1309160).sum := by decide
  have hdescent : baseEnd_1309160 < baseStart_1309160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309163 : List Nat := [1, 1, 1, 1, 2, 3, 6, 2, 1, 2, 3]
def baseStart_1309163 : Nat := 118140960795 + 1309163 * 2 ^ 59
def prefixEnd_1309163 : Nat := 4983230072969 + 3 ^ 40 * 1309163 * 2
def baseEnd_1309163 : Nat := 672229874082166627441775

theorem tailTrace_1309163 : CollatzResearch.WordTrace tailWord_1309163 prefixEnd_1309163 672229874082166627441775 := by
  unfold tailWord_1309163
  simp only [CollatzResearch.WordTrace]
  refine ⟨47749097356133513084820143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31832731570755675389880095 47749097356133513084820143)
  ·
    refine ⟨71623646034200269627230215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47749097356133513084820143 71623646034200269627230215)
    ·
      refine ⟨107435469051300404440845323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71623646034200269627230215 107435469051300404440845323)
      ·
        refine ⟨161153203576950606661267985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107435469051300404440845323 161153203576950606661267985)
        ·
          refine ⟨120864902682712954995950989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161153203576950606661267985 120864902682712954995950989)
          ·
            refine ⟨45324338506017358123481621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120864902682712954995950989 45324338506017358123481621)
            ·
              refine ⟨2124578367469563662038201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 45324338506017358123481621 2124578367469563662038201)
              ·
                refine ⟨1593433775602172746528651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2124578367469563662038201 1593433775602172746528651)
                ·
                  refine ⟨2390150663403259119792977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1593433775602172746528651 2390150663403259119792977)
                  ·
                    refine ⟨1792612997552444339844733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2390150663403259119792977 1792612997552444339844733)
                    ·
                      refine ⟨672229874082166627441775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1792612997552444339844733 672229874082166627441775)
                      ·
                        rfl

theorem cell23_1309163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 2, 1, 2, 3].length) (baseStart_1309163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309163 prefixEnd_1309163 := by exact prefixLift 1309163
  have htrace : WordTrace (prefixWord ++ tailWord_1309163) baseStart_1309163 baseEnd_1309163 := by
    simpa [prefixWord, tailWord_1309163, baseEnd_1309163] using wordTrace_append hprefix tailTrace_1309163
  have hstable : (prefixWord ++ tailWord_1309163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309163).length < 2 ^ (prefixWord ++ tailWord_1309163).sum := by decide
  have hdescent : baseEnd_1309163 < baseStart_1309163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309166 : List Nat := [4, 1, 2, 1, 2, 3, 1, 9]
def baseStart_1309166 : Nat := 118140960795 + 1309166 * 2 ^ 59
def prefixEnd_1309166 : Nat := 4983230072969 + 3 ^ 40 * 1309166 * 2
def baseEnd_1309166 : Nat := 24897459797190004285343

theorem tailTrace_1309166 : CollatzResearch.WordTrace tailWord_1309166 prefixEnd_1309166 24897459797190004285343 := by
  unfold tailWord_1309166
  simp only [CollatzResearch.WordTrace]
  refine ⟨5968650846890330574647419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31832804516748429731452901 5968650846890330574647419)
  ·
    refine ⟨8952976270335495861971129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5968650846890330574647419 8952976270335495861971129)
    ·
      refine ⟨6714732202751621896478347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8952976270335495861971129 6714732202751621896478347)
      ·
        refine ⟨10072098304127432844717521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6714732202751621896478347 10072098304127432844717521)
        ·
          refine ⟨7554073728095574633538141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10072098304127432844717521 7554073728095574633538141)
          ·
            refine ⟨2832777648035840487576803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7554073728095574633538141 2832777648035840487576803)
            ·
              refine ⟨4249166472053760731365205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2832777648035840487576803 4249166472053760731365205)
              ·
                refine ⟨24897459797190004285343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4249166472053760731365205 24897459797190004285343)
                ·
                  rfl

theorem cell23_1309166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 9].length) (baseStart_1309166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309166 prefixEnd_1309166 := by exact prefixLift 1309166
  have htrace : WordTrace (prefixWord ++ tailWord_1309166) baseStart_1309166 baseEnd_1309166 := by
    simpa [prefixWord, tailWord_1309166, baseEnd_1309166] using wordTrace_append hprefix tailTrace_1309166
  have hstable : (prefixWord ++ tailWord_1309166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309166).length < 2 ^ (prefixWord ++ tailWord_1309166).sum := by decide
  have hdescent : baseEnd_1309166 < baseStart_1309166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309176 : List Nat := [2, 1, 2, 1, 1, 4, 2, 1, 3, 3, 3]
def baseStart_1309176 : Nat := 118140960795 + 1309176 * 2 ^ 59
def prefixEnd_1309176 : Nat := 4983230072969 + 3 ^ 40 * 1309176 * 2
def baseEnd_1309176 : Nat := 672236549330675076579215

theorem tailTrace_1309176 : CollatzResearch.WordTrace tailWord_1309176 prefixEnd_1309176 672236549330675076579215 := by
  unfold tailWord_1309176
  simp only [CollatzResearch.WordTrace]
  refine ⟨23874785752543208152521691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31833047670057610870028921 23874785752543208152521691)
  ·
    refine ⟨35812178628814812228782537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23874785752543208152521691 35812178628814812228782537)
    ·
      refine ⟨26859133971611109171586903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35812178628814812228782537 26859133971611109171586903)
      ·
        refine ⟨40288700957416663757380355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26859133971611109171586903 40288700957416663757380355)
        ·
          refine ⟨60433051436124995636070533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40288700957416663757380355 60433051436124995636070533)
          ·
            refine ⟨11331197144273436681763225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60433051436124995636070533 11331197144273436681763225)
            ·
              refine ⟨8498397858205077511322419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11331197144273436681763225 8498397858205077511322419)
              ·
                refine ⟨12747596787307616266983629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8498397858205077511322419 12747596787307616266983629)
                ·
                  refine ⟨4780348795240356100118861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12747596787307616266983629 4780348795240356100118861)
                  ·
                    refine ⟨1792630798215133537544573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4780348795240356100118861 1792630798215133537544573)
                    ·
                      refine ⟨672236549330675076579215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1792630798215133537544573 672236549330675076579215)
                      ·
                        rfl

theorem cell23_1309176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 3, 3, 3].length) (baseStart_1309176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309176 prefixEnd_1309176 := by exact prefixLift 1309176
  have htrace : WordTrace (prefixWord ++ tailWord_1309176) baseStart_1309176 baseEnd_1309176 := by
    simpa [prefixWord, tailWord_1309176, baseEnd_1309176] using wordTrace_append hprefix tailTrace_1309176
  have hstable : (prefixWord ++ tailWord_1309176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309176).length < 2 ^ (prefixWord ++ tailWord_1309176).sum := by decide
  have hdescent : baseEnd_1309176 < baseStart_1309176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309177 : List Nat := [1, 2, 1, 3, 1, 2, 5, 3, 1, 2, 2]
def baseStart_1309177 : Nat := 118140960795 + 1309177 * 2 ^ 59
def prefixEnd_1309177 : Nat := 4983230072969 + 3 ^ 40 * 1309177 * 2
def baseEnd_1309177 : Nat := 672237062811329572666711

theorem tailTrace_1309177 : CollatzResearch.WordTrace tailWord_1309177 prefixEnd_1309177 672237062811329572666711 := by
  unfold tailWord_1309177
  simp only [CollatzResearch.WordTrace]
  refine ⟨47749607978082793475829785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31833071985388528983886523 47749607978082793475829785)
  ·
    refine ⟨35812205983562095106872339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47749607978082793475829785 35812205983562095106872339)
    ·
      refine ⟨53718308975343142660308509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35812205983562095106872339 53718308975343142660308509)
      ·
        refine ⟨20144365865753678497615691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53718308975343142660308509 20144365865753678497615691)
        ·
          refine ⟨30216548798630517746423537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20144365865753678497615691 30216548798630517746423537)
          ·
            refine ⟨22662411598972888309817653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30216548798630517746423537 22662411598972888309817653)
            ·
              refine ⟨2124601087403708279045405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22662411598972888309817653 2124601087403708279045405)
              ·
                refine ⟨796725407776390604642027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2124601087403708279045405 796725407776390604642027)
                ·
                  refine ⟨1195088111664585906963041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 796725407776390604642027 1195088111664585906963041)
                  ·
                    refine ⟨896316083748439430222281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1195088111664585906963041 896316083748439430222281)
                    ·
                      refine ⟨672237062811329572666711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 896316083748439430222281 672237062811329572666711)
                      ·
                        rfl

theorem cell23_1309177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 3, 1, 2, 2].length) (baseStart_1309177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309177 prefixEnd_1309177 := by exact prefixLift 1309177
  have htrace : WordTrace (prefixWord ++ tailWord_1309177) baseStart_1309177 baseEnd_1309177 := by
    simpa [prefixWord, tailWord_1309177, baseEnd_1309177] using wordTrace_append hprefix tailTrace_1309177
  have hstable : (prefixWord ++ tailWord_1309177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309177).length < 2 ^ (prefixWord ++ tailWord_1309177).sum := by decide
  have hdescent : baseEnd_1309177 < baseStart_1309177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309194 : List Nat := [3, 1, 2, 2, 2, 1, 5, 2, 1, 2, 2]
def baseStart_1309194 : Nat := 118140960795 + 1309194 * 2 ^ 59
def prefixEnd_1309194 : Nat := 4983230072969 + 3 ^ 40 * 1309194 * 2
def baseEnd_1309194 : Nat := 672245791982456006154133

theorem tailTrace_1309194 : CollatzResearch.WordTrace tailWord_1309194 prefixEnd_1309194 672245791982456006154133 := by
  unfold tailWord_1309194
  simp only [CollatzResearch.WordTrace]
  refine ⟨11937557004755301344799659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31833485346014136919465757 11937557004755301344799659)
  ·
    refine ⟨17906335507132952017199489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11937557004755301344799659 17906335507132952017199489)
    ·
      refine ⟨13429751630349714012899617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17906335507132952017199489 13429751630349714012899617)
      ·
        refine ⟨10072313722762285509674713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13429751630349714012899617 10072313722762285509674713)
        ·
          refine ⟨7554235292071714132256035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10072313722762285509674713 7554235292071714132256035)
          ·
            refine ⟨11331352938107571198384053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7554235292071714132256035 11331352938107571198384053)
            ·
              refine ⟨1062314337947584799848505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11331352938107571198384053 1062314337947584799848505)
              ·
                refine ⟨796735753460688599886379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1062314337947584799848505 796735753460688599886379)
                ·
                  refine ⟨1195103630191032899829569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 796735753460688599886379 1195103630191032899829569)
                  ·
                    refine ⟨896327722643274674872177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1195103630191032899829569 896327722643274674872177)
                    ·
                      refine ⟨672245791982456006154133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 896327722643274674872177 672245791982456006154133)
                      ·
                        rfl

theorem cell23_1309194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 2, 1, 2, 2].length) (baseStart_1309194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309194 prefixEnd_1309194 := by exact prefixLift 1309194
  have htrace : WordTrace (prefixWord ++ tailWord_1309194) baseStart_1309194 baseEnd_1309194 := by
    simpa [prefixWord, tailWord_1309194, baseEnd_1309194] using wordTrace_append hprefix tailTrace_1309194
  have hstable : (prefixWord ++ tailWord_1309194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309194).length < 2 ^ (prefixWord ++ tailWord_1309194).sum := by decide
  have hdescent : baseEnd_1309194 < baseStart_1309194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309203 : List Nat := [1, 1, 1, 2, 1, 5, 2, 2, 3, 3, 2]
def baseStart_1309203 : Nat := 118140960795 + 1309203 * 2 ^ 59
def prefixEnd_1309203 : Nat := 4983230072969 + 3 ^ 40 * 1309203 * 2
def baseEnd_1309203 : Nat := 672250413308346470941591

theorem tailTrace_1309203 : CollatzResearch.WordTrace tailWord_1309203 prefixEnd_1309203 672250413308346470941591 := by
  unfold tailWord_1309203
  simp only [CollatzResearch.WordTrace]
  refine ⟨47750556275988599916276263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31833704183992399944184175 47750556275988599916276263)
  ·
    refine ⟨71625834413982899874414395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47750556275988599916276263 71625834413982899874414395)
    ·
      refine ⟨107438751620974349811621593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71625834413982899874414395 107438751620974349811621593)
      ·
        refine ⟨80579063715730762358716195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107438751620974349811621593 80579063715730762358716195)
        ·
          refine ⟨120868595573596143538074293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80579063715730762358716195 120868595573596143538074293)
          ·
            refine ⟨11331430835024638456694465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 120868595573596143538074293 11331430835024638456694465)
            ·
              refine ⟨8498573126268478842520849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11331430835024638456694465 8498573126268478842520849)
              ·
                refine ⟨6373929844701359131890637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8498573126268478842520849 6373929844701359131890637)
                ·
                  refine ⟨2390223691763009674458989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6373929844701359131890637 2390223691763009674458989)
                  ·
                    refine ⟨896333884411128627922121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2390223691763009674458989 896333884411128627922121)
                    ·
                      refine ⟨672250413308346470941591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 896333884411128627922121 672250413308346470941591)
                      ·
                        rfl

theorem cell23_1309203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 3, 3, 2].length) (baseStart_1309203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309203 prefixEnd_1309203 := by exact prefixLift 1309203
  have htrace : WordTrace (prefixWord ++ tailWord_1309203) baseStart_1309203 baseEnd_1309203 := by
    simpa [prefixWord, tailWord_1309203, baseEnd_1309203] using wordTrace_append hprefix tailTrace_1309203
  have hstable : (prefixWord ++ tailWord_1309203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309203).length < 2 ^ (prefixWord ++ tailWord_1309203).sum := by decide
  have hdescent : baseEnd_1309203 < baseStart_1309203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309204 : List Nat := [2, 4, 3, 1, 1, 3, 2, 1, 2, 4]
def baseStart_1309204 : Nat := 118140960795 + 1309204 * 2 ^ 59
def prefixEnd_1309204 : Nat := 4983230072969 + 3 ^ 40 * 1309204 * 2
def baseEnd_1309204 : Nat := 224083642263000322343029

theorem tailTrace_1309204 : CollatzResearch.WordTrace tailWord_1309204 prefixEnd_1309204 224083642263000322343029 := by
  unfold tailWord_1309204
  simp only [CollatzResearch.WordTrace]
  refine ⟨23875296374492488543531333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31833728499323318058041777 23875296374492488543531333)
  ·
    refine ⟨4476618070217341601912125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23875296374492488543531333 4476618070217341601912125)
    ·
      refine ⟨1678731776331503100717047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4476618070217341601912125 1678731776331503100717047)
      ·
        refine ⟨2518097664497254651075571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1678731776331503100717047 2518097664497254651075571)
        ·
          refine ⟨3777146496745881976613357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2518097664497254651075571 3777146496745881976613357)
          ·
            refine ⟨1416429936279705741230009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3777146496745881976613357 1416429936279705741230009)
            ·
              refine ⟨1062322452209779305922507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1416429936279705741230009 1062322452209779305922507)
              ·
                refine ⟨1593483678314668958883761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1062322452209779305922507 1593483678314668958883761)
                ·
                  refine ⟨1195112758736001719162821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1593483678314668958883761 1195112758736001719162821)
                  ·
                    refine ⟨224083642263000322343029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1195112758736001719162821 224083642263000322343029)
                    ·
                      rfl

theorem cell23_1309204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_1309204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309204 prefixEnd_1309204 := by exact prefixLift 1309204
  have htrace : WordTrace (prefixWord ++ tailWord_1309204) baseStart_1309204 baseEnd_1309204 := by
    simpa [prefixWord, tailWord_1309204, baseEnd_1309204] using wordTrace_append hprefix tailTrace_1309204
  have hstable : (prefixWord ++ tailWord_1309204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309204).length < 2 ^ (prefixWord ++ tailWord_1309204).sum := by decide
  have hdescent : baseEnd_1309204 < baseStart_1309204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309233 : List Nat := [1, 2, 2, 3, 1, 1, 3, 1, 3, 4, 2]
def baseStart_1309233 : Nat := 118140960795 + 1309233 * 2 ^ 59
def prefixEnd_1309233 : Nat := 4983230072969 + 3 ^ 40 * 1309233 * 2
def baseEnd_1309233 : Nat := 672265817727981353566453

theorem tailTrace_1309233 : CollatzResearch.WordTrace tailWord_1309233 prefixEnd_1309233 672265817727981353566453 := by
  unfold tailWord_1309233
  simp only [CollatzResearch.WordTrace]
  refine ⟨47751650465879915039868353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31834433643919943359912235 47751650465879915039868353)
  ·
    refine ⟨35813737849409936279901265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47751650465879915039868353 35813737849409936279901265)
    ·
      refine ⟨26860303387057452209925949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35813737849409936279901265 26860303387057452209925949)
      ·
        refine ⟨10072613770146544578722231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26860303387057452209925949 10072613770146544578722231)
        ·
          refine ⟨15108920655219816868083347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10072613770146544578722231 15108920655219816868083347)
          ·
            refine ⟨22663380982829725302125021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15108920655219816868083347 22663380982829725302125021)
            ·
              refine ⟨8498767868561146988296883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22663380982829725302125021 8498767868561146988296883)
              ·
                refine ⟨12748151802841720482445325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8498767868561146988296883 12748151802841720482445325)
                ·
                  refine ⟨4780556926065645180916997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12748151802841720482445325 4780556926065645180916997)
                  ·
                    refine ⟨896354423637308471421937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4780556926065645180916997 896354423637308471421937)
                    ·
                      refine ⟨672265817727981353566453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 896354423637308471421937 672265817727981353566453)
                      ·
                        rfl

theorem cell23_1309233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 4, 2].length) (baseStart_1309233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309233 prefixEnd_1309233 := by exact prefixLift 1309233
  have htrace : WordTrace (prefixWord ++ tailWord_1309233) baseStart_1309233 baseEnd_1309233 := by
    simpa [prefixWord, tailWord_1309233, baseEnd_1309233] using wordTrace_append hprefix tailTrace_1309233
  have hstable : (prefixWord ++ tailWord_1309233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309233).length < 2 ^ (prefixWord ++ tailWord_1309233).sum := by decide
  have hdescent : baseEnd_1309233 < baseStart_1309233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309237 : List Nat := [1, 3, 3, 1, 1, 2, 5, 1, 1, 3, 2]
def baseStart_1309237 : Nat := 118140960795 + 1309237 * 2 ^ 59
def prefixEnd_1309237 : Nat := 4983230072969 + 3 ^ 40 * 1309237 * 2
def baseEnd_1309237 : Nat := 672267871650599337916435

theorem tailTrace_1309237 : CollatzResearch.WordTrace tailWord_1309237 prefixEnd_1309237 672267871650599337916435 := by
  unfold tailWord_1309237
  simp only [CollatzResearch.WordTrace]
  refine ⟨47751796357865423723013965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31834530905243615815342643 47751796357865423723013965)
  ·
    refine ⟨17906923634199533896130237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47751796357865423723013965 17906923634199533896130237)
    ·
      refine ⟨6715096362824825211048839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17906923634199533896130237 6715096362824825211048839)
      ·
        refine ⟨10072644544237237816573259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6715096362824825211048839 10072644544237237816573259)
        ·
          refine ⟨15108966816355856724859889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10072644544237237816573259 15108966816355856724859889)
          ·
            refine ⟨11331725112266892543644917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15108966816355856724859889 11331725112266892543644917)
            ·
              refine ⟨1062349229275021175966711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11331725112266892543644917 1062349229275021175966711)
              ·
                refine ⟨1593523843912531763950067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1062349229275021175966711 1593523843912531763950067)
                ·
                  refine ⟨2390285765868797645925101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1593523843912531763950067 2390285765868797645925101)
                  ·
                    refine ⟨896357162200799117221913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2390285765868797645925101 896357162200799117221913)
                    ·
                      refine ⟨672267871650599337916435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 896357162200799117221913 672267871650599337916435)
                      ·
                        rfl

theorem cell23_1309237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 1, 1, 3, 2].length) (baseStart_1309237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309237 prefixEnd_1309237 := by exact prefixLift 1309237
  have htrace : WordTrace (prefixWord ++ tailWord_1309237) baseStart_1309237 baseEnd_1309237 := by
    simpa [prefixWord, tailWord_1309237, baseEnd_1309237] using wordTrace_append hprefix tailTrace_1309237
  have hstable : (prefixWord ++ tailWord_1309237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309237).length < 2 ^ (prefixWord ++ tailWord_1309237).sum := by decide
  have hdescent : baseEnd_1309237 < baseStart_1309237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309290 : List Nat := [3, 1, 3, 2, 1, 1, 4, 3, 5]
def baseStart_1309290 : Nat := 118140960795 + 1309290 * 2 ^ 59
def prefixEnd_1309290 : Nat := 4983230072969 + 3 ^ 40 * 1309290 * 2
def baseEnd_1309290 : Nat := 74699454013920847839299

theorem tailTrace_1309290 : CollatzResearch.WordTrace tailWord_1309290 prefixEnd_1309290 74699454013920847839299 := by
  unfold tailWord_1309290
  simp only [CollatzResearch.WordTrace]
  refine ⟨11938432356668353443673331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31835819617782275849795549 11938432356668353443673331)
  ·
    refine ⟨17907648535002530165509997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11938432356668353443673331 17907648535002530165509997)
    ·
      refine ⟨6715368200625948812066249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17907648535002530165509997 6715368200625948812066249)
      ·
        refine ⟨5036526150469461609049687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6715368200625948812066249 5036526150469461609049687)
        ·
          refine ⟨7554789225704192413574531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5036526150469461609049687 7554789225704192413574531)
          ·
            refine ⟨11332183838556288620361797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7554789225704192413574531 11332183838556288620361797)
            ·
              refine ⟨2124784469729304116317837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11332183838556288620361797 2124784469729304116317837)
              ·
                refine ⟨796794176148489043619189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2124784469729304116317837 796794176148489043619189)
                ·
                  refine ⟨74699454013920847839299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 796794176148489043619189 74699454013920847839299)
                  ·
                    rfl

theorem cell23_1309290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 3, 5].length) (baseStart_1309290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309290 prefixEnd_1309290 := by exact prefixLift 1309290
  have htrace : WordTrace (prefixWord ++ tailWord_1309290) baseStart_1309290 baseEnd_1309290 := by
    simpa [prefixWord, tailWord_1309290, baseEnd_1309290] using wordTrace_append hprefix tailTrace_1309290
  have hstable : (prefixWord ++ tailWord_1309290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309290).length < 2 ^ (prefixWord ++ tailWord_1309290).sum := by decide
  have hdescent : baseEnd_1309290 < baseStart_1309290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309301 : List Nat := [1, 3, 4, 2, 2, 2, 1, 2, 2, 2, 2]
def baseStart_1309301 : Nat := 118140960795 + 1309301 * 2 ^ 59
def prefixEnd_1309301 : Nat := 4983230072969 + 3 ^ 40 * 1309301 * 2
def baseEnd_1309301 : Nat := 672300734412487087516141

theorem tailTrace_1309301 : CollatzResearch.WordTrace tailWord_1309301 prefixEnd_1309301 672300734412487087516141 := by
  unfold tailWord_1309301
  simp only [CollatzResearch.WordTrace]
  refine ⟨47754130629633562653343757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31836087086422375102229171 47754130629633562653343757)
  ·
    refine ⟨17907798986112585995003909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47754130629633562653343757 17907798986112585995003909)
    ·
      refine ⟨3357712309896109874063233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17907798986112585995003909 3357712309896109874063233)
      ·
        refine ⟨2518284232422082405547425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3357712309896109874063233 2518284232422082405547425)
        ·
          refine ⟨1888713174316561804160569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2518284232422082405547425 1888713174316561804160569)
          ·
            refine ⟨1416534880737421353120427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1888713174316561804160569 1416534880737421353120427)
            ·
              refine ⟨2124802321106132029680641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1416534880737421353120427 2124802321106132029680641)
              ·
                refine ⟨1593601740829599022260481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2124802321106132029680641 1593601740829599022260481)
                ·
                  refine ⟨1195201305622199266695361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1593601740829599022260481 1195201305622199266695361)
                  ·
                    refine ⟨896400979216649450021521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1195201305622199266695361 896400979216649450021521)
                    ·
                      refine ⟨672300734412487087516141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 896400979216649450021521 672300734412487087516141)
                      ·
                        rfl

theorem cell23_1309301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_1309301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309301 prefixEnd_1309301 := by exact prefixLift 1309301
  have htrace : WordTrace (prefixWord ++ tailWord_1309301) baseStart_1309301 baseEnd_1309301 := by
    simpa [prefixWord, tailWord_1309301, baseEnd_1309301] using wordTrace_append hprefix tailTrace_1309301
  have hstable : (prefixWord ++ tailWord_1309301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309301).length < 2 ^ (prefixWord ++ tailWord_1309301).sum := by decide
  have hdescent : baseEnd_1309301 < baseStart_1309301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309323 : List Nat := [1, 1, 1, 1, 4, 1, 2, 3, 1, 6, 2]
def baseStart_1309323 : Nat := 118140960795 + 1309323 * 2 ^ 59
def prefixEnd_1309323 : Nat := 4983230072969 + 3 ^ 40 * 1309323 * 2
def baseEnd_1309323 : Nat := 672312030986886001441039

theorem tailTrace_1309323 : CollatzResearch.WordTrace tailWord_1309323 prefixEnd_1309323 672312030986886001441039 := by
  unfold tailWord_1309323
  simp only [CollatzResearch.WordTrace]
  refine ⟨47754933035553860410644623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31836622023702573607096415 47754933035553860410644623)
  ·
    refine ⟨71632399553330790615966935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47754933035553860410644623 71632399553330790615966935)
    ·
      refine ⟨107448599329996185923950403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71632399553330790615966935 107448599329996185923950403)
      ·
        refine ⟨161172898994994278885925605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107448599329996185923950403 161172898994994278885925605)
        ·
          refine ⟨30219918561561427291111051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 161172898994994278885925605 30219918561561427291111051)
          ·
            refine ⟨45329877842342140936666577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30219918561561427291111051 45329877842342140936666577)
            ·
              refine ⟨33997408381756605702499933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45329877842342140936666577 33997408381756605702499933)
              ·
                refine ⟨12749028143158727138437475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33997408381756605702499933 12749028143158727138437475)
                ·
                  refine ⟨19123542214738090707656213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12749028143158727138437475 19123542214738090707656213)
                  ·
                    refine ⟨896416041315848001921385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19123542214738090707656213 896416041315848001921385)
                    ·
                      refine ⟨672312030986886001441039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 896416041315848001921385 672312030986886001441039)
                      ·
                        rfl

theorem cell23_1309323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 6, 2].length) (baseStart_1309323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309323 prefixEnd_1309323 := by exact prefixLift 1309323
  have htrace : WordTrace (prefixWord ++ tailWord_1309323) baseStart_1309323 baseEnd_1309323 := by
    simpa [prefixWord, tailWord_1309323, baseEnd_1309323] using wordTrace_append hprefix tailTrace_1309323
  have hstable : (prefixWord ++ tailWord_1309323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309323).length < 2 ^ (prefixWord ++ tailWord_1309323).sum := by decide
  have hdescent : baseEnd_1309323 < baseStart_1309323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309367 : List Nat := [1, 1, 3, 1, 6, 2, 1, 1, 3, 4]
def baseStart_1309367 : Nat := 118140960795 + 1309367 * 2 ^ 59
def prefixEnd_1309367 : Nat := 4983230072969 + 3 ^ 40 * 1309367 * 2
def baseEnd_1309367 : Nat := 224111541378561276430279

theorem tailTrace_1309367 : CollatzResearch.WordTrace tailWord_1309367 prefixEnd_1309367 224111541378561276430279 := by
  unfold tailWord_1309367
  simp only [CollatzResearch.WordTrace]
  refine ⟨47756537847394455925246355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31837691898262970616830903 47756537847394455925246355)
  ·
    refine ⟨71634806771091683887869533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47756537847394455925246355 71634806771091683887869533)
    ·
      refine ⟨26863052539159381457951075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71634806771091683887869533 26863052539159381457951075)
      ·
        refine ⟨40294578808739072186926613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26863052539159381457951075 40294578808739072186926613)
        ·
          refine ⟨1888808381659644008762185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 40294578808739072186926613 1888808381659644008762185)
          ·
            refine ⟨1416606286244733006571639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1888808381659644008762185 1416606286244733006571639)
            ·
              refine ⟨2124909429367099509857459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1416606286244733006571639 2124909429367099509857459)
              ·
                refine ⟨3187364144050649264786189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2124909429367099509857459 3187364144050649264786189)
                ·
                  refine ⟨1195261554018993474294821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3187364144050649264786189 1195261554018993474294821)
                  ·
                    refine ⟨224111541378561276430279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1195261554018993474294821 224111541378561276430279)
                    ·
                      rfl

theorem cell23_1309367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 3, 4].length) (baseStart_1309367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309367 prefixEnd_1309367 := by exact prefixLift 1309367
  have htrace : WordTrace (prefixWord ++ tailWord_1309367) baseStart_1309367 baseEnd_1309367 := by
    simpa [prefixWord, tailWord_1309367, baseEnd_1309367] using wordTrace_append hprefix tailTrace_1309367
  have hstable : (prefixWord ++ tailWord_1309367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309367).length < 2 ^ (prefixWord ++ tailWord_1309367).sum := by decide
  have hdescent : baseEnd_1309367 < baseStart_1309367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309380 : List Nat := [2, 3, 3, 1, 1, 3, 1, 3, 6]
def baseStart_1309380 : Nat := 118140960795 + 1309380 * 2 ^ 59
def prefixEnd_1309380 : Nat := 4983230072969 + 3 ^ 40 * 1309380 * 2
def baseEnd_1309380 : Nat := 74704588820465808714253

theorem tailTrace_1309380 : CollatzResearch.WordTrace tailWord_1309380 prefixEnd_1309380 74704588820465808714253 := by
  unfold tailWord_1309380
  simp only [CollatzResearch.WordTrace]
  refine ⟨23878505998173679572734797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31838007997564906096979729 23878505998173679572734797)
  ·
    refine ⟨8954439749315129839775549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23878505998173679572734797 8954439749315129839775549)
    ·
      refine ⟨3357914905993173689915831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8954439749315129839775549 3357914905993173689915831)
      ·
        refine ⟨5036872358989760534873747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3357914905993173689915831 5036872358989760534873747)
        ·
          refine ⟨7555308538484640802310621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5036872358989760534873747 7555308538484640802310621)
          ·
            refine ⟨2833240701931740300866483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7555308538484640802310621 2833240701931740300866483)
            ·
              refine ⟨4249861052897610451299725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2833240701931740300866483 4249861052897610451299725)
              ·
                refine ⟨1593697894836603919237397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4249861052897610451299725 1593697894836603919237397)
                ·
                  refine ⟨74704588820465808714253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1593697894836603919237397 74704588820465808714253)
                  ·
                    rfl

theorem cell23_1309380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 3, 6].length) (baseStart_1309380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309380 prefixEnd_1309380 := by exact prefixLift 1309380
  have htrace : WordTrace (prefixWord ++ tailWord_1309380) baseStart_1309380 baseEnd_1309380 := by
    simpa [prefixWord, tailWord_1309380, baseEnd_1309380] using wordTrace_append hprefix tailTrace_1309380
  have hstable : (prefixWord ++ tailWord_1309380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309380).length < 2 ^ (prefixWord ++ tailWord_1309380).sum := by decide
  have hdescent : baseEnd_1309380 < baseStart_1309380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309393 : List Nat := [1, 2, 2, 1, 2, 3, 3, 1, 3, 5]
def baseStart_1309393 : Nat := 118140960795 + 1309393 * 2 ^ 59
def prefixEnd_1309393 : Nat := 4983230072969 + 3 ^ 40 * 1309393 * 2
def baseEnd_1309393 : Nat := 224115991544233575855239

theorem tailTrace_1309393 : CollatzResearch.WordTrace tailWord_1309393 prefixEnd_1309393 224115991544233575855239 := by
  unfold tailWord_1309393
  simp only [CollatzResearch.WordTrace]
  refine ⟨47757486145300262365692833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31838324096866841577128555 47757486145300262365692833)
  ·
    refine ⟨35818114608975196774269625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47757486145300262365692833 35818114608975196774269625)
    ·
      refine ⟨26863585956731397580702219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35818114608975196774269625 26863585956731397580702219)
      ·
        refine ⟨40295378935097096371053329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26863585956731397580702219 40295378935097096371053329)
        ·
          refine ⟨30221534201322822278289997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40295378935097096371053329 30221534201322822278289997)
          ·
            refine ⟨11333075325496058354358749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30221534201322822278289997 11333075325496058354358749)
            ·
              refine ⟨4249903247061021882884531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11333075325496058354358749 4249903247061021882884531)
              ·
                refine ⟨6374854870591532824326797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4249903247061021882884531 6374854870591532824326797)
                ·
                  refine ⟨2390570576471824809122549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6374854870591532824326797 2390570576471824809122549)
                  ·
                    refine ⟨224115991544233575855239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2390570576471824809122549 224115991544233575855239)
                    ·
                      rfl

theorem cell23_1309393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 3, 5].length) (baseStart_1309393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309393 prefixEnd_1309393 := by exact prefixLift 1309393
  have htrace : WordTrace (prefixWord ++ tailWord_1309393) baseStart_1309393 baseEnd_1309393 := by
    simpa [prefixWord, tailWord_1309393, baseEnd_1309393] using wordTrace_append hprefix tailTrace_1309393
  have hstable : (prefixWord ++ tailWord_1309393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309393).length < 2 ^ (prefixWord ++ tailWord_1309393).sum := by decide
  have hdescent : baseEnd_1309393 < baseStart_1309393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309430 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4]
def baseStart_1309430 : Nat := 118140960795 + 1309430 * 2 ^ 59
def prefixEnd_1309430 : Nat := 4983230072969 + 3 ^ 40 * 1309430 * 2
def baseEnd_1309430 : Nat := 672366973416917082803047

theorem tailTrace_1309430 : CollatzResearch.WordTrace tailWord_1309430 prefixEnd_1309430 672366973416917082803047 := by
  unfold tailWord_1309430
  simp only [CollatzResearch.WordTrace]
  refine ⟨2984927227885388605299359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31839223764110811789859829 2984927227885388605299359)
  ·
    refine ⟨4477390841828082907949039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2984927227885388605299359 4477390841828082907949039)
    ·
      refine ⟨6716086262742124361923559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4477390841828082907949039 6716086262742124361923559)
      ·
        refine ⟨10074129394113186542885339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6716086262742124361923559 10074129394113186542885339)
        ·
          refine ⟨15111194091169779814328009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10074129394113186542885339 15111194091169779814328009)
          ·
            refine ⟨11333395568377334860746007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15111194091169779814328009 11333395568377334860746007)
            ·
              refine ⟨17000093352566002291119011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11333395568377334860746007 17000093352566002291119011)
              ·
                refine ⟨25500140028849003436678517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17000093352566002291119011 25500140028849003436678517)
                ·
                  refine ⟨2390638127704594072188611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25500140028849003436678517 2390638127704594072188611)
                  ·
                    refine ⟨3585957191556891108282917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2390638127704594072188611 3585957191556891108282917)
                    ·
                      refine ⟨672366973416917082803047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3585957191556891108282917 672366973416917082803047)
                      ·
                        rfl

theorem cell23_1309430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_1309430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309430 prefixEnd_1309430 := by exact prefixLift 1309430
  have htrace : WordTrace (prefixWord ++ tailWord_1309430) baseStart_1309430 baseEnd_1309430 := by
    simpa [prefixWord, tailWord_1309430, baseEnd_1309430] using wordTrace_append hprefix tailTrace_1309430
  have hstable : (prefixWord ++ tailWord_1309430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309430).length < 2 ^ (prefixWord ++ tailWord_1309430).sum := by decide
  have hdescent : baseEnd_1309430 < baseStart_1309430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309433 : List Nat := [1, 2, 1, 3, 1, 1, 1, 6, 1, 1, 5]
def baseStart_1309433 : Nat := 118140960795 + 1309433 * 2 ^ 59
def prefixEnd_1309433 : Nat := 4983230072969 + 3 ^ 40 * 1309433 * 2
def baseEnd_1309433 : Nat := 672368513858880571065533

theorem tailTrace_1309433 : CollatzResearch.WordTrace tailWord_1309433 prefixEnd_1309433 672368513858880571065533 := by
  unfold tailWord_1309433
  simp only [CollatzResearch.WordTrace]
  refine ⟨47758945065155349197148953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31839296710103566131432635 47758945065155349197148953)
  ·
    refine ⟨35819208798866511897861715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47758945065155349197148953 35819208798866511897861715)
    ·
      refine ⟨53728813198299767846792573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35819208798866511897861715 53728813198299767846792573)
      ·
        refine ⟨20148304949362412942547215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53728813198299767846792573 20148304949362412942547215)
        ·
          refine ⟨30222457424043619413820823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20148304949362412942547215 30222457424043619413820823)
          ·
            refine ⟨45333686136065429120731235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30222457424043619413820823 45333686136065429120731235)
            ·
              refine ⟨68000529204098143681096853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45333686136065429120731235 68000529204098143681096853)
              ·
                refine ⟨3187524806442100485051415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68000529204098143681096853 3187524806442100485051415)
                ·
                  refine ⟨4781287209663150727577123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3187524806442100485051415 4781287209663150727577123)
                  ·
                    refine ⟨7171930814494726091365685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4781287209663150727577123 7171930814494726091365685)
                    ·
                      refine ⟨672368513858880571065533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7171930814494726091365685 672368513858880571065533)
                      ·
                        rfl

theorem cell23_1309433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_1309433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309433 prefixEnd_1309433 := by exact prefixLift 1309433
  have htrace : WordTrace (prefixWord ++ tailWord_1309433) baseStart_1309433 baseEnd_1309433 := by
    simpa [prefixWord, tailWord_1309433, baseEnd_1309433] using wordTrace_append hprefix tailTrace_1309433
  have hstable : (prefixWord ++ tailWord_1309433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309433).length < 2 ^ (prefixWord ++ tailWord_1309433).sum := by decide
  have hdescent : baseEnd_1309433 < baseStart_1309433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309450 : List Nat := [3, 1, 2, 2, 1, 2, 1, 3, 3, 2, 3]
def baseStart_1309450 : Nat := 118140960795 + 1309450 * 2 ^ 59
def prefixEnd_1309450 : Nat := 4983230072969 + 3 ^ 40 * 1309450 * 2
def baseEnd_1309450 : Nat := 672377243030007004552955

theorem tailTrace_1309450 : CollatzResearch.WordTrace tailWord_1309450 prefixEnd_1309450 672377243030007004552955 := by
  unfold tailWord_1309450
  simp only [CollatzResearch.WordTrace]
  refine ⟨11939891276523440275129451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31839710070729174067011869 11939891276523440275129451)
  ·
    refine ⟨17909836914785160412694177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11939891276523440275129451 17909836914785160412694177)
    ·
      refine ⟨13432377686088870309520633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17909836914785160412694177 13432377686088870309520633)
      ·
        refine ⟨10074283264566652732140475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13432377686088870309520633 10074283264566652732140475)
        ·
          refine ⟨15111424896849979098210713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10074283264566652732140475 15111424896849979098210713)
          ·
            refine ⟨11333568672637484323658035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15111424896849979098210713 11333568672637484323658035)
            ·
              refine ⟨17000353008956226485487053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11333568672637484323658035 17000353008956226485487053)
              ·
                refine ⟨6375132378358584932057645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17000353008956226485487053 6375132378358584932057645)
                ·
                  refine ⟨2390674641884469349521617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6375132378358584932057645 2390674641884469349521617)
                  ·
                    refine ⟨1793005981413352012141213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2390674641884469349521617 1793005981413352012141213)
                    ·
                      refine ⟨672377243030007004552955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1793005981413352012141213 672377243030007004552955)
                      ·
                        rfl

theorem cell23_1309450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_1309450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309450 prefixEnd_1309450 := by exact prefixLift 1309450
  have htrace : WordTrace (prefixWord ++ tailWord_1309450) baseStart_1309450 baseEnd_1309450 := by
    simpa [prefixWord, tailWord_1309450, baseEnd_1309450] using wordTrace_append hprefix tailTrace_1309450
  have hstable : (prefixWord ++ tailWord_1309450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309450).length < 2 ^ (prefixWord ++ tailWord_1309450).sum := by decide
  have hdescent : baseEnd_1309450 < baseStart_1309450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309458 : List Nat := [3, 2, 4, 1, 2, 1, 2, 3, 1, 1, 3]
def baseStart_1309458 : Nat := 118140960795 + 1309458 * 2 ^ 59
def prefixEnd_1309458 : Nat := 4983230072969 + 3 ^ 40 * 1309458 * 2
def baseEnd_1309458 : Nat := 672381350875242973252919

theorem tailTrace_1309458 : CollatzResearch.WordTrace tailWord_1309458 prefixEnd_1309458 672381350875242973252919 := by
  unfold tailWord_1309458
  simp only [CollatzResearch.WordTrace]
  refine ⟨11939964222516194616702257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31839904593376518977872685 11939964222516194616702257)
  ·
    refine ⟨8954973166887145962526693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11939964222516194616702257 8954973166887145962526693)
    ·
      refine ⟨1679057468791339867973755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8954973166887145962526693 1679057468791339867973755)
      ·
        refine ⟨2518586203187009801960633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1679057468791339867973755 2518586203187009801960633)
        ·
          refine ⟨1888939652390257351470475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2518586203187009801960633 1888939652390257351470475)
          ·
            refine ⟨2833409478585386027205713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1888939652390257351470475 2833409478585386027205713)
            ·
              refine ⟨2125057108939039520404285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2833409478585386027205713 2125057108939039520404285)
              ·
                refine ⟨796896415852139820151607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2125057108939039520404285 796896415852139820151607)
                ·
                  refine ⟨1195344623778209730227411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 796896415852139820151607 1195344623778209730227411)
                  ·
                    refine ⟨1793016935667314595341117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1195344623778209730227411 1793016935667314595341117)
                    ·
                      refine ⟨672381350875242973252919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1793016935667314595341117 672381350875242973252919)
                      ·
                        rfl

theorem cell23_1309458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_1309458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309458 prefixEnd_1309458 := by exact prefixLift 1309458
  have htrace : WordTrace (prefixWord ++ tailWord_1309458) baseStart_1309458 baseEnd_1309458 := by
    simpa [prefixWord, tailWord_1309458, baseEnd_1309458] using wordTrace_append hprefix tailTrace_1309458
  have hstable : (prefixWord ++ tailWord_1309458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309458).length < 2 ^ (prefixWord ++ tailWord_1309458).sum := by decide
  have hdescent : baseEnd_1309458 < baseStart_1309458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309474 : List Nat := [3, 3, 1, 1, 2, 4, 1, 2, 2, 4]
def baseStart_1309474 : Nat := 118140960795 + 1309474 * 2 ^ 59
def prefixEnd_1309474 : Nat := 4983230072969 + 3 ^ 40 * 1309474 * 2
def baseEnd_1309474 : Nat := 224129855521904970217615

theorem tailTrace_1309474 : CollatzResearch.WordTrace tailWord_1309474 prefixEnd_1309474 224129855521904970217615 := by
  unfold tailWord_1309474
  simp only [CollatzResearch.WordTrace]
  refine ⟨11940110114501703299847869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31840293638671208799594317 11940110114501703299847869)
  ·
    refine ⟨4477541292938138737442951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11940110114501703299847869 4477541292938138737442951)
    ·
      refine ⟨6716311939407208106164427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4477541292938138737442951 6716311939407208106164427)
      ·
        refine ⟨10074467909110812159246641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6716311939407208106164427 10074467909110812159246641)
        ·
          refine ⟨7555850931833109119434981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10074467909110812159246641 7555850931833109119434981)
          ·
            refine ⟨1416722049718707959894059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7555850931833109119434981 1416722049718707959894059)
            ·
              refine ⟨2125083074578061939841089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1416722049718707959894059 2125083074578061939841089)
              ·
                refine ⟨1593812305933546454880817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2125083074578061939841089 1593812305933546454880817)
                ·
                  refine ⟨1195359229450159841160613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1593812305933546454880817 1195359229450159841160613)
                  ·
                    refine ⟨224129855521904970217615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1195359229450159841160613 224129855521904970217615)
                    ·
                      rfl

theorem cell23_1309474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_1309474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309474 prefixEnd_1309474 := by exact prefixLift 1309474
  have htrace : WordTrace (prefixWord ++ tailWord_1309474) baseStart_1309474 baseEnd_1309474 := by
    simpa [prefixWord, tailWord_1309474, baseEnd_1309474] using wordTrace_append hprefix tailTrace_1309474
  have hstable : (prefixWord ++ tailWord_1309474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309474).length < 2 ^ (prefixWord ++ tailWord_1309474).sum := by decide
  have hdescent : baseEnd_1309474 < baseStart_1309474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309558 : List Nat := [5, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2]
def baseStart_1309558 : Nat := 118140960795 + 1309558 * 2 ^ 59
def prefixEnd_1309558 : Nat := 4983230072969 + 3 ^ 40 * 1309558 * 2
def baseEnd_1309558 : Nat := 672432698940692582002459

theorem tailTrace_1309558 : CollatzResearch.WordTrace tailWord_1309558 prefixEnd_1309558 672432698940692582002459 := by
  unfold tailWord_1309558
  simp only [CollatzResearch.WordTrace]
  refine ⟨2985219011856405971590583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31842336126468330363632885 2985219011856405971590583)
  ·
    refine ⟨4477828517784608957385875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2985219011856405971590583 4477828517784608957385875)
    ·
      refine ⟨6716742776676913436078813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4477828517784608957385875 6716742776676913436078813)
      ·
        refine ⟨2518778541253842538529555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6716742776676913436078813 2518778541253842538529555)
        ·
          refine ⟨3778167811880763807794333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2518778541253842538529555 3778167811880763807794333)
          ·
            refine ⟨1416812929455286427922875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3778167811880763807794333 1416812929455286427922875)
            ·
              refine ⟨2125219394182929641884313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1416812929455286427922875 2125219394182929641884313)
              ·
                refine ⟨1593914545637197231413235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2125219394182929641884313 1593914545637197231413235)
                ·
                  refine ⟨2390871818455795847119853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1593914545637197231413235 2390871818455795847119853)
                  ·
                    refine ⟨896576931920923442669945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2390871818455795847119853 896576931920923442669945)
                    ·
                      refine ⟨672432698940692582002459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 896576931920923442669945 672432698940692582002459)
                      ·
                        rfl

theorem cell23_1309558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_1309558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309558 prefixEnd_1309558 := by exact prefixLift 1309558
  have htrace : WordTrace (prefixWord ++ tailWord_1309558) baseStart_1309558 baseEnd_1309558 := by
    simpa [prefixWord, tailWord_1309558, baseEnd_1309558] using wordTrace_append hprefix tailTrace_1309558
  have hstable : (prefixWord ++ tailWord_1309558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309558).length < 2 ^ (prefixWord ++ tailWord_1309558).sum := by decide
  have hdescent : baseEnd_1309558 < baseStart_1309558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309583 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 7]
def baseStart_1309583 : Nat := 118140960795 + 1309583 * 2 ^ 59
def prefixEnd_1309583 : Nat := 4983230072969 + 3 ^ 40 * 1309583 * 2
def baseEnd_1309583 : Nat := 672445535957054984189843

theorem tailTrace_1309583 : CollatzResearch.WordTrace tailWord_1309583 prefixEnd_1309583 672445535957054984189843 := by
  unfold tailWord_1309583
  simp only [CollatzResearch.WordTrace]
  refine ⟨47764416014611924815109403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31842944009741283210072935 47764416014611924815109403)
  ·
    refine ⟨71646624021917887222664105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47764416014611924815109403 71646624021917887222664105)
    ·
      refine ⟨53734968016438415416998079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71646624021917887222664105 53734968016438415416998079)
      ·
        refine ⟨80602452024657623125497119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53734968016438415416998079 80602452024657623125497119)
        ·
          refine ⟨120903678036986434688245679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80602452024657623125497119 120903678036986434688245679)
          ·
            refine ⟨181355517055479652032368519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120903678036986434688245679 181355517055479652032368519)
            ·
              refine ⟨272033275583219478048552779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181355517055479652032368519 272033275583219478048552779)
              ·
                refine ⟨408049913374829217072829169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 272033275583219478048552779 408049913374829217072829169)
                ·
                  refine ⟨306037435031121912804621877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 408049913374829217072829169 306037435031121912804621877)
                  ·
                    refine ⟨28691009534167679325433301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 306037435031121912804621877 28691009534167679325433301)
                    ·
                      refine ⟨672445535957054984189843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 28691009534167679325433301 672445535957054984189843)
                      ·
                        rfl

theorem cell23_1309583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 7].length) (baseStart_1309583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309583 prefixEnd_1309583 := by exact prefixLift 1309583
  have htrace : WordTrace (prefixWord ++ tailWord_1309583) baseStart_1309583 baseEnd_1309583 := by
    simpa [prefixWord, tailWord_1309583, baseEnd_1309583] using wordTrace_append hprefix tailTrace_1309583
  have hstable : (prefixWord ++ tailWord_1309583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309583).length < 2 ^ (prefixWord ++ tailWord_1309583).sum := by decide
  have hdescent : baseEnd_1309583 < baseStart_1309583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309594 : List Nat := [3, 1, 1, 4, 3, 1, 1, 4, 5]
def baseStart_1309594 : Nat := 118140960795 + 1309594 * 2 ^ 59
def prefixEnd_1309594 : Nat := 4983230072969 + 3 ^ 40 * 1309594 * 2
def baseEnd_1309594 : Nat := 74716798249361604572477

theorem tailTrace_1309594 : CollatzResearch.WordTrace tailWord_1309594 prefixEnd_1309594 74716798249361604572477 := by
  unfold tailWord_1309594
  simp only [CollatzResearch.WordTrace]
  refine ⟨11941204304393018423439959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31843211478381382462506557 11941204304393018423439959)
  ·
    refine ⟨17911806456589527635159939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11941204304393018423439959 17911806456589527635159939)
    ·
      refine ⟨26867709684884291452739909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17911806456589527635159939 26867709684884291452739909)
      ·
        refine ⟨5037695565915804647388733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26867709684884291452739909 5037695565915804647388733)
        ·
          refine ⟨1889135837218426742770775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5037695565915804647388733 1889135837218426742770775)
          ·
            refine ⟨2833703755827640114156163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1889135837218426742770775 2833703755827640114156163)
            ·
              refine ⟨4250555633741460171234245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2833703755827640114156163 4250555633741460171234245)
              ·
                refine ⟨796979181326523782106421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4250555633741460171234245 796979181326523782106421)
                ·
                  refine ⟨74716798249361604572477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 796979181326523782106421 74716798249361604572477)
                  ·
                    rfl

theorem cell23_1309594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 4, 5].length) (baseStart_1309594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309594 prefixEnd_1309594 := by exact prefixLift 1309594
  have htrace : WordTrace (prefixWord ++ tailWord_1309594) baseStart_1309594 baseEnd_1309594 := by
    simpa [prefixWord, tailWord_1309594, baseEnd_1309594] using wordTrace_append hprefix tailTrace_1309594
  have hstable : (prefixWord ++ tailWord_1309594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309594).length < 2 ^ (prefixWord ++ tailWord_1309594).sum := by decide
  have hdescent : baseEnd_1309594 < baseStart_1309594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309597 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 1, 7, 2]
def baseStart_1309597 : Nat := 118140960795 + 1309597 * 2 ^ 59
def prefixEnd_1309597 : Nat := 4983230072969 + 3 ^ 40 * 1309597 * 2
def baseEnd_1309597 : Nat := 672452724686217929414779

theorem tailTrace_1309597 : CollatzResearch.WordTrace tailWord_1309597 prefixEnd_1309597 672452724686217929414779 := by
  unfold tailWord_1309597
  simp only [CollatzResearch.WordTrace]
  refine ⟨47764926636561205206119045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31843284424374136804079363 47764926636561205206119045)
  ·
    refine ⟨8955923744355225976147321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47764926636561205206119045 8955923744355225976147321)
    ·
      refine ⟨6716942808266419482110491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8955923744355225976147321 6716942808266419482110491)
      ·
        refine ⟨10075414212399629223165737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6716942808266419482110491 10075414212399629223165737)
        ·
          refine ⟨7556560659299721917374303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10075414212399629223165737 7556560659299721917374303)
          ·
            refine ⟨11334840988949582876061455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7556560659299721917374303 11334840988949582876061455)
            ·
              refine ⟨17002261483424374314092183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11334840988949582876061455 17002261483424374314092183)
              ·
                refine ⟨25503392225136561471138275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17002261483424374314092183 25503392225136561471138275)
                ·
                  refine ⟨38255088337704842206707413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25503392225136561471138275 38255088337704842206707413)
                  ·
                    refine ⟨896603632914957239219705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38255088337704842206707413 896603632914957239219705)
                    ·
                      refine ⟨672452724686217929414779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 896603632914957239219705 672452724686217929414779)
                      ·
                        rfl

theorem cell23_1309597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 7, 2].length) (baseStart_1309597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309597 prefixEnd_1309597 := by exact prefixLift 1309597
  have htrace : WordTrace (prefixWord ++ tailWord_1309597) baseStart_1309597 baseEnd_1309597 := by
    simpa [prefixWord, tailWord_1309597, baseEnd_1309597] using wordTrace_append hprefix tailTrace_1309597
  have hstable : (prefixWord ++ tailWord_1309597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309597).length < 2 ^ (prefixWord ++ tailWord_1309597).sum := by decide
  have hdescent : baseEnd_1309597 < baseStart_1309597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309600 : List Nat := [2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 5]
def baseStart_1309600 : Nat := 118140960795 + 1309600 * 2 ^ 59
def prefixEnd_1309600 : Nat := 4983230072969 + 3 ^ 40 * 1309600 * 2
def baseEnd_1309600 : Nat := 672454265128181417677265

theorem tailTrace_1309600 : CollatzResearch.WordTrace tailWord_1309600 prefixEnd_1309600 672454265128181417677265 := by
  unfold tailWord_1309600
  simp only [CollatzResearch.WordTrace]
  refine ⟨23882518027775168359239127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31843357370366891145652169 23882518027775168359239127)
  ·
    refine ⟨35823777041662752538858691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23882518027775168359239127 35823777041662752538858691)
    ·
      refine ⟨53735665562494128808288037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35823777041662752538858691 53735665562494128808288037)
      ·
        refine ⟨10075437292967649151554007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53735665562494128808288037 10075437292967649151554007)
        ·
          refine ⟨15113155939451473727331011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10075437292967649151554007 15113155939451473727331011)
          ·
            refine ⟨22669733909177210590996517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15113155939451473727331011 22669733909177210590996517)
            ·
              refine ⟨4250575107970726985811847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22669733909177210590996517 4250575107970726985811847)
              ·
                refine ⟨6375862661956090478717771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4250575107970726985811847 6375862661956090478717771)
                ·
                  refine ⟨9563793992934135718076657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6375862661956090478717771 9563793992934135718076657)
                  ·
                    refine ⟨7172845494700601788557493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9563793992934135718076657 7172845494700601788557493)
                    ·
                      refine ⟨672454265128181417677265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7172845494700601788557493 672454265128181417677265)
                      ·
                        rfl

theorem cell23_1309600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_1309600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309600 prefixEnd_1309600 := by exact prefixLift 1309600
  have htrace : WordTrace (prefixWord ++ tailWord_1309600) baseStart_1309600 baseEnd_1309600 := by
    simpa [prefixWord, tailWord_1309600, baseEnd_1309600] using wordTrace_append hprefix tailTrace_1309600
  have hstable : (prefixWord ++ tailWord_1309600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309600).length < 2 ^ (prefixWord ++ tailWord_1309600).sum := by decide
  have hdescent : baseEnd_1309600 < baseStart_1309600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309698 : List Nat := [3, 4, 1, 3, 1, 1, 1, 2, 2, 2, 3]
def baseStart_1309698 : Nat := 118140960795 + 1309698 * 2 ^ 59
def prefixEnd_1309698 : Nat := 4983230072969 + 3 ^ 40 * 1309698 * 2
def baseEnd_1309698 : Nat := 672504586232322034251815

theorem tailTrace_1309698 : CollatzResearch.WordTrace tailWord_1309698 prefixEnd_1309698 672504586232322034251815 := by
  unfold tailWord_1309698
  simp only [CollatzResearch.WordTrace]
  refine ⟨11942152602298824863886437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31845740272796866303697165 11942152602298824863886437)
  ·
    refine ⟨2239153612931029661978707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11942152602298824863886437 2239153612931029661978707)
    ·
      refine ⟨3358730419396544492968061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2239153612931029661978707 3358730419396544492968061)
      ·
        refine ⟨1259523907273704184863023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3358730419396544492968061 1259523907273704184863023)
        ·
          refine ⟨1889285860910556277294535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1259523907273704184863023 1889285860910556277294535)
          ·
            refine ⟨2833928791365834415941803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1889285860910556277294535 2833928791365834415941803)
            ·
              refine ⟨4250893187048751623912705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2833928791365834415941803 4250893187048751623912705)
              ·
                refine ⟨3188169890286563717934529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4250893187048751623912705 3188169890286563717934529)
                ·
                  refine ⟨2391127417714922788450897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3188169890286563717934529 2391127417714922788450897)
                  ·
                    refine ⟨1793345563286192091338173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2391127417714922788450897 1793345563286192091338173)
                    ·
                      refine ⟨672504586232322034251815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1793345563286192091338173 672504586232322034251815)
                      ·
                        rfl

theorem cell23_1309698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_1309698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309698 prefixEnd_1309698 := by exact prefixLift 1309698
  have htrace : WordTrace (prefixWord ++ tailWord_1309698) baseStart_1309698 baseEnd_1309698 := by
    simpa [prefixWord, tailWord_1309698, baseEnd_1309698] using wordTrace_append hprefix tailTrace_1309698
  have hstable : (prefixWord ++ tailWord_1309698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309698).length < 2 ^ (prefixWord ++ tailWord_1309698).sum := by decide
  have hdescent : baseEnd_1309698 < baseStart_1309698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309704 : List Nat := [2, 1, 3, 2, 1, 3, 1, 1, 4, 3, 2]
def baseStart_1309704 : Nat := 118140960795 + 1309704 * 2 ^ 59
def prefixEnd_1309704 : Nat := 4983230072969 + 3 ^ 40 * 1309704 * 2
def baseEnd_1309704 : Nat := 672507667116249010776787

theorem tailTrace_1309704 : CollatzResearch.WordTrace tailWord_1309704 prefixEnd_1309704 672507667116249010776787 := by
  unfold tailWord_1309704
  simp only [CollatzResearch.WordTrace]
  refine ⟨23884414623586781240132083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31845886164782374986842777 23884414623586781240132083)
  ·
    refine ⟨35826621935380171860198125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23884414623586781240132083 35826621935380171860198125)
    ·
      refine ⟨13434983225767564447574297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35826621935380171860198125 13434983225767564447574297)
      ·
        refine ⟨10076237419325673335680723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13434983225767564447574297 10076237419325673335680723)
        ·
          refine ⟨15114356128988510003521085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10076237419325673335680723 15114356128988510003521085)
          ·
            refine ⟨5667883548370691251320407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15114356128988510003521085 5667883548370691251320407)
            ·
              refine ⟨8501825322556036876980611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5667883548370691251320407 8501825322556036876980611)
              ·
                refine ⟨12752737983834055315470917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8501825322556036876980611 12752737983834055315470917)
                ·
                  refine ⟨2391138371968885371650797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12752737983834055315470917 2391138371968885371650797)
                  ·
                    refine ⟨896676889488332014369049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2391138371968885371650797 896676889488332014369049)
                    ·
                      refine ⟨672507667116249010776787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 896676889488332014369049 672507667116249010776787)
                      ·
                        rfl

theorem cell23_1309704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 4, 3, 2].length) (baseStart_1309704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309704 prefixEnd_1309704 := by exact prefixLift 1309704
  have htrace : WordTrace (prefixWord ++ tailWord_1309704) baseStart_1309704 baseEnd_1309704 := by
    simpa [prefixWord, tailWord_1309704, baseEnd_1309704] using wordTrace_append hprefix tailTrace_1309704
  have hstable : (prefixWord ++ tailWord_1309704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309704).length < 2 ^ (prefixWord ++ tailWord_1309704).sum := by decide
  have hdescent : baseEnd_1309704 < baseStart_1309704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309738 : List Nat := [3, 1, 4, 1, 3, 1, 2, 1, 2, 3, 2]
def baseStart_1309738 : Nat := 118140960795 + 1309738 * 2 ^ 59
def prefixEnd_1309738 : Nat := 4983230072969 + 3 ^ 40 * 1309738 * 2
def baseEnd_1309738 : Nat := 672525125458501877751631

theorem tailTrace_1309738 : CollatzResearch.WordTrace tailWord_1309738 prefixEnd_1309738 672525125458501877751631 := by
  unfold tailWord_1309738
  simp only [CollatzResearch.WordTrace]
  refine ⟨11942517332262596571750467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31846712886033590858001245 11942517332262596571750467)
  ·
    refine ⟨17913775998393894857625701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11942517332262596571750467 17913775998393894857625701)
    ·
      refine ⟨3358832999698855285804819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17913775998393894857625701 3358832999698855285804819)
      ·
        refine ⟨5038249499548282928707229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3358832999698855285804819 5038249499548282928707229)
        ·
          refine ⟨1889343562330606098265211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5038249499548282928707229 1889343562330606098265211)
          ·
            refine ⟨2834015343495909147397817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1889343562330606098265211 2834015343495909147397817)
            ·
              refine ⟨2125511507621931860548363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2834015343495909147397817 2125511507621931860548363)
              ·
                refine ⟨3188267261432897790822545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2125511507621931860548363 3188267261432897790822545)
                ·
                  refine ⟨2391200446074673343116909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3188267261432897790822545 2391200446074673343116909)
                  ·
                    refine ⟨896700167278002503668841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2391200446074673343116909 896700167278002503668841)
                    ·
                      refine ⟨672525125458501877751631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 896700167278002503668841 672525125458501877751631)
                      ·
                        rfl

theorem cell23_1309738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_1309738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309738 prefixEnd_1309738 := by exact prefixLift 1309738
  have htrace : WordTrace (prefixWord ++ tailWord_1309738) baseStart_1309738 baseEnd_1309738 := by
    simpa [prefixWord, tailWord_1309738, baseEnd_1309738] using wordTrace_append hprefix tailTrace_1309738
  have hstable : (prefixWord ++ tailWord_1309738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309738).length < 2 ^ (prefixWord ++ tailWord_1309738).sum := by decide
  have hdescent : baseEnd_1309738 < baseStart_1309738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309740 : List Nat := [2, 2, 1, 1, 1, 2, 3, 11]
def baseStart_1309740 : Nat := 118140960795 + 1309740 * 2 ^ 59
def prefixEnd_1309740 : Nat := 4983230072969 + 3 ^ 40 * 1309740 * 2
def baseEnd_1309740 : Nat := 24908376015548550738023

theorem tailTrace_1309740 : CollatzResearch.WordTrace tailWord_1309740 prefixEnd_1309740 24908376015548550738023 := by
  unfold tailWord_1309740
  simp only [CollatzResearch.WordTrace]
  refine ⟨23885071137521570314287337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31846761516695427085716449 23885071137521570314287337)
  ·
    refine ⟨17913803353141177735715503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23885071137521570314287337 17913803353141177735715503)
    ·
      refine ⟨26870705029711766603573255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17913803353141177735715503 26870705029711766603573255)
      ·
        refine ⟨40306057544567649905359883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26870705029711766603573255 40306057544567649905359883)
        ·
          refine ⟨60459086316851474858039825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40306057544567649905359883 60459086316851474858039825)
          ·
            refine ⟨45344314737638606143529869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60459086316851474858039825 45344314737638606143529869)
            ·
              refine ⟨17004118026614477303823701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45344314737638606143529869 17004118026614477303823701)
              ·
                refine ⟨24908376015548550738023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 17004118026614477303823701 24908376015548550738023)
                ·
                  rfl

theorem cell23_1309740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 11].length) (baseStart_1309740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309740 prefixEnd_1309740 := by exact prefixLift 1309740
  have htrace : WordTrace (prefixWord ++ tailWord_1309740) baseStart_1309740 baseEnd_1309740 := by
    simpa [prefixWord, tailWord_1309740, baseEnd_1309740] using wordTrace_append hprefix tailTrace_1309740
  have hstable : (prefixWord ++ tailWord_1309740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309740).length < 2 ^ (prefixWord ++ tailWord_1309740).sum := by decide
  have hdescent : baseEnd_1309740 < baseStart_1309740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309748 : List Nat := [2, 5, 1, 2, 1, 2, 3, 1, 1, 5]
def baseStart_1309748 : Nat := 118140960795 + 1309748 * 2 ^ 59
def prefixEnd_1309748 : Nat := 4983230072969 + 3 ^ 40 * 1309748 * 2
def baseEnd_1309748 : Nat := 224176753421682279542195

theorem tailTrace_1309748 : CollatzResearch.WordTrace tailWord_1309748 prefixEnd_1309748 224176753421682279542195 := by
  unfold tailWord_1309748
  simp only [CollatzResearch.WordTrace]
  refine ⟨23885217029507078997432949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31846956039342771996577265 23885217029507078997432949)
  ·
    refine ⟨2239239096516288656009339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23885217029507078997432949 2239239096516288656009339)
    ·
      refine ⟨3358858644774432984014009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2239239096516288656009339 3358858644774432984014009)
      ·
        refine ⟨2519143983580824738010507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3358858644774432984014009 2519143983580824738010507)
        ·
          refine ⟨3778715975371237107015761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2519143983580824738010507 3778715975371237107015761)
          ·
            refine ⟨2834036981528427830261821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3778715975371237107015761 2834036981528427830261821)
            ·
              refine ⟨1062763868073160436348183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2834036981528427830261821 1062763868073160436348183)
              ·
                refine ⟨1594145802109740654522275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1062763868073160436348183 1594145802109740654522275)
                ·
                  refine ⟨2391218703164610981783413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1594145802109740654522275 2391218703164610981783413)
                  ·
                    refine ⟨224176753421682279542195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2391218703164610981783413 224176753421682279542195)
                    ·
                      rfl

theorem cell23_1309748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_1309748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309748 prefixEnd_1309748 := by exact prefixLift 1309748
  have htrace : WordTrace (prefixWord ++ tailWord_1309748) baseStart_1309748 baseEnd_1309748 := by
    simpa [prefixWord, tailWord_1309748, baseEnd_1309748] using wordTrace_append hprefix tailTrace_1309748
  have hstable : (prefixWord ++ tailWord_1309748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309748).length < 2 ^ (prefixWord ++ tailWord_1309748).sum := by decide
  have hdescent : baseEnd_1309748 < baseStart_1309748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309754 : List Nat := [3, 1, 1, 1, 3, 1, 2, 5, 1, 2, 3]
def baseStart_1309754 : Nat := 118140960795 + 1309754 * 2 ^ 59
def prefixEnd_1309754 : Nat := 4983230072969 + 3 ^ 40 * 1309754 * 2
def baseEnd_1309754 : Nat := 672533341148973815151557

theorem tailTrace_1309754 : CollatzResearch.WordTrace tailWord_1309754 prefixEnd_1309754 672533341148973815151557 := by
  unfold tailWord_1309754
  simp only [CollatzResearch.WordTrace]
  refine ⟨11942663224248105254896079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31847101931328280679722877 11942663224248105254896079)
  ·
    refine ⟨17913994836372157882344119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11942663224248105254896079 17913994836372157882344119)
    ·
      refine ⟨26870992254558236823516179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17913994836372157882344119 26870992254558236823516179)
      ·
        refine ⟨40306488381837355235274269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26870992254558236823516179 40306488381837355235274269)
        ·
          refine ⟨15114933143189008213227851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40306488381837355235274269 15114933143189008213227851)
          ·
            refine ⟨22672399714783512319841777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15114933143189008213227851 22672399714783512319841777)
            ·
              refine ⟨17004299786087634239881333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22672399714783512319841777 17004299786087634239881333)
              ·
                refine ⟨1594153104945715709988875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17004299786087634239881333 1594153104945715709988875)
                ·
                  refine ⟨2391229657418573564983313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1594153104945715709988875 2391229657418573564983313)
                  ·
                    refine ⟨1793422243063930173737485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2391229657418573564983313 1793422243063930173737485)
                    ·
                      refine ⟨672533341148973815151557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1793422243063930173737485 672533341148973815151557)
                      ·
                        rfl

theorem cell23_1309754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 5, 1, 2, 3].length) (baseStart_1309754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309754 prefixEnd_1309754 := by exact prefixLift 1309754
  have htrace : WordTrace (prefixWord ++ tailWord_1309754) baseStart_1309754 baseEnd_1309754 := by
    simpa [prefixWord, tailWord_1309754, baseEnd_1309754] using wordTrace_append hprefix tailTrace_1309754
  have hstable : (prefixWord ++ tailWord_1309754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309754).length < 2 ^ (prefixWord ++ tailWord_1309754).sum := by decide
  have hdescent : baseEnd_1309754 < baseStart_1309754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309768 : List Nat := [2, 1, 3, 1, 1, 1, 5, 4, 1, 2, 2]
def baseStart_1309768 : Nat := 118140960795 + 1309768 * 2 ^ 59
def prefixEnd_1309768 : Nat := 4983230072969 + 3 ^ 40 * 1309768 * 2
def baseEnd_1309768 : Nat := 672540529878136760376493

theorem tailTrace_1309768 : CollatzResearch.WordTrace tailWord_1309768 prefixEnd_1309768 672540529878136760376493 := by
  unfold tailWord_1309768
  simp only [CollatzResearch.WordTrace]
  refine ⟨23885581759470850705296979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31847442345961134273729305 23885581759470850705296979)
  ·
    refine ⟨35828372639206276057945469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23885581759470850705296979 35828372639206276057945469)
    ·
      refine ⟨13435639739702353521729551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35828372639206276057945469 13435639739702353521729551)
      ·
        refine ⟨20153459609553530282594327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13435639739702353521729551 20153459609553530282594327)
        ·
          refine ⟨30230189414330295423891491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20153459609553530282594327 30230189414330295423891491)
          ·
            refine ⟨45345284121495443135837237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30230189414330295423891491 45345284121495443135837237)
            ·
              refine ⟨4251120386390197793984741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45345284121495443135837237 4251120386390197793984741)
              ·
                refine ⟨797085072448162086372139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4251120386390197793984741 797085072448162086372139)
                ·
                  refine ⟨1195627608672243129558209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 797085072448162086372139 1195627608672243129558209)
                  ·
                    refine ⟨896720706504182347168657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1195627608672243129558209 896720706504182347168657)
                    ·
                      refine ⟨672540529878136760376493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 896720706504182347168657 672540529878136760376493)
                      ·
                        rfl

theorem cell23_1309768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 4, 1, 2, 2].length) (baseStart_1309768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309768 prefixEnd_1309768 := by exact prefixLift 1309768
  have htrace : WordTrace (prefixWord ++ tailWord_1309768) baseStart_1309768 baseEnd_1309768 := by
    simpa [prefixWord, tailWord_1309768, baseEnd_1309768] using wordTrace_append hprefix tailTrace_1309768
  have hstable : (prefixWord ++ tailWord_1309768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309768).length < 2 ^ (prefixWord ++ tailWord_1309768).sum := by decide
  have hdescent : baseEnd_1309768 < baseStart_1309768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309784 : List Nat := [2, 1, 2, 2, 1, 3, 4, 1, 1, 3, 3]
def baseStart_1309784 : Nat := 118140960795 + 1309784 * 2 ^ 59
def prefixEnd_1309784 : Nat := 4983230072969 + 3 ^ 40 * 1309784 * 2
def baseEnd_1309784 : Nat := 672548745568608697776419

theorem tailTrace_1309784 : CollatzResearch.WordTrace tailWord_1309784 prefixEnd_1309784 672548745568608697776419 := by
  unfold tailWord_1309784
  simp only [CollatzResearch.WordTrace]
  refine ⟨23885873543441868071588203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31847831391255824095450937 23885873543441868071588203)
  ·
    refine ⟨35828810315162802107382305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23885873543441868071588203 35828810315162802107382305)
    ·
      refine ⟨26871607736372101580536729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35828810315162802107382305 26871607736372101580536729)
      ·
        refine ⟨20153705802279076185402547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26871607736372101580536729 20153705802279076185402547)
        ·
          refine ⟨30230558703418614278103821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20153705802279076185402547 30230558703418614278103821)
          ·
            refine ⟨11336459513781980354288933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30230558703418614278103821 11336459513781980354288933)
            ·
              refine ⟨2125586158834121316429175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11336459513781980354288933 2125586158834121316429175)
              ·
                refine ⟨3188379238251181974643763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2125586158834121316429175 3188379238251181974643763)
                ·
                  refine ⟨4782568857376772961965645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3188379238251181974643763 4782568857376772961965645)
                  ·
                    refine ⟨1793463321516289860737117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4782568857376772961965645 1793463321516289860737117)
                    ·
                      refine ⟨672548745568608697776419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1793463321516289860737117 672548745568608697776419)
                      ·
                        rfl

theorem cell23_1309784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 1, 3, 3].length) (baseStart_1309784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309784 prefixEnd_1309784 := by exact prefixLift 1309784
  have htrace : WordTrace (prefixWord ++ tailWord_1309784) baseStart_1309784 baseEnd_1309784 := by
    simpa [prefixWord, tailWord_1309784, baseEnd_1309784] using wordTrace_append hprefix tailTrace_1309784
  have hstable : (prefixWord ++ tailWord_1309784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309784).length < 2 ^ (prefixWord ++ tailWord_1309784).sum := by decide
  have hdescent : baseEnd_1309784 < baseStart_1309784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309797 : List Nat := [1, 3, 1, 3, 2, 1, 2, 1, 2, 2, 5]
def baseStart_1309797 : Nat := 118140960795 + 1309797 * 2 ^ 59
def prefixEnd_1309797 : Nat := 4983230072969 + 3 ^ 40 * 1309797 * 2
def baseEnd_1309797 : Nat := 672555420817117146913859

theorem tailTrace_1309797 : CollatzResearch.WordTrace tailWord_1309797 prefixEnd_1309797 672555420817117146913859 := by
  unfold tailWord_1309797
  simp only [CollatzResearch.WordTrace]
  refine ⟨47772221235836639363399645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31848147490557759575599763 47772221235836639363399645)
  ·
    refine ⟨17914582963438739761274867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47772221235836639363399645 17914582963438739761274867)
    ·
      refine ⟨26871874445158109641912301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17914582963438739761274867 26871874445158109641912301)
      ·
        refine ⟨10076952916934291115717113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26871874445158109641912301 10076952916934291115717113)
        ·
          refine ⟨7557714687700718336787835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10076952916934291115717113 7557714687700718336787835)
          ·
            refine ⟨11336572031551077505181753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7557714687700718336787835 11336572031551077505181753)
            ·
              refine ⟨8502429023663308128886315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11336572031551077505181753 8502429023663308128886315)
              ·
                refine ⟨12753643535494962193329473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8502429023663308128886315 12753643535494962193329473)
                ·
                  refine ⟨9565232651621221644997105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12753643535494962193329473 9565232651621221644997105)
                  ·
                    refine ⟨7173924488715916233747829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9565232651621221644997105 7173924488715916233747829)
                    ·
                      refine ⟨672555420817117146913859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7173924488715916233747829 672555420817117146913859)
                      ·
                        rfl

theorem cell23_1309797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_1309797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309797 prefixEnd_1309797 := by exact prefixLift 1309797
  have htrace : WordTrace (prefixWord ++ tailWord_1309797) baseStart_1309797 baseEnd_1309797 := by
    simpa [prefixWord, tailWord_1309797, baseEnd_1309797] using wordTrace_append hprefix tailTrace_1309797
  have hstable : (prefixWord ++ tailWord_1309797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309797).length < 2 ^ (prefixWord ++ tailWord_1309797).sum := by decide
  have hdescent : baseEnd_1309797 < baseStart_1309797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309824 : List Nat := [2, 1, 1, 2, 1, 3, 2, 2, 3, 4, 2]
def baseStart_1309824 : Nat := 118140960795 + 1309824 * 2 ^ 59
def prefixEnd_1309824 : Nat := 4983230072969 + 3 ^ 40 * 1309824 * 2
def baseEnd_1309824 : Nat := 672569284794788541276235

theorem tailTrace_1309824 : CollatzResearch.WordTrace tailWord_1309824 prefixEnd_1309824 672569284794788541276235 := by
  unfold tailWord_1309824
  simp only [CollatzResearch.WordTrace]
  refine ⟨23886603003369411487316263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31848804004492548649755017 23886603003369411487316263)
  ·
    refine ⟨35829904505054117230974395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23886603003369411487316263 35829904505054117230974395)
    ·
      refine ⟨53744856757581175846461593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35829904505054117230974395 53744856757581175846461593)
      ·
        refine ⟨40308642568185881884846195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53744856757581175846461593 40308642568185881884846195)
        ·
          refine ⟨60462963852278822827269293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40308642568185881884846195 60462963852278822827269293)
          ·
            refine ⟨22673611444604558560225985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60462963852278822827269293 22673611444604558560225985)
            ·
              refine ⟨17005208583453418920169489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22673611444604558560225985 17005208583453418920169489)
              ·
                refine ⟨12753906437590064190127117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17005208583453418920169489 12753906437590064190127117)
                ·
                  refine ⟨4782714914096274071297669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12753906437590064190127117 4782714914096274071297669)
                  ·
                    refine ⟨896759046393051388368313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4782714914096274071297669 896759046393051388368313)
                    ·
                      refine ⟨672569284794788541276235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 896759046393051388368313 672569284794788541276235)
                      ·
                        rfl

theorem cell23_1309824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 3, 4, 2].length) (baseStart_1309824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309824 prefixEnd_1309824 := by exact prefixLift 1309824
  have htrace : WordTrace (prefixWord ++ tailWord_1309824) baseStart_1309824 baseEnd_1309824 := by
    simpa [prefixWord, tailWord_1309824, baseEnd_1309824] using wordTrace_append hprefix tailTrace_1309824
  have hstable : (prefixWord ++ tailWord_1309824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309824).length < 2 ^ (prefixWord ++ tailWord_1309824).sum := by decide
  have hdescent : baseEnd_1309824 < baseStart_1309824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309887 : List Nat := [1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 7]
def baseStart_1309887 : Nat := 118140960795 + 1309887 * 2 ^ 59
def prefixEnd_1309887 : Nat := 4983230072969 + 3 ^ 40 * 1309887 * 2
def baseEnd_1309887 : Nat := 672601634076021794788445

theorem tailTrace_1309887 : CollatzResearch.WordTrace tailWord_1309887 prefixEnd_1309887 672601634076021794788445 := by
  unfold tailWord_1309887
  simp only [CollatzResearch.WordTrace]
  refine ⟨47775503805510584734175915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31850335870340389822783943 47775503805510584734175915)
  ·
    refine ⟨71663255708265877101263873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47775503805510584734175915 71663255708265877101263873)
    ·
      refine ⟨53747441781199407825947905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71663255708265877101263873 53747441781199407825947905)
      ·
        refine ⟨40310581335899555869460929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53747441781199407825947905 40310581335899555869460929)
        ·
          refine ⟨30232936001924666902095697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40310581335899555869460929 30232936001924666902095697)
          ·
            refine ⟨22674702001443500176571773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30232936001924666902095697 22674702001443500176571773)
            ·
              refine ⟨8503013250541312566214415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22674702001443500176571773 8503013250541312566214415)
              ·
                refine ⟨12754519875811968849321623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8503013250541312566214415 12754519875811968849321623)
                ·
                  refine ⟨19131779813717953273982435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12754519875811968849321623 19131779813717953273982435)
                  ·
                    refine ⟨28697669720576929910973653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19131779813717953273982435 28697669720576929910973653)
                    ·
                      refine ⟨672601634076021794788445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 28697669720576929910973653 672601634076021794788445)
                      ·
                        rfl

theorem cell23_1309887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_1309887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309887 prefixEnd_1309887 := by exact prefixLift 1309887
  have htrace : WordTrace (prefixWord ++ tailWord_1309887) baseStart_1309887 baseEnd_1309887 := by
    simpa [prefixWord, tailWord_1309887, baseEnd_1309887] using wordTrace_append hprefix tailTrace_1309887
  have hstable : (prefixWord ++ tailWord_1309887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309887).length < 2 ^ (prefixWord ++ tailWord_1309887).sum := by decide
  have hdescent : baseEnd_1309887 < baseStart_1309887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309948 : List Nat := [2, 2, 2, 1, 5, 1, 1, 1, 2, 4, 2]
def baseStart_1309948 : Nat := 118140960795 + 1309948 * 2 ^ 59
def prefixEnd_1309948 : Nat := 4983230072969 + 3 ^ 40 * 1309948 * 2
def baseEnd_1309948 : Nat := 672632956395946056125665

theorem tailTrace_1309948 : CollatzResearch.WordTrace tailWord_1309948 prefixEnd_1309948 672632956395946056125665 := by
  unfold tailWord_1309948
  simp only [CollatzResearch.WordTrace]
  refine ⟨23888864329144796076073249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31851819105526394768097665 23888864329144796076073249)
  ·
    refine ⟨17916648246858597057054937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23888864329144796076073249 17916648246858597057054937)
    ·
      refine ⟨13437486185143947792791203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17916648246858597057054937 13437486185143947792791203)
      ·
        refine ⟨20156229277715921689186805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13437486185143947792791203 20156229277715921689186805)
        ·
          refine ⟨1889646494785867658361263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20156229277715921689186805 1889646494785867658361263)
          ·
            refine ⟨2834469742178801487541895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1889646494785867658361263 2834469742178801487541895)
            ·
              refine ⟨4251704613268202231312843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2834469742178801487541895 4251704613268202231312843)
              ·
                refine ⟨6377556919902303346969265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4251704613268202231312843 6377556919902303346969265)
                ·
                  refine ⟨4783167689926727510226949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6377556919902303346969265 4783167689926727510226949)
                  ·
                    refine ⟨896843941861261408167553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4783167689926727510226949 896843941861261408167553)
                    ·
                      refine ⟨672632956395946056125665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 896843941861261408167553 672632956395946056125665)
                      ·
                        rfl

theorem cell23_1309948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 2, 4, 2].length) (baseStart_1309948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1309948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1309948 prefixEnd_1309948 := by exact prefixLift 1309948
  have htrace : WordTrace (prefixWord ++ tailWord_1309948) baseStart_1309948 baseEnd_1309948 := by
    simpa [prefixWord, tailWord_1309948, baseEnd_1309948] using wordTrace_append hprefix tailTrace_1309948
  have hstable : (prefixWord ++ tailWord_1309948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309948).length < 2 ^ (prefixWord ++ tailWord_1309948).sum := by decide
  have hdescent : baseEnd_1309948 < baseStart_1309948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310024 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 5, 1, 5]
def baseStart_1310024 : Nat := 118140960795 + 1310024 * 2 ^ 59
def prefixEnd_1310024 : Nat := 4983230072969 + 3 ^ 40 * 1310024 * 2
def baseEnd_1310024 : Nat := 672671980925687758775315

theorem tailTrace_1310024 : CollatzResearch.WordTrace tailWord_1310024 prefixEnd_1310024 672671980925687758775315 := by
  unfold tailWord_1310024
  simp only [CollatzResearch.WordTrace]
  refine ⟨23890250303007128565956563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31853667070676171421275417 23890250303007128565956563)
  ·
    refine ⟨35835375454510692848934845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23890250303007128565956563 35835375454510692848934845)
    ·
      refine ⟨13438265795441509818350567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35835375454510692848934845 13438265795441509818350567)
      ·
        refine ⟨20157398693162264727525851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13438265795441509818350567 20157398693162264727525851)
        ·
          refine ⟨30236098039743397091288777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20157398693162264727525851 30236098039743397091288777)
          ·
            refine ⟨22677073529807547818466583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30236098039743397091288777 22677073529807547818466583)
            ·
              refine ⟨34015610294711321727699875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22677073529807547818466583 34015610294711321727699875)
              ·
                refine ⟨51023415442066982591549813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34015610294711321727699875 51023415442066982591549813)
                ·
                  refine ⟨4783445197693779617957795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51023415442066982591549813 4783445197693779617957795)
                  ·
                    refine ⟨7175167796540669426936693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4783445197693779617957795 7175167796540669426936693)
                    ·
                      refine ⟨672671980925687758775315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7175167796540669426936693 672671980925687758775315)
                      ·
                        rfl

theorem cell23_1310024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_1310024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310024 prefixEnd_1310024 := by exact prefixLift 1310024
  have htrace : WordTrace (prefixWord ++ tailWord_1310024) baseStart_1310024 baseEnd_1310024 := by
    simpa [prefixWord, tailWord_1310024, baseEnd_1310024] using wordTrace_append hprefix tailTrace_1310024
  have hstable : (prefixWord ++ tailWord_1310024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310024).length < 2 ^ (prefixWord ++ tailWord_1310024).sum := by decide
  have hdescent : baseEnd_1310024 < baseStart_1310024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310061 : List Nat := [1, 5, 1, 1, 1, 4, 2, 8]
def baseStart_1310061 : Nat := 118140960795 + 1310061 * 2 ^ 59
def prefixEnd_1310061 : Nat := 4983230072969 + 3 ^ 40 * 1310061 * 2
def baseEnd_1310061 : Nat := 24914480729996448667135

theorem tailTrace_1310061 : CollatzResearch.WordTrace tailWord_1310061 prefixEnd_1310061 24914480729996448667135 := by
  unfold tailWord_1310061
  simp only [CollatzResearch.WordTrace]
  refine ⟨47781850106880212451010037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31854566737920141634006691 47781850106880212451010037)
  ·
    refine ⟨4479548447520019917282191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47781850106880212451010037 4479548447520019917282191)
    ·
      refine ⟨6719322671280029875923287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4479548447520019917282191 6719322671280029875923287)
      ·
        refine ⟨10078984006920044813884931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6719322671280029875923287 10078984006920044813884931)
        ·
          refine ⟨15118476010380067220827397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10078984006920044813884931 15118476010380067220827397)
          ·
            refine ⟨2834714251946262603905137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15118476010380067220827397 2834714251946262603905137)
            ·
              refine ⟨2126035688959696952928853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2834714251946262603905137 2126035688959696952928853)
              ·
                refine ⟨24914480729996448667135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2126035688959696952928853 24914480729996448667135)
                ·
                  rfl

theorem cell23_1310061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 8].length) (baseStart_1310061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310061 prefixEnd_1310061 := by exact prefixLift 1310061
  have htrace : WordTrace (prefixWord ++ tailWord_1310061) baseStart_1310061 baseEnd_1310061 := by
    simpa [prefixWord, tailWord_1310061, baseEnd_1310061] using wordTrace_append hprefix tailTrace_1310061
  have hstable : (prefixWord ++ tailWord_1310061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310061).length < 2 ^ (prefixWord ++ tailWord_1310061).sum := by decide
  have hdescent : baseEnd_1310061 < baseStart_1310061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310064 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 6]
def baseStart_1310064 : Nat := 118140960795 + 1310064 * 2 ^ 59
def prefixEnd_1310064 : Nat := 4983230072969 + 3 ^ 40 * 1310064 * 2
def baseEnd_1310064 : Nat := 672692520151867602275131

theorem tailTrace_1310064 : CollatzResearch.WordTrace tailWord_1310064 prefixEnd_1310064 672692520151867602275131 := by
  unfold tailWord_1310064
  simp only [CollatzResearch.WordTrace]
  refine ⟨23890979762934671981684623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31854639683912895975579497 23890979762934671981684623)
  ·
    refine ⟨35836469644402007972526935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23890979762934671981684623 35836469644402007972526935)
    ·
      refine ⟨53754704466603011958790403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35836469644402007972526935 53754704466603011958790403)
      ·
        refine ⟨80632056699904517938185605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53754704466603011958790403 80632056699904517938185605)
        ·
          refine ⟨15118510631232097113409801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80632056699904517938185605 15118510631232097113409801)
          ·
            refine ⟨11338882973424072835057351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15118510631232097113409801 11338882973424072835057351)
            ·
              refine ⟨17008324460136109252586027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11338882973424072835057351 17008324460136109252586027)
              ·
                refine ⟨25512486690204163878879041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17008324460136109252586027 25512486690204163878879041)
                ·
                  refine ⟨19134365017653122909159281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25512486690204163878879041 19134365017653122909159281)
                  ·
                    refine ⟨14350773763239842181869461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19134365017653122909159281 14350773763239842181869461)
                    ·
                      refine ⟨672692520151867602275131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14350773763239842181869461 672692520151867602275131)
                      ·
                        rfl

theorem cell23_1310064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 6].length) (baseStart_1310064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310064 prefixEnd_1310064 := by exact prefixLift 1310064
  have htrace : WordTrace (prefixWord ++ tailWord_1310064) baseStart_1310064 baseEnd_1310064 := by
    simpa [prefixWord, tailWord_1310064, baseEnd_1310064] using wordTrace_append hprefix tailTrace_1310064
  have hstable : (prefixWord ++ tailWord_1310064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310064).length < 2 ^ (prefixWord ++ tailWord_1310064).sum := by decide
  have hdescent : baseEnd_1310064 < baseStart_1310064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310071 : List Nat := [1, 1, 3, 1, 1, 2, 4, 3, 1, 3, 3]
def baseStart_1310071 : Nat := 118140960795 + 1310071 * 2 ^ 59
def prefixEnd_1310071 : Nat := 4983230072969 + 3 ^ 40 * 1310071 * 2
def baseEnd_1310071 : Nat := 672696114516449074887599

theorem tailTrace_1310071 : CollatzResearch.WordTrace tailWord_1310071 prefixEnd_1310071 672696114516449074887599 := by
  unfold tailWord_1310071
  simp only [CollatzResearch.WordTrace]
  refine ⟨47782214836843984158874067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31854809891229322772582711 47782214836843984158874067)
  ·
    refine ⟨71673322255265976238311101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47782214836843984158874067 71673322255265976238311101)
    ·
      refine ⟨26877495845724741089366663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71673322255265976238311101 26877495845724741089366663)
      ·
        refine ⟨40316243768587111634049995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26877495845724741089366663 40316243768587111634049995)
        ·
          refine ⟨60474365652880667451074993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40316243768587111634049995 60474365652880667451074993)
          ·
            refine ⟨45355774239660500588306245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60474365652880667451074993 45355774239660500588306245)
            ·
              refine ⟨8504207669936343860307421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45355774239660500588306245 8504207669936343860307421)
              ·
                refine ⟨3189077876226128947615283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8504207669936343860307421 3189077876226128947615283)
                ·
                  refine ⟨4783616814339193421422925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3189077876226128947615283 4783616814339193421422925)
                  ·
                    refine ⟨1793856305377197533033597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4783616814339193421422925 1793856305377197533033597)
                    ·
                      refine ⟨672696114516449074887599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1793856305377197533033597 672696114516449074887599)
                      ·
                        rfl

theorem cell23_1310071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 3, 3].length) (baseStart_1310071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310071 prefixEnd_1310071 := by exact prefixLift 1310071
  have htrace : WordTrace (prefixWord ++ tailWord_1310071) baseStart_1310071 baseEnd_1310071 := by
    simpa [prefixWord, tailWord_1310071, baseEnd_1310071] using wordTrace_append hprefix tailTrace_1310071
  have hstable : (prefixWord ++ tailWord_1310071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310071).length < 2 ^ (prefixWord ++ tailWord_1310071).sum := by decide
  have hdescent : baseEnd_1310071 < baseStart_1310071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310074 : List Nat := [3, 1, 1, 1, 1, 1, 2, 4, 2, 7]
def baseStart_1310074 : Nat := 118140960795 + 1310074 * 2 ^ 59
def prefixEnd_1310074 : Nat := 4983230072969 + 3 ^ 40 * 1310074 * 2
def baseEnd_1310074 : Nat := 224232551652804187716695

theorem tailTrace_1310074 : CollatzResearch.WordTrace tailWord_1310074 prefixEnd_1310074 224232551652804187716695 := by
  unfold tailWord_1310074
  simp only [CollatzResearch.WordTrace]
  refine ⟨11945581063958278917808319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31854882837222077114155517 11945581063958278917808319)
  ·
    refine ⟨17918371595937418376712479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11945581063958278917808319 17918371595937418376712479)
    ·
      refine ⟨26877557393906127565068719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17918371595937418376712479 26877557393906127565068719)
      ·
        refine ⟨40316336090859191347603079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26877557393906127565068719 40316336090859191347603079)
        ·
          refine ⟨60474504136288787021404619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40316336090859191347603079 60474504136288787021404619)
          ·
            refine ⟨90711756204433180532106929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60474504136288787021404619 90711756204433180532106929)
            ·
              refine ⟨68033817153324885399080197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90711756204433180532106929 68033817153324885399080197)
              ·
                refine ⟨12756340716248416012327537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68033817153324885399080197 12756340716248416012327537)
                ·
                  refine ⟨9567255537186312009245653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12756340716248416012327537 9567255537186312009245653)
                  ·
                    refine ⟨224232551652804187716695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9567255537186312009245653 224232551652804187716695)
                    ·
                      rfl

theorem cell23_1310074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 2, 7].length) (baseStart_1310074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310074 prefixEnd_1310074 := by exact prefixLift 1310074
  have htrace : WordTrace (prefixWord ++ tailWord_1310074) baseStart_1310074 baseEnd_1310074 := by
    simpa [prefixWord, tailWord_1310074, baseEnd_1310074] using wordTrace_append hprefix tailTrace_1310074
  have hstable : (prefixWord ++ tailWord_1310074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310074).length < 2 ^ (prefixWord ++ tailWord_1310074).sum := by decide
  have hdescent : baseEnd_1310074 < baseStart_1310074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310088 : List Nat := [2, 1, 3, 3, 1, 3, 1, 2, 1, 3, 3]
def baseStart_1310088 : Nat := 118140960795 + 1310088 * 2 ^ 59
def prefixEnd_1310088 : Nat := 4983230072969 + 3 ^ 40 * 1310088 * 2
def baseEnd_1310088 : Nat := 672704843687575508375021

theorem tailTrace_1310088 : CollatzResearch.WordTrace tailWord_1310088 prefixEnd_1310088 672704843687575508375021 := by
  unfold tailWord_1310088
  simp only [CollatzResearch.WordTrace]
  refine ⟨23891417438891198031121459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31855223251854930708161945 23891417438891198031121459)
  ·
    refine ⟨35837126158336797046682189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23891417438891198031121459 35837126158336797046682189)
    ·
      refine ⟨13438922309376298892505821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35837126158336797046682189 13438922309376298892505821)
      ·
        refine ⟨5039595866016112084689683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13438922309376298892505821 5039595866016112084689683)
        ·
          refine ⟨7559393799024168127034525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5039595866016112084689683 7559393799024168127034525)
          ·
            refine ⟨2834772674634063047637947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7559393799024168127034525 2834772674634063047637947)
            ·
              refine ⟨4252159011951094571456921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2834772674634063047637947 4252159011951094571456921)
              ·
                refine ⟨3189119258963320928592691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4252159011951094571456921 3189119258963320928592691)
                ·
                  refine ⟨4783678888444981392889037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3189119258963320928592691 4783678888444981392889037)
                  ·
                    refine ⟨1793879583166868022333389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4783678888444981392889037 1793879583166868022333389)
                    ·
                      refine ⟨672704843687575508375021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1793879583166868022333389 672704843687575508375021)
                      ·
                        rfl

theorem cell23_1310088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_1310088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310088 prefixEnd_1310088 := by exact prefixLift 1310088
  have htrace : WordTrace (prefixWord ++ tailWord_1310088) baseStart_1310088 baseEnd_1310088 := by
    simpa [prefixWord, tailWord_1310088, baseEnd_1310088] using wordTrace_append hprefix tailTrace_1310088
  have hstable : (prefixWord ++ tailWord_1310088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310088).length < 2 ^ (prefixWord ++ tailWord_1310088).sum := by decide
  have hdescent : baseEnd_1310088 < baseStart_1310088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310105 : List Nat := [1, 2, 1, 2, 1, 6, 2, 2, 2, 1, 3]
def baseStart_1310105 : Nat := 118140960795 + 1310105 * 2 ^ 59
def prefixEnd_1310105 : Nat := 4983230072969 + 3 ^ 40 * 1310105 * 2
def baseEnd_1310105 : Nat := 672713572858701941862443

theorem tailTrace_1310105 : CollatzResearch.WordTrace tailWord_1310105 prefixEnd_1310105 672713572858701941862443 := by
  unfold tailWord_1310105
  simp only [CollatzResearch.WordTrace]
  refine ⟨47783454918720807965611769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31855636612480538643741179 47783454918720807965611769)
  ·
    refine ⟨35837591189040605974208827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47783454918720807965611769 35837591189040605974208827)
    ·
      refine ⟨53756386783560908961313241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35837591189040605974208827 53756386783560908961313241)
      ·
        refine ⟨40317290087670681720984931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53756386783560908961313241 40317290087670681720984931)
        ·
          refine ⟨60475935131506022581477397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40317290087670681720984931 60475935131506022581477397)
          ·
            refine ⟨2834809459289344808506753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 60475935131506022581477397 2834809459289344808506753)
            ·
              refine ⟨2126107094467008606380065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2834809459289344808506753 2126107094467008606380065)
              ·
                refine ⟨1594580320850256454785049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2126107094467008606380065 1594580320850256454785049)
                ·
                  refine ⟨1195935240637692341088787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1594580320850256454785049 1195935240637692341088787)
                  ·
                    refine ⟨1793902860956538511633181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1195935240637692341088787 1793902860956538511633181)
                    ·
                      refine ⟨672713572858701941862443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1793902860956538511633181 672713572858701941862443)
                      ·
                        rfl

theorem cell23_1310105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 2, 2, 1, 3].length) (baseStart_1310105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310105 prefixEnd_1310105 := by exact prefixLift 1310105
  have htrace : WordTrace (prefixWord ++ tailWord_1310105) baseStart_1310105 baseEnd_1310105 := by
    simpa [prefixWord, tailWord_1310105, baseEnd_1310105] using wordTrace_append hprefix tailTrace_1310105
  have hstable : (prefixWord ++ tailWord_1310105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310105).length < 2 ^ (prefixWord ++ tailWord_1310105).sum := by decide
  have hdescent : baseEnd_1310105 < baseStart_1310105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310111 : List Nat := [1, 1, 2, 5, 1, 2, 1, 1, 2, 3, 4]
def baseStart_1310111 : Nat := 118140960795 + 1310111 * 2 ^ 59
def prefixEnd_1310111 : Nat := 4983230072969 + 3 ^ 40 * 1310111 * 2
def baseEnd_1310111 : Nat := 672716653742628918387415

theorem tailTrace_1310111 : CollatzResearch.WordTrace tailWord_1310111 prefixEnd_1310111 672716653742628918387415 := by
  unfold tailWord_1310111
  simp only [CollatzResearch.WordTrace]
  refine ⟨47783673756699070990330187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31855782504466047326886791 47783673756699070990330187)
  ·
    refine ⟨71675510635048606485495281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47783673756699070990330187 71675510635048606485495281)
    ·
      refine ⟨53756632976286454864121461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71675510635048606485495281 53756632976286454864121461)
      ·
        refine ⟨5039684341526855143511387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53756632976286454864121461 5039684341526855143511387)
        ·
          refine ⟨7559526512290282715267081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5039684341526855143511387 7559526512290282715267081)
          ·
            refine ⟨5669644884217712036450311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7559526512290282715267081 5669644884217712036450311)
            ·
              refine ⟨8504467326326568054675467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5669644884217712036450311 8504467326326568054675467)
              ·
                refine ⟨12756700989489852082013201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8504467326326568054675467 12756700989489852082013201)
                ·
                  refine ⟨9567525742117389061509901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12756700989489852082013201 9567525742117389061509901)
                  ·
                    refine ⟨3587822153294020898066213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9567525742117389061509901 3587822153294020898066213)
                    ·
                      refine ⟨672716653742628918387415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3587822153294020898066213 672716653742628918387415)
                      ·
                        rfl

theorem cell23_1310111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_1310111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310111 prefixEnd_1310111 := by exact prefixLift 1310111
  have htrace : WordTrace (prefixWord ++ tailWord_1310111) baseStart_1310111 baseEnd_1310111 := by
    simpa [prefixWord, tailWord_1310111, baseEnd_1310111] using wordTrace_append hprefix tailTrace_1310111
  have hstable : (prefixWord ++ tailWord_1310111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310111).length < 2 ^ (prefixWord ++ tailWord_1310111).sum := by decide
  have hdescent : baseEnd_1310111 < baseStart_1310111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310141 : List Nat := [1, 4, 1, 2, 2, 1, 1, 2, 1, 4, 4]
def baseStart_1310141 : Nat := 118140960795 + 1310141 * 2 ^ 59
def prefixEnd_1310141 : Nat := 4983230072969 + 3 ^ 40 * 1310141 * 2
def baseEnd_1310141 : Nat := 672732058162263801012277

theorem tailTrace_1310141 : CollatzResearch.WordTrace tailWord_1310141 prefixEnd_1310141 672732058162263801012277 := by
  unfold tailWord_1310141
  simp only [CollatzResearch.WordTrace]
  refine ⟨47784767946590386113922277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31856511964393590742614851 47784767946590386113922277)
  ·
    refine ⟨8959643989985697396360427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47784767946590386113922277 8959643989985697396360427)
    ·
      refine ⟨13439465984978546094540641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8959643989985697396360427 13439465984978546094540641)
      ·
        refine ⟨10079599488733909570905481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13439465984978546094540641 10079599488733909570905481)
        ·
          refine ⟨7559699616550432178179111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10079599488733909570905481 7559699616550432178179111)
          ·
            refine ⟨11339549424825648267268667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7559699616550432178179111 11339549424825648267268667)
            ·
              refine ⟨17009324137238472400903001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11339549424825648267268667 17009324137238472400903001)
              ·
                refine ⟨12756993102928854300677251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17009324137238472400903001 12756993102928854300677251)
                ·
                  refine ⟨19135489654393281451015877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12756993102928854300677251 19135489654393281451015877)
                  ·
                    refine ⟨3587904310198740272065477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19135489654393281451015877 3587904310198740272065477)
                    ·
                      refine ⟨672732058162263801012277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3587904310198740272065477 672732058162263801012277)
                      ·
                        rfl

theorem cell23_1310141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_1310141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310141 prefixEnd_1310141 := by exact prefixLift 1310141
  have htrace : WordTrace (prefixWord ++ tailWord_1310141) baseStart_1310141 baseEnd_1310141 := by
    simpa [prefixWord, tailWord_1310141, baseEnd_1310141] using wordTrace_append hprefix tailTrace_1310141
  have hstable : (prefixWord ++ tailWord_1310141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310141).length < 2 ^ (prefixWord ++ tailWord_1310141).sum := by decide
  have hdescent : baseEnd_1310141 < baseStart_1310141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310168 : List Nat := [2, 1, 2, 2, 2, 1, 4, 4, 5]
def baseStart_1310168 : Nat := 118140960795 + 1310168 * 2 ^ 59
def prefixEnd_1310168 : Nat := 4983230072969 + 3 ^ 40 * 1310168 * 2
def baseEnd_1310168 : Nat := 74749546904437243930517

theorem tailTrace_1310168 : CollatzResearch.WordTrace tailWord_1310168 prefixEnd_1310168 74749546904437243930517 := by
  unfold tailWord_1310168
  simp only [CollatzResearch.WordTrace]
  refine ⟨23892876358746284862577579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31857168478328379816770105 23892876358746284862577579)
  ·
    refine ⟨35839314538119427293866369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23892876358746284862577579 35839314538119427293866369)
    ·
      refine ⟨26879485903589570470399777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35839314538119427293866369 26879485903589570470399777)
      ·
        refine ⟨20159614427692177852799833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26879485903589570470399777 20159614427692177852799833)
        ·
          refine ⟨15119710820769133389599875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20159614427692177852799833 15119710820769133389599875)
          ·
            refine ⟨22679566231153700084399813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15119710820769133389599875 22679566231153700084399813)
            ·
              refine ⟨4252418668341318765824965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22679566231153700084399813 4252418668341318765824965)
              ·
                refine ⟨797328500313997268592181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4252418668341318765824965 797328500313997268592181)
                ·
                  refine ⟨74749546904437243930517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 797328500313997268592181 74749546904437243930517)
                  ·
                    rfl

theorem cell23_1310168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 4, 5].length) (baseStart_1310168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310168 prefixEnd_1310168 := by exact prefixLift 1310168
  have htrace : WordTrace (prefixWord ++ tailWord_1310168) baseStart_1310168 baseEnd_1310168 := by
    simpa [prefixWord, tailWord_1310168, baseEnd_1310168] using wordTrace_append hprefix tailTrace_1310168
  have hstable : (prefixWord ++ tailWord_1310168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310168).length < 2 ^ (prefixWord ++ tailWord_1310168).sum := by decide
  have hdescent : baseEnd_1310168 < baseStart_1310168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310179 : List Nat := [1, 1, 1, 6, 2, 2, 3, 1, 2, 2, 2]
def baseStart_1310179 : Nat := 118140960795 + 1310179 * 2 ^ 59
def prefixEnd_1310179 : Nat := 4983230072969 + 3 ^ 40 * 1310179 * 2
def baseEnd_1310179 : Nat := 672751570427134652337103

theorem tailTrace_1310179 : CollatzResearch.WordTrace tailWord_1310179 prefixEnd_1310179 672751570427134652337103 := by
  unfold tailWord_1310179
  simp only [CollatzResearch.WordTrace]
  refine ⟨47786153920452718603805591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31857435946968479069203727 47786153920452718603805591)
  ·
    refine ⟨71679230880679077905708387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47786153920452718603805591 71679230880679077905708387)
    ·
      refine ⟨107518846321018616858562581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71679230880679077905708387 107518846321018616858562581)
      ·
        refine ⟨5039945921297747665245121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 107518846321018616858562581 5039945921297747665245121)
        ·
          refine ⟨3779959440973310748933841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5039945921297747665245121 3779959440973310748933841)
          ·
            refine ⟨2834969580729983061700381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3779959440973310748933841 2834969580729983061700381)
            ·
              refine ⟨1063113592773743648137643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2834969580729983061700381 1063113592773743648137643)
              ·
                refine ⟨1594670389160615472206465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1063113592773743648137643 1594670389160615472206465)
                ·
                  refine ⟨1196002791870461604154849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1594670389160615472206465 1196002791870461604154849)
                  ·
                    refine ⟨897002093902846203116137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1196002791870461604154849 897002093902846203116137)
                    ·
                      refine ⟨672751570427134652337103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 897002093902846203116137 672751570427134652337103)
                      ·
                        rfl

theorem cell23_1310179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_1310179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310179 prefixEnd_1310179 := by exact prefixLift 1310179
  have htrace : WordTrace (prefixWord ++ tailWord_1310179) baseStart_1310179 baseEnd_1310179 := by
    simpa [prefixWord, tailWord_1310179, baseEnd_1310179] using wordTrace_append hprefix tailTrace_1310179
  have hstable : (prefixWord ++ tailWord_1310179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310179).length < 2 ^ (prefixWord ++ tailWord_1310179).sum := by decide
  have hdescent : baseEnd_1310179 < baseStart_1310179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310198 : List Nat := [5, 1, 1, 1, 2, 2, 2, 1, 1, 7]
def baseStart_1310198 : Nat := 118140960795 + 1310198 * 2 ^ 59
def prefixEnd_1310198 : Nat := 4983230072969 + 3 ^ 40 * 1310198 * 2
def baseEnd_1310198 : Nat := 224253775519856692666505

theorem tailTrace_1310198 : CollatzResearch.WordTrace tailWord_1310198 prefixEnd_1310198 224253775519856692666505 := by
  unfold tailWord_1310198
  simp only [CollatzResearch.WordTrace]
  refine ⟨2986677931711492803046703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31857897938255923232498165 2986677931711492803046703)
  ·
    refine ⟨4480016897567239204570055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2986677931711492803046703 4480016897567239204570055)
    ·
      refine ⟨6720025346350858806855083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4480016897567239204570055 6720025346350858806855083)
      ·
        refine ⟨10080038019526288210282625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6720025346350858806855083 10080038019526288210282625)
        ·
          refine ⟨7560028514644716157711969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10080038019526288210282625 7560028514644716157711969)
          ·
            refine ⟨5670021385983537118283977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7560028514644716157711969 5670021385983537118283977)
            ·
              refine ⟨4252516039487652838712983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5670021385983537118283977 4252516039487652838712983)
              ·
                refine ⟨6378774059231479258069475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4252516039487652838712983 6378774059231479258069475)
                ·
                  refine ⟨9568161088847218887104213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6378774059231479258069475 9568161088847218887104213)
                  ·
                    refine ⟨224253775519856692666505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9568161088847218887104213 224253775519856692666505)
                    ·
                      rfl

theorem cell23_1310198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_1310198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310198 prefixEnd_1310198 := by exact prefixLift 1310198
  have htrace : WordTrace (prefixWord ++ tailWord_1310198) baseStart_1310198 baseEnd_1310198 := by
    simpa [prefixWord, tailWord_1310198, baseEnd_1310198] using wordTrace_append hprefix tailTrace_1310198
  have hstable : (prefixWord ++ tailWord_1310198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310198).length < 2 ^ (prefixWord ++ tailWord_1310198).sum := by decide
  have hdescent : baseEnd_1310198 < baseStart_1310198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310218 : List Nat := [3, 1, 2, 2, 2, 2, 1, 1, 4, 1, 4]
def baseStart_1310218 : Nat := 118140960795 + 1310218 * 2 ^ 59
def prefixEnd_1310218 : Nat := 4983230072969 + 3 ^ 40 * 1310218 * 2
def baseEnd_1310218 : Nat := 672771596172659999749423

theorem tailTrace_1310218 : CollatzResearch.WordTrace tailWord_1310218 prefixEnd_1310218 672771596172659999749423 := by
  unfold tailWord_1310218
  simp only [CollatzResearch.WordTrace]
  refine ⟨11946894091827857066118827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31858384244874285509650205 11946894091827857066118827)
  ·
    refine ⟨17920341137741785599178241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11946894091827857066118827 17920341137741785599178241)
    ·
      refine ⟨13440255853306339199383681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17920341137741785599178241 13440255853306339199383681)
      ·
        refine ⟨10080191889979754399537761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13440255853306339199383681 10080191889979754399537761)
        ·
          refine ⟨7560143917484815799653321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10080191889979754399537761 7560143917484815799653321)
          ·
            refine ⟨5670107938113611849739991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7560143917484815799653321 5670107938113611849739991)
            ·
              refine ⟨8505161907170417774609987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5670107938113611849739991 8505161907170417774609987)
              ·
                refine ⟨12757742860755626661914981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8505161907170417774609987 12757742860755626661914981)
                ·
                  refine ⟨2392076786391679999109059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12757742860755626661914981 2392076786391679999109059)
                  ·
                    refine ⟨3588115179587519998663589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2392076786391679999109059 3588115179587519998663589)
                    ·
                      refine ⟨672771596172659999749423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3588115179587519998663589 672771596172659999749423)
                      ·
                        rfl

theorem cell23_1310218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_1310218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310218 prefixEnd_1310218 := by exact prefixLift 1310218
  have htrace : WordTrace (prefixWord ++ tailWord_1310218) baseStart_1310218 baseEnd_1310218 := by
    simpa [prefixWord, tailWord_1310218, baseEnd_1310218] using wordTrace_append hprefix tailTrace_1310218
  have hstable : (prefixWord ++ tailWord_1310218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310218).length < 2 ^ (prefixWord ++ tailWord_1310218).sum := by decide
  have hdescent : baseEnd_1310218 < baseStart_1310218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310281 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 2, 4, 5]
def baseStart_1310281 : Nat := 118140960795 + 1310281 * 2 ^ 59
def prefixEnd_1310281 : Nat := 4983230072969 + 3 ^ 40 * 1310281 * 2
def baseEnd_1310281 : Nat := 672803945453893253261633

theorem tailTrace_1310281 : CollatzResearch.WordTrace tailWord_1310281 prefixEnd_1310281 672803945453893253261633 := by
  unfold tailWord_1310281
  simp only [CollatzResearch.WordTrace]
  refine ⟨47789874166083190024018697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31859916110722126682679131 47789874166083190024018697)
  ·
    refine ⟨35842405624562392518014023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47789874166083190024018697 35842405624562392518014023)
    ·
      refine ⟨53763608436843588777021035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35842405624562392518014023 53763608436843588777021035)
      ·
        refine ⟨80645412655265383165531553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53763608436843588777021035 80645412655265383165531553)
        ·
          refine ⟨60484059491449037374148665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80645412655265383165531553 60484059491449037374148665)
          ·
            refine ⟨45363044618586778030611499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60484059491449037374148665 45363044618586778030611499)
            ·
              refine ⟨68044566927880167045917249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45363044618586778030611499 68044566927880167045917249)
              ·
                refine ⟨51033425195910125284437937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68044566927880167045917249 51033425195910125284437937)
                ·
                  refine ⟨38275068896932593963328453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51033425195910125284437937 38275068896932593963328453)
                  ·
                    refine ⟨7176575418174861368124085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38275068896932593963328453 7176575418174861368124085)
                    ·
                      refine ⟨672803945453893253261633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7176575418174861368124085 672803945453893253261633)
                      ·
                        rfl

theorem cell23_1310281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 4, 5].length) (baseStart_1310281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310281 prefixEnd_1310281 := by exact prefixLift 1310281
  have htrace : WordTrace (prefixWord ++ tailWord_1310281) baseStart_1310281 baseEnd_1310281 := by
    simpa [prefixWord, tailWord_1310281, baseEnd_1310281] using wordTrace_append hprefix tailTrace_1310281
  have hstable : (prefixWord ++ tailWord_1310281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310281).length < 2 ^ (prefixWord ++ tailWord_1310281).sum := by decide
  have hdescent : baseEnd_1310281 < baseStart_1310281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310312 : List Nat := [2, 1, 4, 3, 1, 2, 1, 1, 1, 5, 2]
def baseStart_1310312 : Nat := 118140960795 + 1310312 * 2 ^ 59
def prefixEnd_1310312 : Nat := 4983230072969 + 3 ^ 40 * 1310312 * 2
def baseEnd_1310312 : Nat := 672819863354182631973991

theorem tailTrace_1310312 : CollatzResearch.WordTrace tailWord_1310312 prefixEnd_1310312 672819863354182631973991 := by
  unfold tailWord_1310312
  simp only [CollatzResearch.WordTrace]
  refine ⟨23895502414485441159198595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31860669885980588212264793 23895502414485441159198595)
  ·
    refine ⟨35843253621728161738797893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23895502414485441159198595 35843253621728161738797893)
    ·
      refine ⟨6720610054074030326024605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35843253621728161738797893 6720610054074030326024605)
      ·
        refine ⟨2520228770277761372259227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6720610054074030326024605 2520228770277761372259227)
        ·
          refine ⟨3780343155416642058388841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2520228770277761372259227 3780343155416642058388841)
          ·
            refine ⟨2835257366562481543791631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3780343155416642058388841 2835257366562481543791631)
            ·
              refine ⟨4252886049843722315687447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2835257366562481543791631 4252886049843722315687447)
              ·
                refine ⟨6379329074765583473531171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4252886049843722315687447 6379329074765583473531171)
                ·
                  refine ⟨9568993612148375210296757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6379329074765583473531171 9568993612148375210296757)
                  ·
                    refine ⟨897093151138910175965321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9568993612148375210296757 897093151138910175965321)
                    ·
                      refine ⟨672819863354182631973991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 897093151138910175965321 672819863354182631973991)
                      ·
                        rfl

theorem cell23_1310312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_1310312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310312 prefixEnd_1310312 := by exact prefixLift 1310312
  have htrace : WordTrace (prefixWord ++ tailWord_1310312) baseStart_1310312 baseEnd_1310312 := by
    simpa [prefixWord, tailWord_1310312, baseEnd_1310312] using wordTrace_append hprefix tailTrace_1310312
  have hstable : (prefixWord ++ tailWord_1310312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310312).length < 2 ^ (prefixWord ++ tailWord_1310312).sum := by decide
  have hdescent : baseEnd_1310312 < baseStart_1310312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310322 : List Nat := [3, 2, 1, 2, 3, 1, 4, 1, 1, 5]
def baseStart_1310322 : Nat := 118140960795 + 1310322 * 2 ^ 59
def prefixEnd_1310322 : Nat := 4983230072969 + 3 ^ 40 * 1310322 * 2
def baseEnd_1310322 : Nat := 224274999386909197616315

theorem tailTrace_1310322 : CollatzResearch.WordTrace tailWord_1310322 prefixEnd_1310322 224274999386909197616315 := by
  unfold tailWord_1310322
  simp only [CollatzResearch.WordTrace]
  refine ⟨11947842389733663506565305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31860913039289769350840813 11947842389733663506565305)
  ·
    refine ⟨8960881792300247629923979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11947842389733663506565305 8960881792300247629923979)
    ·
      refine ⟨13441322688450371444885969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8960881792300247629923979 13441322688450371444885969)
      ·
        refine ⟨10080992016337778583664477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13441322688450371444885969 10080992016337778583664477)
        ·
          refine ⟨3780372006126666968874179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10080992016337778583664477 3780372006126666968874179)
          ·
            refine ⟨5670558009190000453311269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3780372006126666968874179 5670558009190000453311269)
            ·
              refine ⟨1063229626723125084995863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5670558009190000453311269 1063229626723125084995863)
              ·
                refine ⟨1594844440084687627493795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1063229626723125084995863 1594844440084687627493795)
                ·
                  refine ⟨2392266660127031441240693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1594844440084687627493795 2392266660127031441240693)
                  ·
                    refine ⟨224274999386909197616315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2392266660127031441240693 224274999386909197616315)
                    ·
                      rfl

theorem cell23_1310322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 1, 1, 5].length) (baseStart_1310322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310322 prefixEnd_1310322 := by exact prefixLift 1310322
  have htrace : WordTrace (prefixWord ++ tailWord_1310322) baseStart_1310322 baseEnd_1310322 := by
    simpa [prefixWord, tailWord_1310322, baseEnd_1310322] using wordTrace_append hprefix tailTrace_1310322
  have hstable : (prefixWord ++ tailWord_1310322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310322).length < 2 ^ (prefixWord ++ tailWord_1310322).sum := by decide
  have hdescent : baseEnd_1310322 < baseStart_1310322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310331 : List Nat := [1, 1, 1, 1, 1, 4, 14]
def baseStart_1310331 : Nat := 118140960795 + 1310331 * 2 ^ 59
def prefixEnd_1310331 : Nat := 4983230072969 + 3 ^ 40 * 1310331 * 2
def baseEnd_1310331 : Nat := 8306538512180469847363

theorem tailTrace_1310331 : CollatzResearch.WordTrace tailWord_1310331 prefixEnd_1310331 8306538512180469847363 := by
  unfold tailWord_1310331
  simp only [CollatzResearch.WordTrace]
  refine ⟨47791697815902048563338847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31861131877268032375559231 47791697815902048563338847)
  ·
    refine ⟨71687546723853072845008271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47791697815902048563338847 71687546723853072845008271)
    ·
      refine ⟨107531320085779609267512407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71687546723853072845008271 107531320085779609267512407)
      ·
        refine ⟨161296980128669413901268611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107531320085779609267512407 161296980128669413901268611)
        ·
          refine ⟨241945470193004120851902917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161296980128669413901268611 241945470193004120851902917)
          ·
            refine ⟨45364775661188272659731797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 241945470193004120851902917 45364775661188272659731797)
            ·
              refine ⟨8306538512180469847363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 45364775661188272659731797 8306538512180469847363)
              ·
                rfl

theorem cell23_1310331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 14].length) (baseStart_1310331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310331 prefixEnd_1310331 := by exact prefixLift 1310331
  have htrace : WordTrace (prefixWord ++ tailWord_1310331) baseStart_1310331 baseEnd_1310331 := by
    simpa [prefixWord, tailWord_1310331, baseEnd_1310331] using wordTrace_append hprefix tailTrace_1310331
  have hstable : (prefixWord ++ tailWord_1310331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310331).length < 2 ^ (prefixWord ++ tailWord_1310331).sum := by decide
  have hdescent : baseEnd_1310331 < baseStart_1310331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310370 : List Nat := [3, 3, 1, 4, 2, 1, 1, 3, 1, 1, 3]
def baseStart_1310370 : Nat := 118140960795 + 1310370 * 2 ^ 59
def prefixEnd_1310370 : Nat := 4983230072969 + 3 ^ 40 * 1310370 * 2
def baseEnd_1310370 : Nat := 672849645232143405048725

theorem tailTrace_1310370 : CollatzResearch.WordTrace tailWord_1310370 prefixEnd_1310370 672849645232143405048725 := by
  unfold tailWord_1310370
  simp only [CollatzResearch.WordTrace]
  refine ⟨11948280065690189556002141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31862080175173838816005709 11948280065690189556002141)
  ·
    refine ⟨4480605024633821083500803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11948280065690189556002141 4480605024633821083500803)
    ·
      refine ⟨6720907536950731625251205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4480605024633821083500803 6720907536950731625251205)
      ·
        refine ⟨1260170163178262179734601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6720907536950731625251205 1260170163178262179734601)
        ·
          refine ⟨945127622383696634800951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1260170163178262179734601 945127622383696634800951)
          ·
            refine ⟨1417691433575544952201427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 945127622383696634800951 1417691433575544952201427)
            ·
              refine ⟨2126537150363317428302141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1417691433575544952201427 2126537150363317428302141)
              ·
                refine ⟨797451431386244035613303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2126537150363317428302141 797451431386244035613303)
                ·
                  refine ⟨1196177147079366053419955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 797451431386244035613303 1196177147079366053419955)
                  ·
                    refine ⟨1794265720619049080129933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1196177147079366053419955 1794265720619049080129933)
                    ·
                      refine ⟨672849645232143405048725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1794265720619049080129933 672849645232143405048725)
                      ·
                        rfl

theorem cell23_1310370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_1310370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310370 prefixEnd_1310370 := by exact prefixLift 1310370
  have htrace : WordTrace (prefixWord ++ tailWord_1310370) baseStart_1310370 baseEnd_1310370 := by
    simpa [prefixWord, tailWord_1310370, baseEnd_1310370] using wordTrace_append hprefix tailTrace_1310370
  have hstable : (prefixWord ++ tailWord_1310370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310370).length < 2 ^ (prefixWord ++ tailWord_1310370).sum := by decide
  have hdescent : baseEnd_1310370 < baseStart_1310370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310382 : List Nat := [4, 1, 4, 1, 2, 2, 9]
def baseStart_1310382 : Nat := 118140960795 + 1310382 * 2 ^ 59
def prefixEnd_1310382 : Nat := 4983230072969 + 3 ^ 40 * 1310382 * 2
def baseEnd_1310382 : Nat := 8306861814814782198749

theorem tailTrace_1310382 : CollatzResearch.WordTrace tailWord_1310382 prefixEnd_1310382 8306861814814782198749 := by
  unfold tailWord_1310382
  simp only [CollatzResearch.WordTrace]
  refine ⟨5974194742339660534180675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31862371959144856182296933 5974194742339660534180675)
  ·
    refine ⟨8961292113509490801271013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5974194742339660534180675 8961292113509490801271013)
    ·
      refine ⟨1680242271283029525238315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8961292113509490801271013 1680242271283029525238315)
      ·
        refine ⟨2520363406924544287857473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1680242271283029525238315 2520363406924544287857473)
        ·
          refine ⟨1890272555193408215893105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2520363406924544287857473 1890272555193408215893105)
          ·
            refine ⟨1417704416395056161919829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1890272555193408215893105 1417704416395056161919829)
            ·
              refine ⟨8306861814814782198749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1417704416395056161919829 8306861814814782198749)
              ·
                rfl

theorem cell23_1310382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 9].length) (baseStart_1310382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310382 prefixEnd_1310382 := by exact prefixLift 1310382
  have htrace : WordTrace (prefixWord ++ tailWord_1310382) baseStart_1310382 baseEnd_1310382 := by
    simpa [prefixWord, tailWord_1310382, baseEnd_1310382] using wordTrace_append hprefix tailTrace_1310382
  have hstable : (prefixWord ++ tailWord_1310382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310382).length < 2 ^ (prefixWord ++ tailWord_1310382).sum := by decide
  have hdescent : baseEnd_1310382 < baseStart_1310382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310408 : List Nat := [2, 1, 3, 1, 2, 2, 2, 1, 1, 8]
def baseStart_1310408 : Nat := 118140960795 + 1310408 * 2 ^ 59
def prefixEnd_1310408 : Nat := 4983230072969 + 3 ^ 40 * 1310408 * 2
def baseEnd_1310408 : Nat := 224289719165671418791183

theorem tailTrace_1310408 : CollatzResearch.WordTrace tailWord_1310408 prefixEnd_1310408 224289719165671418791183 := by
  unfold tailWord_1310408
  simp only [CollatzResearch.WordTrace]
  refine ⟨23897253118311545356945939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31863004157748727142594585 23897253118311545356945939)
  ·
    refine ⟨35845879677467318035418909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23897253118311545356945939 35845879677467318035418909)
    ·
      refine ⟨13442204879050244263282091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35845879677467318035418909 13442204879050244263282091)
      ·
        refine ⟨20163307318575366394923137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13442204879050244263282091 20163307318575366394923137)
        ·
          refine ⟨15122480488931524796192353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20163307318575366394923137 15122480488931524796192353)
          ·
            refine ⟨11341860366698643597144265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15122480488931524796192353 11341860366698643597144265)
            ·
              refine ⟨8506395275023982697858199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11341860366698643597144265 8506395275023982697858199)
              ·
                refine ⟨12759592912535974046787299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8506395275023982697858199 12759592912535974046787299)
                ·
                  refine ⟨19139389368803961070180949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12759592912535974046787299 19139389368803961070180949)
                  ·
                    refine ⟨224289719165671418791183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 19139389368803961070180949 224289719165671418791183)
                    ·
                      rfl

theorem cell23_1310408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_1310408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310408 prefixEnd_1310408 := by exact prefixLift 1310408
  have htrace : WordTrace (prefixWord ++ tailWord_1310408) baseStart_1310408 baseEnd_1310408 := by
    simpa [prefixWord, tailWord_1310408, baseEnd_1310408] using wordTrace_append hprefix tailTrace_1310408
  have hstable : (prefixWord ++ tailWord_1310408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310408).length < 2 ^ (prefixWord ++ tailWord_1310408).sum := by decide
  have hdescent : baseEnd_1310408 < baseStart_1310408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310415 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 5, 4, 2]
def baseStart_1310415 : Nat := 118140960795 + 1310415 * 2 ^ 59
def prefixEnd_1310415 : Nat := 4983230072969 + 3 ^ 40 * 1310415 * 2
def baseEnd_1310415 : Nat := 672872751861595728986017

theorem tailTrace_1310415 : CollatzResearch.WordTrace tailWord_1310415 prefixEnd_1310415 672872751861595728986017 := by
  unfold tailWord_1310415
  simp only [CollatzResearch.WordTrace]
  refine ⟨47794761547597730909396699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31863174365065153939597799 47794761547597730909396699)
  ·
    refine ⟨71692142321396596364095049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47794761547597730909396699 71692142321396596364095049)
    ·
      refine ⟨53769106741047447273071287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71692142321396596364095049 53769106741047447273071287)
      ·
        refine ⟨80653660111571170909606931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53769106741047447273071287 80653660111571170909606931)
        ·
          refine ⟨120980490167356756364410397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80653660111571170909606931 120980490167356756364410397)
          ·
            refine ⟨45367683812758783636653899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120980490167356756364410397 45367683812758783636653899)
            ·
              refine ⟨68051525719138175454980849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45367683812758783636653899 68051525719138175454980849)
              ·
                refine ⟨51038644289353631591235637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68051525719138175454980849 51038644289353631591235637)
                ·
                  refine ⟨4784872902126902961678341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51038644289353631591235637 4784872902126902961678341)
                  ·
                    refine ⟨897163669148794305314689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4784872902126902961678341 897163669148794305314689)
                    ·
                      refine ⟨672872751861595728986017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 897163669148794305314689 672872751861595728986017)
                      ·
                        rfl

theorem cell23_1310415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 4, 2].length) (baseStart_1310415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310415 prefixEnd_1310415 := by exact prefixLift 1310415
  have htrace : WordTrace (prefixWord ++ tailWord_1310415) baseStart_1310415 baseEnd_1310415 := by
    simpa [prefixWord, tailWord_1310415, baseEnd_1310415] using wordTrace_append hprefix tailTrace_1310415
  have hstable : (prefixWord ++ tailWord_1310415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310415).length < 2 ^ (prefixWord ++ tailWord_1310415).sum := by decide
  have hdescent : baseEnd_1310415 < baseStart_1310415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310432 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 6, 2, 2]
def baseStart_1310432 : Nat := 118140960795 + 1310432 * 2 ^ 59
def prefixEnd_1310432 : Nat := 4983230072969 + 3 ^ 40 * 1310432 * 2
def baseEnd_1310432 : Nat := 672881481032722162473439

theorem tailTrace_1310432 : CollatzResearch.WordTrace tailWord_1310432 prefixEnd_1310432 672881481032722162473439 := by
  unfold tailWord_1310432
  simp only [CollatzResearch.WordTrace]
  refine ⟨23897690794268071406382775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31863587725690761875177033 23897690794268071406382775)
  ·
    refine ⟨35846536191402107109574163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23897690794268071406382775 35846536191402107109574163)
    ·
      refine ⟨53769804287103160664361245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35846536191402107109574163 53769804287103160664361245)
      ·
        refine ⟨20163676607663685249135467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53769804287103160664361245 20163676607663685249135467)
        ·
          refine ⟨30245514911495527873703201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20163676607663685249135467 30245514911495527873703201)
          ·
            refine ⟨22684136183621645905277401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30245514911495527873703201 22684136183621645905277401)
            ·
              refine ⟨17013102137716234428958051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22684136183621645905277401 17013102137716234428958051)
              ·
                refine ⟨25519653206574351643437077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17013102137716234428958051 25519653206574351643437077)
                ·
                  refine ⟨1196233744058172733286113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 25519653206574351643437077 1196233744058172733286113)
                  ·
                    refine ⟨897175308043629549964585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1196233744058172733286113 897175308043629549964585)
                    ·
                      refine ⟨672881481032722162473439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 897175308043629549964585 672881481032722162473439)
                      ·
                        rfl

theorem cell23_1310432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 6, 2, 2].length) (baseStart_1310432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310432 prefixEnd_1310432 := by exact prefixLift 1310432
  have htrace : WordTrace (prefixWord ++ tailWord_1310432) baseStart_1310432 baseEnd_1310432 := by
    simpa [prefixWord, tailWord_1310432, baseEnd_1310432] using wordTrace_append hprefix tailTrace_1310432
  have hstable : (prefixWord ++ tailWord_1310432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310432).length < 2 ^ (prefixWord ++ tailWord_1310432).sum := by decide
  have hdescent : baseEnd_1310432 < baseStart_1310432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310449 : List Nat := [1, 2, 2, 2, 2, 3, 1, 4, 2, 2, 2]
def baseStart_1310449 : Nat := 118140960795 + 1310449 * 2 ^ 59
def prefixEnd_1310449 : Nat := 4983230072969 + 3 ^ 40 * 1310449 * 2
def baseEnd_1310449 : Nat := 672890210203848595960861

theorem tailTrace_1310449 : CollatzResearch.WordTrace tailWord_1310449 prefixEnd_1310449 672890210203848595960861 := by
  unfold tailWord_1310449
  simp only [CollatzResearch.WordTrace]
  refine ⟨47796001629474554716134401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31864001086316369810756267 47796001629474554716134401)
  ·
    refine ⟨35847001222105916037100801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47796001629474554716134401 35847001222105916037100801)
    ·
      refine ⟨26885250916579437027825601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35847001222105916037100801 26885250916579437027825601)
      ·
        refine ⟨20163938187434577770869201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26885250916579437027825601 20163938187434577770869201)
        ·
          refine ⟨15122953640575933328151901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20163938187434577770869201 15122953640575933328151901)
          ·
            refine ⟨5671107615215974998056963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15122953640575933328151901 5671107615215974998056963)
            ·
              refine ⟨8506661422823962497085445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5671107615215974998056963 8506661422823962497085445)
              ·
                refine ⟨1594999016779492968203521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8506661422823962497085445 1594999016779492968203521)
                ·
                  refine ⟨1196249262584619726152641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1594999016779492968203521 1196249262584619726152641)
                  ·
                    refine ⟨897186946938464794614481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1196249262584619726152641 897186946938464794614481)
                    ·
                      refine ⟨672890210203848595960861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 897186946938464794614481 672890210203848595960861)
                      ·
                        rfl

theorem cell23_1310449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 4, 2, 2, 2].length) (baseStart_1310449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310449 prefixEnd_1310449 := by exact prefixLift 1310449
  have htrace : WordTrace (prefixWord ++ tailWord_1310449) baseStart_1310449 baseEnd_1310449 := by
    simpa [prefixWord, tailWord_1310449, baseEnd_1310449] using wordTrace_append hprefix tailTrace_1310449
  have hstable : (prefixWord ++ tailWord_1310449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310449).length < 2 ^ (prefixWord ++ tailWord_1310449).sum := by decide
  have hdescent : baseEnd_1310449 < baseStart_1310449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310458 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 2, 1, 8]
def baseStart_1310458 : Nat := 118140960795 + 1310458 * 2 ^ 59
def prefixEnd_1310458 : Nat := 4983230072969 + 3 ^ 40 * 1310458 * 2
def baseEnd_1310458 : Nat := 672894831529739060748319

theorem tailTrace_1310458 : CollatzResearch.WordTrace tailWord_1310458 prefixEnd_1310458 672894831529739060748319 := by
  unfold tailWord_1310458
  simp only [CollatzResearch.WordTrace]
  refine ⟨11949082471610487313303007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31864219924294632835474685 11949082471610487313303007)
  ·
    refine ⟨17923623707415730969954511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11949082471610487313303007 17923623707415730969954511)
    ·
      refine ⟨26885435561123596454931767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17923623707415730969954511 26885435561123596454931767)
      ·
        refine ⟨40328153341685394682397651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26885435561123596454931767 40328153341685394682397651)
        ·
          refine ⟨60492230012528092023596477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40328153341685394682397651 60492230012528092023596477)
          ·
            refine ⟨22684586254698034508848679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60492230012528092023596477 22684586254698034508848679)
            ·
              refine ⟨34026879382047051763273019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22684586254698034508848679 34026879382047051763273019)
              ·
                refine ⟨51040319073070577644909529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34026879382047051763273019 51040319073070577644909529)
                ·
                  refine ⟨38280239304802933233682147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51040319073070577644909529 38280239304802933233682147)
                  ·
                    refine ⟨57420358957204399850523221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38280239304802933233682147 57420358957204399850523221)
                    ·
                      refine ⟨672894831529739060748319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 57420358957204399850523221 672894831529739060748319)
                      ·
                        rfl

theorem cell23_1310458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_1310458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310458 prefixEnd_1310458 := by exact prefixLift 1310458
  have htrace : WordTrace (prefixWord ++ tailWord_1310458) baseStart_1310458 baseEnd_1310458 := by
    simpa [prefixWord, tailWord_1310458, baseEnd_1310458] using wordTrace_append hprefix tailTrace_1310458
  have hstable : (prefixWord ++ tailWord_1310458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310458).length < 2 ^ (prefixWord ++ tailWord_1310458).sum := by decide
  have hdescent : baseEnd_1310458 < baseStart_1310458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310465 : List Nat := [1, 2, 4, 1, 1, 1, 3, 1, 1, 5, 3]
def baseStart_1310465 : Nat := 118140960795 + 1310465 * 2 ^ 59
def prefixEnd_1310465 : Nat := 4983230072969 + 3 ^ 40 * 1310465 * 2
def baseEnd_1310465 : Nat := 672898425894320533360787

theorem tailTrace_1310465 : CollatzResearch.WordTrace tailWord_1310465 prefixEnd_1310465 672898425894320533360787 := by
  unfold tailWord_1310465
  simp only [CollatzResearch.WordTrace]
  refine ⟨47796585197416589448716849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31864390131611059632477899 47796585197416589448716849)
  ·
    refine ⟨35847438898062442086537637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47796585197416589448716849 35847438898062442086537637)
    ·
      refine ⟨6721394793386707891225807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35847438898062442086537637 6721394793386707891225807)
      ·
        refine ⟨10082092190080061836838711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6721394793386707891225807 10082092190080061836838711)
        ·
          refine ⟨15123138285120092755258067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10082092190080061836838711 15123138285120092755258067)
          ·
            refine ⟨22684707427680139132887101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15123138285120092755258067 22684707427680139132887101)
            ·
              refine ⟨8506765285380052174832663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22684707427680139132887101 8506765285380052174832663)
              ·
                refine ⟨12760147928070078262248995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8506765285380052174832663 12760147928070078262248995)
                ·
                  refine ⟨19140221892105117393373493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12760147928070078262248995 19140221892105117393373493)
                  ·
                    refine ⟨1794395802384854755628765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19140221892105117393373493 1794395802384854755628765)
                    ·
                      refine ⟨672898425894320533360787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1794395802384854755628765 672898425894320533360787)
                      ·
                        rfl

theorem cell23_1310465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_1310465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310465 prefixEnd_1310465 := by exact prefixLift 1310465
  have htrace : WordTrace (prefixWord ++ tailWord_1310465) baseStart_1310465 baseEnd_1310465 := by
    simpa [prefixWord, tailWord_1310465, baseEnd_1310465] using wordTrace_append hprefix tailTrace_1310465
  have hstable : (prefixWord ++ tailWord_1310465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310465).length < 2 ^ (prefixWord ++ tailWord_1310465).sum := by decide
  have hdescent : baseEnd_1310465 < baseStart_1310465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310466 : List Nat := [3, 4, 1, 1, 1, 1, 1, 5, 2, 2, 2]
def baseStart_1310466 : Nat := 118140960795 + 1310466 * 2 ^ 59
def prefixEnd_1310466 : Nat := 4983230072969 + 3 ^ 40 * 1310466 * 2
def baseEnd_1310466 : Nat := 672898939374975029448283

theorem tailTrace_1310466 : CollatzResearch.WordTrace tailWord_1310466 prefixEnd_1310466 672898939374975029448283 := by
  unfold tailWord_1310466
  simp only [CollatzResearch.WordTrace]
  refine ⟨11949155417603241654875813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31864414446941977746335501 11949155417603241654875813)
  ·
    refine ⟨2240466640800607810289215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11949155417603241654875813 2240466640800607810289215)
    ·
      refine ⟨3360699961200911715433823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2240466640800607810289215 3360699961200911715433823)
      ·
        refine ⟨5041049941801367573150735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3360699961200911715433823 5041049941801367573150735)
        ·
          refine ⟨7561574912702051359726103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5041049941801367573150735 7561574912702051359726103)
          ·
            refine ⟨11342362369053077039589155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7561574912702051359726103 11342362369053077039589155)
            ·
              refine ⟨17013543553579615559383733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11342362369053077039589155 17013543553579615559383733)
              ·
                refine ⟨1595019708148088958692225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17013543553579615559383733 1595019708148088958692225)
                ·
                  refine ⟨1196264781111066719019169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1595019708148088958692225 1196264781111066719019169)
                  ·
                    refine ⟨897198585833300039264377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1196264781111066719019169 897198585833300039264377)
                    ·
                      refine ⟨672898939374975029448283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 897198585833300039264377 672898939374975029448283)
                      ·
                        rfl

theorem cell23_1310466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_1310466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310466 prefixEnd_1310466 := by exact prefixLift 1310466
  have htrace : WordTrace (prefixWord ++ tailWord_1310466) baseStart_1310466 baseEnd_1310466 := by
    simpa [prefixWord, tailWord_1310466, baseEnd_1310466] using wordTrace_append hprefix tailTrace_1310466
  have hstable : (prefixWord ++ tailWord_1310466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310466).length < 2 ^ (prefixWord ++ tailWord_1310466).sum := by decide
  have hdescent : baseEnd_1310466 < baseStart_1310466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310485 : List Nat := [1, 3, 2, 1, 2, 4, 1, 1, 1, 7]
def baseStart_1310485 : Nat := 118140960795 + 1310485 * 2 ^ 59
def prefixEnd_1310485 : Nat := 4983230072969 + 3 ^ 40 * 1310485 * 2
def baseEnd_1310485 : Nat := 224302898502470151703565

theorem tailTrace_1310485 : CollatzResearch.WordTrace tailWord_1310485 prefixEnd_1310485 224302898502470151703565 := by
  unfold tailWord_1310485
  simp only [CollatzResearch.WordTrace]
  refine ⟨47797314657344132864444909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31864876438229421909629939 47797314657344132864444909)
  ·
    refine ⟨17923992996504049824166841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47797314657344132864444909 17923992996504049824166841)
    ·
      refine ⟨13442994747378037368125131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17923992996504049824166841 13442994747378037368125131)
      ·
        refine ⟨20164492121067056052187697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13442994747378037368125131 20164492121067056052187697)
        ·
          refine ⟨15123369090800292039140773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20164492121067056052187697 15123369090800292039140773)
          ·
            refine ⟨2835631704525054757338895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15123369090800292039140773 2835631704525054757338895)
            ·
              refine ⟨4253447556787582136008343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2835631704525054757338895 4253447556787582136008343)
              ·
                refine ⟨6380171335181373204012515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4253447556787582136008343 6380171335181373204012515)
                ·
                  refine ⟨9570257002772059806018773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6380171335181373204012515 9570257002772059806018773)
                  ·
                    refine ⟨224302898502470151703565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9570257002772059806018773 224302898502470151703565)
                    ·
                      rfl

theorem cell23_1310485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_1310485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310485 prefixEnd_1310485 := by exact prefixLift 1310485
  have htrace : WordTrace (prefixWord ++ tailWord_1310485) baseStart_1310485 baseEnd_1310485 := by
    simpa [prefixWord, tailWord_1310485, baseEnd_1310485] using wordTrace_append hprefix tailTrace_1310485
  have hstable : (prefixWord ++ tailWord_1310485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310485).length < 2 ^ (prefixWord ++ tailWord_1310485).sum := by decide
  have hdescent : baseEnd_1310485 < baseStart_1310485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310545 : List Nat := [1, 2, 2, 1, 5, 1, 1, 2, 8]
def baseStart_1310545 : Nat := 118140960795 + 1310545 * 2 ^ 59
def prefixEnd_1310545 : Nat := 4983230072969 + 3 ^ 40 * 1310545 * 2
def baseEnd_1310545 : Nat := 74771056038520024484491

theorem tailTrace_1310545 : CollatzResearch.WordTrace tailWord_1310545 prefixEnd_1310545 74771056038520024484491 := by
  unfold tailWord_1310545
  simp only [CollatzResearch.WordTrace]
  refine ⟨47799503037126763111629089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31866335358084508741086059 47799503037126763111629089)
  ·
    refine ⟨35849627277845072333721817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47799503037126763111629089 35849627277845072333721817)
    ·
      refine ⟨26887220458383804250291363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35849627277845072333721817 26887220458383804250291363)
      ·
        refine ⟨40330830687575706375437045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26887220458383804250291363 40330830687575706375437045)
        ·
          refine ⟨3781015376960222472697223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40330830687575706375437045 3781015376960222472697223)
          ·
            refine ⟨5671523065440333709045835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3781015376960222472697223 5671523065440333709045835)
            ·
              refine ⟨8507284598160500563568753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5671523065440333709045835 8507284598160500563568753)
              ·
                refine ⟨6380463448620375422676565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8507284598160500563568753 6380463448620375422676565)
                ·
                  refine ⟨74771056038520024484491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6380463448620375422676565 74771056038520024484491)
                  ·
                    rfl

theorem cell23_1310545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 8].length) (baseStart_1310545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310545 prefixEnd_1310545 := by exact prefixLift 1310545
  have htrace : WordTrace (prefixWord ++ tailWord_1310545) baseStart_1310545 baseEnd_1310545 := by
    simpa [prefixWord, tailWord_1310545, baseEnd_1310545] using wordTrace_append hprefix tailTrace_1310545
  have hstable : (prefixWord ++ tailWord_1310545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310545).length < 2 ^ (prefixWord ++ tailWord_1310545).sum := by decide
  have hdescent : baseEnd_1310545 < baseStart_1310545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310562 : List Nat := [3, 3, 2, 1, 2, 1, 2, 1, 8]
def baseStart_1310562 : Nat := 118140960795 + 1310562 * 2 ^ 59
def prefixEnd_1310562 : Nat := 4983230072969 + 3 ^ 40 * 1310562 * 2
def baseEnd_1310562 : Nat := 74772025946422961538649

theorem tailTrace_1310562 : CollatzResearch.WordTrace tailWord_1310562 prefixEnd_1310562 74772025946422961538649 := by
  unfold tailWord_1310562
  simp only [CollatzResearch.WordTrace]
  refine ⟨11950030769516293753749485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31866748718710116676665293 11950030769516293753749485)
  ·
    refine ⟨4481261538568610157656057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11950030769516293753749485 4481261538568610157656057)
    ·
      refine ⟨3360946153926457618242043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4481261538568610157656057 3360946153926457618242043)
      ·
        refine ⟨5041419230889686427363065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3360946153926457618242043 5041419230889686427363065)
        ·
          refine ⟨3781064423167264820522299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5041419230889686427363065 3781064423167264820522299)
          ·
            refine ⟨5671596634750897230783449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3781064423167264820522299 5671596634750897230783449)
            ·
              refine ⟨4253697476063172923087587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5671596634750897230783449 4253697476063172923087587)
              ·
                refine ⟨6380546214094759384631381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4253697476063172923087587 6380546214094759384631381)
                ·
                  refine ⟨74772025946422961538649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6380546214094759384631381 74772025946422961538649)
                  ·
                    rfl

theorem cell23_1310562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_1310562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310562 prefixEnd_1310562 := by exact prefixLift 1310562
  have htrace : WordTrace (prefixWord ++ tailWord_1310562) baseStart_1310562 baseEnd_1310562 := by
    simpa [prefixWord, tailWord_1310562, baseEnd_1310562] using wordTrace_append hprefix tailTrace_1310562
  have hstable : (prefixWord ++ tailWord_1310562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310562).length < 2 ^ (prefixWord ++ tailWord_1310562).sum := by decide
  have hdescent : baseEnd_1310562 < baseStart_1310562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310623 : List Nat := [1, 1, 2, 5, 3, 1, 1, 4, 1, 1, 3]
def baseStart_1310623 : Nat := 118140960795 + 1310623 * 2 ^ 59
def prefixEnd_1310623 : Nat := 4983230072969 + 3 ^ 40 * 1310623 * 2
def baseEnd_1310623 : Nat := 672979555837730915185061

theorem tailTrace_1310623 : CollatzResearch.WordTrace tailWord_1310623 prefixEnd_1310623 672979555837730915185061 := by
  unfold tailWord_1310623
  simp only [CollatzResearch.WordTrace]
  refine ⟨47802347930844182432968523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31868231953896121621979015 47802347930844182432968523)
  ·
    refine ⟨71703521896266273649452785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47802347930844182432968523 71703521896266273649452785)
    ·
      refine ⟨53777641422199705237089589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71703521896266273649452785 53777641422199705237089589)
      ·
        refine ⟨5041653883331222365977149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53777641422199705237089589 5041653883331222365977149)
        ·
          refine ⟨1890620206249208387241431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5041653883331222365977149 1890620206249208387241431)
          ·
            refine ⟨2835930309373812580862147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1890620206249208387241431 2835930309373812580862147)
            ·
              refine ⟨4253895464060718871293221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2835930309373812580862147 4253895464060718871293221)
              ·
                refine ⟨797605399511384788367479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4253895464060718871293221 797605399511384788367479)
                ·
                  refine ⟨1196408099267077182551219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 797605399511384788367479 1196408099267077182551219)
                  ·
                    refine ⟨1794612148900615773826829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1196408099267077182551219 1794612148900615773826829)
                    ·
                      refine ⟨672979555837730915185061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1794612148900615773826829 672979555837730915185061)
                      ·
                        rfl

theorem cell23_1310623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_1310623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310623 prefixEnd_1310623 := by exact prefixLift 1310623
  have htrace : WordTrace (prefixWord ++ tailWord_1310623) baseStart_1310623 baseEnd_1310623 := by
    simpa [prefixWord, tailWord_1310623, baseEnd_1310623] using wordTrace_append hprefix tailTrace_1310623
  have hstable : (prefixWord ++ tailWord_1310623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310623).length < 2 ^ (prefixWord ++ tailWord_1310623).sum := by decide
  have hdescent : baseEnd_1310623 < baseStart_1310623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310629 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 7, 2, 2]
def baseStart_1310629 : Nat := 118140960795 + 1310629 * 2 ^ 59
def prefixEnd_1310629 : Nat := 4983230072969 + 3 ^ 40 * 1310629 * 2
def baseEnd_1310629 : Nat := 672982636721657891710033

theorem tailTrace_1310629 : CollatzResearch.WordTrace tailWord_1310629 prefixEnd_1310629 672982636721657891710033 := by
  unfold tailWord_1310629
  simp only [CollatzResearch.WordTrace]
  refine ⟨47802566768822445457686941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31868377845881630305124627 47802566768822445457686941)
  ·
    refine ⟨17925962538308417046632603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47802566768822445457686941 17925962538308417046632603)
    ·
      refine ⟨26888943807462625569948905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17925962538308417046632603 26888943807462625569948905)
      ·
        refine ⟨20166707855596969177461679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26888943807462625569948905 20166707855596969177461679)
        ·
          refine ⟨30250061783395453766192519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20166707855596969177461679 30250061783395453766192519)
          ·
            refine ⟨45375092675093180649288779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30250061783395453766192519 45375092675093180649288779)
            ·
              refine ⟨68062639012639770973933169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45375092675093180649288779 68062639012639770973933169)
              ·
                refine ⟨51046979259479828230449877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68062639012639770973933169 51046979259479828230449877)
                ·
                  refine ⟨1196413576394058474151169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 51046979259479828230449877 1196413576394058474151169)
                  ·
                    refine ⟨897310182295543855613377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1196413576394058474151169 897310182295543855613377)
                    ·
                      refine ⟨672982636721657891710033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 897310182295543855613377 672982636721657891710033)
                      ·
                        rfl

theorem cell23_1310629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 7, 2, 2].length) (baseStart_1310629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310629 prefixEnd_1310629 := by exact prefixLift 1310629
  have htrace : WordTrace (prefixWord ++ tailWord_1310629) baseStart_1310629 baseEnd_1310629 := by
    simpa [prefixWord, tailWord_1310629, baseEnd_1310629] using wordTrace_append hprefix tailTrace_1310629
  have hstable : (prefixWord ++ tailWord_1310629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310629).length < 2 ^ (prefixWord ++ tailWord_1310629).sum := by decide
  have hdescent : baseEnd_1310629 < baseStart_1310629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310649 : List Nat := [1, 2, 1, 4, 2, 1, 2, 4, 1, 2, 3]
def baseStart_1310649 : Nat := 118140960795 + 1310649 * 2 ^ 59
def prefixEnd_1310649 : Nat := 4983230072969 + 3 ^ 40 * 1310649 * 2
def baseEnd_1310649 : Nat := 672992906334747813459941

theorem tailTrace_1310649 : CollatzResearch.WordTrace tailWord_1310649 prefixEnd_1310649 672992906334747813459941 := by
  unfold tailWord_1310649
  simp only [CollatzResearch.WordTrace]
  refine ⟨47803296228749988873415001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31868864152499992582276667 47803296228749988873415001)
  ·
    refine ⟨35852472171562491655061251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47803296228749988873415001 35852472171562491655061251)
    ·
      refine ⟨53778708257343737482591877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35852472171562491655061251 53778708257343737482591877)
      ·
        refine ⟨10083507798251950777985977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53778708257343737482591877 10083507798251950777985977)
        ·
          refine ⟨7562630848688963083489483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10083507798251950777985977 7562630848688963083489483)
          ·
            refine ⟨11343946273033444625234225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7562630848688963083489483 11343946273033444625234225)
            ·
              refine ⟨8507959704775083468925669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11343946273033444625234225 8507959704775083468925669)
              ·
                refine ⟨1595242444645328150423563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8507959704775083468925669 1595242444645328150423563)
                ·
                  refine ⟨2392863666967992225635345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1595242444645328150423563 2392863666967992225635345)
                  ·
                    refine ⟨1794647750225994169226509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2392863666967992225635345 1794647750225994169226509)
                    ·
                      refine ⟨672992906334747813459941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1794647750225994169226509 672992906334747813459941)
                      ·
                        rfl

theorem cell23_1310649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_1310649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310649 prefixEnd_1310649 := by exact prefixLift 1310649
  have htrace : WordTrace (prefixWord ++ tailWord_1310649) baseStart_1310649 baseEnd_1310649 := by
    simpa [prefixWord, tailWord_1310649, baseEnd_1310649] using wordTrace_append hprefix tailTrace_1310649
  have hstable : (prefixWord ++ tailWord_1310649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310649).length < 2 ^ (prefixWord ++ tailWord_1310649).sum := by decide
  have hdescent : baseEnd_1310649 < baseStart_1310649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310665 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 4, 7]
def baseStart_1310665 : Nat := 118140960795 + 1310665 * 2 ^ 59
def prefixEnd_1310665 : Nat := 4983230072969 + 3 ^ 40 * 1310665 * 2
def baseEnd_1310665 : Nat := 224333707341739916953289

theorem tailTrace_1310665 : CollatzResearch.WordTrace tailWord_1310665 prefixEnd_1310665 224333707341739916953289 := by
  unfold tailWord_1310665
  simp only [CollatzResearch.WordTrace]
  refine ⟨47803879796692023605997449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31869253197794682403998299 47803879796692023605997449)
  ·
    refine ⟨35852909847519017704498087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47803879796692023605997449 35852909847519017704498087)
    ·
      refine ⟨53779364771278526556747131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35852909847519017704498087 53779364771278526556747131)
      ·
        refine ⟨80669047156917789835120697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53779364771278526556747131 80669047156917789835120697)
        ·
          refine ⟨60501785367688342376340523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80669047156917789835120697 60501785367688342376340523)
          ·
            refine ⟨90752678051532513564510785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60501785367688342376340523 90752678051532513564510785)
            ·
              refine ⟨68064508538649385173383089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90752678051532513564510785 68064508538649385173383089)
              ·
                refine ⟨51048381403987038880037317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68064508538649385173383089 51048381403987038880037317)
                ·
                  refine ⟨9571571513247569790006997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51048381403987038880037317 9571571513247569790006997)
                  ·
                    refine ⟨224333707341739916953289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9571571513247569790006997 224333707341739916953289)
                    ·
                      rfl

theorem cell23_1310665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 7].length) (baseStart_1310665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310665 prefixEnd_1310665 := by exact prefixLift 1310665
  have htrace : WordTrace (prefixWord ++ tailWord_1310665) baseStart_1310665 baseEnd_1310665 := by
    simpa [prefixWord, tailWord_1310665, baseEnd_1310665] using wordTrace_append hprefix tailTrace_1310665
  have hstable : (prefixWord ++ tailWord_1310665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310665).length < 2 ^ (prefixWord ++ tailWord_1310665).sum := by decide
  have hdescent : baseEnd_1310665 < baseStart_1310665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310666 : List Nat := [3, 1, 2, 1, 2, 1, 6, 1, 1, 2, 3]
def baseStart_1310666 : Nat := 118140960795 + 1310666 * 2 ^ 59
def prefixEnd_1310666 : Nat := 4983230072969 + 3 ^ 40 * 1310666 * 2
def baseEnd_1310666 : Nat := 673001635505874246947363

theorem tailTrace_1310666 : CollatzResearch.WordTrace tailWord_1310666 prefixEnd_1310666 673001635505874246947363 := by
  unfold tailWord_1310666
  simp only [CollatzResearch.WordTrace]
  refine ⟨11950979067422100194195963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31869277513125600517855901 11950979067422100194195963)
  ·
    refine ⟨17926468601133150291293945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11950979067422100194195963 17926468601133150291293945)
    ·
      refine ⟨13444851450849862718470459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17926468601133150291293945 13444851450849862718470459)
      ·
        refine ⟨20167277176274794077705689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13444851450849862718470459 20167277176274794077705689)
        ·
          refine ⟨15125457882206095558279267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20167277176274794077705689 15125457882206095558279267)
          ·
            refine ⟨22688186823309143337418901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15125457882206095558279267 22688186823309143337418901)
            ·
              refine ⟨1063508757342616093941511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22688186823309143337418901 1063508757342616093941511)
              ·
                refine ⟨1595263136013924140912267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1063508757342616093941511 1595263136013924140912267)
                ·
                  refine ⟨2392894704020886211368401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1595263136013924140912267 2392894704020886211368401)
                  ·
                    refine ⟨1794671028015664658526301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2392894704020886211368401 1794671028015664658526301)
                    ·
                      refine ⟨673001635505874246947363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1794671028015664658526301 673001635505874246947363)
                      ·
                        rfl

theorem cell23_1310666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 1, 1, 2, 3].length) (baseStart_1310666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310666 prefixEnd_1310666 := by exact prefixLift 1310666
  have htrace : WordTrace (prefixWord ++ tailWord_1310666) baseStart_1310666 baseEnd_1310666 := by
    simpa [prefixWord, tailWord_1310666, baseEnd_1310666] using wordTrace_append hprefix tailTrace_1310666
  have hstable : (prefixWord ++ tailWord_1310666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310666).length < 2 ^ (prefixWord ++ tailWord_1310666).sum := by decide
  have hdescent : baseEnd_1310666 < baseStart_1310666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310679 : List Nat := [1, 1, 3, 2, 1, 1, 5, 1, 4, 1, 3]
def baseStart_1310679 : Nat := 118140960795 + 1310679 * 2 ^ 59
def prefixEnd_1310679 : Nat := 4983230072969 + 3 ^ 40 * 1310679 * 2
def baseEnd_1310679 : Nat := 673008310754382696084803

theorem tailTrace_1310679 : CollatzResearch.WordTrace tailWord_1310679 prefixEnd_1310679 673008310754382696084803 := by
  unfold tailWord_1310679
  simp only [CollatzResearch.WordTrace]
  refine ⟨47804390418641303997007091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31869593612427535998004727 47804390418641303997007091)
  ·
    refine ⟨71706585627961955995510637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47804390418641303997007091 71706585627961955995510637)
    ·
      refine ⟨26889969610485733498316489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71706585627961955995510637 26889969610485733498316489)
      ·
        refine ⟨20167477207864300123737367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26889969610485733498316489 20167477207864300123737367)
        ·
          refine ⟨30251215811796450185606051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20167477207864300123737367 30251215811796450185606051)
          ·
            refine ⟨45376823717694675278409077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30251215811796450185606051 45376823717694675278409077)
            ·
              refine ⟨4254077223533875807350851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45376823717694675278409077 4254077223533875807350851)
              ·
                refine ⟨6381115835300813711026277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4254077223533875807350851 6381115835300813711026277)
                ·
                  refine ⟨1196459219118902570817427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6381115835300813711026277 1196459219118902570817427)
                  ·
                    refine ⟨1794688828678353856226141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1196459219118902570817427 1794688828678353856226141)
                    ·
                      refine ⟨673008310754382696084803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1794688828678353856226141 673008310754382696084803)
                      ·
                        rfl

theorem cell23_1310679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 4, 1, 3].length) (baseStart_1310679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310679 prefixEnd_1310679 := by exact prefixLift 1310679
  have htrace : WordTrace (prefixWord ++ tailWord_1310679) baseStart_1310679 baseEnd_1310679 := by
    simpa [prefixWord, tailWord_1310679, baseEnd_1310679] using wordTrace_append hprefix tailTrace_1310679
  have hstable : (prefixWord ++ tailWord_1310679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310679).length < 2 ^ (prefixWord ++ tailWord_1310679).sum := by decide
  have hdescent : baseEnd_1310679 < baseStart_1310679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310689 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 5, 3, 2]
def baseStart_1310689 : Nat := 118140960795 + 1310689 * 2 ^ 59
def prefixEnd_1310689 : Nat := 4983230072969 + 3 ^ 40 * 1310689 * 2
def baseEnd_1310689 : Nat := 673013445560927656959757

theorem tailTrace_1310689 : CollatzResearch.WordTrace tailWord_1310689 prefixEnd_1310689 673013445560927656959757 := by
  unfold tailWord_1310689
  simp only [CollatzResearch.WordTrace]
  refine ⟨47804755148605075704871121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31869836765736717136580747 47804755148605075704871121)
  ·
    refine ⟨35853566361453806778653341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47804755148605075704871121 35853566361453806778653341)
    ·
      refine ⟨13445087385545177541995003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35853566361453806778653341 13445087385545177541995003)
      ·
        refine ⟨20167631078317766312992505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13445087385545177541995003 20167631078317766312992505)
        ·
          refine ⟨15125723308738324734744379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20167631078317766312992505 15125723308738324734744379)
          ·
            refine ⟨22688584963107487102116569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15125723308738324734744379 22688584963107487102116569)
            ·
              refine ⟨17016438722330615326587427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22688584963107487102116569 17016438722330615326587427)
              ·
                refine ⟨25524658083495922989881141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17016438722330615326587427 25524658083495922989881141)
                ·
                  refine ⟨2392936695327742780301357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25524658083495922989881141 2392936695327742780301357)
                  ·
                    refine ⟨897351260747903542613009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2392936695327742780301357 897351260747903542613009)
                    ·
                      refine ⟨673013445560927656959757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 897351260747903542613009 673013445560927656959757)
                      ·
                        rfl

theorem cell23_1310689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 5, 3, 2].length) (baseStart_1310689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310689 prefixEnd_1310689 := by exact prefixLift 1310689
  have htrace : WordTrace (prefixWord ++ tailWord_1310689) baseStart_1310689 baseEnd_1310689 := by
    simpa [prefixWord, tailWord_1310689, baseEnd_1310689] using wordTrace_append hprefix tailTrace_1310689
  have hstable : (prefixWord ++ tailWord_1310689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310689).length < 2 ^ (prefixWord ++ tailWord_1310689).sum := by decide
  have hdescent : baseEnd_1310689 < baseStart_1310689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310690 : List Nat := [3, 3, 3, 1, 2, 1, 3, 1, 2, 4]
def baseStart_1310690 : Nat := 118140960795 + 1310690 * 2 ^ 59
def prefixEnd_1310690 : Nat := 4983230072969 + 3 ^ 40 * 1310690 * 2
def baseEnd_1310690 : Nat := 224337986347194051015751

theorem tailTrace_1310690 : CollatzResearch.WordTrace tailWord_1310690 prefixEnd_1310690 224337986347194051015751 := by
  unfold tailWord_1310690
  simp only [CollatzResearch.WordTrace]
  refine ⟨11951197905400363218914381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31869861081067635250438349 11951197905400363218914381)
  ·
    refine ⟨4481699214525136207092893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11951197905400363218914381 4481699214525136207092893)
    ·
      refine ⟨1680637205446926077659835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4481699214525136207092893 1680637205446926077659835)
      ·
        refine ⟨2520955808170389116489753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1680637205446926077659835 2520955808170389116489753)
        ·
          refine ⟨1890716856127791837367315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2520955808170389116489753 1890716856127791837367315)
          ·
            refine ⟨2836075284191687756050973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1890716856127791837367315 2836075284191687756050973)
            ·
              refine ⟨1063528231571882908519115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2836075284191687756050973 1063528231571882908519115)
              ·
                refine ⟨1595292347357824362778673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1063528231571882908519115 1595292347357824362778673)
                ·
                  refine ⟨1196469260518368272084005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1595292347357824362778673 1196469260518368272084005)
                  ·
                    refine ⟨224337986347194051015751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1196469260518368272084005 224337986347194051015751)
                    ·
                      rfl

theorem cell23_1310690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_1310690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310690 prefixEnd_1310690 := by exact prefixLift 1310690
  have htrace : WordTrace (prefixWord ++ tailWord_1310690) baseStart_1310690 baseEnd_1310690 := by
    simpa [prefixWord, tailWord_1310690, baseEnd_1310690] using wordTrace_append hprefix tailTrace_1310690
  have hstable : (prefixWord ++ tailWord_1310690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310690).length < 2 ^ (prefixWord ++ tailWord_1310690).sum := by decide
  have hdescent : baseEnd_1310690 < baseStart_1310690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310719 : List Nat := [1, 1, 2, 2, 1, 2, 1, 6, 1, 4, 2]
def baseStart_1310719 : Nat := 118140960795 + 1310719 * 2 ^ 59
def prefixEnd_1310719 : Nat := 4983230072969 + 3 ^ 40 * 1310719 * 2
def baseEnd_1310719 : Nat := 673028849980562539584619

theorem tailTrace_1310719 : CollatzResearch.WordTrace tailWord_1310719 prefixEnd_1310719 673028849980562539584619 := by
  unfold tailWord_1310719
  simp only [CollatzResearch.WordTrace]
  refine ⟨47805849338496390828463211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31870566225664260552308807 47805849338496390828463211)
  ·
    refine ⟨71708774007744586242694817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47805849338496390828463211 71708774007744586242694817)
    ·
      refine ⟨53781580505808439682021113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71708774007744586242694817 53781580505808439682021113)
      ·
        refine ⟨40336185379356329761515835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53781580505808439682021113 40336185379356329761515835)
        ·
          refine ⟨60504278069034494642273753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40336185379356329761515835 60504278069034494642273753)
          ·
            refine ⟨45378208551775870981705315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60504278069034494642273753 45378208551775870981705315)
            ·
              refine ⟨68067312827663806472557973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45378208551775870981705315 68067312827663806472557973)
              ·
                refine ⟨3190655288796740928401155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68067312827663806472557973 3190655288796740928401155)
                ·
                  refine ⟨4785982933195111392601733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3190655288796740928401155 4785982933195111392601733)
                  ·
                    refine ⟨897371799974083386112825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4785982933195111392601733 897371799974083386112825)
                    ·
                      refine ⟨673028849980562539584619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 897371799974083386112825 673028849980562539584619)
                      ·
                        rfl

theorem cell23_1310719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 4, 2].length) (baseStart_1310719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310719 prefixEnd_1310719 := by exact prefixLift 1310719
  have htrace : WordTrace (prefixWord ++ tailWord_1310719) baseStart_1310719 baseEnd_1310719 := by
    simpa [prefixWord, tailWord_1310719, baseEnd_1310719] using wordTrace_append hprefix tailTrace_1310719
  have hstable : (prefixWord ++ tailWord_1310719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310719).length < 2 ^ (prefixWord ++ tailWord_1310719).sum := by decide
  have hdescent : baseEnd_1310719 < baseStart_1310719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310819 : List Nat := [1, 1, 1, 5, 1, 1, 3, 1, 5, 4]
def baseStart_1310819 : Nat := 118140960795 + 1310819 * 2 ^ 59
def prefixEnd_1310819 : Nat := 4983230072969 + 3 ^ 40 * 1310819 * 2
def baseEnd_1310819 : Nat := 224360066015337382778053

theorem tailTrace_1310819 : CollatzResearch.WordTrace tailWord_1310819 prefixEnd_1310819 224360066015337382778053 := by
  unfold tailWord_1310819
  simp only [CollatzResearch.WordTrace]
  refine ⟨47809496638134107907103511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31872997758756071938069007 47809496638134107907103511)
  ·
    refine ⟨71714244957201161860655267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47809496638134107907103511 71714244957201161860655267)
    ·
      refine ⟨107571367435801742790982901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71714244957201161860655267 107571367435801742790982901)
      ·
        refine ⟨10084815697106413386654647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 107571367435801742790982901 10084815697106413386654647)
        ·
          refine ⟨15127223545659620079981971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10084815697106413386654647 15127223545659620079981971)
          ·
            refine ⟨22690835318489430119972957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15127223545659620079981971 22690835318489430119972957)
            ·
              refine ⟨8509063244433536294989859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22690835318489430119972957 8509063244433536294989859)
              ·
                refine ⟨12763594866650304442484789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8509063244433536294989859 12763594866650304442484789)
                ·
                  refine ⟨1196587018748466041482949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12763594866650304442484789 1196587018748466041482949)
                  ·
                    refine ⟨224360066015337382778053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1196587018748466041482949 224360066015337382778053)
                    ·
                      rfl

theorem cell23_1310819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 5, 4].length) (baseStart_1310819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310819 prefixEnd_1310819 := by exact prefixLift 1310819
  have htrace : WordTrace (prefixWord ++ tailWord_1310819) baseStart_1310819 baseEnd_1310819 := by
    simpa [prefixWord, tailWord_1310819, baseEnd_1310819] using wordTrace_append hprefix tailTrace_1310819
  have hstable : (prefixWord ++ tailWord_1310819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310819).length < 2 ^ (prefixWord ++ tailWord_1310819).sum := by decide
  have hdescent : baseEnd_1310819 < baseStart_1310819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310826 : List Nat := [3, 1, 3, 2, 3, 1, 1, 1, 1, 3, 4]
def baseStart_1310826 : Nat := 118140960795 + 1310826 * 2 ^ 59
def prefixEnd_1310826 : Nat := 4983230072969 + 3 ^ 40 * 1310826 * 2
def baseEnd_1310826 : Nat := 673083792410593620946627

theorem tailTrace_1310826 : CollatzResearch.WordTrace tailWord_1310826 prefixEnd_1310826 673083792410593620946627 := by
  unfold tailWord_1310826
  simp only [CollatzResearch.WordTrace]
  refine ⟨11952437987277187025652083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31873167966072498735072221 11952437987277187025652083)
  ·
    refine ⟨17928656980915780538478125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11952437987277187025652083 17928656980915780538478125)
    ·
      refine ⟨6723246367843417701929297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17928656980915780538478125 6723246367843417701929297)
      ·
        refine ⟨5042434775882563276446973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6723246367843417701929297 5042434775882563276446973)
        ·
          refine ⟨1890913040955961228667615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5042434775882563276446973 1890913040955961228667615)
          ·
            refine ⟨2836369561433941843001423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1890913040955961228667615 2836369561433941843001423)
            ·
              refine ⟨4254554342150912764502135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2836369561433941843001423 4254554342150912764502135)
              ·
                refine ⟨6381831513226369146753203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4254554342150912764502135 6381831513226369146753203)
                ·
                  refine ⟨9572747269839553720129805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6381831513226369146753203 9572747269839553720129805)
                  ·
                    refine ⟨3589780226189832645048677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9572747269839553720129805 3589780226189832645048677)
                    ·
                      refine ⟨673083792410593620946627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3589780226189832645048677 673083792410593620946627)
                      ·
                        rfl

theorem cell23_1310826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_1310826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310826 prefixEnd_1310826 := by exact prefixLift 1310826
  have htrace : WordTrace (prefixWord ++ tailWord_1310826) baseStart_1310826 baseEnd_1310826 := by
    simpa [prefixWord, tailWord_1310826, baseEnd_1310826] using wordTrace_append hprefix tailTrace_1310826
  have hstable : (prefixWord ++ tailWord_1310826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310826).length < 2 ^ (prefixWord ++ tailWord_1310826).sum := by decide
  have hdescent : baseEnd_1310826 < baseStart_1310826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310842 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7]
def baseStart_1310842 : Nat := 118140960795 + 1310842 * 2 ^ 59
def prefixEnd_1310842 : Nat := 4983230072969 + 3 ^ 40 * 1310842 * 2
def baseEnd_1310842 : Nat := 673092008101065558346553

theorem tailTrace_1310842 : CollatzResearch.WordTrace tailWord_1310842 prefixEnd_1310842 673092008101065558346553 := by
  unfold tailWord_1310842
  simp only [CollatzResearch.WordTrace]
  refine ⟨11952583879262695708797695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31873557011367188556793853 11952583879262695708797695)
  ·
    refine ⟨17928875818894043563196543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11952583879262695708797695 17928875818894043563196543)
    ·
      refine ⟨26893313728341065344794815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17928875818894043563196543 26893313728341065344794815)
      ·
        refine ⟨40339970592511598017192223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26893313728341065344794815 40339970592511598017192223)
        ·
          refine ⟨60509955888767397025788335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40339970592511598017192223 60509955888767397025788335)
          ·
            refine ⟨90764933833151095538682503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60509955888767397025788335 90764933833151095538682503)
            ·
              refine ⟨136147400749726643308023755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90764933833151095538682503 136147400749726643308023755)
              ·
                refine ⟨204221101124589964962035633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136147400749726643308023755 204221101124589964962035633)
                ·
                  refine ⟨153165825843442473721526725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204221101124589964962035633 153165825843442473721526725)
                  ·
                    refine ⟨28718592345645463822786261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 153165825843442473721526725 28718592345645463822786261)
                    ·
                      refine ⟨673092008101065558346553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 28718592345645463822786261 673092008101065558346553)
                      ·
                        rfl

theorem cell23_1310842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_1310842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310842 prefixEnd_1310842 := by exact prefixLift 1310842
  have htrace : WordTrace (prefixWord ++ tailWord_1310842) baseStart_1310842 baseEnd_1310842 := by
    simpa [prefixWord, tailWord_1310842, baseEnd_1310842] using wordTrace_append hprefix tailTrace_1310842
  have hstable : (prefixWord ++ tailWord_1310842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310842).length < 2 ^ (prefixWord ++ tailWord_1310842).sum := by decide
  have hdescent : baseEnd_1310842 < baseStart_1310842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310853 : List Nat := [1, 3, 1, 1, 5, 1, 2, 4, 1, 4]
def baseStart_1310853 : Nat := 118140960795 + 1310853 * 2 ^ 59
def prefixEnd_1310853 : Nat := 4983230072969 + 3 ^ 40 * 1310853 * 2
def baseEnd_1310853 : Nat := 224365885462755005103001

theorem tailTrace_1310853 : CollatzResearch.WordTrace tailWord_1310853 prefixEnd_1310853 224365885462755005103001 := by
  unfold tailWord_1310853
  simp only [CollatzResearch.WordTrace]
  refine ⟨47810736720010931713841213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31873824480007287809227475 47810736720010931713841213)
  ·
    refine ⟨17929026270004099392690455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47810736720010931713841213 17929026270004099392690455)
    ·
      refine ⟨26893539405006149089035683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17929026270004099392690455 26893539405006149089035683)
      ·
        refine ⟨40340309107509223633553525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26893539405006149089035683 40340309107509223633553525)
        ·
          refine ⟨3781903978828989715645643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40340309107509223633553525 3781903978828989715645643)
          ·
            refine ⟨5672855968243484573468465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3781903978828989715645643 5672855968243484573468465)
            ·
              refine ⟨4254641976182613430101349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5672855968243484573468465 4254641976182613430101349)
              ·
                refine ⟨797745370534240018144003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4254641976182613430101349 797745370534240018144003)
                ·
                  refine ⟨1196618055801360027216005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 797745370534240018144003 1196618055801360027216005)
                  ·
                    refine ⟨224365885462755005103001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1196618055801360027216005 224365885462755005103001)
                    ·
                      rfl

theorem cell23_1310853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 4, 1, 4].length) (baseStart_1310853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310853 prefixEnd_1310853 := by exact prefixLift 1310853
  have htrace : WordTrace (prefixWord ++ tailWord_1310853) baseStart_1310853 baseEnd_1310853 := by
    simpa [prefixWord, tailWord_1310853, baseEnd_1310853] using wordTrace_append hprefix tailTrace_1310853
  have hstable : (prefixWord ++ tailWord_1310853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310853).length < 2 ^ (prefixWord ++ tailWord_1310853).sum := by decide
  have hdescent : baseEnd_1310853 < baseStart_1310853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310887 : List Nat := [1, 1, 6, 2, 2, 2, 1, 3, 1, 4]
def baseStart_1310887 : Nat := 118140960795 + 1310887 * 2 ^ 59
def prefixEnd_1310887 : Nat := 4983230072969 + 3 ^ 40 * 1310887 * 2
def baseEnd_1310887 : Nat := 224371704910172627427949

theorem tailTrace_1310887 : CollatzResearch.WordTrace tailWord_1310887 prefixEnd_1310887 224371704910172627427949 := by
  unfold tailWord_1310887
  simp only [CollatzResearch.WordTrace]
  refine ⟨47811976801887755520578915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31874651201258503680385943 47811976801887755520578915)
  ·
    refine ⟨71717965202831633280868373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47811976801887755520578915 71717965202831633280868373)
    ·
      refine ⟨3361779618882732810040705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 71717965202831633280868373 3361779618882732810040705)
      ·
        refine ⟨2521334714162049607530529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3361779618882732810040705 2521334714162049607530529)
        ·
          refine ⟨1891001035621537205647897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2521334714162049607530529 1891001035621537205647897)
          ·
            refine ⟨1418250776716152904235923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1891001035621537205647897 1418250776716152904235923)
            ·
              refine ⟨2127376165074229356353885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1418250776716152904235923 2127376165074229356353885)
              ·
                refine ⟨797766061902836008632707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2127376165074229356353885 797766061902836008632707)
                ·
                  refine ⟨1196649092854254012949061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 797766061902836008632707 1196649092854254012949061)
                  ·
                    refine ⟨224371704910172627427949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1196649092854254012949061 224371704910172627427949)
                    ·
                      rfl

theorem cell23_1310887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_1310887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310887 prefixEnd_1310887 := by exact prefixLift 1310887
  have htrace : WordTrace (prefixWord ++ tailWord_1310887) baseStart_1310887 baseEnd_1310887 := by
    simpa [prefixWord, tailWord_1310887, baseEnd_1310887] using wordTrace_append hprefix tailTrace_1310887
  have hstable : (prefixWord ++ tailWord_1310887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310887).length < 2 ^ (prefixWord ++ tailWord_1310887).sum := by decide
  have hdescent : baseEnd_1310887 < baseStart_1310887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310899 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 5, 1, 4]
def baseStart_1310899 : Nat := 118140960795 + 1310899 * 2 ^ 59
def prefixEnd_1310899 : Nat := 4983230072969 + 3 ^ 40 * 1310899 * 2
def baseEnd_1310899 : Nat := 673121276498371835333791

theorem tailTrace_1310899 : CollatzResearch.WordTrace tailWord_1310899 prefixEnd_1310899 673121276498371835333791 := by
  unfold tailWord_1310899
  simp only [CollatzResearch.WordTrace]
  refine ⟨47812414477844281570015751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31874942985229521046677167 47812414477844281570015751)
  ·
    refine ⟨71718621716766422355023627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47812414477844281570015751 71718621716766422355023627)
    ·
      refine ⟨107577932575149633532535441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71718621716766422355023627 107577932575149633532535441)
      ·
        refine ⟨80683449431362225149401581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107577932575149633532535441 80683449431362225149401581)
        ·
          refine ⟨30256293536760834431025593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80683449431362225149401581 30256293536760834431025593)
          ·
            refine ⟨22692220152570625823269195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30256293536760834431025593 22692220152570625823269195)
            ·
              refine ⟨34038330228855938734903793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22692220152570625823269195 34038330228855938734903793)
              ·
                refine ⟨25528747671641954051177845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34038330228855938734903793 25528747671641954051177845)
                ·
                  refine ⟨2393320094216433192297923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25528747671641954051177845 2393320094216433192297923)
                  ·
                    refine ⟨3589980141324649788446885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2393320094216433192297923 3589980141324649788446885)
                    ·
                      refine ⟨673121276498371835333791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3589980141324649788446885 673121276498371835333791)
                      ·
                        rfl

theorem cell23_1310899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 5, 1, 4].length) (baseStart_1310899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310899 prefixEnd_1310899 := by exact prefixLift 1310899
  have htrace : WordTrace (prefixWord ++ tailWord_1310899) baseStart_1310899 baseEnd_1310899 := by
    simpa [prefixWord, tailWord_1310899, baseEnd_1310899] using wordTrace_append hprefix tailTrace_1310899
  have hstable : (prefixWord ++ tailWord_1310899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310899).length < 2 ^ (prefixWord ++ tailWord_1310899).sum := by decide
  have hdescent : baseEnd_1310899 < baseStart_1310899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310903 : List Nat := [1, 1, 3, 1, 4, 3, 1, 2, 2, 3, 2]
def baseStart_1310903 : Nat := 118140960795 + 1310903 * 2 ^ 59
def prefixEnd_1310903 : Nat := 4983230072969 + 3 ^ 40 * 1310903 * 2
def baseEnd_1310903 : Nat := 673123330420989819683773

theorem tailTrace_1310903 : CollatzResearch.WordTrace tailWord_1310903 prefixEnd_1310903 673123330420989819683773 := by
  unfold tailWord_1310903
  simp only [CollatzResearch.WordTrace]
  refine ⟨47812560369829790253161363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31875040246553193502107575 47812560369829790253161363)
  ·
    refine ⟨71718840554744685379742045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47812560369829790253161363 71718840554744685379742045)
    ·
      refine ⟨26894565208029257017403267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71718840554744685379742045 26894565208029257017403267)
      ·
        refine ⟨40341847812043885526104901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26894565208029257017403267 40341847812043885526104901)
        ·
          refine ⟨7564096464758228536144669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40341847812043885526104901 7564096464758228536144669)
          ·
            refine ⟨2836536174284335701054251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7564096464758228536144669 2836536174284335701054251)
            ·
              refine ⟨4254804261426503551581377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2836536174284335701054251 4254804261426503551581377)
              ·
                refine ⟨3191103196069877663686033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4254804261426503551581377 3191103196069877663686033)
                ·
                  refine ⟨2393327397052408247764525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3191103196069877663686033 2393327397052408247764525)
                  ·
                    refine ⟨897497773894653092911697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2393327397052408247764525 897497773894653092911697)
                    ·
                      refine ⟨673123330420989819683773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 897497773894653092911697 673123330420989819683773)
                      ·
                        rfl

theorem cell23_1310903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 2, 3, 2].length) (baseStart_1310903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310903 prefixEnd_1310903 := by exact prefixLift 1310903
  have htrace : WordTrace (prefixWord ++ tailWord_1310903) baseStart_1310903 baseEnd_1310903 := by
    simpa [prefixWord, tailWord_1310903, baseEnd_1310903] using wordTrace_append hprefix tailTrace_1310903
  have hstable : (prefixWord ++ tailWord_1310903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310903).length < 2 ^ (prefixWord ++ tailWord_1310903).sum := by decide
  have hdescent : baseEnd_1310903 < baseStart_1310903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310919 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 1, 8, 3]
def baseStart_1310919 : Nat := 118140960795 + 1310919 * 2 ^ 59
def prefixEnd_1310919 : Nat := 4983230072969 + 3 ^ 40 * 1310919 * 2
def baseEnd_1310919 : Nat := 673131546111461757083699

theorem tailTrace_1310919 : CollatzResearch.WordTrace tailWord_1310919 prefixEnd_1310919 673131546111461757083699 := by
  unfold tailWord_1310919
  simp only [CollatzResearch.WordTrace]
  refine ⟨47813143937771824985743811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31875429291847883323829207 47813143937771824985743811)
  ·
    refine ⟨71719715906657737478615717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47813143937771824985743811 71719715906657737478615717)
    ·
      refine ⟨13447446732498325777240447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71719715906657737478615717 13447446732498325777240447)
      ·
        refine ⟨20171170098747488665860671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13447446732498325777240447 20171170098747488665860671)
        ·
          refine ⟨30256755148121232998791007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20171170098747488665860671 30256755148121232998791007)
          ·
            refine ⟨45385132722181849498186511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30256755148121232998791007 45385132722181849498186511)
            ·
              refine ⟨68077699083272774247279767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45385132722181849498186511 68077699083272774247279767)
              ·
                refine ⟨102116548624909161370919651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68077699083272774247279767 102116548624909161370919651)
                ·
                  refine ⟨153174822937363742056379477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102116548624909161370919651 153174822937363742056379477)
                  ·
                    refine ⟨1795017456297231352223197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 153174822937363742056379477 1795017456297231352223197)
                    ·
                      refine ⟨673131546111461757083699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1795017456297231352223197 673131546111461757083699)
                      ·
                        rfl

theorem cell23_1310919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 8, 3].length) (baseStart_1310919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310919 prefixEnd_1310919 := by exact prefixLift 1310919
  have htrace : WordTrace (prefixWord ++ tailWord_1310919) baseStart_1310919 baseEnd_1310919 := by
    simpa [prefixWord, tailWord_1310919, baseEnd_1310919] using wordTrace_append hprefix tailTrace_1310919
  have hstable : (prefixWord ++ tailWord_1310919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310919).length < 2 ^ (prefixWord ++ tailWord_1310919).sum := by decide
  have hdescent : baseEnd_1310919 < baseStart_1310919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310929 : List Nat := [1, 2, 2, 1, 2, 2, 4, 1, 1, 1, 6]
def baseStart_1310929 : Nat := 118140960795 + 1310929 * 2 ^ 59
def prefixEnd_1310929 : Nat := 4983230072969 + 3 ^ 40 * 1310929 * 2
def baseEnd_1310929 : Nat := 673136680918006717958653

theorem tailTrace_1310929 : CollatzResearch.WordTrace tailWord_1310929 prefixEnd_1310929 673136680918006717958653 := by
  unfold tailWord_1310929
  simp only [CollatzResearch.WordTrace]
  refine ⟨47813508667735596693607841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31875672445157064462405227 47813508667735596693607841)
  ·
    refine ⟨35860131500801697520205881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47813508667735596693607841 35860131500801697520205881)
    ·
      refine ⟨26895098625601273140154411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35860131500801697520205881 26895098625601273140154411)
      ·
        refine ⟨40342647938401909710231617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26895098625601273140154411 40342647938401909710231617)
        ·
          refine ⟨30256985953801432282673713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40342647938401909710231617 30256985953801432282673713)
          ·
            refine ⟨22692739465351074212005285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30256985953801432282673713 22692739465351074212005285)
            ·
              refine ⟨4254888649753326414750991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22692739465351074212005285 4254888649753326414750991)
              ·
                refine ⟨6382332974629989622126487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4254888649753326414750991 6382332974629989622126487)
                ·
                  refine ⟨9573499461944984433189731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6382332974629989622126487 9573499461944984433189731)
                  ·
                    refine ⟨14360249192917476649784597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9573499461944984433189731 14360249192917476649784597)
                    ·
                      refine ⟨673136680918006717958653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14360249192917476649784597 673136680918006717958653)
                      ·
                        rfl

theorem cell23_1310929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 1, 6].length) (baseStart_1310929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310929 prefixEnd_1310929 := by exact prefixLift 1310929
  have htrace : WordTrace (prefixWord ++ tailWord_1310929) baseStart_1310929 baseEnd_1310929 := by
    simpa [prefixWord, tailWord_1310929, baseEnd_1310929] using wordTrace_append hprefix tailTrace_1310929
  have hstable : (prefixWord ++ tailWord_1310929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310929).length < 2 ^ (prefixWord ++ tailWord_1310929).sum := by decide
  have hdescent : baseEnd_1310929 < baseStart_1310929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310933 : List Nat := [1, 3, 2, 4, 2, 1, 1, 1, 3, 1, 4]
def baseStart_1310933 : Nat := 118140960795 + 1310933 * 2 ^ 59
def prefixEnd_1310933 : Nat := 4983230072969 + 3 ^ 40 * 1310933 * 2
def baseEnd_1310933 : Nat := 673138734840624702308635

theorem tailTrace_1310933 : CollatzResearch.WordTrace tailWord_1310933 prefixEnd_1310933 673138734840624702308635 := by
  unfold tailWord_1310933
  simp only [CollatzResearch.WordTrace]
  refine ⟨47813654559721105376753453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31875769706480736917835635 47813654559721105376753453)
  ·
    refine ⟨17930120459895414516282545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47813654559721105376753453 17930120459895414516282545)
    ·
      refine ⟨13447590344921560887211909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17930120459895414516282545 13447590344921560887211909)
      ·
        refine ⟨2521423189672792666352233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13447590344921560887211909 2521423189672792666352233)
        ·
          refine ⟨1891067392254594499764175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2521423189672792666352233 1891067392254594499764175)
          ·
            refine ⟨2836601088381891749646263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1891067392254594499764175 2836601088381891749646263)
            ·
              refine ⟨4254901632572837624469395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2836601088381891749646263 4254901632572837624469395)
              ·
                refine ⟨6382352448859256436704093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4254901632572837624469395 6382352448859256436704093)
                ·
                  refine ⟨2393382168322221163764035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6382352448859256436704093 2393382168322221163764035)
                  ·
                    refine ⟨3590073252483331745646053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2393382168322221163764035 3590073252483331745646053)
                    ·
                      refine ⟨673138734840624702308635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3590073252483331745646053 673138734840624702308635)
                      ·
                        rfl

theorem cell23_1310933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_1310933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310933 prefixEnd_1310933 := by exact prefixLift 1310933
  have htrace : WordTrace (prefixWord ++ tailWord_1310933) baseStart_1310933 baseEnd_1310933 := by
    simpa [prefixWord, tailWord_1310933, baseEnd_1310933] using wordTrace_append hprefix tailTrace_1310933
  have hstable : (prefixWord ++ tailWord_1310933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310933).length < 2 ^ (prefixWord ++ tailWord_1310933).sum := by decide
  have hdescent : baseEnd_1310933 < baseStart_1310933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310993 : List Nat := [1, 2, 2, 1, 1, 5, 2, 1, 3, 3, 2]
def baseStart_1310993 : Nat := 118140960795 + 1310993 * 2 ^ 59
def prefixEnd_1310993 : Nat := 4983230072969 + 3 ^ 40 * 1310993 * 2
def baseEnd_1310993 : Nat := 673169543679894467558359

theorem tailTrace_1310993 : CollatzResearch.WordTrace tailWord_1310993 prefixEnd_1310993 673169543679894467558359 := by
  unfold tailWord_1310993
  simp only [CollatzResearch.WordTrace]
  refine ⟨47815842939503735623937633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31877228626335823749291755 47815842939503735623937633)
  ·
    refine ⟨35861882204627801717953225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47815842939503735623937633 35861882204627801717953225)
    ·
      refine ⟨26896411653470851288464919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35861882204627801717953225 26896411653470851288464919)
      ·
        refine ⟨40344617480206276932697379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26896411653470851288464919 40344617480206276932697379)
        ·
          refine ⟨60516926220309415399046069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40344617480206276932697379 60516926220309415399046069)
          ·
            refine ⟨5673461833154007693660569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60516926220309415399046069 5673461833154007693660569)
            ·
              refine ⟨4255096374865505770245427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5673461833154007693660569 4255096374865505770245427)
              ·
                refine ⟨6382644562298258655368141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4255096374865505770245427 6382644562298258655368141)
                ·
                  refine ⟨2393491710861846995763053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6382644562298258655368141 2393491710861846995763053)
                  ·
                    refine ⟨897559391573192623411145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2393491710861846995763053 897559391573192623411145)
                    ·
                      refine ⟨673169543679894467558359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 897559391573192623411145 673169543679894467558359)
                      ·
                        rfl

theorem cell23_1310993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 3, 2].length) (baseStart_1310993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1310993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1310993 prefixEnd_1310993 := by exact prefixLift 1310993
  have htrace : WordTrace (prefixWord ++ tailWord_1310993) baseStart_1310993 baseEnd_1310993 := by
    simpa [prefixWord, tailWord_1310993, baseEnd_1310993] using wordTrace_append hprefix tailTrace_1310993
  have hstable : (prefixWord ++ tailWord_1310993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310993).length < 2 ^ (prefixWord ++ tailWord_1310993).sum := by decide
  have hdescent : baseEnd_1310993 < baseStart_1310993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311036 : List Nat := [2, 2, 2, 2, 1, 2, 1, 3, 2, 2, 4]
def baseStart_1311036 : Nat := 118140960795 + 1311036 * 2 ^ 59
def prefixEnd_1311036 : Nat := 4983230072969 + 3 ^ 40 * 1311036 * 2
def baseEnd_1311036 : Nat := 673191623348037799320661

theorem tailTrace_1311036 : CollatzResearch.WordTrace tailWord_1311036 prefixEnd_1311036 673191623348037799320661 := by
  unfold tailWord_1311036
  simp only [CollatzResearch.WordTrace]
  refine ⟨23908705639173976983876481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31878274185565302645168641 23908705639173976983876481)
  ·
    refine ⟨17931529229380482737907361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23908705639173976983876481 17931529229380482737907361)
    ·
      refine ⟨13448646922035362053430521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17931529229380482737907361 13448646922035362053430521)
      ·
        refine ⟨10086485191526521540072891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13448646922035362053430521 10086485191526521540072891)
        ·
          refine ⟨15129727787289782310109337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10086485191526521540072891 15129727787289782310109337)
          ·
            refine ⟨11347295840467336732582003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15129727787289782310109337 11347295840467336732582003)
            ·
              refine ⟨17020943760701005098873005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11347295840467336732582003 17020943760701005098873005)
              ·
                refine ⟨6382853910262876912077377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17020943760701005098873005 6382853910262876912077377)
                ·
                  refine ⟨4787140432697157684058033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6382853910262876912077377 4787140432697157684058033)
                  ·
                    refine ⟨3590355324522868263043525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4787140432697157684058033 3590355324522868263043525)
                    ·
                      refine ⟨673191623348037799320661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3590355324522868263043525 673191623348037799320661)
                      ·
                        rfl

theorem cell23_1311036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_1311036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1311036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1311036 prefixEnd_1311036 := by exact prefixLift 1311036
  have htrace : WordTrace (prefixWord ++ tailWord_1311036) baseStart_1311036 baseEnd_1311036 := by
    simpa [prefixWord, tailWord_1311036, baseEnd_1311036] using wordTrace_append hprefix tailTrace_1311036
  have hstable : (prefixWord ++ tailWord_1311036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311036).length < 2 ^ (prefixWord ++ tailWord_1311036).sum := by decide
  have hdescent : baseEnd_1311036 < baseStart_1311036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311044 : List Nat := [2, 3, 4, 1, 2, 1, 2, 2, 1, 3, 2]
def baseStart_1311044 : Nat := 118140960795 + 1311044 * 2 ^ 59
def prefixEnd_1311044 : Nat := 4983230072969 + 3 ^ 40 * 1311044 * 2
def baseEnd_1311044 : Nat := 673195731193273768020625

theorem tailTrace_1311044 : CollatzResearch.WordTrace tailWord_1311044 prefixEnd_1311044 673195731193273768020625 := by
  unfold tailWord_1311044
  simp only [CollatzResearch.WordTrace]
  refine ⟨23908851531159485667022093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31878468708212647556029457 23908851531159485667022093)
  ·
    refine ⟨8965819324184807125133285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23908851531159485667022093 8965819324184807125133285)
    ·
      refine ⟨1681091123284651335962491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8965819324184807125133285 1681091123284651335962491)
      ·
        refine ⟨2521636684926977003943737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1681091123284651335962491 2521636684926977003943737)
        ·
          refine ⟨1891227513695232752957803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2521636684926977003943737 1891227513695232752957803)
          ·
            refine ⟨2836841270542849129436705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1891227513695232752957803 2836841270542849129436705)
            ·
              refine ⟨2127630952907136847077529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2836841270542849129436705 2127630952907136847077529)
              ·
                refine ⟨1595723214680352635308147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2127630952907136847077529 1595723214680352635308147)
                ·
                  refine ⟨2393584822020528952962221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1595723214680352635308147 2393584822020528952962221)
                  ·
                    refine ⟨897594308257698357360833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2393584822020528952962221 897594308257698357360833)
                    ·
                      refine ⟨673195731193273768020625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 897594308257698357360833 673195731193273768020625)
                      ·
                        rfl

theorem cell23_1311044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_1311044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1311044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1311044 prefixEnd_1311044 := by exact prefixLift 1311044
  have htrace : WordTrace (prefixWord ++ tailWord_1311044) baseStart_1311044 baseEnd_1311044 := by
    simpa [prefixWord, tailWord_1311044, baseEnd_1311044] using wordTrace_append hprefix tailTrace_1311044
  have hstable : (prefixWord ++ tailWord_1311044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311044).length < 2 ^ (prefixWord ++ tailWord_1311044).sum := by decide
  have hdescent : baseEnd_1311044 < baseStart_1311044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311113 : List Nat := [1, 2, 1, 1, 6, 1, 1, 3, 2, 1, 4]
def baseStart_1311113 : Nat := 118140960795 + 1311113 * 2 ^ 59
def prefixEnd_1311113 : Nat := 4983230072969 + 3 ^ 40 * 1311113 * 2
def baseEnd_1311113 : Nat := 673231161358433998057807

theorem tailTrace_1311113 : CollatzResearch.WordTrace tailWord_1311113 prefixEnd_1311113 673231161358433998057807 := by
  unfold tailWord_1311113
  simp only [CollatzResearch.WordTrace]
  refine ⟨47820219699068996118305993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31880146466045997412203995 47820219699068996118305993)
  ·
    refine ⟨35865164774301747088729495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47820219699068996118305993 35865164774301747088729495)
    ·
      refine ⟨53797747161452620633094243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35865164774301747088729495 53797747161452620633094243)
      ·
        refine ⟨80696620742178930949641365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53797747161452620633094243 80696620742178930949641365)
        ·
          refine ⟨3782654097289637388264439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 80696620742178930949641365 3782654097289637388264439)
          ·
            refine ⟨5673981145934456082396659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3782654097289637388264439 5673981145934456082396659)
            ·
              refine ⟨8510971718901684123594989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5673981145934456082396659 8510971718901684123594989)
              ·
                refine ⟨3191614394588131546348121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8510971718901684123594989 3191614394588131546348121)
                ·
                  refine ⟨2393710795941098659761091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3191614394588131546348121 2393710795941098659761091)
                  ·
                    refine ⟨3590566193911647989641637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2393710795941098659761091 3590566193911647989641637)
                    ·
                      refine ⟨673231161358433998057807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3590566193911647989641637 673231161358433998057807)
                      ·
                        rfl

theorem cell23_1311113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 2, 1, 4].length) (baseStart_1311113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1311113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1311113 prefixEnd_1311113 := by exact prefixLift 1311113
  have htrace : WordTrace (prefixWord ++ tailWord_1311113) baseStart_1311113 baseEnd_1311113 := by
    simpa [prefixWord, tailWord_1311113, baseEnd_1311113] using wordTrace_append hprefix tailTrace_1311113
  have hstable : (prefixWord ++ tailWord_1311113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311113).length < 2 ^ (prefixWord ++ tailWord_1311113).sum := by decide
  have hdescent : baseEnd_1311113 < baseStart_1311113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311153 : List Nat := [1, 2, 2, 4, 1, 2, 2, 3, 6]
def baseStart_1311153 : Nat := 118140960795 + 1311153 * 2 ^ 59
def prefixEnd_1311153 : Nat := 4983230072969 + 3 ^ 40 * 1311153 * 2
def baseEnd_1311153 : Nat := 74805744509401537950847

theorem tailTrace_1311153 : CollatzResearch.WordTrace tailWord_1311153 prefixEnd_1311153 74805744509401537950847 := by
  unfold tailWord_1311153
  simp only [CollatzResearch.WordTrace]
  refine ⟨47821678618924082949762113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31881119079282721966508075 47821678618924082949762113)
  ·
    refine ⟨35866258964193062212321585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47821678618924082949762113 35866258964193062212321585)
    ·
      refine ⟨26899694223144796659241189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35866258964193062212321585 26899694223144796659241189)
      ·
        refine ⟨5043692666839649373607723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26899694223144796659241189 5043692666839649373607723)
        ·
          refine ⟨7565539000259474060411585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5043692666839649373607723 7565539000259474060411585)
          ·
            refine ⟨5674154250194605545308689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7565539000259474060411585 5674154250194605545308689)
            ·
              refine ⟨4255615687645954158981517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5674154250194605545308689 4255615687645954158981517)
              ·
                refine ⟨1595855882867232809618069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4255615687645954158981517 1595855882867232809618069)
                ·
                  refine ⟨74805744509401537950847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1595855882867232809618069 74805744509401537950847)
                  ·
                    rfl

theorem cell23_1311153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 3, 6].length) (baseStart_1311153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1311153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1311153 prefixEnd_1311153 := by exact prefixLift 1311153
  have htrace : WordTrace (prefixWord ++ tailWord_1311153) baseStart_1311153 baseEnd_1311153 := by
    simpa [prefixWord, tailWord_1311153, baseEnd_1311153] using wordTrace_append hprefix tailTrace_1311153
  have hstable : (prefixWord ++ tailWord_1311153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311153).length < 2 ^ (prefixWord ++ tailWord_1311153).sum := by decide
  have hdescent : baseEnd_1311153 < baseStart_1311153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311197 : List Nat := [1, 4, 3, 1, 1, 1, 4, 1, 3, 1, 3]
def baseStart_1311197 : Nat := 118140960795 + 1311197 * 2 ^ 59
def prefixEnd_1311197 : Nat := 4983230072969 + 3 ^ 40 * 1311197 * 2
def baseEnd_1311197 : Nat := 673274293733411669407421

theorem tailTrace_1311197 : CollatzResearch.WordTrace tailWord_1311197 prefixEnd_1311197 673274293733411669407421 := by
  unfold tailWord_1311197
  simp only [CollatzResearch.WordTrace]
  refine ⟨47823283430764678464363845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31882188953843118976242563 47823283430764678464363845)
  ·
    refine ⟨8966865643268377212068221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47823283430764678464363845 8966865643268377212068221)
    ·
      refine ⟨3362574616225641454525583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8966865643268377212068221 3362574616225641454525583)
      ·
        refine ⟨5043861924338462181788375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3362574616225641454525583 5043861924338462181788375)
        ·
          refine ⟨7565792886507693272682563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5043861924338462181788375 7565792886507693272682563)
          ·
            refine ⟨11348689329761539909023845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7565792886507693272682563 11348689329761539909023845)
            ·
              refine ⟨2127879249330288732941971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11348689329761539909023845 2127879249330288732941971)
              ·
                refine ⟨3191818873995433099412957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2127879249330288732941971 3191818873995433099412957)
                ·
                  refine ⟨1196932077748287412279859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3191818873995433099412957 1196932077748287412279859)
                  ·
                    refine ⟨1795398116622431118419789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1196932077748287412279859 1795398116622431118419789)
                    ·
                      refine ⟨673274293733411669407421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1795398116622431118419789 673274293733411669407421)
                      ·
                        rfl

theorem cell23_1311197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_1311197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1311197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1311197 prefixEnd_1311197 := by exact prefixLift 1311197
  have htrace : WordTrace (prefixWord ++ tailWord_1311197) baseStart_1311197 baseEnd_1311197 := by
    simpa [prefixWord, tailWord_1311197, baseEnd_1311197] using wordTrace_append hprefix tailTrace_1311197
  have hstable : (prefixWord ++ tailWord_1311197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311197).length < 2 ^ (prefixWord ++ tailWord_1311197).sum := by decide
  have hdescent : baseEnd_1311197 < baseStart_1311197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311223 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 7, 2, 3]
def baseStart_1311223 : Nat := 118140960795 + 1311223 * 2 ^ 59
def prefixEnd_1311223 : Nat := 4983230072969 + 3 ^ 40 * 1311223 * 2
def baseEnd_1311223 : Nat := 673287644230428567682301

theorem tailTrace_1311223 : CollatzResearch.WordTrace tailWord_1311223 prefixEnd_1311223 673287644230428567682301 := by
  unfold tailWord_1311223
  simp only [CollatzResearch.WordTrace]
  refine ⟨47824231728670484904810323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31882821152446989936540215 47824231728670484904810323)
  ·
    refine ⟨71736347593005727357215485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47824231728670484904810323 71736347593005727357215485)
    ·
      refine ⟨26901130347377147758955807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71736347593005727357215485 26901130347377147758955807)
      ·
        refine ⟨40351695521065721638433711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26901130347377147758955807 40351695521065721638433711)
        ·
          refine ⟨60527543281598582457650567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40351695521065721638433711 60527543281598582457650567)
          ·
            refine ⟨90791314922397873686475851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60527543281598582457650567 90791314922397873686475851)
            ·
              refine ⟨136186972383596810529713777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90791314922397873686475851 136186972383596810529713777)
              ·
                refine ⟨102140229287697607897285333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136186972383596810529713777 102140229287697607897285333)
                ·
                  refine ⟨2393911623930412685092625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 102140229287697607897285333 2393911623930412685092625)
                  ·
                    refine ⟨1795433717947809513819469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2393911623930412685092625 1795433717947809513819469)
                    ·
                      refine ⟨673287644230428567682301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1795433717947809513819469 673287644230428567682301)
                      ·
                        rfl

theorem cell23_1311223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 7, 2, 3].length) (baseStart_1311223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1311223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1311223 prefixEnd_1311223 := by exact prefixLift 1311223
  have htrace : WordTrace (prefixWord ++ tailWord_1311223) baseStart_1311223 baseEnd_1311223 := by
    simpa [prefixWord, tailWord_1311223, baseEnd_1311223] using wordTrace_append hprefix tailTrace_1311223
  have hstable : (prefixWord ++ tailWord_1311223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311223).length < 2 ^ (prefixWord ++ tailWord_1311223).sum := by decide
  have hdescent : baseEnd_1311223 < baseStart_1311223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311243 : List Nat := [1, 1, 1, 1, 7, 3, 9]
def baseStart_1311243 : Nat := 118140960795 + 1311243 * 2 ^ 59
def prefixEnd_1311243 : Nat := 4983230072969 + 3 ^ 40 * 1311243 * 2
def baseEnd_1311243 : Nat := 8312319923994055425089

theorem tailTrace_1311243 : CollatzResearch.WordTrace tailWord_1311243 prefixEnd_1311243 8312319923994055425089 := by
  unfold tailWord_1311243
  simp only [CollatzResearch.WordTrace]
  refine ⟨47824961188598028320538383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31883307459065352213692255 47824961188598028320538383)
  ·
    refine ⟨71737441782897042480807575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47824961188598028320538383 71737441782897042480807575)
    ·
      refine ⟨107606162674345563721211363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71737441782897042480807575 107606162674345563721211363)
      ·
        refine ⟨161409244011518345581817045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107606162674345563721211363 161409244011518345581817045)
        ·
          refine ⟨3783029156519961224573837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 161409244011518345581817045 3783029156519961224573837)
          ·
            refine ⟨1418635933694985459215189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3783029156519961224573837 1418635933694985459215189)
            ·
              refine ⟨8312319923994055425089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1418635933694985459215189 8312319923994055425089)
              ·
                rfl

theorem cell23_1311243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 9].length) (baseStart_1311243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1311243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1311243 prefixEnd_1311243 := by exact prefixLift 1311243
  have htrace : WordTrace (prefixWord ++ tailWord_1311243) baseStart_1311243 baseEnd_1311243 := by
    simpa [prefixWord, tailWord_1311243, baseEnd_1311243] using wordTrace_append hprefix tailTrace_1311243
  have hstable : (prefixWord ++ tailWord_1311243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311243).length < 2 ^ (prefixWord ++ tailWord_1311243).sum := by decide
  have hdescent : baseEnd_1311243 < baseStart_1311243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311271 : List Nat := [1, 1, 7, 2, 1, 2, 1, 2, 1, 1, 4]
def baseStart_1311271 : Nat := 118140960795 + 1311271 * 2 ^ 59
def prefixEnd_1311271 : Nat := 4983230072969 + 3 ^ 40 * 1311271 * 2
def baseEnd_1311271 : Nat := 673312291301844379882081

theorem tailTrace_1311271 : CollatzResearch.WordTrace tailWord_1311271 prefixEnd_1311271 673312291301844379882081 := by
  unfold tailWord_1311271
  simp only [CollatzResearch.WordTrace]
  refine ⟨47825982432496589102557667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31883988288331059401705111 47825982432496589102557667)
  ·
    refine ⟨71738973648744883653836501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47825982432496589102557667 71738973648744883653836501)
    ·
      refine ⟨1681382194892458210636793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 71738973648744883653836501 1681382194892458210636793)
      ·
        refine ⟨1261036646169343657977595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1681382194892458210636793 1261036646169343657977595)
        ·
          refine ⟨1891554969254015486966393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1261036646169343657977595 1891554969254015486966393)
          ·
            refine ⟨1418666226940511615224795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1891554969254015486966393 1418666226940511615224795)
            ·
              refine ⟨2127999340410767422837193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1418666226940511615224795 2127999340410767422837193)
              ·
                refine ⟨1595999505308075567127895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2127999340410767422837193 1595999505308075567127895)
                ·
                  refine ⟨2393999257962113350691843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1595999505308075567127895 2393999257962113350691843)
                  ·
                    refine ⟨3590998886943170026037765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2393999257962113350691843 3590998886943170026037765)
                    ·
                      refine ⟨673312291301844379882081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3590998886943170026037765 673312291301844379882081)
                      ·
                        rfl

theorem cell23_1311271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_1311271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1311271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1311271 prefixEnd_1311271 := by exact prefixLift 1311271
  have htrace : WordTrace (prefixWord ++ tailWord_1311271) baseStart_1311271 baseEnd_1311271 := by
    simpa [prefixWord, tailWord_1311271, baseEnd_1311271] using wordTrace_append hprefix tailTrace_1311271
  have hstable : (prefixWord ++ tailWord_1311271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311271).length < 2 ^ (prefixWord ++ tailWord_1311271).sum := by decide
  have hdescent : baseEnd_1311271 < baseStart_1311271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311274 : List Nat := [3, 1, 4, 1, 1, 4, 1, 2, 1, 2, 3]
def baseStart_1311274 : Nat := 118140960795 + 1311274 * 2 ^ 59
def prefixEnd_1311274 : Nat := 4983230072969 + 3 ^ 40 * 1311274 * 2
def baseEnd_1311274 : Nat := 673313831743807868144567

theorem tailTrace_1311274 : CollatzResearch.WordTrace tailWord_1311274 prefixEnd_1311274 673313831743807868144567 := by
  unfold tailWord_1311274
  simp only [CollatzResearch.WordTrace]
  refine ⟨11956522962871430153729219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31884061234323813743277917 11956522962871430153729219)
  ·
    refine ⟨17934784444307145230593829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11956522962871430153729219 17934784444307145230593829)
    ·
      refine ⟨3362772083307589730736343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17934784444307145230593829 3362772083307589730736343)
      ·
        refine ⟨5044158124961384596104515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3362772083307589730736343 5044158124961384596104515)
        ·
          refine ⟨7566237187442076894156773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5044158124961384596104515 7566237187442076894156773)
          ·
            refine ⟨1418669472645389417654395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7566237187442076894156773 1418669472645389417654395)
            ·
              refine ⟨2128004208968084126481593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1418669472645389417654395 2128004208968084126481593)
              ·
                refine ⟨1596003156726063094861195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2128004208968084126481593 1596003156726063094861195)
                ·
                  refine ⟨2394004735089094642291793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1596003156726063094861195 2394004735089094642291793)
                  ·
                    refine ⟨1795503551316820981718845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2394004735089094642291793 1795503551316820981718845)
                    ·
                      refine ⟨673313831743807868144567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1795503551316820981718845 673313831743807868144567)
                      ·
                        rfl

theorem cell23_1311274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_1311274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1311274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1311274 prefixEnd_1311274 := by exact prefixLift 1311274
  have htrace : WordTrace (prefixWord ++ tailWord_1311274) baseStart_1311274 baseEnd_1311274 := by
    simpa [prefixWord, tailWord_1311274, baseEnd_1311274] using wordTrace_append hprefix tailTrace_1311274
  have hstable : (prefixWord ++ tailWord_1311274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311274).length < 2 ^ (prefixWord ++ tailWord_1311274).sum := by decide
  have hdescent : baseEnd_1311274 < baseStart_1311274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311284 : List Nat := [2, 5, 1, 3, 1, 1, 1, 2, 1, 2, 4]
def baseStart_1311284 : Nat := 118140960795 + 1311284 * 2 ^ 59
def prefixEnd_1311284 : Nat := 4983230072969 + 3 ^ 40 * 1311284 * 2
def baseEnd_1311284 : Nat := 673318966550352829019521

theorem tailTrace_1311284 : CollatzResearch.WordTrace tailWord_1311284 prefixEnd_1311284 673318966550352829019521 := by
  unfold tailWord_1311284
  simp only [CollatzResearch.WordTrace]
  refine ⟨23913228290724746161390453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31884304387632994881853937 23913228290724746161390453)
  ·
    refine ⟨2241865152255444952630355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23913228290724746161390453 2241865152255444952630355)
    ·
      refine ⟨3362797728383167428945533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2241865152255444952630355 3362797728383167428945533)
      ·
        refine ⟨1261049148143687785854575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3362797728383167428945533 1261049148143687785854575)
        ·
          refine ⟨1891573722215531678781863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1261049148143687785854575 1891573722215531678781863)
          ·
            refine ⟨2837360583323297518172795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1891573722215531678781863 2837360583323297518172795)
            ·
              refine ⟨4256040874984946277259193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2837360583323297518172795 4256040874984946277259193)
              ·
                refine ⟨3192030656238709707944395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4256040874984946277259193 3192030656238709707944395)
                ·
                  refine ⟨4788045984358064561916593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3192030656238709707944395 4788045984358064561916593)
                  ·
                    refine ⟨3591034488268548421437445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4788045984358064561916593 3591034488268548421437445)
                    ·
                      refine ⟨673318966550352829019521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3591034488268548421437445 673318966550352829019521)
                      ·
                        rfl

theorem cell23_1311284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_1311284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1311284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1311284 prefixEnd_1311284 := by exact prefixLift 1311284
  have htrace : WordTrace (prefixWord ++ tailWord_1311284) baseStart_1311284 baseEnd_1311284 := by
    simpa [prefixWord, tailWord_1311284, baseEnd_1311284] using wordTrace_append hprefix tailTrace_1311284
  have hstable : (prefixWord ++ tailWord_1311284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311284).length < 2 ^ (prefixWord ++ tailWord_1311284).sum := by decide
  have hdescent : baseEnd_1311284 < baseStart_1311284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311360 : List Nat := [2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 3]
def baseStart_1311360 : Nat := 118140960795 + 1311360 * 2 ^ 59
def prefixEnd_1311360 : Nat := 4983230072969 + 3 ^ 40 * 1311360 * 2
def baseEnd_1311360 : Nat := 673357991080094531669171

theorem tailTrace_1311360 : CollatzResearch.WordTrace tailWord_1311360 prefixEnd_1311360 673357991080094531669171 := by
  unfold tailWord_1311360
  simp only [CollatzResearch.WordTrace]
  refine ⟨23914614264587078651273767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31886152352782771535031689 23914614264587078651273767)
  ·
    refine ⟨35871921396880617976910651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23914614264587078651273767 35871921396880617976910651)
    ·
      refine ⟨53807882095320926965365977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35871921396880617976910651 53807882095320926965365977)
      ·
        refine ⟨40355911571490695224024483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53807882095320926965365977 40355911571490695224024483)
        ·
          refine ⟨60533867357236042836036725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40355911571490695224024483 60533867357236042836036725)
          ·
            refine ⟨5675050064740879015878443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60533867357236042836036725 5675050064740879015878443)
            ·
              refine ⟨8512575097111318523817665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5675050064740879015878443 8512575097111318523817665)
              ·
                refine ⟨6384431322833488892863249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8512575097111318523817665 6384431322833488892863249)
                ·
                  refine ⟨4788323492125116669647437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6384431322833488892863249 4788323492125116669647437)
                  ·
                    refine ⟨1795621309546918751117789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4788323492125116669647437 1795621309546918751117789)
                    ·
                      refine ⟨673357991080094531669171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1795621309546918751117789 673357991080094531669171)
                      ·
                        rfl

theorem cell23_1311360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 3].length) (baseStart_1311360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1311360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1311360 prefixEnd_1311360 := by exact prefixLift 1311360
  have htrace : WordTrace (prefixWord ++ tailWord_1311360) baseStart_1311360 baseEnd_1311360 := by
    simpa [prefixWord, tailWord_1311360, baseEnd_1311360] using wordTrace_append hprefix tailTrace_1311360
  have hstable : (prefixWord ++ tailWord_1311360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311360).length < 2 ^ (prefixWord ++ tailWord_1311360).sum := by decide
  have hdescent : baseEnd_1311360 < baseStart_1311360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311378 : List Nat := [3, 2, 3, 1, 2, 2, 3, 1, 2, 2, 2]
def baseStart_1311378 : Nat := 118140960795 + 1311378 * 2 ^ 59
def prefixEnd_1311378 : Nat := 4983230072969 + 3 ^ 40 * 1311378 * 2
def baseEnd_1311378 : Nat := 673367233731875461244089

theorem tailTrace_1311378 : CollatzResearch.WordTrace tailWord_1311378 prefixEnd_1311378 673367233731875461244089 := by
  unfold tailWord_1311378
  simp only [CollatzResearch.WordTrace]
  refine ⟨11957471260777236594175697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31886590028739297584468525 11957471260777236594175697)
  ·
    refine ⟨8968103445582927445631773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11957471260777236594175697 8968103445582927445631773)
    ·
      refine ⟨3363038792093597792111915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8968103445582927445631773 3363038792093597792111915)
      ·
        refine ⟨5044558188140396688167873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3363038792093597792111915 5044558188140396688167873)
        ·
          refine ⟨3783418641105297516125905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5044558188140396688167873 3783418641105297516125905)
          ·
            refine ⟨2837563980828973137094429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3783418641105297516125905 2837563980828973137094429)
            ·
              refine ⟨1064086492810864926410411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2837563980828973137094429 1064086492810864926410411)
              ·
                refine ⟨1596129739216297389615617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1064086492810864926410411 1596129739216297389615617)
                ·
                  refine ⟨1197097304412223042211713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1596129739216297389615617 1197097304412223042211713)
                  ·
                    refine ⟨897822978309167281658785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1197097304412223042211713 897822978309167281658785)
                    ·
                      refine ⟨673367233731875461244089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 897822978309167281658785 673367233731875461244089)
                      ·
                        rfl

theorem cell23_1311378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_1311378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1311378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1311378 prefixEnd_1311378 := by exact prefixLift 1311378
  have htrace : WordTrace (prefixWord ++ tailWord_1311378) baseStart_1311378 baseEnd_1311378 := by
    simpa [prefixWord, tailWord_1311378, baseEnd_1311378] using wordTrace_append hprefix tailTrace_1311378
  have hstable : (prefixWord ++ tailWord_1311378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311378).length < 2 ^ (prefixWord ++ tailWord_1311378).sum := by decide
  have hdescent : baseEnd_1311378 < baseStart_1311378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311507 : List Nat := [1, 1, 1, 2, 1, 3, 4, 4, 1, 1, 4]
def baseStart_1311507 : Nat := 118140960795 + 1311507 * 2 ^ 59
def prefixEnd_1311507 : Nat := 4983230072969 + 3 ^ 40 * 1311507 * 2
def baseEnd_1311507 : Nat := 673433472736305456530995

theorem tailTrace_1311507 : CollatzResearch.WordTrace tailWord_1311507 prefixEnd_1311507 673433472736305456530995 := by
  unfold tailWord_1311507
  simp only [CollatzResearch.WordTrace]
  refine ⟨47834590059641601408148775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31889726706427734272099183 47834590059641601408148775)
  ·
    refine ⟨71751885089462402112223163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47834590059641601408148775 71751885089462402112223163)
    ·
      refine ⟨107627827634193603168334745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71751885089462402112223163 107627827634193603168334745)
      ·
        refine ⟨80720870725645202376251059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107627827634193603168334745 80720870725645202376251059)
        ·
          refine ⟨121081306088467803564376589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80720870725645202376251059 121081306088467803564376589)
          ·
            refine ⟨45405489783175426336641221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121081306088467803564376589 45405489783175426336641221)
            ·
              refine ⟨8513529334345392438120229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45405489783175426336641221 8513529334345392438120229)
              ·
                refine ⟨1596286750189761082147543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8513529334345392438120229 1596286750189761082147543)
                ·
                  refine ⟨2394430125284641623221315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1596286750189761082147543 2394430125284641623221315)
                  ·
                    refine ⟨3591645187926962434831973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2394430125284641623221315 3591645187926962434831973)
                    ·
                      refine ⟨673433472736305456530995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3591645187926962434831973 673433472736305456530995)
                      ·
                        rfl

theorem cell23_1311507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4, 1, 1, 4].length) (baseStart_1311507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1311507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1311507 prefixEnd_1311507 := by exact prefixLift 1311507
  have htrace : WordTrace (prefixWord ++ tailWord_1311507) baseStart_1311507 baseEnd_1311507 := by
    simpa [prefixWord, tailWord_1311507, baseEnd_1311507] using wordTrace_append hprefix tailTrace_1311507
  have hstable : (prefixWord ++ tailWord_1311507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311507).length < 2 ^ (prefixWord ++ tailWord_1311507).sum := by decide
  have hdescent : baseEnd_1311507 < baseStart_1311507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311541 : List Nat := [1, 3, 3, 1, 3, 1, 1, 3, 3, 2, 2]
def baseStart_1311541 : Nat := 118140960795 + 1311541 * 2 ^ 59
def prefixEnd_1311541 : Nat := 4983230072969 + 3 ^ 40 * 1311541 * 2
def baseEnd_1311541 : Nat := 673450931078558323505839

theorem tailTrace_1311541 : CollatzResearch.WordTrace tailWord_1311541 prefixEnd_1311541 673450931078558323505839 := by
  unfold tailWord_1311541
  simp only [CollatzResearch.WordTrace]
  refine ⟨47835830141518425214886477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31890553427678950143257651 47835830141518425214886477)
  ·
    refine ⟨17938436303069409455582429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47835830141518425214886477 17938436303069409455582429)
    ·
      refine ⟨6726913613651028545843411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17938436303069409455582429 6726913613651028545843411)
      ·
        refine ⟨10090370420476542818765117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6726913613651028545843411 10090370420476542818765117)
        ·
          refine ⟨3783888907678703557036919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10090370420476542818765117 3783888907678703557036919)
          ·
            refine ⟨5675833361518055335555379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3783888907678703557036919 5675833361518055335555379)
            ·
              refine ⟨8513750042277083003333069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5675833361518055335555379 8513750042277083003333069)
              ·
                refine ⟨3192656265853906126249901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8513750042277083003333069 3192656265853906126249901)
                ·
                  refine ⟨1197246099695214797343713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3192656265853906126249901 1197246099695214797343713)
                  ·
                    refine ⟨897934574771411098007785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1197246099695214797343713 897934574771411098007785)
                    ·
                      refine ⟨673450931078558323505839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 897934574771411098007785 673450931078558323505839)
                      ·
                        rfl

theorem cell23_1311541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 3, 2, 2].length) (baseStart_1311541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1311541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1311541 prefixEnd_1311541 := by exact prefixLift 1311541
  have htrace : WordTrace (prefixWord ++ tailWord_1311541) baseStart_1311541 baseEnd_1311541 := by
    simpa [prefixWord, tailWord_1311541, baseEnd_1311541] using wordTrace_append hprefix tailTrace_1311541
  have hstable : (prefixWord ++ tailWord_1311541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311541).length < 2 ^ (prefixWord ++ tailWord_1311541).sum := by decide
  have hdescent : baseEnd_1311541 < baseStart_1311541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311551 : List Nat := [1, 1, 2, 2, 5, 2, 3, 1, 2, 4]
def baseStart_1311551 : Nat := 118140960795 + 1311551 * 2 ^ 59
def prefixEnd_1311551 : Nat := 4983230072969 + 3 ^ 40 * 1311551 * 2
def baseEnd_1311551 : Nat := 224485355295034428126931

theorem tailTrace_1311551 : CollatzResearch.WordTrace tailWord_1311551 prefixEnd_1311551 224485355295034428126931 := by
  unfold tailWord_1311551
  simp only [CollatzResearch.WordTrace]
  refine ⟨47836194871482196922750507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31890796580988131281833671 47836194871482196922750507)
  ·
    refine ⟨71754292307223295384125761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47836194871482196922750507 71754292307223295384125761)
    ·
      refine ⟨53815719230417471538094321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71754292307223295384125761 53815719230417471538094321)
      ·
        refine ⟨40361789422813103653570741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53815719230417471538094321 40361789422813103653570741)
        ·
          refine ⟨3783917758388728467522257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40361789422813103653570741 3783917758388728467522257)
          ·
            refine ⟨2837938318791546350641693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3783917758388728467522257 2837938318791546350641693)
            ·
              refine ⟨1064226869546829881490635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2837938318791546350641693 1064226869546829881490635)
              ·
                refine ⟨1596340304320244822235953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1064226869546829881490635 1596340304320244822235953)
                ·
                  refine ⟨1197255228240183616676965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1596340304320244822235953 1197255228240183616676965)
                  ·
                    refine ⟨224485355295034428126931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1197255228240183616676965 224485355295034428126931)
                    ·
                      rfl

theorem cell23_1311551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 1, 2, 4].length) (baseStart_1311551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1311551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1311551 prefixEnd_1311551 := by exact prefixLift 1311551
  have htrace : WordTrace (prefixWord ++ tailWord_1311551) baseStart_1311551 baseEnd_1311551 := by
    simpa [prefixWord, tailWord_1311551, baseEnd_1311551] using wordTrace_append hprefix tailTrace_1311551
  have hstable : (prefixWord ++ tailWord_1311551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311551).length < 2 ^ (prefixWord ++ tailWord_1311551).sum := by decide
  have hdescent : baseEnd_1311551 < baseStart_1311551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311557 : List Nat := [1, 3, 1, 1, 1, 2, 2, 5, 1, 3, 3]
def baseStart_1311557 : Nat := 118140960795 + 1311557 * 2 ^ 59
def prefixEnd_1311557 : Nat := 4983230072969 + 3 ^ 40 * 1311557 * 2
def baseEnd_1311557 : Nat := 673459146769030260905765

theorem tailTrace_1311557 : CollatzResearch.WordTrace tailWord_1311557 prefixEnd_1311557 673459146769030260905765 := by
  unfold tailWord_1311557
  simp only [CollatzResearch.WordTrace]
  refine ⟨47836413709460459947468925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31890942472973639964979283 47836413709460459947468925)
  ·
    refine ⟨17938655141047672480300847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47836413709460459947468925 17938655141047672480300847)
    ·
      refine ⟨26907982711571508720451271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17938655141047672480300847 26907982711571508720451271)
      ·
        refine ⟨40361974067357263080676907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26907982711571508720451271 40361974067357263080676907)
        ·
          refine ⟨60542961101035894621015361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40361974067357263080676907 60542961101035894621015361)
          ·
            refine ⟨45407220825776920965761521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60542961101035894621015361 45407220825776920965761521)
            ·
              refine ⟨34055415619332690724321141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45407220825776920965761521 34055415619332690724321141)
              ·
                refine ⟨3192695214312439755405107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34055415619332690724321141 3192695214312439755405107)
                ·
                  refine ⟨4789042821468659633107661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3192695214312439755405107 4789042821468659633107661)
                  ·
                    refine ⟨1795891058050747362415373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4789042821468659633107661 1795891058050747362415373)
                    ·
                      refine ⟨673459146769030260905765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1795891058050747362415373 673459146769030260905765)
                      ·
                        rfl

theorem cell23_1311557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 3, 3].length) (baseStart_1311557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1311557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1311557 prefixEnd_1311557 := by exact prefixLift 1311557
  have htrace : WordTrace (prefixWord ++ tailWord_1311557) baseStart_1311557 baseEnd_1311557 := by
    simpa [prefixWord, tailWord_1311557, baseEnd_1311557] using wordTrace_append hprefix tailTrace_1311557
  have hstable : (prefixWord ++ tailWord_1311557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311557).length < 2 ^ (prefixWord ++ tailWord_1311557).sum := by decide
  have hdescent : baseEnd_1311557 < baseStart_1311557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311564 : List Nat := [2, 2, 1, 3, 3, 3, 2, 7]
def baseStart_1311564 : Nat := 118140960795 + 1311564 * 2 ^ 59
def prefixEnd_1311564 : Nat := 4983230072969 + 3 ^ 40 * 1311564 * 2
def baseEnd_1311564 : Nat := 24943064486430064204379

theorem tailTrace_1311564 : CollatzResearch.WordTrace tailWord_1311564 prefixEnd_1311564 24943064486430064204379 := by
  unfold tailWord_1311564
  simp only [CollatzResearch.WordTrace]
  refine ⟨23918334510217550071486873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31891112680290066761982497 23918334510217550071486873)
  ·
    refine ⟨17938750882663162553615155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23918334510217550071486873 17938750882663162553615155)
    ·
      refine ⟨26908126323994743830422733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17938750882663162553615155 26908126323994743830422733)
      ·
        refine ⟨10090547371498028936408525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26908126323994743830422733 10090547371498028936408525)
        ·
          refine ⟨3783955264311760851153197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10090547371498028936408525 3783955264311760851153197)
          ·
            refine ⟨1418983224116910319182449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3783955264311760851153197 1418983224116910319182449)
            ·
              refine ⟨1064237418087682739386837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1418983224116910319182449 1064237418087682739386837)
              ·
                refine ⟨24943064486430064204379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1064237418087682739386837 24943064486430064204379)
                ·
                  rfl

theorem cell23_1311564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 7].length) (baseStart_1311564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1311564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1311564 prefixEnd_1311564 := by exact prefixLift 1311564
  have htrace : WordTrace (prefixWord ++ tailWord_1311564) baseStart_1311564 baseEnd_1311564 := by
    simpa [prefixWord, tailWord_1311564, baseEnd_1311564] using wordTrace_append hprefix tailTrace_1311564
  have hstable : (prefixWord ++ tailWord_1311564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311564).length < 2 ^ (prefixWord ++ tailWord_1311564).sum := by decide
  have hdescent : baseEnd_1311564 < baseStart_1311564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311567 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 4, 7, 2]
def baseStart_1311567 : Nat := 118140960795 + 1311567 * 2 ^ 59
def prefixEnd_1311567 : Nat := 4983230072969 + 3 ^ 40 * 1311567 * 2
def baseEnd_1311567 : Nat := 673464281575575221780719

theorem tailTrace_1311567 : CollatzResearch.WordTrace tailWord_1311567 prefixEnd_1311567 673464281575575221780719 := by
  unfold tailWord_1311567
  simp only [CollatzResearch.WordTrace]
  refine ⟨47836778439424231655332955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31891185626282821103555303 47836778439424231655332955)
  ·
    refine ⟨71755167659136347482999433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47836778439424231655332955 71755167659136347482999433)
    ·
      refine ⟨53816375744352260612249575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71755167659136347482999433 53816375744352260612249575)
      ·
        refine ⟨80724563616528390918374363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53816375744352260612249575 80724563616528390918374363)
        ·
          refine ⟨121086845424792586377561545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80724563616528390918374363 121086845424792586377561545)
          ·
            refine ⟨90815134068594439783171159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121086845424792586377561545 90815134068594439783171159)
            ·
              refine ⟨136222701102891659674756739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90815134068594439783171159 136222701102891659674756739)
              ·
                refine ⟨204334051654337489512135109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136222701102891659674756739 204334051654337489512135109)
                ·
                  refine ⟨38312634685188279283525333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 204334051654337489512135109 38312634685188279283525333)
                  ·
                    refine ⟨897952375434100295707625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38312634685188279283525333 897952375434100295707625)
                    ·
                      refine ⟨673464281575575221780719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 897952375434100295707625 673464281575575221780719)
                      ·
                        rfl

theorem cell23_1311567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 7, 2].length) (baseStart_1311567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1311567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1311567 prefixEnd_1311567 := by exact prefixLift 1311567
  have htrace : WordTrace (prefixWord ++ tailWord_1311567) baseStart_1311567 baseEnd_1311567 := by
    simpa [prefixWord, tailWord_1311567, baseEnd_1311567] using wordTrace_append hprefix tailTrace_1311567
  have hstable : (prefixWord ++ tailWord_1311567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311567).length < 2 ^ (prefixWord ++ tailWord_1311567).sum := by decide
  have hdescent : baseEnd_1311567 < baseStart_1311567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311575 : List Nat := [1, 1, 3, 2, 4, 3, 1, 3, 1, 2, 2]
def baseStart_1311575 : Nat := 118140960795 + 1311575 * 2 ^ 59
def prefixEnd_1311575 : Nat := 4983230072969 + 3 ^ 40 * 1311575 * 2
def baseEnd_1311575 : Nat := 673468389420811190480683

theorem tailTrace_1311575 : CollatzResearch.WordTrace tailWord_1311575 prefixEnd_1311575 673468389420811190480683 := by
  unfold tailWord_1311575
  simp only [CollatzResearch.WordTrace]
  refine ⟨47837070223395249021624179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31891380148930166014416119 47837070223395249021624179)
  ·
    refine ⟨71755605335092873532436269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47837070223395249021624179 71755605335092873532436269)
    ·
      refine ⟨26908352000659827574663601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71755605335092873532436269 26908352000659827574663601)
      ·
        refine ⟨20181264000494870680997701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26908352000659827574663601 20181264000494870680997701)
        ·
          refine ⟨3783987000092788252687069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20181264000494870680997701 3783987000092788252687069)
          ·
            refine ⟨1418995125034795594757651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3783987000092788252687069 1418995125034795594757651)
            ·
              refine ⟨2128492687552193392136477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1418995125034795594757651 2128492687552193392136477)
              ·
                refine ⟨798184757832072522051179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2128492687552193392136477 798184757832072522051179)
                ·
                  refine ⟨1197277136748108783076769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 798184757832072522051179 1197277136748108783076769)
                  ·
                    refine ⟨897957852561081587307577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1197277136748108783076769 897957852561081587307577)
                    ·
                      refine ⟨673468389420811190480683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 897957852561081587307577 673468389420811190480683)
                      ·
                        rfl

theorem cell23_1311575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 3, 1, 2, 2].length) (baseStart_1311575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1311575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1311575 prefixEnd_1311575 := by exact prefixLift 1311575
  have htrace : WordTrace (prefixWord ++ tailWord_1311575) baseStart_1311575 baseEnd_1311575 := by
    simpa [prefixWord, tailWord_1311575, baseEnd_1311575] using wordTrace_append hprefix tailTrace_1311575
  have hstable : (prefixWord ++ tailWord_1311575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311575).length < 2 ^ (prefixWord ++ tailWord_1311575).sum := by decide
  have hdescent : baseEnd_1311575 < baseStart_1311575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311597 : List Nat := [1, 5, 1, 1, 1, 1, 1, 3, 2, 3, 4]
def baseStart_1311597 : Nat := 118140960795 + 1311597 * 2 ^ 59
def prefixEnd_1311597 : Nat := 4983230072969 + 3 ^ 40 * 1311597 * 2
def baseEnd_1311597 : Nat := 673479685995210104405581

theorem tailTrace_1311597 : CollatzResearch.WordTrace tailWord_1311597 prefixEnd_1311597 673479685995210104405581 := by
  unfold tailWord_1311597
  simp only [CollatzResearch.WordTrace]
  refine ⟨47837872629315546778925045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31891915086210364519283363 47837872629315546778925045)
  ·
    refine ⟨4484800558998332510524223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47837872629315546778925045 4484800558998332510524223)
    ·
      refine ⟨6727200838497498765786335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4484800558998332510524223 6727200838497498765786335)
      ·
        refine ⟨10090801257746248148679503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6727200838497498765786335 10090801257746248148679503)
        ·
          refine ⟨15136201886619372223019255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10090801257746248148679503 15136201886619372223019255)
          ·
            refine ⟨22704302829929058334528883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15136201886619372223019255 22704302829929058334528883)
            ·
              refine ⟨34056454244893587501793325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22704302829929058334528883 34056454244893587501793325)
              ·
                refine ⟨12771170341835095313172497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34056454244893587501793325 12771170341835095313172497)
                ·
                  refine ⟨9578377756376321484879373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12771170341835095313172497 9578377756376321484879373)
                  ·
                    refine ⟨3591891658641120556829765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9578377756376321484879373 3591891658641120556829765)
                    ·
                      refine ⟨673479685995210104405581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3591891658641120556829765 673479685995210104405581)
                      ·
                        rfl

theorem cell23_1311597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_1311597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1311597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1311597 prefixEnd_1311597 := by exact prefixLift 1311597
  have htrace : WordTrace (prefixWord ++ tailWord_1311597) baseStart_1311597 baseEnd_1311597 := by
    simpa [prefixWord, tailWord_1311597, baseEnd_1311597] using wordTrace_append hprefix tailTrace_1311597
  have hstable : (prefixWord ++ tailWord_1311597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311597).length < 2 ^ (prefixWord ++ tailWord_1311597).sum := by decide
  have hdescent : baseEnd_1311597 < baseStart_1311597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311674 : List Nat := [3, 1, 1, 1, 2, 1, 3, 2, 2, 5, 2]
def baseStart_1311674 : Nat := 118140960795 + 1311674 * 2 ^ 59
def prefixEnd_1311674 : Nat := 4983230072969 + 3 ^ 40 * 1311674 * 2
def baseEnd_1311674 : Nat := 673519224005606303142727

theorem tailTrace_1311674 : CollatzResearch.WordTrace tailWord_1311674 prefixEnd_1311674 673519224005606303142727 := by
  unfold tailWord_1311674
  simp only [CollatzResearch.WordTrace]
  refine ⟨11960170262509147232369519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31893787366691059286318717 11960170262509147232369519)
  ·
    refine ⟨17940255393763720848554279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11960170262509147232369519 17940255393763720848554279)
    ·
      refine ⟨26910383090645581272831419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17940255393763720848554279 26910383090645581272831419)
      ·
        refine ⟨40365574635968371909247129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26910383090645581272831419 40365574635968371909247129)
        ·
          refine ⟨30274180976976278931935347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40365574635968371909247129 30274180976976278931935347)
          ·
            refine ⟨45411271465464418397903021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30274180976976278931935347 45411271465464418397903021)
            ·
              refine ⟨17029226799549156899213633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45411271465464418397903021 17029226799549156899213633)
              ·
                refine ⟨12771920099661867674410225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17029226799549156899213633 12771920099661867674410225)
                ·
                  refine ⟨9578940074746400755807669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12771920099661867674410225 9578940074746400755807669)
                  ·
                    refine ⟨898025632007475070856969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9578940074746400755807669 898025632007475070856969)
                    ·
                      refine ⟨673519224005606303142727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 898025632007475070856969 673519224005606303142727)
                      ·
                        rfl

theorem cell23_1311674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 2, 5, 2].length) (baseStart_1311674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1311674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1311674 prefixEnd_1311674 := by exact prefixLift 1311674
  have htrace : WordTrace (prefixWord ++ tailWord_1311674) baseStart_1311674 baseEnd_1311674 := by
    simpa [prefixWord, tailWord_1311674, baseEnd_1311674] using wordTrace_append hprefix tailTrace_1311674
  have hstable : (prefixWord ++ tailWord_1311674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311674).length < 2 ^ (prefixWord ++ tailWord_1311674).sum := by decide
  have hdescent : baseEnd_1311674 < baseStart_1311674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311765 : List Nat := [1, 3, 2, 1, 4, 2, 3, 2, 1, 4]
def baseStart_1311765 : Nat := 118140960795 + 1311765 * 2 ^ 59
def prefixEnd_1311765 : Nat := 4983230072969 + 3 ^ 40 * 1311765 * 2
def baseEnd_1311765 : Nat := 224521983581721815701603

theorem tailTrace_1311765 : CollatzResearch.WordTrace tailWord_1311765 prefixEnd_1311765 224521983581721815701603 := by
  unfold tailWord_1311765
  simp only [CollatzResearch.WordTrace]
  refine ⟨47844000092706911471040749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31896000061804607647360499 47844000092706911471040749)
  ·
    refine ⟨17941500034765091801640281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47844000092706911471040749 17941500034765091801640281)
    ·
      refine ⟨13456125026073818851230211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17941500034765091801640281 13456125026073818851230211)
      ·
        refine ⟨20184187539110728276845317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13456125026073818851230211 20184187539110728276845317)
        ·
          refine ⟨3784535163583261551908497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20184187539110728276845317 3784535163583261551908497)
          ·
            refine ⟨2838401372687446163931373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3784535163583261551908497 2838401372687446163931373)
            ·
              refine ⟨1064400514757792311474265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2838401372687446163931373 1064400514757792311474265)
              ·
                refine ⟨798300386068344233605699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1064400514757792311474265 798300386068344233605699)
                ·
                  refine ⟨1197450579102516350408549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 798300386068344233605699 1197450579102516350408549)
                  ·
                    refine ⟨224521983581721815701603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1197450579102516350408549 224521983581721815701603)
                    ·
                      rfl

theorem cell23_1311765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 2, 1, 4].length) (baseStart_1311765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1311765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1311765 prefixEnd_1311765 := by exact prefixLift 1311765
  have htrace : WordTrace (prefixWord ++ tailWord_1311765) baseStart_1311765 baseEnd_1311765 := by
    simpa [prefixWord, tailWord_1311765, baseEnd_1311765] using wordTrace_append hprefix tailTrace_1311765
  have hstable : (prefixWord ++ tailWord_1311765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311765).length < 2 ^ (prefixWord ++ tailWord_1311765).sum := by decide
  have hdescent : baseEnd_1311765 < baseStart_1311765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311778 : List Nat := [3, 3, 1, 1, 1, 5, 2, 1, 6]
def baseStart_1311778 : Nat := 118140960795 + 1311778 * 2 ^ 59
def prefixEnd_1311778 : Nat := 4983230072969 + 3 ^ 40 * 1311778 * 2
def baseEnd_1311778 : Nat := 74841402888185988471361

theorem tailTrace_1311778 : CollatzResearch.WordTrace tailWord_1311778 prefixEnd_1311778 74841402888185988471361 := by
  unfold tailWord_1311778
  simp only [CollatzResearch.WordTrace]
  refine ⟨11961118560414953672815997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31896316161106543127509325 11961118560414953672815997)
  ·
    refine ⟨4485419460155607627305999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11961118560414953672815997 4485419460155607627305999)
    ·
      refine ⟨6728129190233411440958999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4485419460155607627305999 6728129190233411440958999)
      ·
        refine ⟨10092193785350117161438499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6728129190233411440958999 10092193785350117161438499)
        ·
          refine ⟨15138290678025175742157749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10092193785350117161438499 15138290678025175742157749)
          ·
            refine ⟨1419214751064860225827289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15138290678025175742157749 1419214751064860225827289)
            ·
              refine ⟨1064411063298645169370467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1419214751064860225827289 1064411063298645169370467)
              ·
                refine ⟨1596616594947967754055701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1064411063298645169370467 1596616594947967754055701)
                ·
                  refine ⟨74841402888185988471361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1596616594947967754055701 74841402888185988471361)
                  ·
                    rfl

theorem cell23_1311778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_1311778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1311778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1311778 prefixEnd_1311778 := by exact prefixLift 1311778
  have htrace : WordTrace (prefixWord ++ tailWord_1311778) baseStart_1311778 baseEnd_1311778 := by
    simpa [prefixWord, tailWord_1311778, baseEnd_1311778] using wordTrace_append hprefix tailTrace_1311778
  have hstable : (prefixWord ++ tailWord_1311778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311778).length < 2 ^ (prefixWord ++ tailWord_1311778).sum := by decide
  have hdescent : baseEnd_1311778 < baseStart_1311778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311781 : List Nat := [1, 3, 1, 2, 2, 2, 1, 2, 4, 3, 2]
def baseStart_1311781 : Nat := 118140960795 + 1311781 * 2 ^ 59
def prefixEnd_1311781 : Nat := 4983230072969 + 3 ^ 40 * 1311781 * 2
def baseEnd_1311781 : Nat := 673574166435637384504735

theorem tailTrace_1311781 : CollatzResearch.WordTrace tailWord_1311781 prefixEnd_1311781 673574166435637384504735 := by
  unfold tailWord_1311781
  simp only [CollatzResearch.WordTrace]
  refine ⟨47844583660648946203623197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31896389107099297469082131 47844583660648946203623197)
  ·
    refine ⟨17941718872743354826358699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47844583660648946203623197 17941718872743354826358699)
    ·
      refine ⟨26912578309115032239538049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17941718872743354826358699 26912578309115032239538049)
      ·
        refine ⟨20184433731836274179653537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26912578309115032239538049 20184433731836274179653537)
        ·
          refine ⟨15138325298877205634740153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20184433731836274179653537 15138325298877205634740153)
          ·
            refine ⟨11353743974157904226055115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15138325298877205634740153 11353743974157904226055115)
            ·
              refine ⟨17030615961236856339082673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11353743974157904226055115 17030615961236856339082673)
              ·
                refine ⟨12772961970927642254312005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17030615961236856339082673 12772961970927642254312005)
                ·
                  refine ⟨2394930369548932922683501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12772961970927642254312005 2394930369548932922683501)
                  ·
                    refine ⟨898098888580849846006313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2394930369548932922683501 898098888580849846006313)
                    ·
                      refine ⟨673574166435637384504735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 898098888580849846006313 673574166435637384504735)
                      ·
                        rfl

theorem cell23_1311781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 4, 3, 2].length) (baseStart_1311781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1311781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1311781 prefixEnd_1311781 := by exact prefixLift 1311781
  have htrace : WordTrace (prefixWord ++ tailWord_1311781) baseStart_1311781 baseEnd_1311781 := by
    simpa [prefixWord, tailWord_1311781, baseEnd_1311781] using wordTrace_append hprefix tailTrace_1311781
  have hstable : (prefixWord ++ tailWord_1311781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311781).length < 2 ^ (prefixWord ++ tailWord_1311781).sum := by decide
  have hdescent : baseEnd_1311781 < baseStart_1311781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311804 : List Nat := [2, 2, 2, 2, 2, 2, 1, 1, 3, 6]
def baseStart_1311804 : Nat := 118140960795 + 1311804 * 2 ^ 59
def prefixEnd_1311804 : Nat := 4983230072969 + 3 ^ 40 * 1311804 * 2
def baseEnd_1311804 : Nat := 224528658830230264839043

theorem tailTrace_1311804 : CollatzResearch.WordTrace tailWord_1311804 prefixEnd_1311804 224528658830230264839043 := by
  unfold tailWord_1311804
  simp only [CollatzResearch.WordTrace]
  refine ⟨23922711269782810565855233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31896948359710414087806977 23922711269782810565855233)
  ·
    refine ⟨17942033452337107924391425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23922711269782810565855233 17942033452337107924391425)
    ·
      refine ⟨13456525089252830943293569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17942033452337107924391425 13456525089252830943293569)
      ·
        refine ⟨10092393816939623207470177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13456525089252830943293569 10092393816939623207470177)
        ·
          refine ⟨7569295362704717405602633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10092393816939623207470177 7569295362704717405602633)
          ·
            refine ⟨5676971522028538054201975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7569295362704717405602633 5676971522028538054201975)
            ·
              refine ⟨8515457283042807081302963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5676971522028538054201975 8515457283042807081302963)
              ·
                refine ⟨12773185924564210621954445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8515457283042807081302963 12773185924564210621954445)
                ·
                  refine ⟨4789944721711578983232917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12773185924564210621954445 4789944721711578983232917)
                  ·
                    refine ⟨224528658830230264839043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4789944721711578983232917 224528658830230264839043)
                    ·
                      rfl

theorem cell23_1311804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_1311804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1311804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1311804 prefixEnd_1311804 := by exact prefixLift 1311804
  have htrace : WordTrace (prefixWord ++ tailWord_1311804) baseStart_1311804 baseEnd_1311804 := by
    simpa [prefixWord, tailWord_1311804, baseEnd_1311804] using wordTrace_append hprefix tailTrace_1311804
  have hstable : (prefixWord ++ tailWord_1311804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311804).length < 2 ^ (prefixWord ++ tailWord_1311804).sum := by decide
  have hdescent : baseEnd_1311804 < baseStart_1311804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311884 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 1, 5, 4]
def baseStart_1311884 : Nat := 118140960795 + 1311884 * 2 ^ 59
def prefixEnd_1311884 : Nat := 4983230072969 + 3 ^ 40 * 1311884 * 2
def baseEnd_1311884 : Nat := 673627054943050481516761

theorem tailTrace_1311884 : CollatzResearch.WordTrace tailWord_1311884 prefixEnd_1311884 673627054943050481516761 := by
  unfold tailWord_1311884
  simp only [CollatzResearch.WordTrace]
  refine ⟨23924170189637897397311353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31898893586183863196415137 23924170189637897397311353)
  ·
    refine ⟨17943127642228423047983515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23924170189637897397311353 17943127642228423047983515)
    ·
      refine ⟨26914691463342634571975273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17943127642228423047983515 26914691463342634571975273)
      ·
        refine ⟨20186018597506975928981455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26914691463342634571975273 20186018597506975928981455)
        ·
          refine ⟨30279027896260463893472183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20186018597506975928981455 30279027896260463893472183)
          ·
            refine ⟨45418541844390695840208275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30279027896260463893472183 45418541844390695840208275)
            ·
              refine ⟨68127812766586043760312413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45418541844390695840208275 68127812766586043760312413)
              ·
                refine ⟨25547929787469766410117155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68127812766586043760312413 25547929787469766410117155)
                ·
                  refine ⟨38321894681204649615175733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25547929787469766410117155 38321894681204649615175733)
                  ·
                    refine ⟨3592677626362935901422725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38321894681204649615175733 3592677626362935901422725)
                    ·
                      refine ⟨673627054943050481516761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3592677626362935901422725 673627054943050481516761)
                      ·
                        rfl

theorem cell23_1311884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_1311884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1311884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1311884 prefixEnd_1311884 := by exact prefixLift 1311884
  have htrace : WordTrace (prefixWord ++ tailWord_1311884) baseStart_1311884 baseEnd_1311884 := by
    simpa [prefixWord, tailWord_1311884, baseEnd_1311884] using wordTrace_append hprefix tailTrace_1311884
  have hstable : (prefixWord ++ tailWord_1311884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311884).length < 2 ^ (prefixWord ++ tailWord_1311884).sum := by decide
  have hdescent : baseEnd_1311884 < baseStart_1311884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311905 : List Nat := [1, 2, 3, 3, 1, 1, 4, 2, 1, 3, 2]
def baseStart_1311905 : Nat := 118140960795 + 1311905 * 2 ^ 59
def prefixEnd_1311905 : Nat := 4983230072969 + 3 ^ 40 * 1311905 * 2
def baseEnd_1311905 : Nat := 673637838036794899354165

theorem tailTrace_1311905 : CollatzResearch.WordTrace tailWord_1311905 prefixEnd_1311905 673637838036794899354165 := by
  unfold tailWord_1311905
  simp only [CollatzResearch.WordTrace]
  refine ⟨47849106312199715381137169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31899404208133143587424779 47849106312199715381137169)
  ·
    refine ⟨35886829734149786535852877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47849106312199715381137169 35886829734149786535852877)
    ·
      refine ⟨13457561150306169950944829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35886829734149786535852877 13457561150306169950944829)
      ·
        refine ⟨5046585431364813731604311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13457561150306169950944829 5046585431364813731604311)
        ·
          refine ⟨7569878147047220597406467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5046585431364813731604311 7569878147047220597406467)
          ·
            refine ⟨11354817220570830896109701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7569878147047220597406467 11354817220570830896109701)
            ·
              refine ⟨2129028228857030793020569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11354817220570830896109701 2129028228857030793020569)
              ·
                refine ⟨1596771171642773094765427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2129028228857030793020569 1596771171642773094765427)
                ·
                  refine ⟨2395156757464159642148141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1596771171642773094765427 2395156757464159642148141)
                  ·
                    refine ⟨898183784049059865805553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2395156757464159642148141 898183784049059865805553)
                    ·
                      refine ⟨673637838036794899354165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 898183784049059865805553 673637838036794899354165)
                      ·
                        rfl

theorem cell23_1311905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_1311905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1311905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1311905 prefixEnd_1311905 := by exact prefixLift 1311905
  have htrace : WordTrace (prefixWord ++ tailWord_1311905) baseStart_1311905 baseEnd_1311905 := by
    simpa [prefixWord, tailWord_1311905, baseEnd_1311905] using wordTrace_append hprefix tailTrace_1311905
  have hstable : (prefixWord ++ tailWord_1311905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311905).length < 2 ^ (prefixWord ++ tailWord_1311905).sum := by decide
  have hdescent : baseEnd_1311905 < baseStart_1311905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311921 : List Nat := [1, 2, 2, 5, 1, 1, 1, 1, 1, 3, 5]
def baseStart_1311921 : Nat := 118140960795 + 1311921 * 2 ^ 59
def prefixEnd_1311921 : Nat := 4983230072969 + 3 ^ 40 * 1311921 * 2
def baseEnd_1311921 : Nat := 673646053727266836754091

theorem tailTrace_1311921 : CollatzResearch.WordTrace tailWord_1311921 prefixEnd_1311921 673646053727266836754091 := by
  unfold tailWord_1311921
  simp only [CollatzResearch.WordTrace]
  refine ⟨47849689880141750113719617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31899793253427833409146411 47849689880141750113719617)
  ·
    refine ⟨35887267410106312585289713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47849689880141750113719617 35887267410106312585289713)
    ·
      refine ⟨26915450557579734438967285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35887267410106312585289713 26915450557579734438967285)
      ·
        refine ⟨2523323489773100103653183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26915450557579734438967285 2523323489773100103653183)
        ·
          refine ⟨3784985234659650155479775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2523323489773100103653183 3784985234659650155479775)
          ·
            refine ⟨5677477851989475233219663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3784985234659650155479775 5677477851989475233219663)
            ·
              refine ⟨8516216777984212849829495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5677477851989475233219663 8516216777984212849829495)
              ·
                refine ⟨12774325166976319274744243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8516216777984212849829495 12774325166976319274744243)
                ·
                  refine ⟨19161487750464478912116365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12774325166976319274744243 19161487750464478912116365)
                  ·
                    refine ⟨7185557906424179592043637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19161487750464478912116365 7185557906424179592043637)
                    ·
                      refine ⟨673646053727266836754091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7185557906424179592043637 673646053727266836754091)
                      ·
                        rfl

theorem cell23_1311921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_1311921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1311921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1311921 prefixEnd_1311921 := by exact prefixLift 1311921
  have htrace : WordTrace (prefixWord ++ tailWord_1311921) baseStart_1311921 baseEnd_1311921 := by
    simpa [prefixWord, tailWord_1311921, baseEnd_1311921] using wordTrace_append hprefix tailTrace_1311921
  have hstable : (prefixWord ++ tailWord_1311921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311921).length < 2 ^ (prefixWord ++ tailWord_1311921).sum := by decide
  have hdescent : baseEnd_1311921 < baseStart_1311921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311956 : List Nat := [2, 4, 1, 4, 2, 1, 1, 2, 1, 3, 2]
def baseStart_1311956 : Nat := 118140960795 + 1311956 * 2 ^ 59
def prefixEnd_1311956 : Nat := 4983230072969 + 3 ^ 40 * 1311956 * 2
def baseEnd_1311956 : Nat := 673664025550174199816431

theorem tailTrace_1311956 : CollatzResearch.WordTrace tailWord_1311956 prefixEnd_1311956 673664025550174199816431 := by
  unfold tailWord_1311956
  simp only [CollatzResearch.WordTrace]
  refine ⟨23925483217507475545621861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31900644290009967394162481 23925483217507475545621861)
  ·
    refine ⟨4486028103282651664804099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23925483217507475545621861 4486028103282651664804099)
    ·
      refine ⟨6729042154923977497206149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4486028103282651664804099 6729042154923977497206149)
      ·
        refine ⟨1261695404048245780726153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6729042154923977497206149 1261695404048245780726153)
        ·
          refine ⟨946271553036184335544615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1261695404048245780726153 946271553036184335544615)
          ·
            refine ⟨1419407329554276503316923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 946271553036184335544615 1419407329554276503316923)
            ·
              refine ⟨2129110994331414754975385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1419407329554276503316923 2129110994331414754975385)
              ·
                refine ⟨1596833245748561066231539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2129110994331414754975385 1596833245748561066231539)
                ·
                  refine ⟨2395249868622841599347309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1596833245748561066231539 2395249868622841599347309)
                  ·
                    refine ⟨898218700733565599755241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2395249868622841599347309 898218700733565599755241)
                    ·
                      refine ⟨673664025550174199816431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 898218700733565599755241 673664025550174199816431)
                      ·
                        rfl

theorem cell23_1311956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_1311956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1311956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1311956 prefixEnd_1311956 := by exact prefixLift 1311956
  have htrace : WordTrace (prefixWord ++ tailWord_1311956) baseStart_1311956 baseEnd_1311956 := by
    simpa [prefixWord, tailWord_1311956, baseEnd_1311956] using wordTrace_append hprefix tailTrace_1311956
  have hstable : (prefixWord ++ tailWord_1311956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311956).length < 2 ^ (prefixWord ++ tailWord_1311956).sum := by decide
  have hdescent : baseEnd_1311956 < baseStart_1311956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311998 : List Nat := [4, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5]
def baseStart_1311998 : Nat := 118140960795 + 1311998 * 2 ^ 59
def prefixEnd_1311998 : Nat := 4983230072969 + 3 ^ 40 * 1311998 * 2
def baseEnd_1311998 : Nat := 673685591737663035491237

theorem tailTrace_1311998 : CollatzResearch.WordTrace tailWord_1311998 prefixEnd_1311998 673685591737663035491237 := by
  unfold tailWord_1311998
  simp only [CollatzResearch.WordTrace]
  refine ⟨5981562287607849033034081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31901665533908528176181765 5981562287607849033034081)
  ·
    refine ⟨4486171715705886774775561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5981562287607849033034081 4486171715705886774775561)
    ·
      refine ⟨3364628786779415081081671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4486171715705886774775561 3364628786779415081081671)
      ·
        refine ⟨5046943180169122621622507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3364628786779415081081671 5046943180169122621622507)
        ·
          refine ⟨7570414770253683932433761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5046943180169122621622507 7570414770253683932433761)
          ·
            refine ⟨5677811077690262949325321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7570414770253683932433761 5677811077690262949325321)
            ·
              refine ⟨4258358308267697211993991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5677811077690262949325321 4258358308267697211993991)
              ·
                refine ⟨6387537462401545817990987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4258358308267697211993991 6387537462401545817990987)
                ·
                  refine ⟨9581306193602318726986481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6387537462401545817990987 9581306193602318726986481)
                  ·
                    refine ⟨7185979645201739045239861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9581306193602318726986481 7185979645201739045239861)
                    ·
                      refine ⟨673685591737663035491237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7185979645201739045239861 673685591737663035491237)
                      ·
                        rfl

theorem cell23_1311998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_1311998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1311998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1311998 prefixEnd_1311998 := by exact prefixLift 1311998
  have htrace : WordTrace (prefixWord ++ tailWord_1311998) baseStart_1311998 baseEnd_1311998 := by
    simpa [prefixWord, tailWord_1311998, baseEnd_1311998] using wordTrace_append hprefix tailTrace_1311998
  have hstable : (prefixWord ++ tailWord_1311998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311998).length < 2 ^ (prefixWord ++ tailWord_1311998).sum := by decide
  have hdescent : baseEnd_1311998 < baseStart_1311998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312035 : List Nat := [1, 1, 1, 4, 2, 3, 1, 5, 1, 4]
def baseStart_1312035 : Nat := 118140960795 + 1312035 * 2 ^ 59
def prefixEnd_1312035 : Nat := 4983230072969 + 3 ^ 40 * 1312035 * 2
def baseEnd_1312035 : Nat := 224568196840626463576189

theorem tailTrace_1312035 : CollatzResearch.WordTrace tailWord_1312035 prefixEnd_1312035 224568196840626463576189 := by
  unfold tailWord_1312035
  simp only [CollatzResearch.WordTrace]
  refine ⟨47853847801728747583369559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31902565201152498388913039 47853847801728747583369559)
  ·
    refine ⟨71780771702593121375054339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47853847801728747583369559 71780771702593121375054339)
    ·
      refine ⟨107671157553889682062581509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71780771702593121375054339 107671157553889682062581509)
      ·
        refine ⟨20188342041354315386734033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107671157553889682062581509 20188342041354315386734033)
        ·
          refine ⟨15141256531015736540050525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20188342041354315386734033 15141256531015736540050525)
          ·
            refine ⟨5677971199130901202518947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15141256531015736540050525 5677971199130901202518947)
            ·
              refine ⟨8516956798696351803778421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5677971199130901202518947 8516956798696351803778421)
              ·
                refine ⟨798464699877782981604227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8516956798696351803778421 798464699877782981604227)
                ·
                  refine ⟨1197697049816674472406341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 798464699877782981604227 1197697049816674472406341)
                  ·
                    refine ⟨224568196840626463576189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1197697049816674472406341 224568196840626463576189)
                    ·
                      rfl

theorem cell23_1312035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 5, 1, 4].length) (baseStart_1312035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312035 prefixEnd_1312035 := by exact prefixLift 1312035
  have htrace : WordTrace (prefixWord ++ tailWord_1312035) baseStart_1312035 baseEnd_1312035 := by
    simpa [prefixWord, tailWord_1312035, baseEnd_1312035] using wordTrace_append hprefix tailTrace_1312035
  have hstable : (prefixWord ++ tailWord_1312035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312035).length < 2 ^ (prefixWord ++ tailWord_1312035).sum := by decide
  have hdescent : baseEnd_1312035 < baseStart_1312035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312051 : List Nat := [1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 6]
def baseStart_1312051 : Nat := 118140960795 + 1312051 * 2 ^ 59
def prefixEnd_1312051 : Nat := 4983230072969 + 3 ^ 40 * 1312051 * 2
def baseEnd_1312051 : Nat := 673712806212351328128493

theorem tailTrace_1312051 : CollatzResearch.WordTrace tailWord_1312051 prefixEnd_1312051 673712806212351328128493 := by
  unfold tailWord_1312051
  simp only [CollatzResearch.WordTrace]
  refine ⟨47854431369670782315952007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31902954246447188210634671 47854431369670782315952007)
  ·
    refine ⟨71781647054506173473928011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47854431369670782315952007 71781647054506173473928011)
    ·
      refine ⟨107672470581759260210892017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71781647054506173473928011 107672470581759260210892017)
      ·
        refine ⟨80754352936319445158169013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107672470581759260210892017 80754352936319445158169013)
        ·
          refine ⟨7570720587779947983578345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80754352936319445158169013 7570720587779947983578345)
          ·
            refine ⟨5678040440834960987683759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7570720587779947983578345 5678040440834960987683759)
            ·
              refine ⟨8517060661252441481525639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5678040440834960987683759 8517060661252441481525639)
              ·
                refine ⟨12775590991878662222288459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8517060661252441481525639 12775590991878662222288459)
                ·
                  refine ⟨19163386487817993333432689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12775590991878662222288459 19163386487817993333432689)
                  ·
                    refine ⟨14372539865863495000074517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19163386487817993333432689 14372539865863495000074517)
                    ·
                      refine ⟨673712806212351328128493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14372539865863495000074517 673712806212351328128493)
                      ·
                        rfl

theorem cell23_1312051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 6].length) (baseStart_1312051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312051 prefixEnd_1312051 := by exact prefixLift 1312051
  have htrace : WordTrace (prefixWord ++ tailWord_1312051) baseStart_1312051 baseEnd_1312051 := by
    simpa [prefixWord, tailWord_1312051, baseEnd_1312051] using wordTrace_append hprefix tailTrace_1312051
  have hstable : (prefixWord ++ tailWord_1312051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312051).length < 2 ^ (prefixWord ++ tailWord_1312051).sum := by decide
  have hdescent : baseEnd_1312051 < baseStart_1312051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312052 : List Nat := [2, 5, 1, 1, 1, 1, 1, 6, 1, 4]
def baseStart_1312052 : Nat := 118140960795 + 1312052 * 2 ^ 59
def prefixEnd_1312052 : Nat := 4983230072969 + 3 ^ 40 * 1312052 * 2
def baseEnd_1312052 : Nat := 224571106564335274738663

theorem tailTrace_1312052 : CollatzResearch.WordTrace tailWord_1312052 prefixEnd_1312052 224571106564335274738663 := by
  unfold tailWord_1312052
  simp only [CollatzResearch.WordTrace]
  refine ⟨23927233921333579743369205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31902978561778106324492273 23927233921333579743369205)
  ·
    refine ⟨2243178180125023100940863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23927233921333579743369205 2243178180125023100940863)
    ·
      refine ⟨3364767270187534651411295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2243178180125023100940863 3364767270187534651411295)
      ·
        refine ⟨5047150905281301977116943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3364767270187534651411295 5047150905281301977116943)
        ·
          refine ⟨7570726357921952965675415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5047150905281301977116943 7570726357921952965675415)
          ·
            refine ⟨11356089536882929448513123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7570726357921952965675415 11356089536882929448513123)
            ·
              refine ⟨17034134305324394172769685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11356089536882929448513123 17034134305324394172769685)
              ·
                refine ⟨798475045562080976848579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17034134305324394172769685 798475045562080976848579)
                ·
                  refine ⟨1197712568343121465272869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 798475045562080976848579 1197712568343121465272869)
                  ·
                    refine ⟨224571106564335274738663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1197712568343121465272869 224571106564335274738663)
                    ·
                      rfl

theorem cell23_1312052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_1312052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312052 prefixEnd_1312052 := by exact prefixLift 1312052
  have htrace : WordTrace (prefixWord ++ tailWord_1312052) baseStart_1312052 baseEnd_1312052 := by
    simpa [prefixWord, tailWord_1312052, baseEnd_1312052] using wordTrace_append hprefix tailTrace_1312052
  have hstable : (prefixWord ++ tailWord_1312052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312052).length < 2 ^ (prefixWord ++ tailWord_1312052).sum := by decide
  have hdescent : baseEnd_1312052 < baseStart_1312052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312085 : List Nat := [1, 3, 2, 2, 3, 1, 2, 1, 1, 5, 2]
def baseStart_1312085 : Nat := 118140960795 + 1312085 * 2 ^ 59
def prefixEnd_1312085 : Nat := 4983230072969 + 3 ^ 40 * 1312085 * 2
def baseEnd_1312085 : Nat := 673730264554604195103337

theorem tailTrace_1312085 : CollatzResearch.WordTrace tailWord_1312085 prefixEnd_1312085 673730264554604195103337 := by
  unfold tailWord_1312085
  simp only [CollatzResearch.WordTrace]
  refine ⟨47855671451547606122689709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31903780967698404081793139 47855671451547606122689709)
  ·
    refine ⟨17945876794330352296008641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47855671451547606122689709 17945876794330352296008641)
    ·
      refine ⟨13459407595747764222006481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17945876794330352296008641 13459407595747764222006481)
      ·
        refine ⟨10094555696810823166504861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13459407595747764222006481 10094555696810823166504861)
        ·
          refine ⟨3785458386304058687439323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10094555696810823166504861 3785458386304058687439323)
          ·
            refine ⟨5678187579456088031158985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3785458386304058687439323 5678187579456088031158985)
            ·
              refine ⟨4258640684592066023369239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5678187579456088031158985 4258640684592066023369239)
              ·
                refine ⟨6387961026888099035053859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4258640684592066023369239 6387961026888099035053859)
                ·
                  refine ⟨9581941540332148552580789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6387961026888099035053859 9581941540332148552580789)
                  ·
                    refine ⟨898307019406138926804449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9581941540332148552580789 898307019406138926804449)
                    ·
                      refine ⟨673730264554604195103337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 898307019406138926804449 673730264554604195103337)
                      ·
                        rfl

theorem cell23_1312085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 5, 2].length) (baseStart_1312085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312085 prefixEnd_1312085 := by exact prefixLift 1312085
  have htrace : WordTrace (prefixWord ++ tailWord_1312085) baseStart_1312085 baseEnd_1312085 := by
    simpa [prefixWord, tailWord_1312085, baseEnd_1312085] using wordTrace_append hprefix tailTrace_1312085
  have hstable : (prefixWord ++ tailWord_1312085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312085).length < 2 ^ (prefixWord ++ tailWord_1312085).sum := by decide
  have hdescent : baseEnd_1312085 < baseStart_1312085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312111 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 6]
def baseStart_1312111 : Nat := 118140960795 + 1312111 * 2 ^ 59
def prefixEnd_1312111 : Nat := 4983230072969 + 3 ^ 40 * 1312111 * 2
def baseEnd_1312111 : Nat := 673743615051621093378217

theorem tailTrace_1312111 : CollatzResearch.WordTrace tailWord_1312111 prefixEnd_1312111 673743615051621093378217 := by
  unfold tailWord_1312111
  simp only [CollatzResearch.WordTrace]
  refine ⟨47856619749453412563136187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31904413166302275042090791 47856619749453412563136187)
  ·
    refine ⟨71784929624180118844704281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47856619749453412563136187 71784929624180118844704281)
    ·
      refine ⟨53838697218135089133528211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71784929624180118844704281 53838697218135089133528211)
      ·
        refine ⟨80758045827202633700292317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53838697218135089133528211 80758045827202633700292317)
        ·
          refine ⟨30284267185200987637609619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80758045827202633700292317 30284267185200987637609619)
          ·
            refine ⟨45426400777801481456414429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30284267185200987637609619 45426400777801481456414429)
            ·
              refine ⟨17034900291675555546155411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45426400777801481456414429 17034900291675555546155411)
              ·
                refine ⟨25552350437513333319233117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17034900291675555546155411 25552350437513333319233117)
                ·
                  refine ⟨9582131414067499994712419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25552350437513333319233117 9582131414067499994712419)
                  ·
                    refine ⟨14373197121101249992068629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9582131414067499994712419 14373197121101249992068629)
                    ·
                      refine ⟨673743615051621093378217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14373197121101249992068629 673743615051621093378217)
                      ·
                        rfl

theorem cell23_1312111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 6].length) (baseStart_1312111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312111 prefixEnd_1312111 := by exact prefixLift 1312111
  have htrace : WordTrace (prefixWord ++ tailWord_1312111) baseStart_1312111 baseEnd_1312111 := by
    simpa [prefixWord, tailWord_1312111, baseEnd_1312111] using wordTrace_append hprefix tailTrace_1312111
  have hstable : (prefixWord ++ tailWord_1312111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312111).length < 2 ^ (prefixWord ++ tailWord_1312111).sum := by decide
  have hdescent : baseEnd_1312111 < baseStart_1312111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312121 : List Nat := [1, 2, 1, 3, 2, 1, 3, 10]
def baseStart_1312121 : Nat := 118140960795 + 1312121 * 2 ^ 59
def prefixEnd_1312121 : Nat := 4983230072969 + 3 ^ 40 * 1312121 * 2
def baseEnd_1312121 : Nat := 24953657402154298305673

theorem tailTrace_1312121 : CollatzResearch.WordTrace tailWord_1312121 prefixEnd_1312121 24953657402154298305673 := by
  unfold tailWord_1312121
  simp only [CollatzResearch.WordTrace]
  refine ⟨47856984479417184271000217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31904656319611456180666811 47856984479417184271000217)
  ·
    refine ⟨35892738359562888203250163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47856984479417184271000217 35892738359562888203250163)
    ·
      refine ⟨53839107539344332304875245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35892738359562888203250163 53839107539344332304875245)
      ·
        refine ⟨20189665327254124614328217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53839107539344332304875245 20189665327254124614328217)
        ·
          refine ⟨15142248995440593460746163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20189665327254124614328217 15142248995440593460746163)
          ·
            refine ⟨22713373493160890191119245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15142248995440593460746163 22713373493160890191119245)
            ·
              refine ⟨8517515059935333821669717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22713373493160890191119245 8517515059935333821669717)
              ·
                refine ⟨24953657402154298305673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 8517515059935333821669717 24953657402154298305673)
                ·
                  rfl

theorem cell23_1312121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 10].length) (baseStart_1312121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312121 prefixEnd_1312121 := by exact prefixLift 1312121
  have htrace : WordTrace (prefixWord ++ tailWord_1312121) baseStart_1312121 baseEnd_1312121 := by
    simpa [prefixWord, tailWord_1312121, baseEnd_1312121] using wordTrace_append hprefix tailTrace_1312121
  have hstable : (prefixWord ++ tailWord_1312121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312121).length < 2 ^ (prefixWord ++ tailWord_1312121).sum := by decide
  have hdescent : baseEnd_1312121 < baseStart_1312121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312125 : List Nat := [1, 4, 1, 1, 2, 2, 3, 3, 2, 4]
def baseStart_1312125 : Nat := 118140960795 + 1312125 * 2 ^ 59
def prefixEnd_1312125 : Nat := 4983230072969 + 3 ^ 40 * 1312125 * 2
def baseEnd_1312125 : Nat := 224583601260261346201051

theorem tailTrace_1312125 : CollatzResearch.WordTrace tailWord_1312125 prefixEnd_1312125 224583601260261346201051 := by
  unfold tailWord_1312125
  simp only [CollatzResearch.WordTrace]
  refine ⟨47857130371402692954145829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31904753580935128636097219 47857130371402692954145829)
  ·
    refine ⟨8973211944638004928902343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47857130371402692954145829 8973211944638004928902343)
    ·
      refine ⟨13459817916957007393353515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8973211944638004928902343 13459817916957007393353515)
      ·
        refine ⟨20189726875435511090030273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13459817916957007393353515 20189726875435511090030273)
        ·
          refine ⟨15142295156576633317522705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20189726875435511090030273 15142295156576633317522705)
          ·
            refine ⟨11356721367432474988142029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15142295156576633317522705 11356721367432474988142029)
            ·
              refine ⟨4258770512787178120553261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11356721367432474988142029 4258770512787178120553261)
              ·
                refine ⟨1597038942295191795207473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4258770512787178120553261 1597038942295191795207473)
                ·
                  refine ⟨1197779206721393846405605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1597038942295191795207473 1197779206721393846405605)
                  ·
                    refine ⟨224583601260261346201051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1197779206721393846405605 224583601260261346201051)
                    ·
                      rfl

theorem cell23_1312125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 3, 2, 4].length) (baseStart_1312125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312125 prefixEnd_1312125 := by exact prefixLift 1312125
  have htrace : WordTrace (prefixWord ++ tailWord_1312125) baseStart_1312125 baseEnd_1312125 := by
    simpa [prefixWord, tailWord_1312125, baseEnd_1312125] using wordTrace_append hprefix tailTrace_1312125
  have hstable : (prefixWord ++ tailWord_1312125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312125).length < 2 ^ (prefixWord ++ tailWord_1312125).sum := by decide
  have hdescent : baseEnd_1312125 < baseStart_1312125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312129 : List Nat := [1, 2, 4, 3, 3, 1, 1, 2, 1, 5]
def baseStart_1312129 : Nat := 118140960795 + 1312129 * 2 ^ 59
def prefixEnd_1312129 : Nat := 4983230072969 + 3 ^ 40 * 1312129 * 2
def baseEnd_1312129 : Nat := 224584285901134007651045

theorem tailTrace_1312129 : CollatzResearch.WordTrace tailWord_1312129 prefixEnd_1312129 224584285901134007651045 := by
  unfold tailWord_1312129
  simp only [CollatzResearch.WordTrace]
  refine ⟨47857276263388201637291441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31904850842258801091527627 47857276263388201637291441)
  ·
    refine ⟨35892957197541151227968581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47857276263388201637291441 35892957197541151227968581)
    ·
      refine ⟨6729929474538965855244109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35892957197541151227968581 6729929474538965855244109)
      ·
        refine ⟨2523723552952112195716541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6729929474538965855244109 2523723552952112195716541)
        ·
          refine ⟨946396332357042073393703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2523723552952112195716541 946396332357042073393703)
          ·
            refine ⟨1419594498535563110090555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 946396332357042073393703 1419594498535563110090555)
            ·
              refine ⟨2129391747803344665135833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1419594498535563110090555 2129391747803344665135833)
              ·
                refine ⟨1597043810852508498851875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2129391747803344665135833 1597043810852508498851875)
                ·
                  refine ⟨2395565716278762748277813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1597043810852508498851875 2395565716278762748277813)
                  ·
                    refine ⟨224584285901134007651045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2395565716278762748277813 224584285901134007651045)
                    ·
                      rfl

theorem cell23_1312129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_1312129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312129 prefixEnd_1312129 := by exact prefixLift 1312129
  have htrace : WordTrace (prefixWord ++ tailWord_1312129) baseStart_1312129 baseEnd_1312129 := by
    simpa [prefixWord, tailWord_1312129, baseEnd_1312129] using wordTrace_append hprefix tailTrace_1312129
  have hstable : (prefixWord ++ tailWord_1312129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312129).length < 2 ^ (prefixWord ++ tailWord_1312129).sum := by decide
  have hdescent : baseEnd_1312129 < baseStart_1312129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312132 : List Nat := [2, 3, 2, 1, 1, 5, 1, 2, 1, 1, 4]
def baseStart_1312132 : Nat := 118140960795 + 1312132 * 2 ^ 59
def prefixEnd_1312132 : Nat := 4983230072969 + 3 ^ 40 * 1312132 * 2
def baseEnd_1312132 : Nat := 673754398145365511215621

theorem tailTrace_1312132 : CollatzResearch.WordTrace tailWord_1312132 prefixEnd_1312132 673754398145365511215621 := by
  unfold tailWord_1312132
  simp only [CollatzResearch.WordTrace]
  refine ⟨23928692841188666574825325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31904923788251555433100433 23928692841188666574825325)
  ·
    refine ⟨8973259815445749965559497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23928692841188666574825325 8973259815445749965559497)
    ·
      refine ⟨6729944861584312474169623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8973259815445749965559497 6729944861584312474169623)
      ·
        refine ⟨10094917292376468711254435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6729944861584312474169623 10094917292376468711254435)
        ·
          refine ⟨15142375938564703066881653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10094917292376468711254435 15142375938564703066881653)
          ·
            refine ⟨1419597744240440912520155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15142375938564703066881653 1419597744240440912520155)
            ·
              refine ⟨2129396616360661368780233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1419597744240440912520155 2129396616360661368780233)
              ·
                refine ⟨1597047462270496026585175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2129396616360661368780233 1597047462270496026585175)
                ·
                  refine ⟨2395571193405744039877763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1597047462270496026585175 2395571193405744039877763)
                  ·
                    refine ⟨3593356790108616059816645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2395571193405744039877763 3593356790108616059816645)
                    ·
                      refine ⟨673754398145365511215621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3593356790108616059816645 673754398145365511215621)
                      ·
                        rfl

theorem cell23_1312132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_1312132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312132 prefixEnd_1312132 := by exact prefixLift 1312132
  have htrace : WordTrace (prefixWord ++ tailWord_1312132) baseStart_1312132 baseEnd_1312132 := by
    simpa [prefixWord, tailWord_1312132, baseEnd_1312132] using wordTrace_append hprefix tailTrace_1312132
  have hstable : (prefixWord ++ tailWord_1312132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312132).length < 2 ^ (prefixWord ++ tailWord_1312132).sum := by decide
  have hdescent : baseEnd_1312132 < baseStart_1312132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312135 : List Nat := [1, 1, 4, 2, 2, 3, 1, 1, 3, 2, 3]
def baseStart_1312135 : Nat := 118140960795 + 1312135 * 2 ^ 59
def prefixEnd_1312135 : Nat := 4983230072969 + 3 ^ 40 * 1312135 * 2
def baseEnd_1312135 : Nat := 673755938587328999478107

theorem tailTrace_1312135 : CollatzResearch.WordTrace tailWord_1312135 prefixEnd_1312135 673755938587328999478107 := by
  unfold tailWord_1312135
  simp only [CollatzResearch.WordTrace]
  refine ⟨47857495101366464662009859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31904996734244309774673239 47857495101366464662009859)
  ·
    refine ⟨71786242652049696993014789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47857495101366464662009859 71786242652049696993014789)
    ·
      refine ⟨13459920497259318186190273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71786242652049696993014789 13459920497259318186190273)
      ·
        refine ⟨10094940372944488639642705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13459920497259318186190273 10094940372944488639642705)
        ·
          refine ⟨7571205279708366479732029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10094940372944488639642705 7571205279708366479732029)
          ·
            refine ⟨2839201979890637429899511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7571205279708366479732029 2839201979890637429899511)
            ·
              refine ⟨4258802969835956144849267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2839201979890637429899511 4258802969835956144849267)
              ·
                refine ⟨6388204454753934217273901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4258802969835956144849267 6388204454753934217273901)
                ·
                  refine ⟨2395576670532725331477713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6388204454753934217273901 2395576670532725331477713)
                  ·
                    refine ⟨1796682502899543998608285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2395576670532725331477713 1796682502899543998608285)
                    ·
                      refine ⟨673755938587328999478107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1796682502899543998608285 673755938587328999478107)
                      ·
                        rfl

theorem cell23_1312135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_1312135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312135 prefixEnd_1312135 := by exact prefixLift 1312135
  have htrace : WordTrace (prefixWord ++ tailWord_1312135) baseStart_1312135 baseEnd_1312135 := by
    simpa [prefixWord, tailWord_1312135, baseEnd_1312135] using wordTrace_append hprefix tailTrace_1312135
  have hstable : (prefixWord ++ tailWord_1312135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312135).length < 2 ^ (prefixWord ++ tailWord_1312135).sum := by decide
  have hdescent : baseEnd_1312135 < baseStart_1312135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312152 : List Nat := [2, 1, 2, 5, 2, 2, 1, 1, 1, 1, 5]
def baseStart_1312152 : Nat := 118140960795 + 1312152 * 2 ^ 59
def prefixEnd_1312152 : Nat := 4983230072969 + 3 ^ 40 * 1312152 * 2
def baseEnd_1312152 : Nat := 673764667758455432965529

theorem tailTrace_1312152 : CollatzResearch.WordTrace tailWord_1312152 prefixEnd_1312152 673764667758455432965529 := by
  unfold tailWord_1312152
  simp only [CollatzResearch.WordTrace]
  refine ⟨23929057571152438282689355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31905410094869917710252473 23929057571152438282689355)
  ·
    refine ⟨35893586356728657424034033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23929057571152438282689355 35893586356728657424034033)
    ·
      refine ⟨26920189767546493068025525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35893586356728657424034033 26920189767546493068025525)
      ·
        refine ⟨2523767790707483725127393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26920189767546493068025525 2523767790707483725127393)
        ·
          refine ⟨1892825843030612793845545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2523767790707483725127393 1892825843030612793845545)
          ·
            refine ⟨1419619382272959595384159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1892825843030612793845545 1419619382272959595384159)
            ·
              refine ⟨2129429073409439393076239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1419619382272959595384159 2129429073409439393076239)
              ·
                refine ⟨3194143610114159089614359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2129429073409439393076239 3194143610114159089614359)
                ·
                  refine ⟨4791215415171238634421539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3194143610114159089614359 4791215415171238634421539)
                  ·
                    refine ⟨7186823122756857951632309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4791215415171238634421539 7186823122756857951632309)
                    ·
                      refine ⟨673764667758455432965529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7186823122756857951632309 673764667758455432965529)
                      ·
                        rfl

theorem cell23_1312152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_1312152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312152 prefixEnd_1312152 := by exact prefixLift 1312152
  have htrace : WordTrace (prefixWord ++ tailWord_1312152) baseStart_1312152 baseEnd_1312152 := by
    simpa [prefixWord, tailWord_1312152, baseEnd_1312152] using wordTrace_append hprefix tailTrace_1312152
  have hstable : (prefixWord ++ tailWord_1312152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312152).length < 2 ^ (prefixWord ++ tailWord_1312152).sum := by decide
  have hdescent : baseEnd_1312152 < baseStart_1312152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312171 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 8]
def baseStart_1312171 : Nat := 118140960795 + 1312171 * 2 ^ 59
def prefixEnd_1312171 : Nat := 4983230072969 + 3 ^ 40 * 1312171 * 2
def baseEnd_1312171 : Nat := 673774423890890858627941

theorem tailTrace_1312171 : CollatzResearch.WordTrace tailWord_1312171 prefixEnd_1312171 673774423890890858627941 := by
  unfold tailWord_1312171
  simp only [CollatzResearch.WordTrace]
  refine ⟨47858808129236042810320367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31905872086157361873546911 47858808129236042810320367)
  ·
    refine ⟨71788212193854064215480551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47858808129236042810320367 71788212193854064215480551)
    ·
      refine ⟨107682318290781096323220827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71788212193854064215480551 107682318290781096323220827)
      ·
        refine ⟨161523477436171644484831241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107682318290781096323220827 161523477436171644484831241)
        ·
          refine ⟨121142608077128733363623431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161523477436171644484831241 121142608077128733363623431)
          ·
            refine ⟨181713912115693100045435147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121142608077128733363623431 181713912115693100045435147)
            ·
              refine ⟨272570868173539650068152721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181713912115693100045435147 272570868173539650068152721)
              ·
                refine ⟨204428151130154737551114541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 272570868173539650068152721 204428151130154737551114541)
                ·
                  refine ⟨76660556673808026581667953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 204428151130154737551114541 76660556673808026581667953)
                  ·
                    refine ⟨57495417505356019936250965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 76660556673808026581667953 57495417505356019936250965)
                    ·
                      refine ⟨673774423890890858627941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 57495417505356019936250965 673774423890890858627941)
                      ·
                        rfl

theorem cell23_1312171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 8].length) (baseStart_1312171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312171 prefixEnd_1312171 := by exact prefixLift 1312171
  have htrace : WordTrace (prefixWord ++ tailWord_1312171) baseStart_1312171 baseEnd_1312171 := by
    simpa [prefixWord, tailWord_1312171, baseEnd_1312171] using wordTrace_append hprefix tailTrace_1312171
  have hstable : (prefixWord ++ tailWord_1312171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312171).length < 2 ^ (prefixWord ++ tailWord_1312171).sum := by decide
  have hdescent : baseEnd_1312171 < baseStart_1312171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312208 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 3]
def baseStart_1312208 : Nat := 118140960795 + 1312208 * 2 ^ 59
def prefixEnd_1312208 : Nat := 4983230072969 + 3 ^ 40 * 1312208 * 2
def baseEnd_1312208 : Nat := 673793422675107213865271

theorem tailTrace_1312208 : CollatzResearch.WordTrace tailWord_1312208 prefixEnd_1312208 673793422675107213865271 := by
  unfold tailWord_1312208
  simp only [CollatzResearch.WordTrace]
  refine ⟨23930078815050999064708639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31906771753401332086278185 23930078815050999064708639)
  ·
    refine ⟨35895118222576498597062959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23930078815050999064708639 35895118222576498597062959)
    ·
      refine ⟨53842677333864747895594439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35895118222576498597062959 53842677333864747895594439)
      ·
        refine ⟨80764016000797121843391659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53842677333864747895594439 80764016000797121843391659)
        ·
          refine ⟨121146024001195682765087489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80764016000797121843391659 121146024001195682765087489)
          ·
            refine ⟨90859518000896762073815617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121146024001195682765087489 90859518000896762073815617)
            ·
              refine ⟨68144638500672571555361713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90859518000896762073815617 68144638500672571555361713)
              ·
                refine ⟨51108478875504428666521285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68144638500672571555361713 51108478875504428666521285)
                ·
                  refine ⟨9582839789157080374972741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51108478875504428666521285 9582839789157080374972741)
                  ·
                    refine ⟨1796782460466952570307389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9582839789157080374972741 1796782460466952570307389)
                    ·
                      refine ⟨673793422675107213865271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1796782460466952570307389 673793422675107213865271)
                      ·
                        rfl

theorem cell23_1312208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 3].length) (baseStart_1312208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312208 prefixEnd_1312208 := by exact prefixLift 1312208
  have htrace : WordTrace (prefixWord ++ tailWord_1312208) baseStart_1312208 baseEnd_1312208 := by
    simpa [prefixWord, tailWord_1312208, baseEnd_1312208] using wordTrace_append hprefix tailTrace_1312208
  have hstable : (prefixWord ++ tailWord_1312208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312208).length < 2 ^ (prefixWord ++ tailWord_1312208).sum := by decide
  have hdescent : baseEnd_1312208 < baseStart_1312208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312275 : List Nat := [1, 1, 1, 2, 1, 7, 1, 2, 2, 5]
def baseStart_1312275 : Nat := 118140960795 + 1312275 * 2 ^ 59
def prefixEnd_1312275 : Nat := 4983230072969 + 3 ^ 40 * 1312275 * 2
def baseEnd_1312275 : Nat := 224609275292986150575821

theorem tailTrace_1312275 : CollatzResearch.WordTrace tailWord_1312275 prefixEnd_1312275 224609275292986150575821 := by
  unfold tailWord_1312275
  simp only [CollatzResearch.WordTrace]
  refine ⟨47862601320859268572106279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31908400880572845714737519 47862601320859268572106279)
  ·
    refine ⟨71793901981288902858159419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47862601320859268572106279 71793901981288902858159419)
    ·
      refine ⟨107690852971933354287239129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71793901981288902858159419 107690852971933354287239129)
      ·
        refine ⟨80768139728950015715429347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107690852971933354287239129 80768139728950015715429347)
        ·
          refine ⟨121152209593425023573144021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80768139728950015715429347 121152209593425023573144021)
          ·
            refine ⟨2839504912345898989995563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 121152209593425023573144021 2839504912345898989995563)
            ·
              refine ⟨4259257368518848484993345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2839504912345898989995563 4259257368518848484993345)
              ·
                refine ⟨3194443026389136363745009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4259257368518848484993345 3194443026389136363745009)
                ·
                  refine ⟨2395832269791852272808757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3194443026389136363745009 2395832269791852272808757)
                  ·
                    refine ⟨224609275292986150575821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2395832269791852272808757 224609275292986150575821)
                    ·
                      rfl

theorem cell23_1312275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 2, 5].length) (baseStart_1312275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312275 prefixEnd_1312275 := by exact prefixLift 1312275
  have htrace : WordTrace (prefixWord ++ tailWord_1312275) baseStart_1312275 baseEnd_1312275 := by
    simpa [prefixWord, tailWord_1312275, baseEnd_1312275] using wordTrace_append hprefix tailTrace_1312275
  have hstable : (prefixWord ++ tailWord_1312275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312275).length < 2 ^ (prefixWord ++ tailWord_1312275).sum := by decide
  have hdescent : baseEnd_1312275 < baseStart_1312275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312285 : List Nat := [1, 4, 2, 2, 1, 1, 3, 1, 1, 2, 5]
def baseStart_1312285 : Nat := 118140960795 + 1312285 * 2 ^ 59
def prefixEnd_1312285 : Nat := 4983230072969 + 3 ^ 40 * 1312285 * 2
def baseEnd_1312285 : Nat := 673832960685503412602417

theorem tailTrace_1312285 : CollatzResearch.WordTrace tailWord_1312285 prefixEnd_1312285 673832960685503412602417 := by
  unfold tailWord_1312285
  simp only [CollatzResearch.WordTrace]
  refine ⟨47862966050823040279970309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31908644033882026853313539 47862966050823040279970309)
  ·
    refine ⟨8974306134529320052494433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47862966050823040279970309 8974306134529320052494433)
    ·
      refine ⟨6730729600896990039370825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8974306134529320052494433 6730729600896990039370825)
      ·
        refine ⟨5048047200672742529528119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6730729600896990039370825 5048047200672742529528119)
        ·
          refine ⟨7572070801009113794292179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5048047200672742529528119 7572070801009113794292179)
          ·
            refine ⟨11358106201513670691438269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7572070801009113794292179 11358106201513670691438269)
            ·
              refine ⟨4259289825567626509289351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11358106201513670691438269 4259289825567626509289351)
              ·
                refine ⟨6388934738351439763934027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4259289825567626509289351 6388934738351439763934027)
                ·
                  refine ⟨9583402107527159645901041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6388934738351439763934027 9583402107527159645901041)
                  ·
                    refine ⟨7187551580645369734425781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9583402107527159645901041 7187551580645369734425781)
                    ·
                      refine ⟨673832960685503412602417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7187551580645369734425781 673832960685503412602417)
                      ·
                        rfl

theorem cell23_1312285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_1312285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312285 prefixEnd_1312285 := by exact prefixLift 1312285
  have htrace : WordTrace (prefixWord ++ tailWord_1312285) baseStart_1312285 baseEnd_1312285 := by
    simpa [prefixWord, tailWord_1312285, baseEnd_1312285] using wordTrace_append hprefix tailTrace_1312285
  have hstable : (prefixWord ++ tailWord_1312285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312285).length < 2 ^ (prefixWord ++ tailWord_1312285).sum := by decide
  have hdescent : baseEnd_1312285 < baseStart_1312285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312305 : List Nat := [1, 2, 2, 3, 1, 1, 1, 3, 5, 4]
def baseStart_1312305 : Nat := 118140960795 + 1312305 * 2 ^ 59
def prefixEnd_1312305 : Nat := 4983230072969 + 3 ^ 40 * 1312305 * 2
def baseEnd_1312305 : Nat := 224614410099531111450775

theorem tailTrace_1312305 : CollatzResearch.WordTrace tailWord_1312305 prefixEnd_1312305 224614410099531111450775 := by
  unfold tailWord_1312305
  simp only [CollatzResearch.WordTrace]
  refine ⟨47863695510750583695698369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31909130340500389130465579 47863695510750583695698369)
  ·
    refine ⟨35897771633062937771773777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47863695510750583695698369 35897771633062937771773777)
    ·
      refine ⟨26923328724797203328830333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35897771633062937771773777 26923328724797203328830333)
      ·
        refine ⟨10096248271798951248311375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26923328724797203328830333 10096248271798951248311375)
        ·
          refine ⟨15144372407698426872467063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10096248271798951248311375 15144372407698426872467063)
          ·
            refine ⟨22716558611547640308700595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15144372407698426872467063 22716558611547640308700595)
            ·
              refine ⟨34074837917321460463050893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22716558611547640308700595 34074837917321460463050893)
              ·
                refine ⟨12778064218995547673644085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34074837917321460463050893 12778064218995547673644085)
                ·
                  refine ⟨1197943520530832594404133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12778064218995547673644085 1197943520530832594404133)
                  ·
                    refine ⟨224614410099531111450775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1197943520530832594404133 224614410099531111450775)
                    ·
                      rfl

theorem cell23_1312305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 5, 4].length) (baseStart_1312305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312305 prefixEnd_1312305 := by exact prefixLift 1312305
  have htrace : WordTrace (prefixWord ++ tailWord_1312305) baseStart_1312305 baseEnd_1312305 := by
    simpa [prefixWord, tailWord_1312305, baseEnd_1312305] using wordTrace_append hprefix tailTrace_1312305
  have hstable : (prefixWord ++ tailWord_1312305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312305).length < 2 ^ (prefixWord ++ tailWord_1312305).sum := by decide
  have hdescent : baseEnd_1312305 < baseStart_1312305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312312 : List Nat := [2, 1, 2, 1, 4, 3, 2, 1, 2, 1, 4]
def baseStart_1312312 : Nat := 118140960795 + 1312312 * 2 ^ 59
def prefixEnd_1312312 : Nat := 4983230072969 + 3 ^ 40 * 1312312 * 2
def baseEnd_1312312 : Nat := 673846824663174806964793

theorem tailTrace_1312312 : CollatzResearch.WordTrace tailWord_1312312 prefixEnd_1312312 673846824663174806964793 := by
  unfold tailWord_1312312
  simp only [CollatzResearch.WordTrace]
  refine ⟨23931975410862611945601595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31909300547816815927468793 23931975410862611945601595)
  ·
    refine ⟨35897963116293917918402393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23931975410862611945601595 35897963116293917918402393)
    ·
      refine ⟨26923472337220438438801795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35897963116293917918402393 26923472337220438438801795)
      ·
        refine ⟨40385208505830657658202693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26923472337220438438801795 40385208505830657658202693)
        ·
          refine ⟨7572226594843248310913005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40385208505830657658202693 7572226594843248310913005)
          ·
            refine ⟨2839584973066218116592377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7572226594843248310913005 2839584973066218116592377)
            ·
              refine ⟨2129688729799663587444283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2839584973066218116592377 2129688729799663587444283)
              ·
                refine ⟨3194533094699495381166425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2129688729799663587444283 3194533094699495381166425)
                ·
                  refine ⟨2395899821024621535874819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3194533094699495381166425 2395899821024621535874819)
                  ·
                    refine ⟨3593849731536932303812229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2395899821024621535874819 3593849731536932303812229)
                    ·
                      refine ⟨673846824663174806964793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3593849731536932303812229 673846824663174806964793)
                      ·
                        rfl

theorem cell23_1312312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 2, 1, 4].length) (baseStart_1312312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312312 prefixEnd_1312312 := by exact prefixLift 1312312
  have htrace : WordTrace (prefixWord ++ tailWord_1312312) baseStart_1312312 baseEnd_1312312 := by
    simpa [prefixWord, tailWord_1312312, baseEnd_1312312] using wordTrace_append hprefix tailTrace_1312312
  have hstable : (prefixWord ++ tailWord_1312312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312312).length < 2 ^ (prefixWord ++ tailWord_1312312).sum := by decide
  have hdescent : baseEnd_1312312 < baseStart_1312312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312332 : List Nat := [2, 2, 1, 3, 1, 3, 2, 2, 2, 2, 3]
def baseStart_1312332 : Nat := 118140960795 + 1312332 * 2 ^ 59
def prefixEnd_1312332 : Nat := 4983230072969 + 3 ^ 40 * 1312332 * 2
def baseEnd_1312332 : Nat := 673857094276264728714701

theorem tailTrace_1312332 : CollatzResearch.WordTrace tailWord_1312332 prefixEnd_1312332 673857094276264728714701 := by
  unfold tailWord_1312332
  simp only [CollatzResearch.WordTrace]
  refine ⟨23932340140826383653465625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31909786854435178204620833 23932340140826383653465625)
  ·
    refine ⟨17949255105619787740099219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23932340140826383653465625 17949255105619787740099219)
    ·
      refine ⟨26923882658429681610148829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17949255105619787740099219 26923882658429681610148829)
      ·
        refine ⟨10096455996911130603805811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26923882658429681610148829 10096455996911130603805811)
        ·
          refine ⟨15144683995366695905708717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10096455996911130603805811 15144683995366695905708717)
          ·
            refine ⟨5679256498262510964640769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15144683995366695905708717 5679256498262510964640769)
            ·
              refine ⟨4259442373696883223480577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5679256498262510964640769 4259442373696883223480577)
              ·
                refine ⟨3194581780272662417610433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4259442373696883223480577 3194581780272662417610433)
                ·
                  refine ⟨2395936335204496813207825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3194581780272662417610433 2395936335204496813207825)
                  ·
                    refine ⟨1796952251403372609905869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2395936335204496813207825 1796952251403372609905869)
                    ·
                      refine ⟨673857094276264728714701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1796952251403372609905869 673857094276264728714701)
                      ·
                        rfl

theorem cell23_1312332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_1312332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312332 prefixEnd_1312332 := by exact prefixLift 1312332
  have htrace : WordTrace (prefixWord ++ tailWord_1312332) baseStart_1312332 baseEnd_1312332 := by
    simpa [prefixWord, tailWord_1312332, baseEnd_1312332] using wordTrace_append hprefix tailTrace_1312332
  have hstable : (prefixWord ++ tailWord_1312332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312332).length < 2 ^ (prefixWord ++ tailWord_1312332).sum := by decide
  have hdescent : baseEnd_1312332 < baseStart_1312332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312366 : List Nat := [4, 1, 2, 2, 3, 2, 1, 1, 2, 2, 3]
def baseStart_1312366 : Nat := 118140960795 + 1312366 * 2 ^ 59
def prefixEnd_1312366 : Nat := 4983230072969 + 3 ^ 40 * 1312366 * 2
def baseEnd_1312366 : Nat := 673874552618517595689545

theorem tailTrace_1312366 : CollatzResearch.WordTrace tailWord_1312366 prefixEnd_1312366 673874552618517595689545 := by
  unfold tailWord_1312366
  simp only [CollatzResearch.WordTrace]
  refine ⟨5983240045441198889208619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31910613575686394075779301 5983240045441198889208619)
  ·
    refine ⟨8974860068161798333812929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5983240045441198889208619 8974860068161798333812929)
    ·
      refine ⟨6731145051121348750359697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8974860068161798333812929 6731145051121348750359697)
      ·
        refine ⟨5048358788341011562769773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6731145051121348750359697 5048358788341011562769773)
        ·
          refine ⟨1893134545627879336038665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5048358788341011562769773 1893134545627879336038665)
          ·
            refine ⟨1419850909220909502028999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1893134545627879336038665 1419850909220909502028999)
            ·
              refine ⟨2129776363831364253043499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1419850909220909502028999 2129776363831364253043499)
              ·
                refine ⟨3194664545747046379565249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2129776363831364253043499 3194664545747046379565249)
                ·
                  refine ⟨2395998409310284784673937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3194664545747046379565249 2395998409310284784673937)
                  ·
                    refine ⟨1796998806982713588505453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2395998409310284784673937 1796998806982713588505453)
                    ·
                      refine ⟨673874552618517595689545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1796998806982713588505453 673874552618517595689545)
                      ·
                        rfl

theorem cell23_1312366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_1312366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312366 prefixEnd_1312366 := by exact prefixLift 1312366
  have htrace : WordTrace (prefixWord ++ tailWord_1312366) baseStart_1312366 baseEnd_1312366 := by
    simpa [prefixWord, tailWord_1312366, baseEnd_1312366] using wordTrace_append hprefix tailTrace_1312366
  have hstable : (prefixWord ++ tailWord_1312366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312366).length < 2 ^ (prefixWord ++ tailWord_1312366).sum := by decide
  have hdescent : baseEnd_1312366 < baseStart_1312366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312419 : List Nat := [1, 1, 1, 4, 1, 1, 3, 4, 3, 2, 2]
def baseStart_1312419 : Nat := 118140960795 + 1312419 * 2 ^ 59
def prefixEnd_1312419 : Nat := 4983230072969 + 3 ^ 40 * 1312419 * 2
def baseEnd_1312419 : Nat := 673901767093205888326801

theorem tailTrace_1312419 : CollatzResearch.WordTrace tailWord_1312419 prefixEnd_1312419 673901767093205888326801 := by
  unfold tailWord_1312419
  simp only [CollatzResearch.WordTrace]
  refine ⟨47867853432337581165348311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31911902288225054110232207 47867853432337581165348311)
  ·
    refine ⟨71801780148506371748022467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47867853432337581165348311 71801780148506371748022467)
    ·
      refine ⟨107702670222759557622033701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71801780148506371748022467 107702670222759557622033701)
      ·
        refine ⟨20194250666767417054131319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107702670222759557622033701 20194250666767417054131319)
        ·
          refine ⟨30291376000151125581196979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20194250666767417054131319 30291376000151125581196979)
          ·
            refine ⟨45437064000226688371795469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30291376000151125581196979 45437064000226688371795469)
            ·
              refine ⟨17038899000085008139423301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45437064000226688371795469 17038899000085008139423301)
              ·
                refine ⟨3194793562515939026141869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17038899000085008139423301 3194793562515939026141869)
                ·
                  refine ⟨1198047585943477134803201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3194793562515939026141869 1198047585943477134803201)
                  ·
                    refine ⟨898535689457607851102401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1198047585943477134803201 898535689457607851102401)
                    ·
                      refine ⟨673901767093205888326801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 898535689457607851102401 673901767093205888326801)
                      ·
                        rfl

theorem cell23_1312419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 3, 2, 2].length) (baseStart_1312419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312419 prefixEnd_1312419 := by exact prefixLift 1312419
  have htrace : WordTrace (prefixWord ++ tailWord_1312419) baseStart_1312419 baseEnd_1312419 := by
    simpa [prefixWord, tailWord_1312419, baseEnd_1312419] using wordTrace_append hprefix tailTrace_1312419
  have hstable : (prefixWord ++ tailWord_1312419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312419).length < 2 ^ (prefixWord ++ tailWord_1312419).sum := by decide
  have hdescent : baseEnd_1312419 < baseStart_1312419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312439 : List Nat := [1, 1, 3, 1, 5, 1, 2, 3, 1, 2, 3]
def baseStart_1312439 : Nat := 118140960795 + 1312439 * 2 ^ 59
def prefixEnd_1312439 : Nat := 4983230072969 + 3 ^ 40 * 1312439 * 2
def baseEnd_1312439 : Nat := 673912036706295810076709

theorem tailTrace_1312439 : CollatzResearch.WordTrace tailWord_1312439 prefixEnd_1312439 673912036706295810076709 := by
  unfold tailWord_1312439
  simp only [CollatzResearch.WordTrace]
  refine ⟨47868582892265124581076371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31912388594843416387384247 47868582892265124581076371)
  ·
    refine ⟨71802874338397686871614557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47868582892265124581076371 71802874338397686871614557)
    ·
      refine ⟨26926077876899132576855459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71802874338397686871614557 26926077876899132576855459)
      ·
        refine ⟨40389116815348698865283189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26926077876899132576855459 40389116815348698865283189)
        ·
          refine ⟨3786479701438940518620299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40389116815348698865283189 3786479701438940518620299)
          ·
            refine ⟨5679719552158410777930449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3786479701438940518620299 5679719552158410777930449)
            ·
              refine ⟨4259789664118808083447837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5679719552158410777930449 4259789664118808083447837)
              ·
                refine ⟨1597421124044553031292939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4259789664118808083447837 1597421124044553031292939)
                ·
                  refine ⟨2396131686066829546939409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1597421124044553031292939 2396131686066829546939409)
                  ·
                    refine ⟨1797098764550122160204557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2396131686066829546939409 1797098764550122160204557)
                    ·
                      refine ⟨673912036706295810076709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1797098764550122160204557 673912036706295810076709)
                      ·
                        rfl

theorem cell23_1312439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 3, 1, 2, 3].length) (baseStart_1312439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312439 prefixEnd_1312439 := by exact prefixLift 1312439
  have htrace : WordTrace (prefixWord ++ tailWord_1312439) baseStart_1312439 baseEnd_1312439 := by
    simpa [prefixWord, tailWord_1312439, baseEnd_1312439] using wordTrace_append hprefix tailTrace_1312439
  have hstable : (prefixWord ++ tailWord_1312439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312439).length < 2 ^ (prefixWord ++ tailWord_1312439).sum := by decide
  have hdescent : baseEnd_1312439 < baseStart_1312439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312455 : List Nat := [1, 1, 4, 1, 1, 1, 4, 1, 2, 7]
def baseStart_1312455 : Nat := 118140960795 + 1312455 * 2 ^ 59
def prefixEnd_1312455 : Nat := 4983230072969 + 3 ^ 40 * 1312455 * 2
def baseEnd_1312455 : Nat := 224640084132255915825545

theorem tailTrace_1312455 : CollatzResearch.WordTrace tailWord_1312455 prefixEnd_1312455 224640084132255915825545 := by
  unfold tailWord_1312455
  simp only [CollatzResearch.WordTrace]
  refine ⟨47869166460207159313658819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31912777640138106209105879 47869166460207159313658819)
  ·
    refine ⟨71803749690310738970488229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47869166460207159313658819 71803749690310738970488229)
    ·
      refine ⟨13463203066933263556966543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71803749690310738970488229 13463203066933263556966543)
      ·
        refine ⟨20194804600399895335449815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13463203066933263556966543 20194804600399895335449815)
        ·
          refine ⟨30292206900599843003174723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20194804600399895335449815 30292206900599843003174723)
          ·
            refine ⟨45438310350899764504762085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30292206900599843003174723 45438310350899764504762085)
            ·
              refine ⟨8519683190793705844642891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45438310350899764504762085 8519683190793705844642891)
              ·
                refine ⟨12779524786190558766964337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8519683190793705844642891 12779524786190558766964337)
                ·
                  refine ⟨9584643589642919075223253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12779524786190558766964337 9584643589642919075223253)
                  ·
                    refine ⟨224640084132255915825545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9584643589642919075223253 224640084132255915825545)
                    ·
                      rfl

theorem cell23_1312455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_1312455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312455 prefixEnd_1312455 := by exact prefixLift 1312455
  have htrace : WordTrace (prefixWord ++ tailWord_1312455) baseStart_1312455 baseEnd_1312455 := by
    simpa [prefixWord, tailWord_1312455, baseEnd_1312455] using wordTrace_append hprefix tailTrace_1312455
  have hstable : (prefixWord ++ tailWord_1312455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312455).length < 2 ^ (prefixWord ++ tailWord_1312455).sum := by decide
  have hdescent : baseEnd_1312455 < baseStart_1312455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312470 : List Nat := [5, 2, 1, 3, 1, 2, 1, 2, 1, 1, 4]
def baseStart_1312470 : Nat := 118140960795 + 1312470 * 2 ^ 59
def prefixEnd_1312470 : Nat := 4983230072969 + 3 ^ 40 * 1312470 * 2
def baseEnd_1312470 : Nat := 673927954606585188789067

theorem tailTrace_1312470 : CollatzResearch.WordTrace tailWord_1312470 prefixEnd_1312470 673927954606585188789067 := by
  unfold tailWord_1312470
  simp only [CollatzResearch.WordTrace]
  refine ⟨2991857097197051054715929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31913142370101877916969909 2991857097197051054715929)
  ·
    refine ⟨2243892822897788291036947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2991857097197051054715929 2243892822897788291036947)
    ·
      refine ⟨3365839234346682436555421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2243892822897788291036947 3365839234346682436555421)
      ·
        refine ⟨1262189712880005913708283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3365839234346682436555421 1262189712880005913708283)
        ·
          refine ⟨1893284569320008870562425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1262189712880005913708283 1893284569320008870562425)
          ·
            refine ⟨1419963426990006652921819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1893284569320008870562425 1419963426990006652921819)
            ·
              refine ⟨2129945140485009979382729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1419963426990006652921819 2129945140485009979382729)
              ·
                refine ⟨1597458855363757484537047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2129945140485009979382729 1597458855363757484537047)
                ·
                  refine ⟨2396188283045636226805571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1597458855363757484537047 2396188283045636226805571)
                  ·
                    refine ⟨3594282424568454340208357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2396188283045636226805571 3594282424568454340208357)
                    ·
                      refine ⟨673927954606585188789067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3594282424568454340208357 673927954606585188789067)
                      ·
                        rfl

theorem cell23_1312470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_1312470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312470 prefixEnd_1312470 := by exact prefixLift 1312470
  have htrace : WordTrace (prefixWord ++ tailWord_1312470) baseStart_1312470 baseEnd_1312470 := by
    simpa [prefixWord, tailWord_1312470, baseEnd_1312470] using wordTrace_append hprefix tailTrace_1312470
  have hstable : (prefixWord ++ tailWord_1312470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312470).length < 2 ^ (prefixWord ++ tailWord_1312470).sum := by decide
  have hdescent : baseEnd_1312470 < baseStart_1312470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312479 : List Nat := [1, 1, 2, 3, 2, 2, 3, 1, 3, 3, 2]
def baseStart_1312479 : Nat := 118140960795 + 1312479 * 2 ^ 59
def prefixEnd_1312479 : Nat := 4983230072969 + 3 ^ 40 * 1312479 * 2
def baseEnd_1312479 : Nat := 673932575932475653576525

theorem tailTrace_1312479 : CollatzResearch.WordTrace tailWord_1312479 prefixEnd_1312479 673932575932475653576525 := by
  unfold tailWord_1312479
  simp only [CollatzResearch.WordTrace]
  refine ⟨47870041812120211412532491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31913361208080140941688327 47870041812120211412532491)
  ·
    refine ⟨71805062718180317118798737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47870041812120211412532491 71805062718180317118798737)
    ·
      refine ⟨53853797038635237839099053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71805062718180317118798737 53853797038635237839099053)
      ·
        refine ⟨20195173889488214189662145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53853797038635237839099053 20195173889488214189662145)
        ·
          refine ⟨15146380417116160642246609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20195173889488214189662145 15146380417116160642246609)
          ·
            refine ⟨11359785312837120481684957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15146380417116160642246609 11359785312837120481684957)
            ·
              refine ⟨4259919492313920180631859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11359785312837120481684957 4259919492313920180631859)
              ·
                refine ⟨6389879238470880270947789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4259919492313920180631859 6389879238470880270947789)
                ·
                  refine ⟨2396204714426580101605421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6389879238470880270947789 2396204714426580101605421)
                  ·
                    refine ⟨898576767909967538102033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2396204714426580101605421 898576767909967538102033)
                    ·
                      refine ⟨673932575932475653576525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 898576767909967538102033 673932575932475653576525)
                      ·
                        rfl

theorem cell23_1312479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 3, 3, 2].length) (baseStart_1312479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312479 prefixEnd_1312479 := by exact prefixLift 1312479
  have htrace : WordTrace (prefixWord ++ tailWord_1312479) baseStart_1312479 baseEnd_1312479 := by
    simpa [prefixWord, tailWord_1312479, baseEnd_1312479] using wordTrace_append hprefix tailTrace_1312479
  have hstable : (prefixWord ++ tailWord_1312479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312479).length < 2 ^ (prefixWord ++ tailWord_1312479).sum := by decide
  have hdescent : baseEnd_1312479 < baseStart_1312479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312505 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 1, 5, 6]
def baseStart_1312505 : Nat := 118140960795 + 1312505 * 2 ^ 59
def prefixEnd_1312505 : Nat := 4983230072969 + 3 ^ 40 * 1312505 * 2
def baseEnd_1312505 : Nat := 673945926429492551851405

theorem tailTrace_1312505 : CollatzResearch.WordTrace tailWord_1312505 prefixEnd_1312505 673945926429492551851405 := by
  unfold tailWord_1312505
  simp only [CollatzResearch.WordTrace]
  refine ⟨47870990110026017852978969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31913993406684011901985979 47870990110026017852978969)
  ·
    refine ⟨35903242582519513389734227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47870990110026017852978969 35903242582519513389734227)
    ·
      refine ⟨53854863873779270084601341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35903242582519513389734227 53854863873779270084601341)
      ·
        refine ⟨20195573952667226281725503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53854863873779270084601341 20195573952667226281725503)
        ·
          refine ⟨30293360929000839422588255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20195573952667226281725503 30293360929000839422588255)
          ·
            refine ⟨45440041393501259133882383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30293360929000839422588255 45440041393501259133882383)
            ·
              refine ⟨68160062090251888700823575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45440041393501259133882383 68160062090251888700823575)
              ·
                refine ⟨102240093135377833051235363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68160062090251888700823575 102240093135377833051235363)
                ·
                  refine ⟨153360139703066749576853045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102240093135377833051235363 153360139703066749576853045)
                  ·
                    refine ⟨14377513097162507772829973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 153360139703066749576853045 14377513097162507772829973)
                    ·
                      refine ⟨673945926429492551851405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14377513097162507772829973 673945926429492551851405)
                      ·
                        rfl

theorem cell23_1312505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_1312505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312505 prefixEnd_1312505 := by exact prefixLift 1312505
  have htrace : WordTrace (prefixWord ++ tailWord_1312505) baseStart_1312505 baseEnd_1312505 := by
    simpa [prefixWord, tailWord_1312505, baseEnd_1312505] using wordTrace_append hprefix tailTrace_1312505
  have hstable : (prefixWord ++ tailWord_1312505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312505).length < 2 ^ (prefixWord ++ tailWord_1312505).sum := by decide
  have hdescent : baseEnd_1312505 < baseStart_1312505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312519 : List Nat := [1, 1, 4, 4, 2, 1, 1, 1, 2, 6]
def baseStart_1312519 : Nat := 118140960795 + 1312519 * 2 ^ 59
def prefixEnd_1312519 : Nat := 4983230072969 + 3 ^ 40 * 1312519 * 2
def baseEnd_1312519 : Nat := 224651038386218499025447

theorem tailTrace_1312519 : CollatzResearch.WordTrace tailWord_1312519 prefixEnd_1312519 224651038386218499025447 := by
  unfold tailWord_1312519
  simp only [CollatzResearch.WordTrace]
  refine ⟨47871500731975298243988611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31914333821316865495992407 47871500731975298243988611)
  ·
    refine ⟨71807251097962947365982917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47871500731975298243988611 71807251097962947365982917)
    ·
      refine ⟨13463859580868052631121797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71807251097962947365982917 13463859580868052631121797)
      ·
        refine ⟨2524473671412759868335337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13463859580868052631121797 2524473671412759868335337)
        ·
          refine ⟨1893355253559569901251503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2524473671412759868335337 1893355253559569901251503)
          ·
            refine ⟨2840032880339354851877255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1893355253559569901251503 2840032880339354851877255)
            ·
              refine ⟨4260049320509032277815883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2840032880339354851877255 4260049320509032277815883)
              ·
                refine ⟨6390073980763548416723825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4260049320509032277815883 6390073980763548416723825)
                ·
                  refine ⟨4792555485572661312542869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6390073980763548416723825 4792555485572661312542869)
                  ·
                    refine ⟨224651038386218499025447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4792555485572661312542869 224651038386218499025447)
                    ·
                      rfl

theorem cell23_1312519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 6].length) (baseStart_1312519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312519 prefixEnd_1312519 := by exact prefixLift 1312519
  have htrace : WordTrace (prefixWord ++ tailWord_1312519) baseStart_1312519 baseEnd_1312519 := by
    simpa [prefixWord, tailWord_1312519, baseEnd_1312519] using wordTrace_append hprefix tailTrace_1312519
  have hstable : (prefixWord ++ tailWord_1312519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312519).length < 2 ^ (prefixWord ++ tailWord_1312519).sum := by decide
  have hdescent : baseEnd_1312519 < baseStart_1312519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312522 : List Nat := [3, 1, 2, 2, 1, 3, 1, 1, 1, 4, 4]
def baseStart_1312522 : Nat := 118140960795 + 1312522 * 2 ^ 59
def prefixEnd_1312522 : Nat := 4983230072969 + 3 ^ 40 * 1312522 * 2
def baseEnd_1312522 : Nat := 673954655600618985338827

theorem tailTrace_1312522 : CollatzResearch.WordTrace tailWord_1312522 prefixEnd_1312522 673954655600618985338827 := by
  unfold tailWord_1312522
  simp only [CollatzResearch.WordTrace]
  refine ⟨11967902537741107439086955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31914406767309619837565213 11967902537741107439086955)
  ·
    refine ⟨17951853806611661158630433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11967902537741107439086955 17951853806611661158630433)
    ·
      refine ⟨13463890354958745868972825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17951853806611661158630433 13463890354958745868972825)
      ·
        refine ⟨10097917766219059401729619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13463890354958745868972825 10097917766219059401729619)
        ·
          refine ⟨15146876649328589102594429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10097917766219059401729619 15146876649328589102594429)
          ·
            refine ⟨5680078743498220913472911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15146876649328589102594429 5680078743498220913472911)
            ·
              refine ⟨8520118115247331370209367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5680078743498220913472911 8520118115247331370209367)
              ·
                refine ⟨12780177172870997055314051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8520118115247331370209367 12780177172870997055314051)
                ·
                  refine ⟨19170265759306495582971077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12780177172870997055314051 19170265759306495582971077)
                  ·
                    refine ⟨3594424829869967921807077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19170265759306495582971077 3594424829869967921807077)
                    ·
                      refine ⟨673954655600618985338827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3594424829869967921807077 673954655600618985338827)
                      ·
                        rfl

theorem cell23_1312522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_1312522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312522 prefixEnd_1312522 := by exact prefixLift 1312522
  have htrace : WordTrace (prefixWord ++ tailWord_1312522) baseStart_1312522 baseEnd_1312522 := by
    simpa [prefixWord, tailWord_1312522, baseEnd_1312522] using wordTrace_append hprefix tailTrace_1312522
  have hstable : (prefixWord ++ tailWord_1312522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312522).length < 2 ^ (prefixWord ++ tailWord_1312522).sum := by decide
  have hdescent : baseEnd_1312522 < baseStart_1312522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312549 : List Nat := [1, 3, 1, 2, 3, 2, 1, 5, 5]
def baseStart_1312549 : Nat := 118140960795 + 1312549 * 2 ^ 59
def prefixEnd_1312549 : Nat := 4983230072969 + 3 ^ 40 * 1312549 * 2
def baseEnd_1312549 : Nat := 74885391064254486633467

theorem tailTrace_1312549 : CollatzResearch.WordTrace tailWord_1312549 prefixEnd_1312549 74885391064254486633467 := by
  unfold tailWord_1312549
  simp only [CollatzResearch.WordTrace]
  refine ⟨47872594921866613367580701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31915063281244408911720467 47872594921866613367580701)
  ·
    refine ⟨17952223095699980012842763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47872594921866613367580701 17952223095699980012842763)
    ·
      refine ⟨26928334643549970019264145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17952223095699980012842763 26928334643549970019264145)
      ·
        refine ⟨20196250982662477514448109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26928334643549970019264145 20196250982662477514448109)
        ·
          refine ⟨7573594118498429067918041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20196250982662477514448109 7573594118498429067918041)
          ·
            refine ⟨5680195588873821800938531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7573594118498429067918041 5680195588873821800938531)
            ·
              refine ⟨8520293383310732701407797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5680195588873821800938531 8520293383310732701407797)
              ·
                refine ⟨798777504685381190756981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8520293383310732701407797 798777504685381190756981)
                ·
                  refine ⟨74885391064254486633467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 798777504685381190756981 74885391064254486633467)
                  ·
                    rfl

theorem cell23_1312549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 5, 5].length) (baseStart_1312549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312549 prefixEnd_1312549 := by exact prefixLift 1312549
  have htrace : WordTrace (prefixWord ++ tailWord_1312549) baseStart_1312549 baseEnd_1312549 := by
    simpa [prefixWord, tailWord_1312549, baseEnd_1312549] using wordTrace_append hprefix tailTrace_1312549
  have hstable : (prefixWord ++ tailWord_1312549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312549).length < 2 ^ (prefixWord ++ tailWord_1312549).sum := by decide
  have hdescent : baseEnd_1312549 < baseStart_1312549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312566 : List Nat := [5, 1, 2, 2, 1, 2, 2, 1, 7]
def baseStart_1312566 : Nat := 118140960795 + 1312566 * 2 ^ 59
def prefixEnd_1312566 : Nat := 4983230072969 + 3 ^ 40 * 1312566 * 2
def baseEnd_1312566 : Nat := 74886360972157423687625

theorem tailTrace_1312566 : CollatzResearch.WordTrace tailWord_1312566 prefixEnd_1312566 74886360972157423687625 := by
  unfold tailWord_1312566
  simp only [CollatzResearch.WordTrace]
  refine ⟨2992075935175314079434347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31915476641870016847299701 2992075935175314079434347)
  ·
    refine ⟨4488113902762971119151521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2992075935175314079434347 4488113902762971119151521)
    ·
      refine ⟨3366085427072228339363641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4488113902762971119151521 3366085427072228339363641)
      ·
        refine ⟨2524564070304171254522731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3366085427072228339363641 2524564070304171254522731)
        ·
          refine ⟨3786846105456256881784097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2524564070304171254522731 3786846105456256881784097)
          ·
            refine ⟨2840134579092192661338073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3786846105456256881784097 2840134579092192661338073)
            ·
              refine ⟨2130100934319144496003555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2840134579092192661338073 2130100934319144496003555)
              ·
                refine ⟨3195151401478716744005333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2130100934319144496003555 3195151401478716744005333)
                ·
                  refine ⟨74886360972157423687625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3195151401478716744005333 74886360972157423687625)
                  ·
                    rfl

theorem cell23_1312566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_1312566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312566 prefixEnd_1312566 := by exact prefixLift 1312566
  have htrace : WordTrace (prefixWord ++ tailWord_1312566) baseStart_1312566 baseEnd_1312566 := by
    simpa [prefixWord, tailWord_1312566, baseEnd_1312566] using wordTrace_append hprefix tailTrace_1312566
  have hstable : (prefixWord ++ tailWord_1312566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312566).length < 2 ^ (prefixWord ++ tailWord_1312566).sum := by decide
  have hdescent : baseEnd_1312566 < baseStart_1312566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312572 : List Nat := [2, 2, 2, 2, 1, 1, 2, 3, 1, 2, 5]
def baseStart_1312572 : Nat := 118140960795 + 1312572 * 2 ^ 59
def prefixEnd_1312572 : Nat := 4983230072969 + 3 ^ 40 * 1312572 * 2
def baseEnd_1312572 : Nat := 673980329633343789713597

theorem tailTrace_1312572 : CollatzResearch.WordTrace tailWord_1312572 prefixEnd_1312572 673980329633343789713597 := by
  unfold tailWord_1312572
  simp only [CollatzResearch.WordTrace]
  refine ⟨23936716900391644147833985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31915622533855525530445313 23936716900391644147833985)
  ·
    refine ⟨17952537675293733110875489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23936716900391644147833985 17952537675293733110875489)
    ·
      refine ⟨13464403256470299833156617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17952537675293733110875489 13464403256470299833156617)
      ·
        refine ⟨10098302442352724874867463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13464403256470299833156617 10098302442352724874867463)
        ·
          refine ⟨15147453663529087312301195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10098302442352724874867463 15147453663529087312301195)
          ·
            refine ⟨22721180495293630968451793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15147453663529087312301195 22721180495293630968451793)
            ·
              refine ⟨17040885371470223226338845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22721180495293630968451793 17040885371470223226338845)
              ·
                refine ⟨6390332014301333709877067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17040885371470223226338845 6390332014301333709877067)
                ·
                  refine ⟨9585498021452000564815601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6390332014301333709877067 9585498021452000564815601)
                  ·
                    refine ⟨7189123516089000423611701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9585498021452000564815601 7189123516089000423611701)
                    ·
                      refine ⟨673980329633343789713597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7189123516089000423611701 673980329633343789713597)
                      ·
                        rfl

theorem cell23_1312572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_1312572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312572 prefixEnd_1312572 := by exact prefixLift 1312572
  have htrace : WordTrace (prefixWord ++ tailWord_1312572) baseStart_1312572 baseEnd_1312572 := by
    simpa [prefixWord, tailWord_1312572, baseEnd_1312572] using wordTrace_append hprefix tailTrace_1312572
  have hstable : (prefixWord ++ tailWord_1312572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312572).length < 2 ^ (prefixWord ++ tailWord_1312572).sum := by decide
  have hdescent : baseEnd_1312572 < baseStart_1312572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312659 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 5, 5, 2]
def baseStart_1312659 : Nat := 118140960795 + 1312659 * 2 ^ 59
def prefixEnd_1312659 : Nat := 4983230072969 + 3 ^ 40 * 1312659 * 2
def baseEnd_1312659 : Nat := 674025002450284949325697

theorem tailTrace_1312659 : CollatzResearch.WordTrace tailWord_1312659 prefixEnd_1312659 674025002450284949325697 := by
  unfold tailWord_1312659
  simp only [CollatzResearch.WordTrace]
  refine ⟨47876606951468102154085031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31917737967645401436056687 47876606951468102154085031)
  ·
    refine ⟨71814910427202153231127547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47876606951468102154085031 71814910427202153231127547)
    ·
      refine ⟨107722365640803229846691321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71814910427202153231127547 107722365640803229846691321)
      ·
        refine ⟨80791774230602422385018491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107722365640803229846691321 80791774230602422385018491)
        ·
          refine ⟨121187661345903633577527737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80791774230602422385018491 121187661345903633577527737)
          ·
            refine ⟨90890746009427725183145803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121187661345903633577527737 90890746009427725183145803)
            ·
              refine ⟨136336119014141587774718705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90890746009427725183145803 136336119014141587774718705)
              ·
                refine ⟨102252089260606190831039029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136336119014141587774718705 102252089260606190831039029)
                ·
                  refine ⟨9586133368181830390409909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 102252089260606190831039029 9586133368181830390409909)
                  ·
                    refine ⟨898700003267046599100929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9586133368181830390409909 898700003267046599100929)
                    ·
                      refine ⟨674025002450284949325697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 898700003267046599100929 674025002450284949325697)
                      ·
                        rfl

theorem cell23_1312659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 5, 2].length) (baseStart_1312659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312659 prefixEnd_1312659 := by exact prefixLift 1312659
  have htrace : WordTrace (prefixWord ++ tailWord_1312659) baseStart_1312659 baseEnd_1312659 := by
    simpa [prefixWord, tailWord_1312659, baseEnd_1312659] using wordTrace_append hprefix tailTrace_1312659
  have hstable : (prefixWord ++ tailWord_1312659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312659).length < 2 ^ (prefixWord ++ tailWord_1312659).sum := by decide
  have hdescent : baseEnd_1312659 < baseStart_1312659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312700 : List Nat := [2, 2, 2, 5, 1, 1, 1, 2, 3, 1, 3]
def baseStart_1312700 : Nat := 118140960795 + 1312700 * 2 ^ 59
def prefixEnd_1312700 : Nat := 4983230072969 + 3 ^ 40 * 1312700 * 2
def baseEnd_1312700 : Nat := 674046055157119288913009

theorem tailTrace_1312700 : CollatzResearch.WordTrace tailWord_1312700 prefixEnd_1312700 674046055157119288913009 := by
  unfold tailWord_1312700
  simp only [CollatzResearch.WordTrace]
  refine ⟨23939051172159783078163777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31918734896213044104218369 23939051172159783078163777)
  ·
    refine ⟨17954288379119837308622833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23939051172159783078163777 17954288379119837308622833)
    ·
      refine ⟨13465716284339877981467125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17954288379119837308622833 13465716284339877981467125)
      ·
        refine ⟨1262410901656863560762543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13465716284339877981467125 1262410901656863560762543)
        ·
          refine ⟨1893616352485295341143815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1262410901656863560762543 1893616352485295341143815)
          ·
            refine ⟨2840424528727943011715723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1893616352485295341143815 2840424528727943011715723)
            ·
              refine ⟨4260636793091914517573585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2840424528727943011715723 4260636793091914517573585)
              ·
                refine ⟨3195477594818935888180189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4260636793091914517573585 3195477594818935888180189)
                ·
                  refine ⟨1198304098057100958067571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3195477594818935888180189 1198304098057100958067571)
                  ·
                    refine ⟨1797456147085651437101357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1198304098057100958067571 1797456147085651437101357)
                    ·
                      refine ⟨674046055157119288913009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1797456147085651437101357 674046055157119288913009)
                      ·
                        rfl

theorem cell23_1312700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_1312700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312700 prefixEnd_1312700 := by exact prefixLift 1312700
  have htrace : WordTrace (prefixWord ++ tailWord_1312700) baseStart_1312700 baseEnd_1312700 := by
    simpa [prefixWord, tailWord_1312700, baseEnd_1312700] using wordTrace_append hprefix tailTrace_1312700
  have hstable : (prefixWord ++ tailWord_1312700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312700).length < 2 ^ (prefixWord ++ tailWord_1312700).sum := by decide
  have hdescent : baseEnd_1312700 < baseStart_1312700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312719 : List Nat := [1, 1, 2, 1, 1, 5, 1, 4, 1, 2, 4]
def baseStart_1312719 : Nat := 118140960795 + 1312719 * 2 ^ 59
def prefixEnd_1312719 : Nat := 4983230072969 + 3 ^ 40 * 1312719 * 2
def baseEnd_1312719 : Nat := 674055811289554714575421

theorem tailTrace_1312719 : CollatzResearch.WordTrace tailWord_1312719 prefixEnd_1312719 674055811289554714575421 := by
  unfold tailWord_1312719
  simp only [CollatzResearch.WordTrace]
  refine ⟨47878795331250732401269211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31919196887500488267512807 47878795331250732401269211)
  ·
    refine ⟨71818192996876098601903817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47878795331250732401269211 71818192996876098601903817)
    ·
      refine ⟨53863644747657073951427863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71818192996876098601903817 53863644747657073951427863)
      ·
        refine ⟨80795467121485610927141795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53863644747657073951427863 80795467121485610927141795)
        ·
          refine ⟨121193200682228416390712693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80795467121485610927141795 121193200682228416390712693)
          ·
            refine ⟨11361862563958914036629315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 121193200682228416390712693 11361862563958914036629315)
            ·
              refine ⟨17042793845938371054943973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11361862563958914036629315 17042793845938371054943973)
              ·
                refine ⟨3195523846113444572801995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17042793845938371054943973 3195523846113444572801995)
                ·
                  refine ⟨4793285769170166859202993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3195523846113444572801995 4793285769170166859202993)
                  ·
                    refine ⟨3594964326877625144402245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4793285769170166859202993 3594964326877625144402245)
                    ·
                      refine ⟨674055811289554714575421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3594964326877625144402245 674055811289554714575421)
                      ·
                        rfl

theorem cell23_1312719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 2, 4].length) (baseStart_1312719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312719 prefixEnd_1312719 := by exact prefixLift 1312719
  have htrace : WordTrace (prefixWord ++ tailWord_1312719) baseStart_1312719 baseEnd_1312719 := by
    simpa [prefixWord, tailWord_1312719, baseEnd_1312719] using wordTrace_append hprefix tailTrace_1312719
  have hstable : (prefixWord ++ tailWord_1312719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312719).length < 2 ^ (prefixWord ++ tailWord_1312719).sum := by decide
  have hdescent : baseEnd_1312719 < baseStart_1312719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312729 : List Nat := [1, 2, 1, 2, 6, 1, 10]
def baseStart_1312729 : Nat := 118140960795 + 1312729 * 2 ^ 59
def prefixEnd_1312729 : Nat := 4983230072969 + 3 ^ 40 * 1312729 * 2
def baseEnd_1312729 : Nat := 8321740075260489820375

theorem tailTrace_1312729 : CollatzResearch.WordTrace tailWord_1312729 prefixEnd_1312729 8321740075260489820375 := by
  unfold tailWord_1312729
  simp only [CollatzResearch.WordTrace]
  refine ⟨47879160061214504109133241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31919440040809669406088827 47879160061214504109133241)
  ·
    refine ⟨35909370045910878081849931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47879160061214504109133241 35909370045910878081849931)
    ·
      refine ⟨53864055068866317122774897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35909370045910878081849931 53864055068866317122774897)
      ·
        refine ⟨40398041301649737842081173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53864055068866317122774897 40398041301649737842081173)
        ·
          refine ⟨1893658186014831461347555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 40398041301649737842081173 1893658186014831461347555)
          ·
            refine ⟨2840487279022247192021333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1893658186014831461347555 2840487279022247192021333)
            ·
              refine ⟨8321740075260489820375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2840487279022247192021333 8321740075260489820375)
              ·
                rfl

theorem cell23_1312729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 10].length) (baseStart_1312729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312729 prefixEnd_1312729 := by exact prefixLift 1312729
  have htrace : WordTrace (prefixWord ++ tailWord_1312729) baseStart_1312729 baseEnd_1312729 := by
    simpa [prefixWord, tailWord_1312729, baseEnd_1312729] using wordTrace_append hprefix tailTrace_1312729
  have hstable : (prefixWord ++ tailWord_1312729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312729).length < 2 ^ (prefixWord ++ tailWord_1312729).sum := by decide
  have hdescent : baseEnd_1312729 < baseStart_1312729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312733 : List Nat := [1, 4, 3, 1, 3, 1, 1, 1, 4, 4]
def baseStart_1312733 : Nat := 118140960795 + 1312733 * 2 ^ 59
def prefixEnd_1312733 : Nat := 4983230072969 + 3 ^ 40 * 1312733 * 2
def baseEnd_1312733 : Nat := 224687666672905886600119

theorem tailTrace_1312733 : CollatzResearch.WordTrace tailWord_1312733 prefixEnd_1312733 224687666672905886600119 := by
  unfold tailWord_1312733
  simp only [CollatzResearch.WordTrace]
  refine ⟨47879305953200012792278853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31919537302133341861519235 47879305953200012792278853)
  ·
    refine ⟨8977369866225002398552285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47879305953200012792278853 8977369866225002398552285)
    ·
      refine ⟨3366513699834375899457107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8977369866225002398552285 3366513699834375899457107)
      ·
        refine ⟨5049770549751563849185661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3366513699834375899457107 5049770549751563849185661)
        ·
          refine ⟨1893663956156836443444623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5049770549751563849185661 1893663956156836443444623)
          ·
            refine ⟨2840495934235254665166935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1893663956156836443444623 2840495934235254665166935)
            ·
              refine ⟨4260743901352881997750403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2840495934235254665166935 4260743901352881997750403)
              ·
                refine ⟨6391115852029322996625605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4260743901352881997750403 6391115852029322996625605)
                ·
                  refine ⟨1198334222255498061867301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6391115852029322996625605 1198334222255498061867301)
                  ·
                    refine ⟨224687666672905886600119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1198334222255498061867301 224687666672905886600119)
                    ·
                      rfl

theorem cell23_1312733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_1312733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312733 prefixEnd_1312733 := by exact prefixLift 1312733
  have htrace : WordTrace (prefixWord ++ tailWord_1312733) baseStart_1312733 baseEnd_1312733 := by
    simpa [prefixWord, tailWord_1312733, baseEnd_1312733] using wordTrace_append hprefix tailTrace_1312733
  have hstable : (prefixWord ++ tailWord_1312733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312733).length < 2 ^ (prefixWord ++ tailWord_1312733).sum := by decide
  have hdescent : baseEnd_1312733 < baseStart_1312733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312740 : List Nat := [2, 3, 1, 1, 1, 1, 3, 6, 1, 2, 2]
def baseStart_1312740 : Nat := 118140960795 + 1312740 * 2 ^ 59
def prefixEnd_1312740 : Nat := 4983230072969 + 3 ^ 40 * 1312740 * 2
def baseEnd_1312740 : Nat := 674066594383299132412825

theorem tailTrace_1312740 : CollatzResearch.WordTrace tailWord_1312740 prefixEnd_1312740 674066594383299132412825 := by
  unfold tailWord_1312740
  simp only [CollatzResearch.WordTrace]
  refine ⟨23939780632087326493891837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31919707509449768658522449 23939780632087326493891837)
  ·
    refine ⟨8977417737032747435209439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23939780632087326493891837 8977417737032747435209439)
    ·
      refine ⟨13466126605549121152814159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8977417737032747435209439 13466126605549121152814159)
      ·
        refine ⟨20199189908323681729221239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13466126605549121152814159 20199189908323681729221239)
        ·
          refine ⟨30298784862485522593831859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20199189908323681729221239 30298784862485522593831859)
          ·
            refine ⟨45448177293728283890747789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30298784862485522593831859 45448177293728283890747789)
            ·
              refine ⟨17043066485148106459030421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45448177293728283890747789 17043066485148106459030421)
              ·
                refine ⟨798893741491317490267051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17043066485148106459030421 798893741491317490267051)
                ·
                  refine ⟨1198340612236976235400577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 798893741491317490267051 1198340612236976235400577)
                  ·
                    refine ⟨898755459177732176550433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1198340612236976235400577 898755459177732176550433)
                    ·
                      refine ⟨674066594383299132412825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 898755459177732176550433 674066594383299132412825)
                      ·
                        rfl

theorem cell23_1312740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 6, 1, 2, 2].length) (baseStart_1312740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312740 prefixEnd_1312740 := by exact prefixLift 1312740
  have htrace : WordTrace (prefixWord ++ tailWord_1312740) baseStart_1312740 baseEnd_1312740 := by
    simpa [prefixWord, tailWord_1312740, baseEnd_1312740] using wordTrace_append hprefix tailTrace_1312740
  have hstable : (prefixWord ++ tailWord_1312740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312740).length < 2 ^ (prefixWord ++ tailWord_1312740).sum := by decide
  have hdescent : baseEnd_1312740 < baseStart_1312740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312750 : List Nat := [4, 1, 2, 1, 3, 2, 3, 1, 2, 4]
def baseStart_1312750 : Nat := 118140960795 + 1312750 * 2 ^ 59
def prefixEnd_1312750 : Nat := 4983230072969 + 3 ^ 40 * 1312750 * 2
def baseEnd_1312750 : Nat := 224690576396614697762593

theorem tailTrace_1312750 : CollatzResearch.WordTrace tailWord_1312750 prefixEnd_1312750 224690576396614697762593 := by
  unfold tailWord_1312750
  simp only [CollatzResearch.WordTrace]
  refine ⟨5984990749267303086955963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31919950662758949797098469 5984990749267303086955963)
  ·
    refine ⟨8977486123900954630433945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5984990749267303086955963 8977486123900954630433945)
    ·
      refine ⟨6733114592925715972825459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8977486123900954630433945 6733114592925715972825459)
      ·
        refine ⟨10099671889388573959238189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6733114592925715972825459 10099671889388573959238189)
        ·
          refine ⟨3787376958520715234714321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10099671889388573959238189 3787376958520715234714321)
          ·
            refine ⟨2840532718890536426035741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3787376958520715234714321 2840532718890536426035741)
            ·
              refine ⟨1065199769583951159763403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2840532718890536426035741 1065199769583951159763403)
              ·
                refine ⟨1597799654375926739645105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1065199769583951159763403 1597799654375926739645105)
                ·
                  refine ⟨1198349740781945054733829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1597799654375926739645105 1198349740781945054733829)
                  ·
                    refine ⟨224690576396614697762593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1198349740781945054733829 224690576396614697762593)
                    ·
                      rfl

theorem cell23_1312750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_1312750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312750 prefixEnd_1312750 := by exact prefixLift 1312750
  have htrace : WordTrace (prefixWord ++ tailWord_1312750) baseStart_1312750 baseEnd_1312750 := by
    simpa [prefixWord, tailWord_1312750, baseEnd_1312750] using wordTrace_append hprefix tailTrace_1312750
  have hstable : (prefixWord ++ tailWord_1312750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312750).length < 2 ^ (prefixWord ++ tailWord_1312750).sum := by decide
  have hdescent : baseEnd_1312750 < baseStart_1312750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312753 : List Nat := [1, 2, 2, 2, 5, 2, 1, 1, 1, 2, 4]
def baseStart_1312753 : Nat := 118140960795 + 1312753 * 2 ^ 59
def prefixEnd_1312753 : Nat := 4983230072969 + 3 ^ 40 * 1312753 * 2
def baseEnd_1312753 : Nat := 674073269631807581550265

theorem tailTrace_1312753 : CollatzResearch.WordTrace tailWord_1312753 prefixEnd_1312753 674073269631807581550265 := by
  unfold tailWord_1312753
  simp only [CollatzResearch.WordTrace]
  refine ⟨47880035413127556208006913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31920023608751704138671275 47880035413127556208006913)
  ·
    refine ⟨35910026559845667156005185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47880035413127556208006913 35910026559845667156005185)
    ·
      refine ⟨26932519919884250367003889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35910026559845667156005185 26932519919884250367003889)
      ·
        refine ⟨20199389939913187775252917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26932519919884250367003889 20199389939913187775252917)
        ·
          refine ⟨1893692806866861353929961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20199389939913187775252917 1893692806866861353929961)
          ·
            refine ⟨1420269605150146015447471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1893692806866861353929961 1420269605150146015447471)
            ·
              refine ⟨2130404407725219023171207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1420269605150146015447471 2130404407725219023171207)
              ·
                refine ⟨3195606611587828534756811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2130404407725219023171207 3195606611587828534756811)
                ·
                  refine ⟨4793409917381742802135217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3195606611587828534756811 4793409917381742802135217)
                  ·
                    refine ⟨3595057438036307101601413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4793409917381742802135217 3595057438036307101601413)
                    ·
                      refine ⟨674073269631807581550265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3595057438036307101601413 674073269631807581550265)
                      ·
                        rfl

theorem cell23_1312753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 2, 4].length) (baseStart_1312753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312753 prefixEnd_1312753 := by exact prefixLift 1312753
  have htrace : WordTrace (prefixWord ++ tailWord_1312753) baseStart_1312753 baseEnd_1312753 := by
    simpa [prefixWord, tailWord_1312753, baseEnd_1312753] using wordTrace_append hprefix tailTrace_1312753
  have hstable : (prefixWord ++ tailWord_1312753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312753).length < 2 ^ (prefixWord ++ tailWord_1312753).sum := by decide
  have hdescent : baseEnd_1312753 < baseStart_1312753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312769 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 1, 4, 5]
def baseStart_1312769 : Nat := 118140960795 + 1312769 * 2 ^ 59
def prefixEnd_1312769 : Nat := 4983230072969 + 3 ^ 40 * 1312769 * 2
def baseEnd_1312769 : Nat := 674081485322279518950191

theorem tailTrace_1312769 : CollatzResearch.WordTrace tailWord_1312769 prefixEnd_1312769 674081485322279518950191 := by
  unfold tailWord_1312769
  simp only [CollatzResearch.WordTrace]
  refine ⟨47880618981069590940589361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31920412654046393960392907 47880618981069590940589361)
  ·
    refine ⟨35910464235802193205442021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47880618981069590940589361 35910464235802193205442021)
    ·
      refine ⟨6733212044212911226020379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35910464235802193205442021 6733212044212911226020379)
      ·
        refine ⟨10099818066319366839030569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6733212044212911226020379 10099818066319366839030569)
        ·
          refine ⟨7574863549739525129272927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10099818066319366839030569 7574863549739525129272927)
          ·
            refine ⟨11362295324609287693909391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7574863549739525129272927 11362295324609287693909391)
            ·
              refine ⟨17043442986913931540864087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11362295324609287693909391 17043442986913931540864087)
              ·
                refine ⟨25565164480370897311296131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17043442986913931540864087 25565164480370897311296131)
                ·
                  refine ⟨38347746720556345966944197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25565164480370897311296131 38347746720556345966944197)
                  ·
                    refine ⟨7190202510104314868802037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38347746720556345966944197 7190202510104314868802037)
                    ·
                      refine ⟨674081485322279518950191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7190202510104314868802037 674081485322279518950191)
                      ·
                        rfl

theorem cell23_1312769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_1312769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312769 prefixEnd_1312769 := by exact prefixLift 1312769
  have htrace : WordTrace (prefixWord ++ tailWord_1312769) baseStart_1312769 baseEnd_1312769 := by
    simpa [prefixWord, tailWord_1312769, baseEnd_1312769] using wordTrace_append hprefix tailTrace_1312769
  have hstable : (prefixWord ++ tailWord_1312769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312769).length < 2 ^ (prefixWord ++ tailWord_1312769).sum := by decide
  have hdescent : baseEnd_1312769 < baseStart_1312769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312799 : List Nat := [1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 5]
def baseStart_1312799 : Nat := 118140960795 + 1312799 * 2 ^ 59
def prefixEnd_1312799 : Nat := 4983230072969 + 3 ^ 40 * 1312799 * 2
def baseEnd_1312799 : Nat := 674096889741914401575053

theorem tailTrace_1312799 : CollatzResearch.WordTrace tailWord_1312799 prefixEnd_1312799 674096889741914401575053 := by
  unfold tailWord_1312799
  simp only [CollatzResearch.WordTrace]
  refine ⟨47881713170960906064181451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31921142113973937376120967 47881713170960906064181451)
  ·
    refine ⟨71822569756441359096272177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47881713170960906064181451 71822569756441359096272177)
    ·
      refine ⟨53866927317331019322204133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71822569756441359096272177 53866927317331019322204133)
      ·
        refine ⟨10100048871999566122913275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53866927317331019322204133 10100048871999566122913275)
        ·
          refine ⟨15150073307999349184369913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10100048871999566122913275 15150073307999349184369913)
          ·
            refine ⟨11362554980999511888277435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15150073307999349184369913 11362554980999511888277435)
            ·
              refine ⟨17043832471499267832416153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11362554980999511888277435 17043832471499267832416153)
              ·
                refine ⟨12782874353624450874312115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17043832471499267832416153 12782874353624450874312115)
                ·
                  refine ⟨19174311530436676311468173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12782874353624450874312115 19174311530436676311468173)
                  ·
                    refine ⟨7190366823913753616800565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19174311530436676311468173 7190366823913753616800565)
                    ·
                      refine ⟨674096889741914401575053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7190366823913753616800565 674096889741914401575053)
                      ·
                        rfl

theorem cell23_1312799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_1312799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312799 prefixEnd_1312799 := by exact prefixLift 1312799
  have htrace : WordTrace (prefixWord ++ tailWord_1312799) baseStart_1312799 baseEnd_1312799 := by
    simpa [prefixWord, tailWord_1312799, baseEnd_1312799] using wordTrace_append hprefix tailTrace_1312799
  have hstable : (prefixWord ++ tailWord_1312799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312799).length < 2 ^ (prefixWord ++ tailWord_1312799).sum := by decide
  have hdescent : baseEnd_1312799 < baseStart_1312799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312807 : List Nat := [1, 1, 7, 1, 2, 1, 1, 3, 2, 1, 3]
def baseStart_1312807 : Nat := 118140960795 + 1312807 * 2 ^ 59
def prefixEnd_1312807 : Nat := 4983230072969 + 3 ^ 40 * 1312807 * 2
def baseEnd_1312807 : Nat := 674100997587150370275017

theorem tailTrace_1312807 : CollatzResearch.WordTrace tailWord_1312807 prefixEnd_1312807 674100997587150370275017 := by
  unfold tailWord_1312807
  simp only [CollatzResearch.WordTrace]
  refine ⟨47882004954931923430472675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31921336636621282286981783 47882004954931923430472675)
  ·
    refine ⟨71823007432397885145709013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47882004954931923430472675 71823007432397885145709013)
    ·
      refine ⟨1683351736696825433102555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 71823007432397885145709013 1683351736696825433102555)
      ·
        refine ⟨2525027605045238149653833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1683351736696825433102555 2525027605045238149653833)
        ·
          refine ⟨1893770703783928612240375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2525027605045238149653833 1893770703783928612240375)
          ·
            refine ⟨2840656055675892918360563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1893770703783928612240375 2840656055675892918360563)
            ·
              refine ⟨4260984083513839377540845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2840656055675892918360563 4260984083513839377540845)
              ·
                refine ⟨1597869031317689766577817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4260984083513839377540845 1597869031317689766577817)
                ·
                  refine ⟨1198401773488267324933363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1597869031317689766577817 1198401773488267324933363)
                  ·
                    refine ⟨1797602660232400987400045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1198401773488267324933363 1797602660232400987400045)
                    ·
                      refine ⟨674100997587150370275017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1797602660232400987400045 674100997587150370275017)
                      ·
                        rfl

theorem cell23_1312807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_1312807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312807 prefixEnd_1312807 := by exact prefixLift 1312807
  have htrace : WordTrace (prefixWord ++ tailWord_1312807) baseStart_1312807 baseEnd_1312807 := by
    simpa [prefixWord, tailWord_1312807, baseEnd_1312807] using wordTrace_append hprefix tailTrace_1312807
  have hstable : (prefixWord ++ tailWord_1312807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312807).length < 2 ^ (prefixWord ++ tailWord_1312807).sum := by decide
  have hdescent : baseEnd_1312807 < baseStart_1312807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312809 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 8, 2, 4]
def baseStart_1312809 : Nat := 118140960795 + 1312809 * 2 ^ 59
def prefixEnd_1312809 : Nat := 4983230072969 + 3 ^ 40 * 1312809 * 2
def baseEnd_1312809 : Nat := 674102024548459362450007

theorem tailTrace_1312809 : CollatzResearch.WordTrace tailWord_1312809 prefixEnd_1312809 674102024548459362450007 := by
  unfold tailWord_1312809
  simp only [CollatzResearch.WordTrace]
  refine ⟨47882077900924677772045481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31921385267283118514696987 47882077900924677772045481)
  ·
    refine ⟨35911558425693508329034111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47882077900924677772045481 35911558425693508329034111)
    ·
      refine ⟨53867337638540262493551167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35911558425693508329034111 53867337638540262493551167)
      ·
        refine ⟨80801006457810393740326751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53867337638540262493551167 80801006457810393740326751)
        ·
          refine ⟨121201509686715590610490127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80801006457810393740326751 121201509686715590610490127)
          ·
            refine ⟨181802264530073385915735191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121201509686715590610490127 181802264530073385915735191)
            ·
              refine ⟨272703396795110078873602787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181802264530073385915735191 272703396795110078873602787)
              ·
                refine ⟨409055095192665118310404181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 272703396795110078873602787 409055095192665118310404181)
                ·
                  refine ⟨4793614396789044355200049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 409055095192665118310404181 4793614396789044355200049)
                  ·
                    refine ⟨3595210797591783266400037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4793614396789044355200049 3595210797591783266400037)
                    ·
                      refine ⟨674102024548459362450007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3595210797591783266400037 674102024548459362450007)
                      ·
                        rfl

theorem cell23_1312809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 2, 4].length) (baseStart_1312809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312809 prefixEnd_1312809 := by exact prefixLift 1312809
  have htrace : WordTrace (prefixWord ++ tailWord_1312809) baseStart_1312809 baseEnd_1312809 := by
    simpa [prefixWord, tailWord_1312809, baseEnd_1312809] using wordTrace_append hprefix tailTrace_1312809
  have hstable : (prefixWord ++ tailWord_1312809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312809).length < 2 ^ (prefixWord ++ tailWord_1312809).sum := by decide
  have hdescent : baseEnd_1312809 < baseStart_1312809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312819 : List Nat := [1, 1, 1, 2, 4, 1, 2, 4, 7]
def baseStart_1312819 : Nat := 118140960795 + 1312819 * 2 ^ 59
def prefixEnd_1312819 : Nat := 4983230072969 + 3 ^ 40 * 1312819 * 2
def baseEnd_1312819 : Nat := 74900795483889369258329

theorem tailTrace_1312819 : CollatzResearch.WordTrace tailWord_1312819 prefixEnd_1312819 74900795483889369258329 := by
  unfold tailWord_1312819
  simp only [CollatzResearch.WordTrace]
  refine ⟨47882442630888449479909511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31921628420592299653273007 47882442630888449479909511)
  ·
    refine ⟨71823663946332674219864267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47882442630888449479909511 71823663946332674219864267)
    ·
      refine ⟨107735495919499011329796401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71823663946332674219864267 107735495919499011329796401)
      ·
        refine ⟨80801621939624258497347301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107735495919499011329796401 80801621939624258497347301)
        ·
          refine ⟨15150304113679548468252619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80801621939624258497347301 15150304113679548468252619)
          ·
            refine ⟨22725456170519322702378929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15150304113679548468252619 22725456170519322702378929)
            ·
              refine ⟨17044092127889492026784197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22725456170519322702378929 17044092127889492026784197)
              ·
                refine ⟨3195767273979279755022037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17044092127889492026784197 3195767273979279755022037)
                ·
                  refine ⟨74900795483889369258329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3195767273979279755022037 74900795483889369258329)
                  ·
                    rfl

theorem cell23_1312819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 7].length) (baseStart_1312819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312819 prefixEnd_1312819 := by exact prefixLift 1312819
  have htrace : WordTrace (prefixWord ++ tailWord_1312819) baseStart_1312819 baseEnd_1312819 := by
    simpa [prefixWord, tailWord_1312819, baseEnd_1312819] using wordTrace_append hprefix tailTrace_1312819
  have hstable : (prefixWord ++ tailWord_1312819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312819).length < 2 ^ (prefixWord ++ tailWord_1312819).sum := by decide
  have hdescent : baseEnd_1312819 < baseStart_1312819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312849 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 3, 7]
def baseStart_1312849 : Nat := 118140960795 + 1312849 * 2 ^ 59
def prefixEnd_1312849 : Nat := 4983230072969 + 3 ^ 40 * 1312849 * 2
def baseEnd_1312849 : Nat := 224707521258213068649941

theorem tailTrace_1312849 : CollatzResearch.WordTrace tailWord_1312849 prefixEnd_1312849 224707521258213068649941 := by
  unfold tailWord_1312849
  simp only [CollatzResearch.WordTrace]
  refine ⟨47883536820779764603501601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31922357880519843069001067 47883536820779764603501601)
  ·
    refine ⟨35912652615584823452626201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47883536820779764603501601 35912652615584823452626201)
    ·
      refine ⟨26934489461688617589469651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35912652615584823452626201 26934489461688617589469651)
      ·
        refine ⟨40401734192532926384204477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26934489461688617589469651 40401734192532926384204477)
        ·
          refine ⟨15150650322199847394076679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40401734192532926384204477 15150650322199847394076679)
          ·
            refine ⟨22725975483299771091115019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15150650322199847394076679 22725975483299771091115019)
            ·
              refine ⟨34088963224949656636672529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22725975483299771091115019 34088963224949656636672529)
              ·
                refine ⟨25566722418712242477504397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34088963224949656636672529 25566722418712242477504397)
                ·
                  refine ⟨9587520907017090929064149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25566722418712242477504397 9587520907017090929064149)
                  ·
                    refine ⟨224707521258213068649941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9587520907017090929064149 224707521258213068649941)
                    ·
                      rfl

theorem cell23_1312849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 7].length) (baseStart_1312849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312849 prefixEnd_1312849 := by exact prefixLift 1312849
  have htrace : WordTrace (prefixWord ++ tailWord_1312849) baseStart_1312849 baseEnd_1312849 := by
    simpa [prefixWord, tailWord_1312849, baseEnd_1312849] using wordTrace_append hprefix tailTrace_1312849
  have hstable : (prefixWord ++ tailWord_1312849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312849).length < 2 ^ (prefixWord ++ tailWord_1312849).sum := by decide
  have hdescent : baseEnd_1312849 < baseStart_1312849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312853 : List Nat := [1, 3, 2, 2, 1, 4, 1, 4, 5]
def baseStart_1312853 : Nat := 118140960795 + 1312853 * 2 ^ 59
def prefixEnd_1312853 : Nat := 4983230072969 + 3 ^ 40 * 1312853 * 2
def baseEnd_1312853 : Nat := 74902735299695243366645

theorem tailTrace_1312853 : CollatzResearch.WordTrace tailWord_1312853 prefixEnd_1312853 74902735299695243366645 := by
  unfold tailWord_1312853
  simp only [CollatzResearch.WordTrace]
  refine ⟨47883682712765273286647213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31922455141843515524431475 47883682712765273286647213)
  ·
    refine ⟨17956381017286977482492705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47883682712765273286647213 17956381017286977482492705)
    ·
      refine ⟨13467285762965233111869529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17956381017286977482492705 13467285762965233111869529)
      ·
        refine ⟨10100464322223924833902147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13467285762965233111869529 10100464322223924833902147)
        ·
          refine ⟨15150696483335887250853221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10100464322223924833902147 15150696483335887250853221)
          ·
            refine ⟨2840755590625478859534979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15150696483335887250853221 2840755590625478859534979)
            ·
              refine ⟨4261133385938218289302469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2840755590625478859534979 4261133385938218289302469)
              ·
                refine ⟨798962509863415929244213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4261133385938218289302469 798962509863415929244213)
                ·
                  refine ⟨74902735299695243366645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 798962509863415929244213 74902735299695243366645)
                  ·
                    rfl

theorem cell23_1312853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 4, 5].length) (baseStart_1312853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312853 prefixEnd_1312853 := by exact prefixLift 1312853
  have htrace : WordTrace (prefixWord ++ tailWord_1312853) baseStart_1312853 baseEnd_1312853 := by
    simpa [prefixWord, tailWord_1312853, baseEnd_1312853] using wordTrace_append hprefix tailTrace_1312853
  have hstable : (prefixWord ++ tailWord_1312853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312853).length < 2 ^ (prefixWord ++ tailWord_1312853).sum := by decide
  have hdescent : baseEnd_1312853 < baseStart_1312853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312896 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 7, 4]
def baseStart_1312896 : Nat := 118140960795 + 1312896 * 2 ^ 59
def prefixEnd_1312896 : Nat := 4983230072969 + 3 ^ 40 * 1312896 * 2
def baseEnd_1312896 : Nat := 224715565788466840687369

theorem tailTrace_1312896 : CollatzResearch.WordTrace tailWord_1312896 prefixEnd_1312896 224715565788466840687369 := by
  unfold tailWord_1312896
  simp only [CollatzResearch.WordTrace]
  refine ⟨23942625525804745815231271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31923500701072994420308361 23942625525804745815231271)
  ·
    refine ⟨35913938288707118722846907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23942625525804745815231271 35913938288707118722846907)
    ·
      refine ⟨53870907433060678084270361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35913938288707118722846907 53870907433060678084270361)
      ·
        refine ⟨40403180574795508563202771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53870907433060678084270361 40403180574795508563202771)
        ·
          refine ⟨60604770862193262844804157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40403180574795508563202771 60604770862193262844804157)
          ·
            refine ⟨22726789073322473566801559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60604770862193262844804157 22726789073322473566801559)
            ·
              refine ⟨34090183609983710350202339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22726789073322473566801559 34090183609983710350202339)
              ·
                refine ⟨51135275414975565525303509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34090183609983710350202339 51135275414975565525303509)
                ·
                  refine ⟨1198483017538489816999301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 51135275414975565525303509 1198483017538489816999301)
                  ·
                    refine ⟨224715565788466840687369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1198483017538489816999301 224715565788466840687369)
                    ·
                      rfl

theorem cell23_1312896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 7, 4].length) (baseStart_1312896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312896 prefixEnd_1312896 := by exact prefixLift 1312896
  have htrace : WordTrace (prefixWord ++ tailWord_1312896) baseStart_1312896 baseEnd_1312896 := by
    simpa [prefixWord, tailWord_1312896, baseEnd_1312896] using wordTrace_append hprefix tailTrace_1312896
  have hstable : (prefixWord ++ tailWord_1312896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312896).length < 2 ^ (prefixWord ++ tailWord_1312896).sum := by decide
  have hdescent : baseEnd_1312896 < baseStart_1312896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312903 : List Nat := [1, 1, 4, 2, 1, 1, 3, 2, 2, 4, 2]
def baseStart_1312903 : Nat := 118140960795 + 1312903 * 2 ^ 59
def prefixEnd_1312903 : Nat := 4983230072969 + 3 ^ 40 * 1312903 * 2
def baseEnd_1312903 : Nat := 674150291729981994674575

theorem tailTrace_1312903 : CollatzResearch.WordTrace tailWord_1312903 prefixEnd_1312903 674150291729981994674575 := by
  unfold tailWord_1312903
  simp only [CollatzResearch.WordTrace]
  refine ⟨47885506362584131825967363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31923670908389421217311575 47885506362584131825967363)
  ·
    refine ⟨71828259543876197738951045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47885506362584131825967363 71828259543876197738951045)
    ·
      refine ⟨13467798664476787076053321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71828259543876197738951045 13467798664476787076053321)
      ·
        refine ⟨10100848998357590307039991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13467798664476787076053321 10100848998357590307039991)
        ·
          refine ⟨15151273497536385460559987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10100848998357590307039991 15151273497536385460559987)
          ·
            refine ⟨22726910246304578190839981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15151273497536385460559987 22726910246304578190839981)
            ·
              refine ⟨8522591342364216821564993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22726910246304578190839981 8522591342364216821564993)
              ·
                refine ⟨6391943506773162616173745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8522591342364216821564993 6391943506773162616173745)
                ·
                  refine ⟨4793957630079871962130309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6391943506773162616173745 4793957630079871962130309)
                  ·
                    refine ⟨898867055639975992899433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4793957630079871962130309 898867055639975992899433)
                    ·
                      refine ⟨674150291729981994674575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 898867055639975992899433 674150291729981994674575)
                      ·
                        rfl

theorem cell23_1312903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 4, 2].length) (baseStart_1312903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312903 prefixEnd_1312903 := by exact prefixLift 1312903
  have htrace : WordTrace (prefixWord ++ tailWord_1312903) baseStart_1312903 baseEnd_1312903 := by
    simpa [prefixWord, tailWord_1312903, baseEnd_1312903] using wordTrace_append hprefix tailTrace_1312903
  have hstable : (prefixWord ++ tailWord_1312903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312903).length < 2 ^ (prefixWord ++ tailWord_1312903).sum := by decide
  have hdescent : baseEnd_1312903 < baseStart_1312903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312930 : List Nat := [3, 3, 1, 3, 1, 1, 2, 2, 3, 4]
def baseStart_1312930 : Nat := 118140960795 + 1312930 * 2 ^ 59
def prefixEnd_1312930 : Nat := 4983230072969 + 3 ^ 40 * 1312930 * 2
def baseEnd_1312930 : Nat := 224721385235884463012317

theorem tailTrace_1312930 : CollatzResearch.WordTrace tailWord_1312930 prefixEnd_1312930 224721385235884463012317 := by
  unfold tailWord_1312930
  simp only [CollatzResearch.WordTrace]
  refine ⟨11971622783371578859300061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31924327422324210291466829 11971622783371578859300061)
  ·
    refine ⟨4489358543764342072237523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11971622783371578859300061 4489358543764342072237523)
    ·
      refine ⟨6734037815646513108356285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4489358543764342072237523 6734037815646513108356285)
      ·
        refine ⟨2525264180867442415633607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6734037815646513108356285 2525264180867442415633607)
        ·
          refine ⟨3787896271301163623450411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2525264180867442415633607 3787896271301163623450411)
          ·
            refine ⟨5681844406951745435175617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3787896271301163623450411 5681844406951745435175617)
            ·
              refine ⟨4261383305213809076381713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5681844406951745435175617 4261383305213809076381713)
              ·
                refine ⟨3196037478910356807286285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4261383305213809076381713 3196037478910356807286285)
                ·
                  refine ⟨1198514054591383802732357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3196037478910356807286285 1198514054591383802732357)
                  ·
                    refine ⟨224721385235884463012317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1198514054591383802732357 224721385235884463012317)
                    ·
                      rfl

theorem cell23_1312930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_1312930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312930 prefixEnd_1312930 := by exact prefixLift 1312930
  have htrace : WordTrace (prefixWord ++ tailWord_1312930) baseStart_1312930 baseEnd_1312930 := by
    simpa [prefixWord, tailWord_1312930, baseEnd_1312930] using wordTrace_append hprefix tailTrace_1312930
  have hstable : (prefixWord ++ tailWord_1312930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312930).length < 2 ^ (prefixWord ++ tailWord_1312930).sum := by decide
  have hdescent : baseEnd_1312930 < baseStart_1312930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312964 : List Nat := [2, 3, 3, 1, 2, 2, 3, 2, 1, 4]
def baseStart_1312964 : Nat := 118140960795 + 1312964 * 2 ^ 59
def prefixEnd_1312964 : Nat := 4983230072969 + 3 ^ 40 * 1312964 * 2
def baseEnd_1312964 : Nat := 224727204683302085337265

theorem tailTrace_1312964 : CollatzResearch.WordTrace tailWord_1312964 prefixEnd_1312964 224727204683302085337265 := by
  unfold tailWord_1312964
  simp only [CollatzResearch.WordTrace]
  refine ⟨23943865607681569621968973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31925154143575426162625297 23943865607681569621968973)
  ·
    refine ⟨8978949602880588608238365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23943865607681569621968973 8978949602880588608238365)
    ·
      refine ⟨3367106101080220728089387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8978949602880588608238365 3367106101080220728089387)
      ·
        refine ⟨5050659151620331092134081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3367106101080220728089387 5050659151620331092134081)
        ·
          refine ⟨3787994363715248319100561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5050659151620331092134081 3787994363715248319100561)
          ·
            refine ⟨2840995772786436239325421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3787994363715248319100561 2840995772786436239325421)
            ·
              refine ⟨1065373414794913589747033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2840995772786436239325421 1065373414794913589747033)
              ·
                refine ⟨799030061096185192310275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1065373414794913589747033 799030061096185192310275)
                ·
                  refine ⟨1198545091644277788465413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 799030061096185192310275 1198545091644277788465413)
                  ·
                    refine ⟨224727204683302085337265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1198545091644277788465413 224727204683302085337265)
                    ·
                      rfl

theorem cell23_1312964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_1312964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312964 prefixEnd_1312964 := by exact prefixLift 1312964
  have htrace : WordTrace (prefixWord ++ tailWord_1312964) baseStart_1312964 baseEnd_1312964 := by
    simpa [prefixWord, tailWord_1312964, baseEnd_1312964] using wordTrace_append hprefix tailTrace_1312964
  have hstable : (prefixWord ++ tailWord_1312964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312964).length < 2 ^ (prefixWord ++ tailWord_1312964).sum := by decide
  have hdescent : baseEnd_1312964 < baseStart_1312964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312993 : List Nat := [1, 2, 3, 1, 3, 1, 3, 1, 3, 1, 4]
def baseStart_1312993 : Nat := 118140960795 + 1312993 * 2 ^ 59
def prefixEnd_1312993 : Nat := 4983230072969 + 3 ^ 40 * 1312993 * 2
def baseEnd_1312993 : Nat := 674196504988886642549161

theorem tailTrace_1312993 : CollatzResearch.WordTrace tailWord_1312993 prefixEnd_1312993 674196504988886642549161 := by
  unfold tailWord_1312993
  simp only [CollatzResearch.WordTrace]
  refine ⟨47888788932258077196743633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31925859288172051464495755 47888788932258077196743633)
  ·
    refine ⟨35916591699193557897557725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47888788932258077196743633 35916591699193557897557725)
    ·
      refine ⟨13468721887197584211584147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35916591699193557897557725 13468721887197584211584147)
      ·
        refine ⟨20203082830796376317376221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13468721887197584211584147 20203082830796376317376221)
        ·
          refine ⟨7576156061548641119016083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20203082830796376317376221 7576156061548641119016083)
          ·
            refine ⟨11364234092322961678524125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7576156061548641119016083 11364234092322961678524125)
            ·
              refine ⟨4261587784621110629446547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11364234092322961678524125 4261587784621110629446547)
              ·
                refine ⟨6392381676931665944169821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4261587784621110629446547 6392381676931665944169821)
                ·
                  refine ⟨2397143128849374729063683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6392381676931665944169821 2397143128849374729063683)
                  ·
                    refine ⟨3595714693274062093595525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2397143128849374729063683 3595714693274062093595525)
                    ·
                      refine ⟨674196504988886642549161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3595714693274062093595525 674196504988886642549161)
                      ·
                        rfl

theorem cell23_1312993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_1312993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312993 prefixEnd_1312993 := by exact prefixLift 1312993
  have htrace : WordTrace (prefixWord ++ tailWord_1312993) baseStart_1312993 baseEnd_1312993 := by
    simpa [prefixWord, tailWord_1312993, baseEnd_1312993] using wordTrace_append hprefix tailTrace_1312993
  have hstable : (prefixWord ++ tailWord_1312993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312993).length < 2 ^ (prefixWord ++ tailWord_1312993).sum := by decide
  have hdescent : baseEnd_1312993 < baseStart_1312993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312997 : List Nat := [1, 3, 1, 4, 2, 2, 2, 1, 2, 3, 2]
def baseStart_1312997 : Nat := 118140960795 + 1312997 * 2 ^ 59
def prefixEnd_1312997 : Nat := 4983230072969 + 3 ^ 40 * 1312997 * 2
def baseEnd_1312997 : Nat := 674198558911504626899143

theorem tailTrace_1312997 : CollatzResearch.WordTrace tailWord_1312997 prefixEnd_1312997 674198558911504626899143 := by
  unfold tailWord_1312997
  simp only [CollatzResearch.WordTrace]
  refine ⟨47888934824243585879889245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31925956549495723919926163 47888934824243585879889245)
  ·
    refine ⟨17958350559091344704958467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47888934824243585879889245 17958350559091344704958467)
    ·
      refine ⟨26937525838637017057437701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17958350559091344704958467 26937525838637017057437701)
      ·
        refine ⟨5050786094744440698269569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26937525838637017057437701 5050786094744440698269569)
        ·
          refine ⟨3788089571058330523702177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5050786094744440698269569 3788089571058330523702177)
          ·
            refine ⟨2841067178293747892776633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3788089571058330523702177 2841067178293747892776633)
            ·
              refine ⟨2130800383720310919582475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2841067178293747892776633 2130800383720310919582475)
              ·
                refine ⟨3196200575580466379373713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2130800383720310919582475 3196200575580466379373713)
                ·
                  refine ⟨2397150431685349784530285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3196200575580466379373713 2397150431685349784530285)
                  ·
                    refine ⟨898931411882006169198857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2397150431685349784530285 898931411882006169198857)
                    ·
                      refine ⟨674198558911504626899143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 898931411882006169198857 674198558911504626899143)
                      ·
                        rfl

theorem cell23_1312997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_1312997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1312997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1312997 prefixEnd_1312997 := by exact prefixLift 1312997
  have htrace : WordTrace (prefixWord ++ tailWord_1312997) baseStart_1312997 baseEnd_1312997 := by
    simpa [prefixWord, tailWord_1312997, baseEnd_1312997] using wordTrace_append hprefix tailTrace_1312997
  have hstable : (prefixWord ++ tailWord_1312997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312997).length < 2 ^ (prefixWord ++ tailWord_1312997).sum := by decide
  have hdescent : baseEnd_1312997 < baseStart_1312997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313020 : List Nat := [2, 2, 2, 1, 4, 1, 1, 4, 2, 4]
def baseStart_1313020 : Nat := 118140960795 + 1313020 * 2 ^ 59
def prefixEnd_1313020 : Nat := 4983230072969 + 3 ^ 40 * 1313020 * 2
def baseEnd_1313020 : Nat := 224736789655519345637179

theorem tailTrace_1313020 : CollatzResearch.WordTrace tailWord_1313020 prefixEnd_1313020 224736789655519345637179 := by
  unfold tailWord_1313020
  simp only [CollatzResearch.WordTrace]
  refine ⟨23944886851580130403988257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31926515802106840538651009 23944886851580130403988257)
  ·
    refine ⟨17958665138685097802991193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23944886851580130403988257 17958665138685097802991193)
    ·
      refine ⟨13468998854013823352243395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17958665138685097802991193 13468998854013823352243395)
      ·
        refine ⟨20203498281020735028365093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13468998854013823352243395 20203498281020735028365093)
        ·
          refine ⟨3788155927691387817818455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20203498281020735028365093 3788155927691387817818455)
          ·
            refine ⟨5682233891537081726727683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3788155927691387817818455 5682233891537081726727683)
            ·
              refine ⟨8523350837305622590091525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5682233891537081726727683 8523350837305622590091525)
              ·
                refine ⟨1598128281994804235642161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8523350837305622590091525 1598128281994804235642161)
                ·
                  refine ⟨1198596211496103176731621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1598128281994804235642161 1198596211496103176731621)
                  ·
                    refine ⟨224736789655519345637179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1198596211496103176731621 224736789655519345637179)
                    ·
                      rfl

theorem cell23_1313020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 4, 2, 4].length) (baseStart_1313020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313020 prefixEnd_1313020 := by exact prefixLift 1313020
  have htrace : WordTrace (prefixWord ++ tailWord_1313020) baseStart_1313020 baseEnd_1313020 := by
    simpa [prefixWord, tailWord_1313020, baseEnd_1313020] using wordTrace_append hprefix tailTrace_1313020
  have hstable : (prefixWord ++ tailWord_1313020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313020).length < 2 ^ (prefixWord ++ tailWord_1313020).sum := by decide
  have hdescent : baseEnd_1313020 < baseStart_1313020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313033 : List Nat := [1, 2, 1, 1, 3, 6, 1, 8]
def baseStart_1313033 : Nat := 118140960795 + 1313033 * 2 ^ 59
def prefixEnd_1313033 : Nat := 4983230072969 + 3 ^ 40 * 1313033 * 2
def baseEnd_1313033 : Nat := 24971001637595055038851

theorem tailTrace_1313033 : CollatzResearch.WordTrace tailWord_1313033 prefixEnd_1313033 24971001637595055038851 := by
  unfold tailWord_1313033
  simp only [CollatzResearch.WordTrace]
  refine ⟨47890247852113164028199753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31926831901408776018799835 47890247852113164028199753)
  ·
    refine ⟨35917685889084873021149815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47890247852113164028199753 35917685889084873021149815)
    ·
      refine ⟨53876528833627309531724723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35917685889084873021149815 53876528833627309531724723)
      ·
        refine ⟨80814793250440964297587085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53876528833627309531724723 80814793250440964297587085)
        ·
          refine ⟨30305547468915361611595157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80814793250440964297587085 30305547468915361611595157)
          ·
            refine ⟨1420572537605407575543523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 30305547468915361611595157 1420572537605407575543523)
            ·
              refine ⟨2130858806408111363315285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1420572537605407575543523 2130858806408111363315285)
              ·
                refine ⟨24971001637595055038851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2130858806408111363315285 24971001637595055038851)
                ·
                  rfl

theorem cell23_1313033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 8].length) (baseStart_1313033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313033 prefixEnd_1313033 := by exact prefixLift 1313033
  have htrace : WordTrace (prefixWord ++ tailWord_1313033) baseStart_1313033 baseEnd_1313033 := by
    simpa [prefixWord, tailWord_1313033, baseEnd_1313033] using wordTrace_append hprefix tailTrace_1313033
  have hstable : (prefixWord ++ tailWord_1313033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313033).length < 2 ^ (prefixWord ++ tailWord_1313033).sum := by decide
  have hdescent : baseEnd_1313033 < baseStart_1313033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313050 : List Nat := [3, 1, 1, 3, 4, 1, 3, 7]
def baseStart_1313050 : Nat := 118140960795 + 1313050 * 2 ^ 59
def prefixEnd_1313050 : Nat := 4983230072969 + 3 ^ 40 * 1313050 * 2
def baseEnd_1313050 : Nat := 24971324940229367390237

theorem tailTrace_1313050 : CollatzResearch.WordTrace tailWord_1313050 prefixEnd_1313050 24971324940229367390237 := by
  unfold tailWord_1313050
  simp only [CollatzResearch.WordTrace]
  refine ⟨11972716973262893982892151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31927245262034383954379069 11972716973262893982892151)
  ·
    refine ⟨17959075459894340974338227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11972716973262893982892151 17959075459894340974338227)
    ·
      refine ⟨26938613189841511461507341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17959075459894340974338227 26938613189841511461507341)
      ·
        refine ⟨10101979946190566798065253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26938613189841511461507341 10101979946190566798065253)
        ·
          refine ⟨1894121239910731274637235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10101979946190566798065253 1894121239910731274637235)
          ·
            refine ⟨2841181859866096911955853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1894121239910731274637235 2841181859866096911955853)
            ·
              refine ⟨1065443197449786341983445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2841181859866096911955853 1065443197449786341983445)
              ·
                refine ⟨24971324940229367390237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1065443197449786341983445 24971324940229367390237)
                ·
                  rfl

theorem cell23_1313050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 7].length) (baseStart_1313050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313050 prefixEnd_1313050 := by exact prefixLift 1313050
  have htrace : WordTrace (prefixWord ++ tailWord_1313050) baseStart_1313050 baseEnd_1313050 := by
    simpa [prefixWord, tailWord_1313050, baseEnd_1313050] using wordTrace_append hprefix tailTrace_1313050
  have hstable : (prefixWord ++ tailWord_1313050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313050).length < 2 ^ (prefixWord ++ tailWord_1313050).sum := by decide
  have hdescent : baseEnd_1313050 < baseStart_1313050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313060 : List Nat := [2, 3, 1, 3, 1, 2, 2, 2, 1, 3, 3]
def baseStart_1313060 : Nat := 118140960795 + 1313060 * 2 ^ 59
def prefixEnd_1313060 : Nat := 4983230072969 + 3 ^ 40 * 1313060 * 2
def baseEnd_1313060 : Nat := 674230908192737880411353

theorem tailTrace_1313060 : CollatzResearch.WordTrace tailWord_1313060 prefixEnd_1313060 674230908192737880411353 := by
  unfold tailWord_1313060
  simp only [CollatzResearch.WordTrace]
  refine ⟨23945616311507673819716317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31927488415343565092955089 23945616311507673819716317)
  ·
    refine ⟨8979606116815377682393619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23945616311507673819716317 8979606116815377682393619)
    ·
      refine ⟨13469409175223066523590429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8979606116815377682393619 13469409175223066523590429)
      ·
        refine ⟨5051028440708649946346411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13469409175223066523590429 5051028440708649946346411)
        ·
          refine ⟨7576542661062974919519617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5051028440708649946346411 7576542661062974919519617)
          ·
            refine ⟨5682406995797231189639713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7576542661062974919519617 5682406995797231189639713)
            ·
              refine ⟨4261805246847923392229785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5682406995797231189639713 4261805246847923392229785)
              ·
                refine ⟨3196353935135942544172339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4261805246847923392229785 3196353935135942544172339)
                ·
                  refine ⟨4794530902703913816258509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3196353935135942544172339 4794530902703913816258509)
                  ·
                    refine ⟨1797949088513967681096941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4794530902703913816258509 1797949088513967681096941)
                    ·
                      refine ⟨674230908192737880411353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1797949088513967681096941 674230908192737880411353)
                      ·
                        rfl

theorem cell23_1313060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_1313060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313060 prefixEnd_1313060 := by exact prefixLift 1313060
  have htrace : WordTrace (prefixWord ++ tailWord_1313060) baseStart_1313060 baseEnd_1313060 := by
    simpa [prefixWord, tailWord_1313060, baseEnd_1313060] using wordTrace_append hprefix tailTrace_1313060
  have hstable : (prefixWord ++ tailWord_1313060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313060).length < 2 ^ (prefixWord ++ tailWord_1313060).sum := by decide
  have hdescent : baseEnd_1313060 < baseStart_1313060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313061 : List Nat := [1, 3, 1, 2, 5, 1, 2, 3, 1, 2, 2]
def baseStart_1313061 : Nat := 118140960795 + 1313061 * 2 ^ 59
def prefixEnd_1313061 : Nat := 4983230072969 + 3 ^ 40 * 1313061 * 2
def baseEnd_1313061 : Nat := 674231421673392376498849

theorem tailTrace_1313061 : CollatzResearch.WordTrace tailWord_1313061 prefixEnd_1313061 674231421673392376498849 := by
  unfold tailWord_1313061
  simp only [CollatzResearch.WordTrace]
  refine ⟨47891269096011724810219037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31927512730674483206812691 47891269096011724810219037)
  ·
    refine ⟨17959225911004396803832139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47891269096011724810219037 17959225911004396803832139)
    ·
      refine ⟨26938838866506595205748209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17959225911004396803832139 26938838866506595205748209)
      ·
        refine ⟨20204129149879946404311157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26938838866506595205748209 20204129149879946404311157)
        ·
          refine ⟨1894137107801244975404171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20204129149879946404311157 1894137107801244975404171)
          ·
            refine ⟨2841205661701867463106257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1894137107801244975404171 2841205661701867463106257)
            ·
              refine ⟨2130904246276400597329693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2841205661701867463106257 2130904246276400597329693)
              ·
                refine ⟨799089092353650223998635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2130904246276400597329693 799089092353650223998635)
                ·
                  refine ⟨1198633638530475335997953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 799089092353650223998635 1198633638530475335997953)
                  ·
                    refine ⟨898975228897856501998465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1198633638530475335997953 898975228897856501998465)
                    ·
                      refine ⟨674231421673392376498849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 898975228897856501998465 674231421673392376498849)
                      ·
                        rfl

theorem cell23_1313061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 3, 1, 2, 2].length) (baseStart_1313061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313061 prefixEnd_1313061 := by exact prefixLift 1313061
  have htrace : WordTrace (prefixWord ++ tailWord_1313061) baseStart_1313061 baseEnd_1313061 := by
    simpa [prefixWord, tailWord_1313061, baseEnd_1313061] using wordTrace_append hprefix tailTrace_1313061
  have hstable : (prefixWord ++ tailWord_1313061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313061).length < 2 ^ (prefixWord ++ tailWord_1313061).sum := by decide
  have hdescent : baseEnd_1313061 < baseStart_1313061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313120 : List Nat := [2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 5]
def baseStart_1313120 : Nat := 118140960795 + 1313120 * 2 ^ 59
def prefixEnd_1313120 : Nat := 4983230072969 + 3 ^ 40 * 1313120 * 2
def baseEnd_1313120 : Nat := 674261717032007645661077

theorem tailTrace_1313120 : CollatzResearch.WordTrace tailWord_1313120 prefixEnd_1313120 674261717032007645661077 := by
  unfold tailWord_1313120
  simp only [CollatzResearch.WordTrace]
  refine ⟨23946710501398988943308407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31928947335198651924411209 23946710501398988943308407)
  ·
    refine ⟨35920065752098483414962611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23946710501398988943308407 35920065752098483414962611)
    ·
      refine ⟨53880098628147725122443917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35920065752098483414962611 53880098628147725122443917)
      ·
        refine ⟨20205036985555396920916469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53880098628147725122443917 20205036985555396920916469)
        ·
          refine ⟨1894222217395818461335919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20205036985555396920916469 1894222217395818461335919)
          ·
            refine ⟨2841333326093727692003879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1894222217395818461335919 2841333326093727692003879)
            ·
              refine ⟨4261999989140591538005819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2841333326093727692003879 4261999989140591538005819)
              ·
                refine ⟨6392999983710887307008729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4261999989140591538005819 6392999983710887307008729)
                ·
                  refine ⟨4794749987783165480256547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6392999983710887307008729 4794749987783165480256547)
                  ·
                    refine ⟨7192124981674748220384821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4794749987783165480256547 7192124981674748220384821)
                    ·
                      refine ⟨674261717032007645661077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7192124981674748220384821 674261717032007645661077)
                      ·
                        rfl

theorem cell23_1313120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 5].length) (baseStart_1313120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313120 prefixEnd_1313120 := by exact prefixLift 1313120
  have htrace : WordTrace (prefixWord ++ tailWord_1313120) baseStart_1313120 baseEnd_1313120 := by
    simpa [prefixWord, tailWord_1313120, baseEnd_1313120] using wordTrace_append hprefix tailTrace_1313120
  have hstable : (prefixWord ++ tailWord_1313120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313120).length < 2 ^ (prefixWord ++ tailWord_1313120).sum := by decide
  have hdescent : baseEnd_1313120 < baseStart_1313120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313133 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 1, 2, 7]
def baseStart_1313133 : Nat := 118140960795 + 1313133 * 2 ^ 59
def prefixEnd_1313133 : Nat := 4983230072969 + 3 ^ 40 * 1313133 * 2
def baseEnd_1313133 : Nat := 674268392280516094798517

theorem tailTrace_1313133 : CollatzResearch.WordTrace tailWord_1313133 prefixEnd_1313133 674268392280516094798517 := by
  unfold tailWord_1313133
  simp only [CollatzResearch.WordTrace]
  refine ⟨47893895151750881106840053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31929263434500587404560035 47893895151750881106840053)
  ·
    refine ⟨4490052670476645103766255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47893895151750881106840053 4490052670476645103766255)
    ·
      refine ⟨6735079005714967655649383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4490052670476645103766255 6735079005714967655649383)
      ·
        refine ⟨10102618508572451483474075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6735079005714967655649383 10102618508572451483474075)
        ·
          refine ⟨15153927762858677225211113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10102618508572451483474075 15153927762858677225211113)
          ·
            refine ⟨11365445822144007918908335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15153927762858677225211113 11365445822144007918908335)
            ·
              refine ⟨17048168733216011878362503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11365445822144007918908335 17048168733216011878362503)
              ·
                refine ⟨25572253099824017817543755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17048168733216011878362503 25572253099824017817543755)
                ·
                  refine ⟨38358379649736026726315633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25572253099824017817543755 38358379649736026726315633)
                  ·
                    refine ⟨28768784737302020044736725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38358379649736026726315633 28768784737302020044736725)
                    ·
                      refine ⟨674268392280516094798517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 28768784737302020044736725 674268392280516094798517)
                      ·
                        rfl

theorem cell23_1313133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_1313133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313133 prefixEnd_1313133 := by exact prefixLift 1313133
  have htrace : WordTrace (prefixWord ++ tailWord_1313133) baseStart_1313133 baseEnd_1313133 := by
    simpa [prefixWord, tailWord_1313133, baseEnd_1313133] using wordTrace_append hprefix tailTrace_1313133
  have hstable : (prefixWord ++ tailWord_1313133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313133).length < 2 ^ (prefixWord ++ tailWord_1313133).sum := by decide
  have hdescent : baseEnd_1313133 < baseStart_1313133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313203 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 4, 4, 4]
def baseStart_1313203 : Nat := 118140960795 + 1313203 * 2 ^ 59
def prefixEnd_1313203 : Nat := 4983230072969 + 3 ^ 40 * 1313203 * 2
def baseEnd_1313203 : Nat := 674304335926330820923195

theorem tailTrace_1313203 : CollatzResearch.WordTrace tailWord_1313203 prefixEnd_1313203 674304335926330820923195 := by
  unfold tailWord_1313203
  simp only [CollatzResearch.WordTrace]
  refine ⟨47896448261497283061888263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31930965507664855374592175 47896448261497283061888263)
  ·
    refine ⟨71844672392245924592832395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47896448261497283061888263 71844672392245924592832395)
    ·
      refine ⟨107767008588368886889248593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71844672392245924592832395 107767008588368886889248593)
      ·
        refine ⟨80825256441276665166936445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107767008588368886889248593 80825256441276665166936445)
        ·
          refine ⟨30309471165478749437601167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80825256441276665166936445 30309471165478749437601167)
          ·
            refine ⟨45464206748218124156401751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30309471165478749437601167 45464206748218124156401751)
            ·
              refine ⟨68196310122327186234602627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45464206748218124156401751 68196310122327186234602627)
              ·
                refine ⟨102294465183490779351903941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68196310122327186234602627 102294465183490779351903941)
                ·
                  refine ⟨19180212221904521128481989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102294465183490779351903941 19180212221904521128481989)
                  ·
                    refine ⟨3596289791607097711590373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19180212221904521128481989 3596289791607097711590373)
                    ·
                      refine ⟨674304335926330820923195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3596289791607097711590373 674304335926330820923195)
                      ·
                        rfl

theorem cell23_1313203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 4, 4].length) (baseStart_1313203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313203 prefixEnd_1313203 := by exact prefixLift 1313203
  have htrace : WordTrace (prefixWord ++ tailWord_1313203) baseStart_1313203 baseEnd_1313203 := by
    simpa [prefixWord, tailWord_1313203, baseEnd_1313203] using wordTrace_append hprefix tailTrace_1313203
  have hstable : (prefixWord ++ tailWord_1313203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313203).length < 2 ^ (prefixWord ++ tailWord_1313203).sum := by decide
  have hdescent : baseEnd_1313203 < baseStart_1313203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313207 : List Nat := [1, 1, 3, 1, 3, 4, 1, 1, 2, 4, 2]
def baseStart_1313207 : Nat := 118140960795 + 1313207 * 2 ^ 59
def prefixEnd_1313207 : Nat := 4983230072969 + 3 ^ 40 * 1313207 * 2
def baseEnd_1313207 : Nat := 674306389848948805273177

theorem tailTrace_1313207 : CollatzResearch.WordTrace tailWord_1313207 prefixEnd_1313207 674306389848948805273177 := by
  unfold tailWord_1313207
  simp only [CollatzResearch.WordTrace]
  refine ⟨47896594153482791745033875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31931062768988527830022583 47896594153482791745033875)
  ·
    refine ⟨71844891230224187617550813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47896594153482791745033875 71844891230224187617550813)
    ·
      refine ⟨26941834211334070356581555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71844891230224187617550813 26941834211334070356581555)
      ·
        refine ⟨40412751317001105534872333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26941834211334070356581555 40412751317001105534872333)
        ·
          refine ⟨15154781743875414575577125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40412751317001105534872333 15154781743875414575577125)
          ·
            refine ⟨2841521576976640232920711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15154781743875414575577125 2841521576976640232920711)
            ·
              refine ⟨4262282365464960349381067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2841521576976640232920711 4262282365464960349381067)
              ·
                refine ⟨6393423548197440524071601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4262282365464960349381067 6393423548197440524071601)
                ·
                  refine ⟨4795067661148080393053701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6393423548197440524071601 4795067661148080393053701)
                  ·
                    refine ⟨899075186465265073697569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4795067661148080393053701 899075186465265073697569)
                    ·
                      refine ⟨674306389848948805273177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 899075186465265073697569 674306389848948805273177)
                      ·
                        rfl

theorem cell23_1313207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 4, 2].length) (baseStart_1313207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313207 prefixEnd_1313207 := by exact prefixLift 1313207
  have htrace : WordTrace (prefixWord ++ tailWord_1313207) baseStart_1313207 baseEnd_1313207 := by
    simpa [prefixWord, tailWord_1313207, baseEnd_1313207] using wordTrace_append hprefix tailTrace_1313207
  have hstable : (prefixWord ++ tailWord_1313207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313207).length < 2 ^ (prefixWord ++ tailWord_1313207).sum := by decide
  have hdescent : baseEnd_1313207 < baseStart_1313207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313210 : List Nat := [3, 1, 1, 1, 2, 1, 1, 4, 4, 2, 3]
def baseStart_1313210 : Nat := 118140960795 + 1313210 * 2 ^ 59
def prefixEnd_1313210 : Nat := 4983230072969 + 3 ^ 40 * 1313210 * 2
def baseEnd_1313210 : Nat := 674307930290912293535663

theorem tailTrace_1313210 : CollatzResearch.WordTrace tailWord_1313210 prefixEnd_1313210 674307930290912293535663 := by
  unfold tailWord_1313210
  simp only [CollatzResearch.WordTrace]
  refine ⟨11974175893117980814348271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31931135714981282171595389 11974175893117980814348271)
  ·
    refine ⟨17961263839676971221522407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11974175893117980814348271 17961263839676971221522407)
    ·
      refine ⟨26941895759515456832283611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17961263839676971221522407 26941895759515456832283611)
      ·
        refine ⟨40412843639273185248425417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26941895759515456832283611 40412843639273185248425417)
        ·
          refine ⟨30309632729454888936319063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40412843639273185248425417 30309632729454888936319063)
          ·
            refine ⟨45464449094182333404478595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30309632729454888936319063 45464449094182333404478595)
            ·
              refine ⟨68196673641273500106717893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45464449094182333404478595 68196673641273500106717893)
              ·
                refine ⟨12786876307738781270009605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68196673641273500106717893 12786876307738781270009605)
                ·
                  refine ⟨2397539307701021488126801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12786876307738781270009605 2397539307701021488126801)
                  ·
                    refine ⟨1798154480775766116095101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2397539307701021488126801 1798154480775766116095101)
                    ·
                      refine ⟨674307930290912293535663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1798154480775766116095101 674307930290912293535663)
                      ·
                        rfl

theorem cell23_1313210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 4, 2, 3].length) (baseStart_1313210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313210 prefixEnd_1313210 := by exact prefixLift 1313210
  have htrace : WordTrace (prefixWord ++ tailWord_1313210) baseStart_1313210 baseEnd_1313210 := by
    simpa [prefixWord, tailWord_1313210, baseEnd_1313210] using wordTrace_append hprefix tailTrace_1313210
  have hstable : (prefixWord ++ tailWord_1313210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313210).length < 2 ^ (prefixWord ++ tailWord_1313210).sum := by decide
  have hdescent : baseEnd_1313210 < baseStart_1313210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313233 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 6]
def baseStart_1313233 : Nat := 118140960795 + 1313233 * 2 ^ 59
def prefixEnd_1313233 : Nat := 4983230072969 + 3 ^ 40 * 1313233 * 2
def baseEnd_1313233 : Nat := 674319740345965703548057

theorem tailTrace_1313233 : CollatzResearch.WordTrace tailWord_1313233 prefixEnd_1313233 674319740345965703548057 := by
  unfold tailWord_1313233
  simp only [CollatzResearch.WordTrace]
  refine ⟨47897542451388598185480353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31931694967592398790320235 47897542451388598185480353)
  ·
    refine ⟨35923156838541448639110265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47897542451388598185480353 35923156838541448639110265)
    ·
      refine ⟨26942367628906086479332699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35923156838541448639110265 26942367628906086479332699)
      ·
        refine ⟨40413551443359129718999049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26942367628906086479332699 40413551443359129718999049)
        ·
          refine ⟨30310163582519347289249287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40413551443359129718999049 30310163582519347289249287)
          ·
            refine ⟨45465245373779020933873931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30310163582519347289249287 45465245373779020933873931)
            ·
              refine ⟨68197868060668531400810897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45465245373779020933873931 68197868060668531400810897)
              ·
                refine ⟨51148401045501398550608173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68197868060668531400810897 51148401045501398550608173)
                ·
                  refine ⟨19180650392063024456478065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51148401045501398550608173 19180650392063024456478065)
                  ·
                    refine ⟨14385487794047268342358549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19180650392063024456478065 14385487794047268342358549)
                    ·
                      refine ⟨674319740345965703548057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14385487794047268342358549 674319740345965703548057)
                      ·
                        rfl

theorem cell23_1313233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_1313233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313233 prefixEnd_1313233 := by exact prefixLift 1313233
  have htrace : WordTrace (prefixWord ++ tailWord_1313233) baseStart_1313233 baseEnd_1313233 := by
    simpa [prefixWord, tailWord_1313233, baseEnd_1313233] using wordTrace_append hprefix tailTrace_1313233
  have hstable : (prefixWord ++ tailWord_1313233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313233).length < 2 ^ (prefixWord ++ tailWord_1313233).sum := by decide
  have hdescent : baseEnd_1313233 < baseStart_1313233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313247 : List Nat := [1, 1, 2, 3, 3, 4, 1, 2, 6]
def baseStart_1313247 : Nat := 118140960795 + 1313247 * 2 ^ 59
def prefixEnd_1313247 : Nat := 4983230072969 + 3 ^ 40 * 1313247 * 2
def baseEnd_1313247 : Nat := 74925214341680960974777

theorem tailTrace_1313247 : CollatzResearch.WordTrace tailWord_1313247 prefixEnd_1313247 74925214341680960974777 := by
  unfold tailWord_1313247
  simp only [CollatzResearch.WordTrace]
  refine ⟨47898053073337878576489995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31932035382225252384326663 47898053073337878576489995)
  ·
    refine ⟨71847079610006817864734993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47898053073337878576489995 71847079610006817864734993)
    ·
      refine ⟨53885309707505113398551245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71847079610006817864734993 53885309707505113398551245)
      ·
        refine ⟨20206991140314417524456717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53885309707505113398551245 20206991140314417524456717)
        ·
          refine ⟨7577621677617906571671269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20206991140314417524456717 7577621677617906571671269)
          ·
            refine ⟨1420804064553357482188363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7577621677617906571671269 1420804064553357482188363)
            ·
              refine ⟨2131206096830036223282545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1420804064553357482188363 2131206096830036223282545)
              ·
                refine ⟨1598404572622527167461909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2131206096830036223282545 1598404572622527167461909)
                ·
                  refine ⟨74925214341680960974777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1598404572622527167461909 74925214341680960974777)
                  ·
                    rfl

theorem cell23_1313247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 2, 6].length) (baseStart_1313247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313247 prefixEnd_1313247 := by exact prefixLift 1313247
  have htrace : WordTrace (prefixWord ++ tailWord_1313247) baseStart_1313247 baseEnd_1313247 := by
    simpa [prefixWord, tailWord_1313247, baseEnd_1313247] using wordTrace_append hprefix tailTrace_1313247
  have hstable : (prefixWord ++ tailWord_1313247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313247).length < 2 ^ (prefixWord ++ tailWord_1313247).sum := by decide
  have hdescent : baseEnd_1313247 < baseStart_1313247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313277 : List Nat := [1, 4, 1, 1, 1, 3, 4, 2, 1, 5]
def baseStart_1313277 : Nat := 118140960795 + 1313277 * 2 ^ 59
def prefixEnd_1313277 : Nat := 4983230072969 + 3 ^ 40 * 1313277 * 2
def baseEnd_1313277 : Nat := 224780777831587843799285

theorem tailTrace_1313277 : CollatzResearch.WordTrace tailWord_1313277 prefixEnd_1313277 224780777831587843799285 := by
  unfold tailWord_1313277
  simp only [CollatzResearch.WordTrace]
  refine ⟨47899147263229193700082085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31932764842152795800054723 47899147263229193700082085)
  ·
    refine ⟨8981090111855473818765391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47899147263229193700082085 8981090111855473818765391)
    ·
      refine ⟨13471635167783210728148087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8981090111855473818765391 13471635167783210728148087)
      ·
        refine ⟨20207452751674816092222131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13471635167783210728148087 20207452751674816092222131)
        ·
          refine ⟨30311179127512224138333197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20207452751674816092222131 30311179127512224138333197)
          ·
            refine ⟨11366692172817084051874949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30311179127512224138333197 11366692172817084051874949)
            ·
              refine ⟨2131254782403203259726553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11366692172817084051874949 2131254782403203259726553)
              ·
                refine ⟨1598441086802402444794915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2131254782403203259726553 1598441086802402444794915)
                ·
                  refine ⟨2397661630203603667192373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1598441086802402444794915 2397661630203603667192373)
                  ·
                    refine ⟨224780777831587843799285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2397661630203603667192373 224780777831587843799285)
                    ·
                      rfl

theorem cell23_1313277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 2, 1, 5].length) (baseStart_1313277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313277 prefixEnd_1313277 := by exact prefixLift 1313277
  have htrace : WordTrace (prefixWord ++ tailWord_1313277) baseStart_1313277 baseEnd_1313277 := by
    simpa [prefixWord, tailWord_1313277, baseEnd_1313277] using wordTrace_append hprefix tailTrace_1313277
  have hstable : (prefixWord ++ tailWord_1313277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313277).length < 2 ^ (prefixWord ++ tailWord_1313277).sum := by decide
  have hdescent : baseEnd_1313277 < baseStart_1313277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313284 : List Nat := [2, 3, 2, 3, 1, 1, 2, 1, 1, 5, 2]
def baseStart_1313284 : Nat := 118140960795 + 1313284 * 2 ^ 59
def prefixEnd_1313284 : Nat := 4983230072969 + 3 ^ 40 * 1313284 * 2
def baseEnd_1313284 : Nat := 674345927859345004010323

theorem tailTrace_1313284 : CollatzResearch.WordTrace tailWord_1313284 prefixEnd_1313284 674345927859345004010323 := by
  unfold tailWord_1313284
  simp only [CollatzResearch.WordTrace]
  refine ⟨23949701287101916947793453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31932935049469222597057937 23949701287101916947793453)
  ·
    refine ⟨8981137982663218855422545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23949701287101916947793453 8981137982663218855422545)
    ·
      refine ⟨6735853486997414141566909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8981137982663218855422545 6735853486997414141566909)
      ·
        refine ⟨2525945057624030303087591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6735853486997414141566909 2525945057624030303087591)
        ·
          refine ⟨3788917586436045454631387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2525945057624030303087591 3788917586436045454631387)
          ·
            refine ⟨5683376379654068181947081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3788917586436045454631387 5683376379654068181947081)
            ·
              refine ⟨4262532284740551136460311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5683376379654068181947081 4262532284740551136460311)
              ·
                refine ⟨6393798427110826704690467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4262532284740551136460311 6393798427110826704690467)
                ·
                  refine ⟨9590697640666240057035701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6393798427110826704690467 9590697640666240057035701)
                  ·
                    refine ⟨899127903812460005347097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9590697640666240057035701 899127903812460005347097)
                    ·
                      refine ⟨674345927859345004010323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 899127903812460005347097 674345927859345004010323)
                      ·
                        rfl

theorem cell23_1313284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_1313284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313284 prefixEnd_1313284 := by exact prefixLift 1313284
  have htrace : WordTrace (prefixWord ++ tailWord_1313284) baseStart_1313284 baseEnd_1313284 := by
    simpa [prefixWord, tailWord_1313284, baseEnd_1313284] using wordTrace_append hprefix tailTrace_1313284
  have hstable : (prefixWord ++ tailWord_1313284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313284).length < 2 ^ (prefixWord ++ tailWord_1313284).sum := by decide
  have hdescent : baseEnd_1313284 < baseStart_1313284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313290 : List Nat := [3, 1, 2, 2, 2, 1, 2, 1, 3, 6]
def baseStart_1313290 : Nat := 118140960795 + 1313290 * 2 ^ 59
def prefixEnd_1313290 : Nat := 4983230072969 + 3 ^ 40 * 1313290 * 2
def baseEnd_1313290 : Nat := 224783002914423993511765

theorem tailTrace_1313290 : CollatzResearch.WordTrace tailWord_1313290 prefixEnd_1313290 224783002914423993511765 := by
  unfold tailWord_1313290
  simp only [CollatzResearch.WordTrace]
  refine ⟨11974905353045524230076331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31933080941454731280203549 11974905353045524230076331)
  ·
    refine ⟨17962358029568286345114497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11974905353045524230076331 17962358029568286345114497)
    ·
      refine ⟨13471768522176214758835873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17962358029568286345114497 13471768522176214758835873)
      ·
        refine ⟨10103826391632161069126905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13471768522176214758835873 10103826391632161069126905)
        ·
          refine ⟨7577869793724120801845179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10103826391632161069126905 7577869793724120801845179)
          ·
            refine ⟨11366804690586181202767769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7577869793724120801845179 11366804690586181202767769)
            ·
              refine ⟨8525103517939635902075827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11366804690586181202767769 8525103517939635902075827)
              ·
                refine ⟨12787655276909453853113741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8525103517939635902075827 12787655276909453853113741)
                ·
                  refine ⟨4795370728841045194917653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12787655276909453853113741 4795370728841045194917653)
                  ·
                    refine ⟨224783002914423993511765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4795370728841045194917653 224783002914423993511765)
                    ·
                      rfl

theorem cell23_1313290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_1313290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313290 prefixEnd_1313290 := by exact prefixLift 1313290
  have htrace : WordTrace (prefixWord ++ tailWord_1313290) baseStart_1313290 baseEnd_1313290 := by
    simpa [prefixWord, tailWord_1313290, baseEnd_1313290] using wordTrace_append hprefix tailTrace_1313290
  have hstable : (prefixWord ++ tailWord_1313290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313290).length < 2 ^ (prefixWord ++ tailWord_1313290).sum := by decide
  have hdescent : baseEnd_1313290 < baseStart_1313290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313291 : List Nat := [1, 1, 1, 1, 7, 1, 3, 3, 1, 1, 3]
def baseStart_1313291 : Nat := 118140960795 + 1313291 * 2 ^ 59
def prefixEnd_1313291 : Nat := 4983230072969 + 3 ^ 40 * 1313291 * 2
def baseEnd_1313291 : Nat := 674349522223926476622791

theorem tailTrace_1313291 : CollatzResearch.WordTrace tailWord_1313291 prefixEnd_1313291 674349522223926476622791 := by
  unfold tailWord_1313291
  simp only [CollatzResearch.WordTrace]
  refine ⟨47899657885178474091091727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31933105256785649394061151 47899657885178474091091727)
  ·
    refine ⟨71849486827767711136637591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47899657885178474091091727 71849486827767711136637591)
    ·
      refine ⟨107774230241651566704956387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71849486827767711136637591 107774230241651566704956387)
      ·
        refine ⟨161661345362477350057434581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107774230241651566704956387 161661345362477350057434581)
        ·
          refine ⟨3788937781933062891971123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 161661345362477350057434581 3788937781933062891971123)
          ·
            refine ⟨5683406672899594337956685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3788937781933062891971123 5683406672899594337956685)
            ·
              refine ⟨2131277502337347876733757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5683406672899594337956685 2131277502337347876733757)
              ·
                refine ⟨799229063376505453775159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2131277502337347876733757 799229063376505453775159)
                ·
                  refine ⟨1198843595064758180662739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 799229063376505453775159 1198843595064758180662739)
                  ·
                    refine ⟨1798265392597137270994109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1198843595064758180662739 1798265392597137270994109)
                    ·
                      refine ⟨674349522223926476622791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1798265392597137270994109 674349522223926476622791)
                      ·
                        rfl

theorem cell23_1313291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 3, 1, 1, 3].length) (baseStart_1313291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313291 prefixEnd_1313291 := by exact prefixLift 1313291
  have htrace : WordTrace (prefixWord ++ tailWord_1313291) baseStart_1313291 baseEnd_1313291 := by
    simpa [prefixWord, tailWord_1313291, baseEnd_1313291] using wordTrace_append hprefix tailTrace_1313291
  have hstable : (prefixWord ++ tailWord_1313291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313291).length < 2 ^ (prefixWord ++ tailWord_1313291).sum := by decide
  have hdescent : baseEnd_1313291 < baseStart_1313291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313308 : List Nat := [2, 2, 3, 1, 2, 3, 3, 2, 1, 1, 3]
def baseStart_1313308 : Nat := 118140960795 + 1313308 * 2 ^ 59
def prefixEnd_1313308 : Nat := 4983230072969 + 3 ^ 40 * 1313308 * 2
def baseEnd_1313308 : Nat := 674358251395052910110213

theorem tailTrace_1313308 : CollatzResearch.WordTrace tailWord_1313308 prefixEnd_1313308 674358251395052910110213 := by
  unfold tailWord_1313308
  simp only [CollatzResearch.WordTrace]
  refine ⟨23950138963058442997230289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31933518617411257329640385 23950138963058442997230289)
  ·
    refine ⟨17962604222293832247922717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23950138963058442997230289 17962604222293832247922717)
    ·
      refine ⟨6735976583360187092971019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17962604222293832247922717 6735976583360187092971019)
      ·
        refine ⟨10103964875040280639456529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6735976583360187092971019 10103964875040280639456529)
        ·
          refine ⟨7577973656280210479592397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10103964875040280639456529 7577973656280210479592397)
          ·
            refine ⟨2841740121105078929847149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7577973656280210479592397 2841740121105078929847149)
            ·
              refine ⟨1065652545414404598692681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2841740121105078929847149 1065652545414404598692681)
              ·
                refine ⟨799239409060803449019511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1065652545414404598692681 799239409060803449019511)
                ·
                  refine ⟨1198859113591205173529267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 799239409060803449019511 1198859113591205173529267)
                  ·
                    refine ⟨1798288670386807760293901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1198859113591205173529267 1798288670386807760293901)
                    ·
                      refine ⟨674358251395052910110213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1798288670386807760293901 674358251395052910110213)
                      ·
                        rfl

theorem cell23_1313308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 2, 1, 1, 3].length) (baseStart_1313308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313308 prefixEnd_1313308 := by exact prefixLift 1313308
  have htrace : WordTrace (prefixWord ++ tailWord_1313308) baseStart_1313308 baseEnd_1313308 := by
    simpa [prefixWord, tailWord_1313308, baseEnd_1313308] using wordTrace_append hprefix tailTrace_1313308
  have hstable : (prefixWord ++ tailWord_1313308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313308).length < 2 ^ (prefixWord ++ tailWord_1313308).sum := by decide
  have hdescent : baseEnd_1313308 < baseStart_1313308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313347 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 6, 1, 3]
def baseStart_1313347 : Nat := 118140960795 + 1313347 * 2 ^ 59
def prefixEnd_1313347 : Nat := 4983230072969 + 3 ^ 40 * 1313347 * 2
def baseEnd_1313347 : Nat := 674378277140578257522533

theorem tailTrace_1313347 : CollatzResearch.WordTrace tailWord_1313347 prefixEnd_1313347 674378277140578257522533 := by
  unfold tailWord_1313347
  simp only [CollatzResearch.WordTrace]
  refine ⟨47901700372975595655130295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31934466915317063770086863 47901700372975595655130295)
  ·
    refine ⟨71852550559463393482695443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47901700372975595655130295 71852550559463393482695443)
    ·
      refine ⟨107778825839195090224043165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71852550559463393482695443 107778825839195090224043165)
      ·
        refine ⟨40417059689698158834016187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107778825839195090224043165 40417059689698158834016187)
        ·
          refine ⟨60625589534547238251024281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40417059689698158834016187 60625589534547238251024281)
          ·
            refine ⟨45469192150910428688268211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60625589534547238251024281 45469192150910428688268211)
            ·
              refine ⟨68203788226365643032402317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45469192150910428688268211 68203788226365643032402317)
              ·
                refine ⟨25576420584887116137150869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68203788226365643032402317 25576420584887116137150869)
                ·
                  refine ⟨1198894714916583568928947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 25576420584887116137150869 1198894714916583568928947)
                  ·
                    refine ⟨1798342072374875353393421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1198894714916583568928947 1798342072374875353393421)
                    ·
                      refine ⟨674378277140578257522533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1798342072374875353393421 674378277140578257522533)
                      ·
                        rfl

theorem cell23_1313347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 6, 1, 3].length) (baseStart_1313347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313347 prefixEnd_1313347 := by exact prefixLift 1313347
  have htrace : WordTrace (prefixWord ++ tailWord_1313347) baseStart_1313347 baseEnd_1313347 := by
    simpa [prefixWord, tailWord_1313347, baseEnd_1313347] using wordTrace_append hprefix tailTrace_1313347
  have hstable : (prefixWord ++ tailWord_1313347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313347).length < 2 ^ (prefixWord ++ tailWord_1313347).sum := by decide
  have hdescent : baseEnd_1313347 < baseStart_1313347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
