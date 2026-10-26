import V185TrunkScan21Chunk112

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1374003 : List Nat := [1, 1, 1, 2, 7, 2, 1, 1, 5]
def baseStart_1374003 : Nat := 118140960795 + 1374003 * 2 ^ 59
def prefixEnd_1374003 : Nat := 4983230072969 + 3 ^ 40 * 1374003 * 2
def baseEnd_1374003 : Nat := 313566204319863529174925

theorem tailTrace_1374003 : CollatzResearch.WordTrace tailWord_1374003 prefixEnd_1374003 313566204319863529174925 := by
  unfold tailWord_1374003
  simp only [CollatzResearch.WordTrace]
  refine ⟨50114006441229266875190663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33409337627486177916793775 50114006441229266875190663)
  ·
    refine ⟨75171009661843900312785995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50114006441229266875190663 75171009661843900312785995)
    ·
      refine ⟨112756514492765850469178993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75171009661843900312785995 112756514492765850469178993)
      ·
        refine ⟨84567385869574387851884245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112756514492765850469178993 84567385869574387851884245)
        ·
          refine ⟨1982048106318149715278537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 84567385869574387851884245 1982048106318149715278537)
          ·
            refine ⟨1486536079738612286458903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1982048106318149715278537 1486536079738612286458903)
            ·
              refine ⟨2229804119607918429688355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1486536079738612286458903 2229804119607918429688355)
              ·
                refine ⟨3344706179411877644532533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2229804119607918429688355 3344706179411877644532533)
                ·
                  refine ⟨313566204319863529174925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3344706179411877644532533 313566204319863529174925)
                  ·
                    rfl

theorem cell21_1374003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 5].length) (baseStart_1374003 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1374003 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1374003 prefixEnd_1374003 := by exact prefixLift 1374003
  have htrace : WordTrace (prefixWord ++ tailWord_1374003) baseStart_1374003 baseEnd_1374003 := by
    simpa [prefixWord, tailWord_1374003, baseEnd_1374003] using wordTrace_append hprefix tailTrace_1374003
  have hstable : (prefixWord ++ tailWord_1374003).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374003).length < 2 ^ (prefixWord ++ tailWord_1374003).sum := by decide
  have hdescent : baseEnd_1374003 < baseStart_1374003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374152 : List Nat := [2, 1, 3, 1, 4, 1, 1, 2, 6]
def baseStart_1374152 : Nat := 118140960795 + 1374152 * 2 ^ 59
def prefixEnd_1374152 : Nat := 4983230072969 + 3 ^ 40 * 1374152 * 2
def baseEnd_1374152 : Nat := 313600208149872381191287

theorem tailTrace_1374152 : CollatzResearch.WordTrace tailWord_1374152 prefixEnd_1374152 313600208149872381191287 := by
  unfold tailWord_1374152
  simp only [CollatzResearch.WordTrace]
  refine ⟨25059720458844732661182355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33412960611792976881576473 25059720458844732661182355)
  ·
    refine ⟨37589580688267098991773533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25059720458844732661182355 37589580688267098991773533)
    ·
      refine ⟨14096092758100162121915075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37589580688267098991773533 14096092758100162121915075)
      ·
        refine ⟨21144139137150243182872613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14096092758100162121915075 21144139137150243182872613)
        ·
          refine ⟨3964526088215670596788615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21144139137150243182872613 3964526088215670596788615)
          ·
            refine ⟨5946789132323505895182923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3964526088215670596788615 5946789132323505895182923)
            ·
              refine ⟨8920183698485258842774385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5946789132323505895182923 8920183698485258842774385)
              ·
                refine ⟨6690137773863944132080789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8920183698485258842774385 6690137773863944132080789)
                ·
                  refine ⟨313600208149872381191287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6690137773863944132080789 313600208149872381191287)
                  ·
                    rfl

theorem cell21_1374152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 6].length) (baseStart_1374152 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1374152 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1374152 prefixEnd_1374152 := by exact prefixLift 1374152
  have htrace : WordTrace (prefixWord ++ tailWord_1374152) baseStart_1374152 baseEnd_1374152 := by
    simpa [prefixWord, tailWord_1374152, baseEnd_1374152] using wordTrace_append hprefix tailTrace_1374152
  have hstable : (prefixWord ++ tailWord_1374152).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374152).length < 2 ^ (prefixWord ++ tailWord_1374152).sum := by decide
  have hdescent : baseEnd_1374152 < baseStart_1374152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374211 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 8]
def baseStart_1374211 : Nat := 118140960795 + 1374211 * 2 ^ 59
def prefixEnd_1374211 : Nat := 4983230072969 + 3 ^ 40 * 1374211 * 2
def baseEnd_1374211 : Nat := 313613672753701389707833

theorem tailTrace_1374211 : CollatzResearch.WordTrace tailWord_1374211 prefixEnd_1374211 313613672753701389707833 := by
  unfold tailWord_1374211
  simp only [CollatzResearch.WordTrace]
  refine ⟨50121592824475718398762487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33414395216317145599174991 50121592824475718398762487)
  ·
    refine ⟨75182389236713577598143731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50121592824475718398762487 75182389236713577598143731)
    ·
      refine ⟨112773583855070366397215597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75182389236713577598143731 112773583855070366397215597)
      ·
        refine ⟨42290093945651387398955849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112773583855070366397215597 42290093945651387398955849)
        ·
          refine ⟨31717570459238540549216887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42290093945651387398955849 31717570459238540549216887)
          ·
            refine ⟨47576355688857810823825331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31717570459238540549216887 47576355688857810823825331)
            ·
              refine ⟨71364533533286716235737997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47576355688857810823825331 71364533533286716235737997)
              ·
                refine ⟨26761700074982518588401749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71364533533286716235737997 26761700074982518588401749)
                ·
                  refine ⟨313613672753701389707833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26761700074982518588401749 313613672753701389707833)
                  ·
                    rfl

theorem cell21_1374211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 8].length) (baseStart_1374211 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1374211 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1374211 prefixEnd_1374211 := by exact prefixLift 1374211
  have htrace : WordTrace (prefixWord ++ tailWord_1374211) baseStart_1374211 baseEnd_1374211 := by
    simpa [prefixWord, tailWord_1374211, baseEnd_1374211] using wordTrace_append hprefix tailTrace_1374211
  have hstable : (prefixWord ++ tailWord_1374211).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374211).length < 2 ^ (prefixWord ++ tailWord_1374211).sum := by decide
  have hdescent : baseEnd_1374211 < baseStart_1374211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374287 : List Nat := [1, 1, 2, 1, 1, 2, 2, 5, 6]
def baseStart_1374287 : Nat := 118140960795 + 1374287 * 2 ^ 59
def prefixEnd_1374287 : Nat := 4983230072969 + 3 ^ 40 * 1374287 * 2
def baseEnd_1374287 : Nat := 313631016989142146441011

theorem tailTrace_1374287 : CollatzResearch.WordTrace tailWord_1374287 prefixEnd_1374287 313631016989142146441011 := by
  unfold tailWord_1374287
  simp only [CollatzResearch.WordTrace]
  refine ⟨50124364772200383378529115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33416243181466922252352743 50124364772200383378529115)
  ·
    refine ⟨75186547158300575067793673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50124364772200383378529115 75186547158300575067793673)
    ·
      refine ⟨56389910368725431300845255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75186547158300575067793673 56389910368725431300845255)
      ·
        refine ⟨84584865553088146951267883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56389910368725431300845255 84584865553088146951267883)
        ·
          refine ⟨126877298329632220426901825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84584865553088146951267883 126877298329632220426901825)
          ·
            refine ⟨95157973747224165320176369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126877298329632220426901825 95157973747224165320176369)
            ·
              refine ⟨71368480310418123990132277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95157973747224165320176369 71368480310418123990132277)
              ·
                refine ⟨6690795029101699124074901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71368480310418123990132277 6690795029101699124074901)
                ·
                  refine ⟨313631016989142146441011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6690795029101699124074901 313631016989142146441011)
                  ·
                    rfl

theorem cell21_1374287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 6].length) (baseStart_1374287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1374287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1374287 prefixEnd_1374287 := by exact prefixLift 1374287
  have htrace : WordTrace (prefixWord ++ tailWord_1374287) baseStart_1374287 baseEnd_1374287 := by
    simpa [prefixWord, tailWord_1374287, baseEnd_1374287] using wordTrace_append hprefix tailTrace_1374287
  have hstable : (prefixWord ++ tailWord_1374287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374287).length < 2 ^ (prefixWord ++ tailWord_1374287).sum := by decide
  have hdescent : baseEnd_1374287 < baseStart_1374287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374400 : List Nat := [2, 1, 1, 2, 5, 3, 2, 2, 3]
def baseStart_1374400 : Nat := 118140960795 + 1374400 * 2 ^ 59
def prefixEnd_1374400 : Nat := 4983230072969 + 3 ^ 40 * 1374400 * 2
def baseEnd_1374400 : Nat := 313656805128679061057447

theorem tailTrace_1374400 : CollatzResearch.WordTrace tailWord_1374400 prefixEnd_1374400 313656805128679061057447 := by
  unfold tailWord_1374400
  simp only [CollatzResearch.WordTrace]
  refine ⟨25064243110395501838696327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33418990813860669118261769 25064243110395501838696327)
  ·
    refine ⟨37596364665593252758044491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25064243110395501838696327 37596364665593252758044491)
    ·
      refine ⟨56394546998389879137066737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37596364665593252758044491 56394546998389879137066737)
      ·
        refine ⟨42295910248792409352800053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56394546998389879137066737 42295910248792409352800053)
        ·
          refine ⟨3965241585824288376825005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42295910248792409352800053 3965241585824288376825005)
          ·
            refine ⟨1486965594684108141309377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3965241585824288376825005 1486965594684108141309377)
            ·
              refine ⟨1115224196013081105982033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1486965594684108141309377 1115224196013081105982033)
              ·
                refine ⟨836418147009810829486525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1115224196013081105982033 836418147009810829486525)
                ·
                  refine ⟨313656805128679061057447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 836418147009810829486525 313656805128679061057447)
                  ·
                    rfl

theorem cell21_1374400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 2, 3].length) (baseStart_1374400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1374400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1374400 prefixEnd_1374400 := by exact prefixLift 1374400
  have htrace : WordTrace (prefixWord ++ tailWord_1374400) baseStart_1374400 baseEnd_1374400 := by
    simpa [prefixWord, tailWord_1374400, baseEnd_1374400] using wordTrace_append hprefix tailTrace_1374400
  have hstable : (prefixWord ++ tailWord_1374400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374400).length < 2 ^ (prefixWord ++ tailWord_1374400).sum := by decide
  have hdescent : baseEnd_1374400 < baseStart_1374400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374434 : List Nat := [3, 3, 4, 1, 1, 1, 2, 3, 3]
def baseStart_1374434 : Nat := 118140960795 + 1374434 * 2 ^ 59
def prefixEnd_1374434 : Nat := 4983230072969 + 3 ^ 40 * 1374434 * 2
def baseEnd_1374434 : Nat := 313664564391902557490711

theorem tailTrace_1374434 : CollatzResearch.WordTrace tailWord_1374434 prefixEnd_1374434 313664564391902557490711 := by
  unfold tailWord_1374434
  simp only [CollatzResearch.WordTrace]
  refine ⟨12532431575666956871032589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33419817535111884989420237 12532431575666956871032589)
  ·
    refine ⟨4699661840875108826637221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12532431575666956871032589 4699661840875108826637221)
    ·
      refine ⟨881186595164082904994479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4699661840875108826637221 881186595164082904994479)
      ·
        refine ⟨1321779892746124357491719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 881186595164082904994479 1321779892746124357491719)
        ·
          refine ⟨1982669839119186536237579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1321779892746124357491719 1982669839119186536237579)
          ·
            refine ⟨2974004758678779804356369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1982669839119186536237579 2974004758678779804356369)
            ·
              refine ⟨2230503569009084853267277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2974004758678779804356369 2230503569009084853267277)
              ·
                refine ⟨836438838378406819975229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2230503569009084853267277 836438838378406819975229)
                ·
                  refine ⟨313664564391902557490711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 836438838378406819975229 313664564391902557490711)
                  ·
                    rfl

theorem cell21_1374434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_1374434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1374434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1374434 prefixEnd_1374434 := by exact prefixLift 1374434
  have htrace : WordTrace (prefixWord ++ tailWord_1374434) baseStart_1374434 baseEnd_1374434 := by
    simpa [prefixWord, tailWord_1374434, baseEnd_1374434] using wordTrace_append hprefix tailTrace_1374434
  have hstable : (prefixWord ++ tailWord_1374434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374434).length < 2 ^ (prefixWord ++ tailWord_1374434).sum := by decide
  have hdescent : baseEnd_1374434 < baseStart_1374434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374473 : List Nat := [1, 2, 1, 1, 3, 5, 3, 1, 4]
def baseStart_1374473 : Nat := 118140960795 + 1374473 * 2 ^ 59
def prefixEnd_1374473 : Nat := 4983230072969 + 3 ^ 40 * 1374473 * 2
def baseEnd_1374473 : Nat := 313673464723247156340631

theorem tailTrace_1374473 : CollatzResearch.WordTrace tailWord_1374473 prefixEnd_1374473 313673464723247156340631 := by
  unfold tailWord_1374473
  simp only [CollatzResearch.WordTrace]
  refine ⟨50131148749526537144800073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33420765833017691429866715 50131148749526537144800073)
  ·
    refine ⟨37598361562144902858600055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50131148749526537144800073 37598361562144902858600055)
    ·
      refine ⟨56397542343217354287900083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37598361562144902858600055 56397542343217354287900083)
      ·
        refine ⟨84596313514826031431850125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56397542343217354287900083 84596313514826031431850125)
        ·
          refine ⟨31723617568059761786943797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84596313514826031431850125 31723617568059761786943797)
          ·
            refine ⟨2974089147005602667525981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31723617568059761786943797 2974089147005602667525981)
            ·
              refine ⟨1115283430127101000322243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2974089147005602667525981 1115283430127101000322243)
              ·
                refine ⟨1672925145190651500483365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1115283430127101000322243 1672925145190651500483365)
                ·
                  refine ⟨313673464723247156340631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1672925145190651500483365 313673464723247156340631)
                  ·
                    rfl

theorem cell21_1374473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 1, 4].length) (baseStart_1374473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1374473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1374473 prefixEnd_1374473 := by exact prefixLift 1374473
  have htrace : WordTrace (prefixWord ++ tailWord_1374473) baseStart_1374473 baseEnd_1374473 := by
    simpa [prefixWord, tailWord_1374473, baseEnd_1374473] using wordTrace_append hprefix tailTrace_1374473
  have hstable : (prefixWord ++ tailWord_1374473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374473).length < 2 ^ (prefixWord ++ tailWord_1374473).sum := by decide
  have hdescent : baseEnd_1374473 < baseStart_1374473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374487 : List Nat := [1, 1, 3, 4, 1, 2, 4, 5]
def baseStart_1374487 : Nat := 118140960795 + 1374487 * 2 ^ 59
def prefixEnd_1374487 : Nat := 4983230072969 + 3 ^ 40 * 1374487 * 2
def baseEnd_1374487 : Nat := 104558886571328747702423

theorem tailTrace_1374487 : CollatzResearch.WordTrace tailWord_1374487 prefixEnd_1374487 104558886571328747702423 := by
  unfold tailWord_1374487
  simp only [CollatzResearch.WordTrace]
  refine ⟨50131659371475817535809715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33421106247650545023873143 50131659371475817535809715)
  ·
    refine ⟨75197489057213726303714573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50131659371475817535809715 75197489057213726303714573)
    ·
      refine ⟨28199058396455147363892965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75197489057213726303714573 28199058396455147363892965)
      ·
        refine ⟨5287323449335340130729931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28199058396455147363892965 5287323449335340130729931)
        ·
          refine ⟨7930985174003010196094897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5287323449335340130729931 7930985174003010196094897)
          ·
            refine ⟨5948238880502257647071173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7930985174003010196094897 5948238880502257647071173)
            ·
              refine ⟨1115294790094173308825845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5948238880502257647071173 1115294790094173308825845)
              ·
                refine ⟨104558886571328747702423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1115294790094173308825845 104558886571328747702423)
                ·
                  rfl

theorem cell21_1374487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 5].length) (baseStart_1374487 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1374487 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1374487 prefixEnd_1374487 := by exact prefixLift 1374487
  have htrace : WordTrace (prefixWord ++ tailWord_1374487) baseStart_1374487 baseEnd_1374487 := by
    simpa [prefixWord, tailWord_1374487, baseEnd_1374487] using wordTrace_append hprefix tailTrace_1374487
  have hstable : (prefixWord ++ tailWord_1374487).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374487).length < 2 ^ (prefixWord ++ tailWord_1374487).sum := by decide
  have hdescent : baseEnd_1374487 < baseStart_1374487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374493 : List Nat := [1, 4, 2, 3, 3, 1, 1, 3, 3]
def baseStart_1374493 : Nat := 118140960795 + 1374493 * 2 ^ 59
def prefixEnd_1374493 : Nat := 4983230072969 + 3 ^ 40 * 1374493 * 2
def baseEnd_1374493 : Nat := 313678028995731566007257

theorem tailTrace_1374493 : CollatzResearch.WordTrace tailWord_1374493 prefixEnd_1374493 313678028995731566007257 := by
  unfold tailWord_1374493
  simp only [CollatzResearch.WordTrace]
  refine ⟨50131878209454080560528133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33421252139636053707018755 50131878209454080560528133)
  ·
    refine ⟨9399727164272640105099025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50131878209454080560528133 9399727164272640105099025)
    ·
      refine ⟨7049795373204480078824269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9399727164272640105099025 7049795373204480078824269)
      ·
        refine ⟨2643673264951680029559101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7049795373204480078824269 2643673264951680029559101)
        ·
          refine ⟨991377474356880011084663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2643673264951680029559101 991377474356880011084663)
          ·
            refine ⟨1487066211535320016626995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 991377474356880011084663 1487066211535320016626995)
            ·
              refine ⟨2230599317302980024940493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1487066211535320016626995 2230599317302980024940493)
              ·
                refine ⟨836474743988617509352685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2230599317302980024940493 836474743988617509352685)
                ·
                  refine ⟨313678028995731566007257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 836474743988617509352685 313678028995731566007257)
                  ·
                    rfl

theorem cell21_1374493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 3, 3].length) (baseStart_1374493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1374493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1374493 prefixEnd_1374493 := by exact prefixLift 1374493
  have htrace : WordTrace (prefixWord ++ tailWord_1374493) baseStart_1374493 baseEnd_1374493 := by
    simpa [prefixWord, tailWord_1374493, baseEnd_1374493] using wordTrace_append hprefix tailTrace_1374493
  have hstable : (prefixWord ++ tailWord_1374493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374493).length < 2 ^ (prefixWord ++ tailWord_1374493).sum := by decide
  have hdescent : baseEnd_1374493 < baseStart_1374493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374504 : List Nat := [2, 1, 5, 1, 4, 1, 7]
def baseStart_1374504 : Nat := 118140960795 + 1374504 * 2 ^ 59
def prefixEnd_1374504 : Nat := 4983230072969 + 3 ^ 40 * 1374504 * 2
def baseEnd_1374504 : Nat := 34853393260621999035989

theorem tailTrace_1374504 : CollatzResearch.WordTrace tailWord_1374504 prefixEnd_1374504 34853393260621999035989 := by
  unfold tailWord_1374504
  simp only [CollatzResearch.WordTrace]
  refine ⟨25066139706207114719589283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33421519608276152959452377 25066139706207114719589283)
  ·
    refine ⟨37599209559310672079383925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25066139706207114719589283 37599209559310672079383925)
    ·
      refine ⟨3524925896185375507442243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37599209559310672079383925 3524925896185375507442243)
      ·
        refine ⟨5287388844278063261163365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3524925896185375507442243 5287388844278063261163365)
        ·
          refine ⟨991385408302136861468131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5287388844278063261163365 991385408302136861468131)
          ·
            refine ⟨1487078112453205292202197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 991385408302136861468131 1487078112453205292202197)
            ·
              refine ⟨34853393260621999035989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1487078112453205292202197 34853393260621999035989)
              ·
                rfl

theorem cell21_1374504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 7].length) (baseStart_1374504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1374504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1374504 prefixEnd_1374504 := by exact prefixLift 1374504
  have htrace : WordTrace (prefixWord ++ tailWord_1374504) baseStart_1374504 baseEnd_1374504 := by
    simpa [prefixWord, tailWord_1374504, baseEnd_1374504] using wordTrace_append hprefix tailTrace_1374504
  have hstable : (prefixWord ++ tailWord_1374504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374504).length < 2 ^ (prefixWord ++ tailWord_1374504).sum := by decide
  have hdescent : baseEnd_1374504 < baseStart_1374504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374515 : List Nat := [1, 1, 1, 2, 5, 1, 1, 3, 6]
def baseStart_1374515 : Nat := 118140960795 + 1374515 * 2 ^ 59
def prefixEnd_1374515 : Nat := 4983230072969 + 3 ^ 40 * 1374515 * 2
def baseEnd_1374515 : Nat := 313683049695464416640545

theorem tailTrace_1374515 : CollatzResearch.WordTrace tailWord_1374515 prefixEnd_1374515 313683049695464416640545 := by
  unfold tailWord_1374515
  simp only [CollatzResearch.WordTrace]
  refine ⟨50132680615374378317828999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33421787076916252211885999 50132680615374378317828999)
  ·
    refine ⟨75199020923061567476743499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50132680615374378317828999 75199020923061567476743499)
    ·
      refine ⟨112798531384592351215115249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75199020923061567476743499 112798531384592351215115249)
      ·
        refine ⟨84598898538444263411336437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112798531384592351215115249 84598898538444263411336437)
        ·
          refine ⟨7931146737979149694812791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84598898538444263411336437 7931146737979149694812791)
          ·
            refine ⟨11896720106968724542219187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7931146737979149694812791 11896720106968724542219187)
            ·
              refine ⟨17845080160453086813328781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11896720106968724542219187 17845080160453086813328781)
              ·
                refine ⟨6691905060169907554998293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17845080160453086813328781 6691905060169907554998293)
                ·
                  refine ⟨313683049695464416640545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6691905060169907554998293 313683049695464416640545)
                  ·
                    rfl

theorem cell21_1374515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 6].length) (baseStart_1374515 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1374515 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1374515 prefixEnd_1374515 := by exact prefixLift 1374515
  have htrace : WordTrace (prefixWord ++ tailWord_1374515) baseStart_1374515 baseEnd_1374515 := by
    simpa [prefixWord, tailWord_1374515, baseEnd_1374515] using wordTrace_append hprefix tailTrace_1374515
  have hstable : (prefixWord ++ tailWord_1374515).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374515).length < 2 ^ (prefixWord ++ tailWord_1374515).sum := by decide
  have hdescent : baseEnd_1374515 < baseStart_1374515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374546 : List Nat := [3, 2, 2, 1, 1, 1, 4, 7]
def baseStart_1374546 : Nat := 118140960795 + 1374546 * 2 ^ 59
def prefixEnd_1374546 : Nat := 4983230072969 + 3 ^ 40 * 1374546 * 2
def baseEnd_1374546 : Nat := 104563374772605083874605

theorem tailTrace_1374546 : CollatzResearch.WordTrace tailWord_1374546 prefixEnd_1374546 104563374772605083874605 := by
  unfold tailWord_1374546
  simp only [CollatzResearch.WordTrace]
  refine ⟨12533452819565517653051873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33422540852174713741471661 12533452819565517653051873)
  ·
    refine ⟨9400089614674138239788905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12533452819565517653051873 9400089614674138239788905)
    ·
      refine ⟨7050067211005603679841679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9400089614674138239788905 7050067211005603679841679)
      ·
        refine ⟨10575100816508405519762519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7050067211005603679841679 10575100816508405519762519)
        ·
          refine ⟨15862651224762608279643779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10575100816508405519762519 15862651224762608279643779)
          ·
            refine ⟨23793976837143912419465669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15862651224762608279643779 23793976837143912419465669)
            ·
              refine ⟨4461370656964483578649813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23793976837143912419465669 4461370656964483578649813)
              ·
                refine ⟨104563374772605083874605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4461370656964483578649813 104563374772605083874605)
                ·
                  rfl

theorem cell21_1374546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 7].length) (baseStart_1374546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1374546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1374546 prefixEnd_1374546 := by exact prefixLift 1374546
  have htrace : WordTrace (prefixWord ++ tailWord_1374546) baseStart_1374546 baseEnd_1374546 := by
    simpa [prefixWord, tailWord_1374546, baseEnd_1374546] using wordTrace_append hprefix tailTrace_1374546
  have hstable : (prefixWord ++ tailWord_1374546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374546).length < 2 ^ (prefixWord ++ tailWord_1374546).sum := by decide
  have hdescent : baseEnd_1374546 < baseStart_1374546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374625 : List Nat := [1, 2, 3, 5, 1, 1, 1, 1, 6]
def baseStart_1374625 : Nat := 118140960795 + 1374625 * 2 ^ 59
def prefixEnd_1374625 : Nat := 4983230072969 + 3 ^ 40 * 1374625 * 2
def baseEnd_1374625 : Nat := 313708153194128669806987

theorem tailTrace_1374625 : CollatzResearch.WordTrace tailWord_1374625 prefixEnd_1374625 313708153194128669806987 := by
  unfold tailWord_1374625
  simp only [CollatzResearch.WordTrace]
  refine ⟨50136692644975867104333329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33424461763317244736222219 50136692644975867104333329)
  ·
    refine ⟨37602519483731900328249997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50136692644975867104333329 37602519483731900328249997)
    ·
      refine ⟨14100944806399462623093749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37602519483731900328249997 14100944806399462623093749)
      ·
        refine ⟨1321963575599949620915039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14100944806399462623093749 1321963575599949620915039)
        ·
          refine ⟨1982945363399924431372559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1321963575599949620915039 1982945363399924431372559)
          ·
            refine ⟨2974418045099886647058839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1982945363399924431372559 2974418045099886647058839)
            ·
              refine ⟨4461627067649829970588259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2974418045099886647058839 4461627067649829970588259)
              ·
                refine ⟨6692440601474744955882389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4461627067649829970588259 6692440601474744955882389)
                ·
                  refine ⟨313708153194128669806987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6692440601474744955882389 313708153194128669806987)
                  ·
                    rfl

theorem cell21_1374625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 6].length) (baseStart_1374625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1374625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1374625 prefixEnd_1374625 := by exact prefixLift 1374625
  have htrace : WordTrace (prefixWord ++ tailWord_1374625) baseStart_1374625 baseEnd_1374625 := by
    simpa [prefixWord, tailWord_1374625, baseEnd_1374625] using wordTrace_append hprefix tailTrace_1374625
  have hstable : (prefixWord ++ tailWord_1374625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374625).length < 2 ^ (prefixWord ++ tailWord_1374625).sum := by decide
  have hdescent : baseEnd_1374625 < baseStart_1374625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374653 : List Nat := [1, 4, 1, 2, 2, 2, 2, 2, 5]
def baseStart_1374653 : Nat := 118140960795 + 1374653 * 2 ^ 59
def prefixEnd_1374653 : Nat := 4983230072969 + 3 ^ 40 * 1374653 * 2
def baseEnd_1374653 : Nat := 313714543175606843340263

theorem tailTrace_1374653 : CollatzResearch.WordTrace tailWord_1374653 prefixEnd_1374653 313714543175606843340263 := by
  unfold tailWord_1374653
  simp only [CollatzResearch.WordTrace]
  refine ⟨50137713888874427886352613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33425142592582951924235075 50137713888874427886352613)
  ·
    refine ⟨9400821354163955228691115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50137713888874427886352613 9400821354163955228691115)
    ·
      refine ⟨14101232031245932843036673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9400821354163955228691115 14101232031245932843036673)
      ·
        refine ⟨10575924023434449632277505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14101232031245932843036673 10575924023434449632277505)
        ·
          refine ⟨7931943017575837224208129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10575924023434449632277505 7931943017575837224208129)
          ·
            refine ⟨5948957263181877918156097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7931943017575837224208129 5948957263181877918156097)
            ·
              refine ⟨4461717947386408438617073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5948957263181877918156097 4461717947386408438617073)
              ·
                refine ⟨3346288460539806328962805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4461717947386408438617073 3346288460539806328962805)
                ·
                  refine ⟨313714543175606843340263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3346288460539806328962805 313714543175606843340263)
                  ·
                    rfl

theorem cell21_1374653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_1374653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1374653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1374653 prefixEnd_1374653 := by exact prefixLift 1374653
  have htrace : WordTrace (prefixWord ++ tailWord_1374653) baseStart_1374653 baseEnd_1374653 := by
    simpa [prefixWord, tailWord_1374653, baseEnd_1374653] using wordTrace_append hprefix tailTrace_1374653
  have hstable : (prefixWord ++ tailWord_1374653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374653).length < 2 ^ (prefixWord ++ tailWord_1374653).sum := by decide
  have hdescent : baseEnd_1374653 < baseStart_1374653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374687 : List Nat := [1, 1, 2, 3, 3, 3, 3, 2, 3]
def baseStart_1374687 : Nat := 118140960795 + 1374687 * 2 ^ 59
def prefixEnd_1374687 : Nat := 4983230072969 + 3 ^ 40 * 1374687 * 2
def baseEnd_1374687 : Nat := 313722302438830339773527

theorem tailTrace_1374687 : CollatzResearch.WordTrace tailWord_1374687 prefixEnd_1374687 313722302438830339773527 := by
  unfold tailWord_1374687
  simp only [CollatzResearch.WordTrace]
  refine ⟨50138953970751251693090315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33425969313834167795393543 50138953970751251693090315)
  ·
    refine ⟨75208430956126877539635473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50138953970751251693090315 75208430956126877539635473)
    ·
      refine ⟨56406323217095158154726605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75208430956126877539635473 56406323217095158154726605)
      ·
        refine ⟨21152371206410684308022477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56406323217095158154726605 21152371206410684308022477)
        ·
          refine ⟨7932139202404006615508429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21152371206410684308022477 7932139202404006615508429)
          ·
            refine ⟨2974552200901502480815661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7932139202404006615508429 2974552200901502480815661)
            ·
              refine ⟨1115457075338063430305873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2974552200901502480815661 1115457075338063430305873)
              ·
                refine ⟨836592806503547572729405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1115457075338063430305873 836592806503547572729405)
                ·
                  refine ⟨313722302438830339773527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 836592806503547572729405 313722302438830339773527)
                  ·
                    rfl

theorem cell21_1374687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 2, 3].length) (baseStart_1374687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1374687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1374687 prefixEnd_1374687 := by exact prefixLift 1374687
  have htrace : WordTrace (prefixWord ++ tailWord_1374687) baseStart_1374687 baseEnd_1374687 := by
    simpa [prefixWord, tailWord_1374687, baseEnd_1374687] using wordTrace_append hprefix tailTrace_1374687
  have hstable : (prefixWord ++ tailWord_1374687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374687).length < 2 ^ (prefixWord ++ tailWord_1374687).sum := by decide
  have hdescent : baseEnd_1374687 < baseStart_1374687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374698 : List Nat := [3, 1, 3, 1, 3, 1, 1, 8]
def baseStart_1374698 : Nat := 118140960795 + 1374698 * 2 ^ 59
def prefixEnd_1374698 : Nat := 4983230072969 + 3 ^ 40 * 1374698 * 2
def baseEnd_1374698 : Nat := 104574937596232255030057

theorem tailTrace_1374698 : CollatzResearch.WordTrace tailWord_1374698 prefixEnd_1374698 104574937596232255030057 := by
  unfold tailWord_1374698
  simp only [CollatzResearch.WordTrace]
  refine ⟨12534838793427850142935187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33426236782474267047827165 12534838793427850142935187)
  ·
    refine ⟨18802258190141775214402781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12534838793427850142935187 18802258190141775214402781)
    ·
      refine ⟨7050846821303165705401043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18802258190141775214402781 7050846821303165705401043)
      ·
        refine ⟨10576270231954748558101565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7050846821303165705401043 10576270231954748558101565)
        ·
          refine ⟨3966101336983030709288087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10576270231954748558101565 3966101336983030709288087)
          ·
            refine ⟨5949152005474546063932131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3966101336983030709288087 5949152005474546063932131)
            ·
              refine ⟨8923728008211819095898197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5949152005474546063932131 8923728008211819095898197)
              ·
                refine ⟨104574937596232255030057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8923728008211819095898197 104574937596232255030057)
                ·
                  rfl

theorem cell21_1374698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 8].length) (baseStart_1374698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1374698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1374698 prefixEnd_1374698 := by exact prefixLift 1374698
  have htrace : WordTrace (prefixWord ++ tailWord_1374698) baseStart_1374698 baseEnd_1374698 := by
    simpa [prefixWord, tailWord_1374698, baseEnd_1374698] using wordTrace_append hprefix tailTrace_1374698
  have hstable : (prefixWord ++ tailWord_1374698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374698).length < 2 ^ (prefixWord ++ tailWord_1374698).sum := by decide
  have hdescent : baseEnd_1374698 < baseStart_1374698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374701 : List Nat := [1, 5, 1, 3, 1, 2, 1, 3, 4]
def baseStart_1374701 : Nat := 118140960795 + 1374701 * 2 ^ 59
def prefixEnd_1374701 : Nat := 4983230072969 + 3 ^ 40 * 1374701 * 2
def baseEnd_1374701 : Nat := 313725497429569426540165

theorem tailTrace_1374701 : CollatzResearch.WordTrace tailWord_1374701 prefixEnd_1374701 313725497429569426540165 := by
  unfold tailWord_1374701
  simp only [CollatzResearch.WordTrace]
  refine ⟨50139464592700532084099957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33426309728467021389399971 50139464592700532084099957)
  ·
    refine ⟨4700574805565674882884371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50139464592700532084099957 4700574805565674882884371)
    ·
      refine ⟨7050862208348512324326557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4700574805565674882884371 7050862208348512324326557)
      ·
        refine ⟨2644073328130692121622459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7050862208348512324326557 2644073328130692121622459)
        ·
          refine ⟨3966109992196038182433689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2644073328130692121622459 3966109992196038182433689)
          ·
            refine ⟨2974582494147028636825267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3966109992196038182433689 2974582494147028636825267)
            ·
              refine ⟨4461873741220542955237901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2974582494147028636825267 4461873741220542955237901)
              ·
                refine ⟨1673202652957703608214213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4461873741220542955237901 1673202652957703608214213)
                ·
                  refine ⟨313725497429569426540165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1673202652957703608214213 313725497429569426540165)
                  ·
                    rfl

theorem cell21_1374701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_1374701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1374701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1374701 prefixEnd_1374701 := by exact prefixLift 1374701
  have htrace : WordTrace (prefixWord ++ tailWord_1374701) baseStart_1374701 baseEnd_1374701 := by
    simpa [prefixWord, tailWord_1374701, baseEnd_1374701] using wordTrace_append hprefix tailTrace_1374701
  have hstable : (prefixWord ++ tailWord_1374701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374701).length < 2 ^ (prefixWord ++ tailWord_1374701).sum := by decide
  have hdescent : baseEnd_1374701 < baseStart_1374701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374712 : List Nat := [2, 1, 2, 1, 1, 4, 2, 1, 7]
def baseStart_1374712 : Nat := 118140960795 + 1374712 * 2 ^ 59
def prefixEnd_1374712 : Nat := 4983230072969 + 3 ^ 40 * 1374712 * 2
def baseEnd_1374712 : Nat := 313728007779435851856809

theorem tailTrace_1374712 : CollatzResearch.WordTrace tailWord_1374712 prefixEnd_1374712 313728007779435851856809 := by
  unfold tailWord_1374712
  simp only [CollatzResearch.WordTrace]
  refine ⟨25069932897830340481375195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33426577197107120641833593 25069932897830340481375195)
  ·
    refine ⟨37604899346745510722062793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25069932897830340481375195 37604899346745510722062793)
    ·
      refine ⟨28203674510059133041547095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37604899346745510722062793 28203674510059133041547095)
      ·
        refine ⟨42305511765088699562320643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28203674510059133041547095 42305511765088699562320643)
        ·
          refine ⟨63458267647633049343480965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42305511765088699562320643 63458267647633049343480965)
          ·
            refine ⟨11898425183931196751902681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63458267647633049343480965 11898425183931196751902681)
            ·
              refine ⟨8923818887948397563927011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11898425183931196751902681 8923818887948397563927011)
              ·
                refine ⟨13385728331922596345890517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8923818887948397563927011 13385728331922596345890517)
                ·
                  refine ⟨313728007779435851856809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13385728331922596345890517 313728007779435851856809)
                  ·
                    rfl

theorem cell21_1374712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 7].length) (baseStart_1374712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1374712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1374712 prefixEnd_1374712 := by exact prefixLift 1374712
  have htrace : WordTrace (prefixWord ++ tailWord_1374712) baseStart_1374712 baseEnd_1374712 := by
    simpa [prefixWord, tailWord_1374712, baseEnd_1374712] using wordTrace_append hprefix tailTrace_1374712
  have hstable : (prefixWord ++ tailWord_1374712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374712).length < 2 ^ (prefixWord ++ tailWord_1374712).sum := by decide
  have hdescent : baseEnd_1374712 < baseStart_1374712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374909 : List Nat := [1, 4, 1, 2, 1, 12]
def baseStart_1374909 : Nat := 118140960795 + 1374909 * 2 ^ 59
def prefixEnd_1374909 : Nat := 4983230072969 + 3 ^ 40 * 1374909 * 2
def baseEnd_1374909 : Nat := 11621220957903973595299

theorem tailTrace_1374909 : CollatzResearch.WordTrace tailWord_1374909 prefixEnd_1374909 11621220957903973595299 := by
  unfold tailWord_1374909
  simp only [CollatzResearch.WordTrace]
  refine ⟨50147050975946983607671781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33431367317297989071781187 50147050975946983607671781)
  ·
    refine ⟨9402572057990059426438459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50147050975946983607671781 9402572057990059426438459)
    ·
      refine ⟨14103858086985089139657689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9402572057990059426438459 14103858086985089139657689)
      ·
        refine ⟨10577893565238816854743267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14103858086985089139657689 10577893565238816854743267)
        ·
          refine ⟨15866840347858225282114901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10577893565238816854743267 15866840347858225282114901)
          ·
            refine ⟨11621220957903973595299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 15866840347858225282114901 11621220957903973595299)
            ·
              rfl

theorem cell21_1374909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 12].length) (baseStart_1374909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1374909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1374909 prefixEnd_1374909 := by exact prefixLift 1374909
  have htrace : WordTrace (prefixWord ++ tailWord_1374909) baseStart_1374909 baseEnd_1374909 := by
    simpa [prefixWord, tailWord_1374909, baseEnd_1374909] using wordTrace_append hprefix tailTrace_1374909
  have hstable : (prefixWord ++ tailWord_1374909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374909).length < 2 ^ (prefixWord ++ tailWord_1374909).sum := by decide
  have hdescent : baseEnd_1374909 < baseStart_1374909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374912 : List Nat := [2, 1, 1, 2, 4, 3, 2, 2, 4]
def baseStart_1374912 : Nat := 118140960795 + 1374912 * 2 ^ 59
def prefixEnd_1374912 : Nat := 4983230072969 + 3 ^ 40 * 1374912 * 2
def baseEnd_1374912 : Nat := 313773650504279948523067

theorem tailTrace_1374912 : CollatzResearch.WordTrace tailWord_1374912 prefixEnd_1374912 313773650504279948523067 := by
  unfold tailWord_1374912
  simp only [CollatzResearch.WordTrace]
  refine ⟨25073580197468057560015495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33431440263290743413353993 25073580197468057560015495)
  ·
    refine ⟨37610370296202086340023243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25073580197468057560015495 37610370296202086340023243)
    ·
      refine ⟨56415555444303129510034865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37610370296202086340023243 56415555444303129510034865)
      ·
        refine ⟨42311666583227347132526149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56415555444303129510034865 42311666583227347132526149)
        ·
          refine ⟨7933437484355127587348653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42311666583227347132526149 7933437484355127587348653)
          ·
            refine ⟨2975039056633172845255745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7933437484355127587348653 2975039056633172845255745)
            ·
              refine ⟨2231279292474879633941809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2975039056633172845255745 2231279292474879633941809)
              ·
                refine ⟨1673459469356159725456357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2231279292474879633941809 1673459469356159725456357)
                ·
                  refine ⟨313773650504279948523067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1673459469356159725456357 313773650504279948523067)
                  ·
                    rfl

theorem cell21_1374912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 2, 4].length) (baseStart_1374912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1374912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1374912 prefixEnd_1374912 := by exact prefixLift 1374912
  have htrace : WordTrace (prefixWord ++ tailWord_1374912) baseStart_1374912 baseEnd_1374912 := by
    simpa [prefixWord, tailWord_1374912, baseEnd_1374912] using wordTrace_append hprefix tailTrace_1374912
  have hstable : (prefixWord ++ tailWord_1374912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374912).length < 2 ^ (prefixWord ++ tailWord_1374912).sum := by decide
  have hdescent : baseEnd_1374912 < baseStart_1374912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374918 : List Nat := [6, 1, 2, 1, 3, 1, 1, 6]
def baseStart_1374918 : Nat := 118140960795 + 1374918 * 2 ^ 59
def prefixEnd_1374918 : Nat := 4983230072969 + 3 ^ 40 * 1374918 * 2
def baseEnd_1374918 : Nat := 104591673262008423807685

theorem tailTrace_1374918 : CollatzResearch.WordTrace tailWord_1374918 prefixEnd_1374918 104591673262008423807685 := by
  unfold tailWord_1374918
  simp only [CollatzResearch.WordTrace]
  refine ⟨1567105601028574317023419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33431586155276252096499605 1567105601028574317023419)
  ·
    refine ⟨2350658401542861475535129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1567105601028574317023419 2350658401542861475535129)
    ·
      refine ⟨1762993801157146106651347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2350658401542861475535129 1762993801157146106651347)
      ·
        refine ⟨2644490701735719159977021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1762993801157146106651347 2644490701735719159977021)
        ·
          refine ⟨991684013150894684991383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2644490701735719159977021 991684013150894684991383)
          ·
            refine ⟨1487526019726342027487075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 991684013150894684991383 1487526019726342027487075)
            ·
              refine ⟨2231289029589513041230613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1487526019726342027487075 2231289029589513041230613)
              ·
                refine ⟨104591673262008423807685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2231289029589513041230613 104591673262008423807685)
                ·
                  rfl

theorem cell21_1374918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_1374918 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1374918 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1374918 prefixEnd_1374918 := by exact prefixLift 1374918
  have htrace : WordTrace (prefixWord ++ tailWord_1374918) baseStart_1374918 baseEnd_1374918 := by
    simpa [prefixWord, tailWord_1374918, baseEnd_1374918] using wordTrace_append hprefix tailTrace_1374918
  have hstable : (prefixWord ++ tailWord_1374918).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374918).length < 2 ^ (prefixWord ++ tailWord_1374918).sum := by decide
  have hdescent : baseEnd_1374918 < baseStart_1374918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374926 : List Nat := [4, 1, 1, 1, 3, 2, 3, 6]
def baseStart_1374926 : Nat := 118140960795 + 1374926 * 2 ^ 59
def prefixEnd_1374926 : Nat := 4983230072969 + 3 ^ 40 * 1374926 * 2
def baseEnd_1374926 : Nat := 104592281831673011763235

theorem tailTrace_1374926 : CollatzResearch.WordTrace tailWord_1374926 prefixEnd_1374926 104592281831673011763235 := by
  unfold tailWord_1374926
  simp only [CollatzResearch.WordTrace]
  refine ⟨6268458877110674438880079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33431780677923597007360421 6268458877110674438880079)
  ·
    refine ⟨9402688315666011658320119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6268458877110674438880079 9402688315666011658320119)
    ·
      refine ⟨14104032473499017487480179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9402688315666011658320119 14104032473499017487480179)
      ·
        refine ⟨21156048710248526231220269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14104032473499017487480179 21156048710248526231220269)
        ·
          refine ⟨7933518266343197336707601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21156048710248526231220269 7933518266343197336707601)
          ·
            refine ⟨5950138699757398002530701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7933518266343197336707601 5950138699757398002530701)
            ·
              refine ⟨2231302012409024250949013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5950138699757398002530701 2231302012409024250949013)
              ·
                refine ⟨104592281831673011763235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2231302012409024250949013 104592281831673011763235)
                ·
                  rfl

theorem cell21_1374926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_1374926 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1374926 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1374926 prefixEnd_1374926 := by exact prefixLift 1374926
  have htrace : WordTrace (prefixWord ++ tailWord_1374926) baseStart_1374926 baseEnd_1374926 := by
    simpa [prefixWord, tailWord_1374926, baseEnd_1374926] using wordTrace_append hprefix tailTrace_1374926
  have hstable : (prefixWord ++ tailWord_1374926).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374926).length < 2 ^ (prefixWord ++ tailWord_1374926).sum := by decide
  have hdescent : baseEnd_1374926 < baseStart_1374926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374974 : List Nat := [4, 2, 2, 1, 2, 2, 2, 1, 5]
def baseStart_1374974 : Nat := 118140960795 + 1374974 * 2 ^ 59
def prefixEnd_1374974 : Nat := 4983230072969 + 3 ^ 40 * 1374974 * 2
def baseEnd_1374974 : Nat := 313787799748981618489607

theorem tailTrace_1374974 : CollatzResearch.WordTrace tailWord_1374974 prefixEnd_1374974 313787799748981618489607 := by
  unfold tailWord_1374974
  simp only [CollatzResearch.WordTrace]
  refine ⟨6268677715088937463598497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33432947813807666472525317 6268677715088937463598497)
  ·
    refine ⟨4701508286316703097698873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6268677715088937463598497 4701508286316703097698873)
    ·
      refine ⟨3526131214737527323274155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4701508286316703097698873 3526131214737527323274155)
      ·
        refine ⟨5289196822106290984911233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3526131214737527323274155 5289196822106290984911233)
        ·
          refine ⟨3966897616579718238683425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5289196822106290984911233 3966897616579718238683425)
          ·
            refine ⟨2975173212434788679012569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3966897616579718238683425 2975173212434788679012569)
            ·
              refine ⟨2231379909326091509259427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2975173212434788679012569 2231379909326091509259427)
              ·
                refine ⟨3347069863989137263889141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2231379909326091509259427 3347069863989137263889141)
                ·
                  refine ⟨313787799748981618489607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3347069863989137263889141 313787799748981618489607)
                  ·
                    rfl

theorem cell21_1374974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_1374974 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1374974 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1374974 prefixEnd_1374974 := by exact prefixLift 1374974
  have htrace : WordTrace (prefixWord ++ tailWord_1374974) baseStart_1374974 baseEnd_1374974 := by
    simpa [prefixWord, tailWord_1374974, baseEnd_1374974] using wordTrace_append hprefix tailTrace_1374974
  have hstable : (prefixWord ++ tailWord_1374974).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374974).length < 2 ^ (prefixWord ++ tailWord_1374974).sum := by decide
  have hdescent : baseEnd_1374974 < baseStart_1374974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375061 : List Nat := [1, 3, 2, 2, 2, 1, 1, 9]
def baseStart_1375061 : Nat := 118140960795 + 1375061 * 2 ^ 59
def prefixEnd_1375061 : Nat := 4983230072969 + 3 ^ 40 * 1375061 * 2
def baseEnd_1375061 : Nat := 104602551444762933513143

theorem tailTrace_1375061 : CollatzResearch.WordTrace tailWord_1375061 prefixEnd_1375061 104602551444762933513143 := by
  unfold tailWord_1375061
  simp only [CollatzResearch.WordTrace]
  refine ⟨50152594871396313567205037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33435063247597542378136691 50152594871396313567205037)
  ·
    refine ⟨18807223076773617587701889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50152594871396313567205037 18807223076773617587701889)
    ·
      refine ⟨14105417307580213190776417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18807223076773617587701889 14105417307580213190776417)
      ·
        refine ⟨10579062980685159893082313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14105417307580213190776417 10579062980685159893082313)
        ·
          refine ⟨7934297235513869919811735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10579062980685159893082313 7934297235513869919811735)
          ·
            refine ⟨11901445853270804879717603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7934297235513869919811735 11901445853270804879717603)
            ·
              refine ⟨17852168779906207319576405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11901445853270804879717603 17852168779906207319576405)
              ·
                refine ⟨104602551444762933513143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17852168779906207319576405 104602551444762933513143)
                ·
                  rfl

theorem cell21_1375061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 9].length) (baseStart_1375061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1375061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1375061 prefixEnd_1375061 := by exact prefixLift 1375061
  have htrace : WordTrace (prefixWord ++ tailWord_1375061) baseStart_1375061 baseEnd_1375061 := by
    simpa [prefixWord, tailWord_1375061, baseEnd_1375061] using wordTrace_append hprefix tailTrace_1375061
  have hstable : (prefixWord ++ tailWord_1375061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375061).length < 2 ^ (prefixWord ++ tailWord_1375061).sum := by decide
  have hdescent : baseEnd_1375061 < baseStart_1375061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375168 : List Nat := [2, 1, 1, 2, 3, 3, 2, 2, 5]
def baseStart_1375168 : Nat := 118140960795 + 1375168 * 2 ^ 59
def prefixEnd_1375168 : Nat := 4983230072969 + 3 ^ 40 * 1375168 * 2
def baseEnd_1375168 : Nat := 313832073192080392255877

theorem tailTrace_1375168 : CollatzResearch.WordTrace tailWord_1375168 prefixEnd_1375168 313832073192080392255877 := by
  unfold tailWord_1375168
  simp only [CollatzResearch.WordTrace]
  refine ⟨25078248741004335420675079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33437664988005780560900105 25078248741004335420675079)
  ·
    refine ⟨37617373111506503131012619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25078248741004335420675079 37617373111506503131012619)
    ·
      refine ⟨56426059667259754696518929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37617373111506503131012619 56426059667259754696518929)
      ·
        refine ⟨42319544750444816022389197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56426059667259754696518929 42319544750444816022389197)
        ·
          refine ⟨15869829281416806008395949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42319544750444816022389197 15869829281416806008395949)
          ·
            refine ⟨5951185980531302253148481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15869829281416806008395949 5951185980531302253148481)
            ·
              refine ⟨4463389485398476689861361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5951185980531302253148481 4463389485398476689861361)
              ·
                refine ⟨3347542114048857517396021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4463389485398476689861361 3347542114048857517396021)
                ·
                  refine ⟨313832073192080392255877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3347542114048857517396021 313832073192080392255877)
                  ·
                    rfl

theorem cell21_1375168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 5].length) (baseStart_1375168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1375168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1375168 prefixEnd_1375168 := by exact prefixLift 1375168
  have htrace : WordTrace (prefixWord ++ tailWord_1375168) baseStart_1375168 baseEnd_1375168 := by
    simpa [prefixWord, tailWord_1375168, baseEnd_1375168] using wordTrace_append hprefix tailTrace_1375168
  have hstable : (prefixWord ++ tailWord_1375168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375168).length < 2 ^ (prefixWord ++ tailWord_1375168).sum := by decide
  have hdescent : baseEnd_1375168 < baseStart_1375168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375202 : List Nat := [3, 3, 3, 1, 1, 1, 3, 1, 5]
def baseStart_1375202 : Nat := 118140960795 + 1375202 * 2 ^ 59
def prefixEnd_1375202 : Nat := 4983230072969 + 3 ^ 40 * 1375202 * 2
def baseEnd_1375202 : Nat := 313839832455303888689141

theorem tailTrace_1375202 : CollatzResearch.WordTrace tailWord_1375202 prefixEnd_1375202 313839832455303888689141 := by
  unfold tailWord_1375202
  simp only [CollatzResearch.WordTrace]
  refine ⟨12539434390971373662021965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33438491709256996432058573 12539434390971373662021965)
  ·
    refine ⟨4702287896614265123258237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12539434390971373662021965 4702287896614265123258237)
    ·
      refine ⟨1763357961230349421221839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4702287896614265123258237 1763357961230349421221839)
      ·
        refine ⟨2645036941845524131832759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1763357961230349421221839 2645036941845524131832759)
        ·
          refine ⟨3967555412768286197749139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2645036941845524131832759 3967555412768286197749139)
          ·
            refine ⟨5951333119152429296623709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3967555412768286197749139 5951333119152429296623709)
            ·
              refine ⟨2231749919682160986233891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5951333119152429296623709 2231749919682160986233891)
              ·
                refine ⟨3347624879523241479350837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2231749919682160986233891 3347624879523241479350837)
                ·
                  refine ⟨313839832455303888689141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3347624879523241479350837 313839832455303888689141)
                  ·
                    rfl

theorem cell21_1375202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_1375202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1375202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1375202 prefixEnd_1375202 := by exact prefixLift 1375202
  have htrace : WordTrace (prefixWord ++ tailWord_1375202) baseStart_1375202 baseEnd_1375202 := by
    simpa [prefixWord, tailWord_1375202, baseEnd_1375202] using wordTrace_append hprefix tailTrace_1375202
  have hstable : (prefixWord ++ tailWord_1375202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375202).length < 2 ^ (prefixWord ++ tailWord_1375202).sum := by decide
  have hdescent : baseEnd_1375202 < baseStart_1375202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375227 : List Nat := [1, 1, 1, 1, 1, 3, 3, 3, 7]
def baseStart_1375227 : Nat := 118140960795 + 1375227 * 2 ^ 59
def prefixEnd_1375227 : Nat := 4983230072969 + 3 ^ 40 * 1375227 * 2
def baseEnd_1375227 : Nat := 313845537795909400772423

theorem tailTrace_1375227 : CollatzResearch.WordTrace tailWord_1375227 prefixEnd_1375227 313845537795909400772423 := by
  unfold tailWord_1375227
  simp only [CollatzResearch.WordTrace]
  refine ⟨50158649388794923917747935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33439099592529949278498623 50158649388794923917747935)
  ·
    refine ⟨75237974083192385876621903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50158649388794923917747935 75237974083192385876621903)
    ·
      refine ⟨112856961124788578814932855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75237974083192385876621903 112856961124788578814932855)
      ·
        refine ⟨169285441687182868222399283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112856961124788578814932855 169285441687182868222399283)
        ·
          refine ⟨253928162530774302333598925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169285441687182868222399283 253928162530774302333598925)
          ·
            refine ⟨95223060949040363375099597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 253928162530774302333598925 95223060949040363375099597)
            ·
              refine ⟨35708647855890136265662349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95223060949040363375099597 35708647855890136265662349)
              ·
                refine ⟨13390742945958801099623381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35708647855890136265662349 13390742945958801099623381)
                ·
                  refine ⟨313845537795909400772423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13390742945958801099623381 313845537795909400772423)
                  ·
                    rfl

theorem cell21_1375227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 7].length) (baseStart_1375227 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1375227 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1375227 prefixEnd_1375227 := by exact prefixLift 1375227
  have htrace : WordTrace (prefixWord ++ tailWord_1375227) baseStart_1375227 baseEnd_1375227 := by
    simpa [prefixWord, tailWord_1375227, baseEnd_1375227] using wordTrace_append hprefix tailTrace_1375227
  have hstable : (prefixWord ++ tailWord_1375227).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375227).length < 2 ^ (prefixWord ++ tailWord_1375227).sum := by decide
  have hdescent : baseEnd_1375227 < baseStart_1375227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375264 : List Nat := [2, 1, 1, 7, 2, 1, 1, 6]
def baseStart_1375264 : Nat := 118140960795 + 1375264 * 2 ^ 59
def prefixEnd_1375264 : Nat := 4983230072969 + 3 ^ 40 * 1375264 * 2
def baseEnd_1375264 : Nat := 104617993900001852885227

theorem tailTrace_1375264 : CollatzResearch.WordTrace tailWord_1375264 prefixEnd_1375264 104617993900001852885227 := by
  unfold tailWord_1375264
  simp only [CollatzResearch.WordTrace]
  refine ⟨25079999444830439618422423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33439999259773919491229897 25079999444830439618422423)
  ·
    refine ⟨37619999167245659427633635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25079999444830439618422423 37619999167245659427633635)
    ·
      refine ⟨56429998750868489141450453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37619999167245659427633635 56429998750868489141450453)
      ·
        refine ⟨1322578095723480214252745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 56429998750868489141450453 1322578095723480214252745)
        ·
          refine ⟨991933571792610160689559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1322578095723480214252745 991933571792610160689559)
          ·
            refine ⟨1487900357688915241034339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 991933571792610160689559 1487900357688915241034339)
            ·
              refine ⟨2231850536533372861551509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1487900357688915241034339 2231850536533372861551509)
              ·
                refine ⟨104617993900001852885227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2231850536533372861551509 104617993900001852885227)
                ·
                  rfl

theorem cell21_1375264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 6].length) (baseStart_1375264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1375264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1375264 prefixEnd_1375264 := by exact prefixLift 1375264
  have htrace : WordTrace (prefixWord ++ tailWord_1375264) baseStart_1375264 baseEnd_1375264 := by
    simpa [prefixWord, tailWord_1375264, baseEnd_1375264] using wordTrace_append hprefix tailTrace_1375264
  have hstable : (prefixWord ++ tailWord_1375264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375264).length < 2 ^ (prefixWord ++ tailWord_1375264).sum := by decide
  have hdescent : baseEnd_1375264 < baseStart_1375264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375309 : List Nat := [1, 6, 1, 1, 1, 4, 1, 2, 4]
def baseStart_1375309 : Nat := 118140960795 + 1375309 * 2 ^ 59
def prefixEnd_1375309 : Nat := 4983230072969 + 3 ^ 40 * 1375309 * 2
def baseEnd_1375309 : Nat := 313864251313095480405589

theorem tailTrace_1375309 : CollatzResearch.WordTrace tailWord_1375309 prefixEnd_1375309 313864251313095480405589 := by
  unfold tailWord_1375309
  simp only [CollatzResearch.WordTrace]
  refine ⟨50161640174497851922232981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33441093449665234614821987 50161640174497851922232981)
  ·
    refine ⟨2351326883179586808854671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 50161640174497851922232981 2351326883179586808854671)
    ·
      refine ⟨3526990324769380213282007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2351326883179586808854671 3526990324769380213282007)
      ·
        refine ⟨5290485487154070319923011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3526990324769380213282007 5290485487154070319923011)
        ·
          refine ⟨7935728230731105479884517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5290485487154070319923011 7935728230731105479884517)
          ·
            refine ⟨1487949043262082277478347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7935728230731105479884517 1487949043262082277478347)
            ·
              refine ⟨2231923564893123416217521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1487949043262082277478347 2231923564893123416217521)
              ·
                refine ⟨1673942673669842562163141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2231923564893123416217521 1673942673669842562163141)
                ·
                  refine ⟨313864251313095480405589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1673942673669842562163141 313864251313095480405589)
                  ·
                    rfl

theorem cell21_1375309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_1375309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1375309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1375309 prefixEnd_1375309 := by exact prefixLift 1375309
  have htrace : WordTrace (prefixWord ++ tailWord_1375309) baseStart_1375309 baseEnd_1375309 := by
    simpa [prefixWord, tailWord_1375309, baseEnd_1375309] using wordTrace_append hprefix tailTrace_1375309
  have hstable : (prefixWord ++ tailWord_1375309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375309).length < 2 ^ (prefixWord ++ tailWord_1375309).sum := by decide
  have hdescent : baseEnd_1375309 < baseStart_1375309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375320 : List Nat := [2, 1, 2, 2, 1, 3, 4, 1, 5]
def baseStart_1375320 : Nat := 118140960795 + 1375320 * 2 ^ 59
def prefixEnd_1375320 : Nat := 4983230072969 + 3 ^ 40 * 1375320 * 2
def baseEnd_1375320 : Nat := 313866761662961905722233

theorem tailTrace_1375320 : CollatzResearch.WordTrace tailWord_1375320 prefixEnd_1375320 313866761662961905722233 := by
  unfold tailWord_1375320
  simp only [CollatzResearch.WordTrace]
  refine ⟨25081020688729000400441707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33441360918305333867255609 25081020688729000400441707)
  ·
    refine ⟨37621531033093500600662561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25081020688729000400441707 37621531033093500600662561)
    ·
      refine ⟨28216148274820125450496921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37621531033093500600662561 28216148274820125450496921)
      ·
        refine ⟨21162111206115094087872691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28216148274820125450496921 21162111206115094087872691)
        ·
          refine ⟨31743166809172641131809037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21162111206115094087872691 31743166809172641131809037)
          ·
            refine ⟨11903687553439740424428389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31743166809172641131809037 11903687553439740424428389)
            ·
              refine ⟨2231941416269951329580323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11903687553439740424428389 2231941416269951329580323)
              ·
                refine ⟨3347912124404926994370485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2231941416269951329580323 3347912124404926994370485)
                ·
                  refine ⟨313866761662961905722233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3347912124404926994370485 313866761662961905722233)
                  ·
                    rfl

theorem cell21_1375320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 5].length) (baseStart_1375320 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1375320 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1375320 prefixEnd_1375320 := by exact prefixLift 1375320
  have htrace : WordTrace (prefixWord ++ tailWord_1375320) baseStart_1375320 baseEnd_1375320 := by
    simpa [prefixWord, tailWord_1375320, baseEnd_1375320] using wordTrace_append hprefix tailTrace_1375320
  have hstable : (prefixWord ++ tailWord_1375320).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375320).length < 2 ^ (prefixWord ++ tailWord_1375320).sum := by decide
  have hdescent : baseEnd_1375320 < baseStart_1375320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375424 : List Nat := [2, 1, 1, 2, 15]
def baseStart_1375424 : Nat := 118140960795 + 1375424 * 2 ^ 59
def prefixEnd_1375424 : Nat := 4983230072969 + 3 ^ 40 * 1375424 * 2
def baseEnd_1375424 : Nat := 3875191307159022666527

theorem tailTrace_1375424 : CollatzResearch.WordTrace tailWord_1375424 prefixEnd_1375424 3875191307159022666527 := by
  unfold tailWord_1375424
  simp only [CollatzResearch.WordTrace]
  refine ⟨25082917284540613281334663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33443889712720817708446217 25082917284540613281334663)
  ·
    refine ⟨37624375926810919922001995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25082917284540613281334663 37624375926810919922001995)
    ·
      refine ⟨56436563890216379883002993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37624375926810919922001995 56436563890216379883002993)
      ·
        refine ⟨42327422917662284912252245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56436563890216379883002993 42327422917662284912252245)
        ·
          refine ⟨3875191307159022666527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 42327422917662284912252245 3875191307159022666527)
          ·
            rfl

theorem cell21_1375424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 15].length) (baseStart_1375424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1375424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1375424 prefixEnd_1375424 := by exact prefixLift 1375424
  have htrace : WordTrace (prefixWord ++ tailWord_1375424) baseStart_1375424 baseEnd_1375424 := by
    simpa [prefixWord, tailWord_1375424, baseEnd_1375424] using wordTrace_append hprefix tailTrace_1375424
  have hstable : (prefixWord ++ tailWord_1375424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375424).length < 2 ^ (prefixWord ++ tailWord_1375424).sum := by decide
  have hdescent : baseEnd_1375424 < baseStart_1375424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375455 : List Nat := [1, 1, 2, 3, 2, 1, 3, 1, 7]
def baseStart_1375455 : Nat := 118140960795 + 1375455 * 2 ^ 59
def prefixEnd_1375455 : Nat := 4983230072969 + 3 ^ 40 * 1375455 * 2
def baseEnd_1375455 : Nat := 313897570502231670971957

theorem tailTrace_1375455 : CollatzResearch.WordTrace tailWord_1375455 prefixEnd_1375455 313897570502231670971957 := by
  unfold tailWord_1375455
  simp only [CollatzResearch.WordTrace]
  refine ⟨50166965231968918857047819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33444643487979279238031879 50166965231968918857047819)
  ·
    refine ⟨75250447847953378285571729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50166965231968918857047819 75250447847953378285571729)
    ·
      refine ⟨56437835885965033714178797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75250447847953378285571729 56437835885965033714178797)
      ·
        refine ⟨21164188457236887642817049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56437835885965033714178797 21164188457236887642817049)
        ·
          refine ⟨15873141342927665732112787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21164188457236887642817049 15873141342927665732112787)
          ·
            refine ⟨23809712014391498598169181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15873141342927665732112787 23809712014391498598169181)
            ·
              refine ⟨8928642005396811974313443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23809712014391498598169181 8928642005396811974313443)
              ·
                refine ⟨13392963008095217961470165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8928642005396811974313443 13392963008095217961470165)
                ·
                  refine ⟨313897570502231670971957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13392963008095217961470165 313897570502231670971957)
                  ·
                    rfl

theorem cell21_1375455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 7].length) (baseStart_1375455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1375455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1375455 prefixEnd_1375455 := by exact prefixLift 1375455
  have htrace : WordTrace (prefixWord ++ tailWord_1375455) baseStart_1375455 baseEnd_1375455 := by
    simpa [prefixWord, tailWord_1375455, baseEnd_1375455] using wordTrace_append hprefix tailTrace_1375455
  have hstable : (prefixWord ++ tailWord_1375455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375455).length < 2 ^ (prefixWord ++ tailWord_1375455).sum := by decide
  have hdescent : baseEnd_1375455 < baseStart_1375455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375489 : List Nat := [1, 2, 4, 1, 1, 3, 2, 4, 3]
def baseStart_1375489 : Nat := 118140960795 + 1375489 * 2 ^ 59
def prefixEnd_1375489 : Nat := 4983230072969 + 3 ^ 40 * 1375489 * 2
def baseEnd_1375489 : Nat := 313905329765455167405221

theorem tailTrace_1375489 : CollatzResearch.WordTrace tailWord_1375489 prefixEnd_1375489 313905329765455167405221 := by
  unfold tailWord_1375489
  simp only [CollatzResearch.WordTrace]
  refine ⟨50168205313845742663785521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33445470209230495109190347 50168205313845742663785521)
  ·
    refine ⟨37626153985384306997839141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50168205313845742663785521 37626153985384306997839141)
    ·
      refine ⟨7054903872259557562094839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37626153985384306997839141 7054903872259557562094839)
      ·
        refine ⟨10582355808389336343142259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7054903872259557562094839 10582355808389336343142259)
        ·
          refine ⟨15873533712584004514713389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10582355808389336343142259 15873533712584004514713389)
          ·
            refine ⟨5952575142219001693017521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15873533712584004514713389 5952575142219001693017521)
            ·
              refine ⟨4464431356664251269763141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5952575142219001693017521 4464431356664251269763141)
              ·
                refine ⟨837080879374547113080589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4464431356664251269763141 837080879374547113080589)
                ·
                  refine ⟨313905329765455167405221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 837080879374547113080589 313905329765455167405221)
                  ·
                    rfl

theorem cell21_1375489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 4, 3].length) (baseStart_1375489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1375489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1375489 prefixEnd_1375489 := by exact prefixLift 1375489
  have htrace : WordTrace (prefixWord ++ tailWord_1375489) baseStart_1375489 baseEnd_1375489 := by
    simpa [prefixWord, tailWord_1375489, baseEnd_1375489] using wordTrace_append hprefix tailTrace_1375489
  have hstable : (prefixWord ++ tailWord_1375489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375489).length < 2 ^ (prefixWord ++ tailWord_1375489).sum := by decide
  have hdescent : baseEnd_1375489 < baseStart_1375489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375548 : List Nat := [2, 2, 2, 2, 1, 3, 3, 1, 5]
def baseStart_1375548 : Nat := 118140960795 + 1375548 * 2 ^ 59
def prefixEnd_1375548 : Nat := 4983230072969 + 3 ^ 40 * 1375548 * 2
def baseEnd_1375548 : Nat := 313918794369284175921767

theorem tailTrace_1375548 : CollatzResearch.WordTrace tailWord_1375548 prefixEnd_1375548 313918794369284175921767 := by
  unfold tailWord_1375548
  simp only [CollatzResearch.WordTrace]
  refine ⟨25085178610315997870091649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33446904813754663826788865 25085178610315997870091649)
  ·
    refine ⟨18813883957736998402568737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25085178610315997870091649 18813883957736998402568737)
    ·
      refine ⟨14110412968302748801926553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18813883957736998402568737 14110412968302748801926553)
      ·
        refine ⟨10582809726227061601444915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14110412968302748801926553 10582809726227061601444915)
        ·
          refine ⟨15874214589340592402167373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10582809726227061601444915 15874214589340592402167373)
          ·
            refine ⟨5952830471002722150812765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15874214589340592402167373 5952830471002722150812765)
            ·
              refine ⟨2232311426626020806554787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5952830471002722150812765 2232311426626020806554787)
              ·
                refine ⟨3348467139939031209832181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2232311426626020806554787 3348467139939031209832181)
                ·
                  refine ⟨313918794369284175921767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3348467139939031209832181 313918794369284175921767)
                  ·
                    rfl

theorem cell21_1375548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 5].length) (baseStart_1375548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1375548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1375548 prefixEnd_1375548 := by exact prefixLift 1375548
  have htrace : WordTrace (prefixWord ++ tailWord_1375548) baseStart_1375548 baseEnd_1375548 := by
    simpa [prefixWord, tailWord_1375548, baseEnd_1375548] using wordTrace_append hprefix tailTrace_1375548
  have hstable : (prefixWord ++ tailWord_1375548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375548).length < 2 ^ (prefixWord ++ tailWord_1375548).sum := by decide
  have hdescent : baseEnd_1375548 < baseStart_1375548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375576 : List Nat := [2, 1, 2, 2, 1, 1, 3, 9]
def baseStart_1375576 : Nat := 118140960795 + 1375576 * 2 ^ 59
def prefixEnd_1375576 : Nat := 4983230072969 + 3 ^ 40 * 1375576 * 2
def baseEnd_1375576 : Nat := 104641728116920783151681

theorem tailTrace_1375576 : CollatzResearch.WordTrace tailWord_1375576 prefixEnd_1375576 104641728116920783151681 := by
  unfold tailWord_1375576
  simp only [CollatzResearch.WordTrace]
  refine ⟨25085689232265278261101291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33447585643020371014801721 25085689232265278261101291)
  ·
    refine ⟨37628533848397917391651937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25085689232265278261101291 37628533848397917391651937)
    ·
      refine ⟨28221400386298438043738953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37628533848397917391651937 28221400386298438043738953)
      ·
        refine ⟨21166050289723828532804215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28221400386298438043738953 21166050289723828532804215)
        ·
          refine ⟨31749075434585742799206323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21166050289723828532804215 31749075434585742799206323)
          ·
            refine ⟨47623613151878614198809485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31749075434585742799206323 47623613151878614198809485)
            ·
              refine ⟨17858854931954480324553557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47623613151878614198809485 17858854931954480324553557)
              ·
                refine ⟨104641728116920783151681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17858854931954480324553557 104641728116920783151681)
                ·
                  rfl

theorem cell21_1375576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 9].length) (baseStart_1375576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1375576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1375576 prefixEnd_1375576 := by exact prefixLift 1375576
  have htrace : WordTrace (prefixWord ++ tailWord_1375576) baseStart_1375576 baseEnd_1375576 := by
    simpa [prefixWord, tailWord_1375576, baseEnd_1375576] using wordTrace_append hprefix tailTrace_1375576
  have hstable : (prefixWord ++ tailWord_1375576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375576).length < 2 ^ (prefixWord ++ tailWord_1375576).sum := by decide
  have hdescent : baseEnd_1375576 < baseStart_1375576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375607 : List Nat := [1, 1, 3, 1, 1, 2, 4, 3, 5]
def baseStart_1375607 : Nat := 118140960795 + 1375607 * 2 ^ 59
def prefixEnd_1375607 : Nat := 4983230072969 + 3 ^ 40 * 1375607 * 2
def baseEnd_1375607 : Nat := 313932258973113184438313

theorem tailTrace_1375607 : CollatzResearch.WordTrace tailWord_1375607 prefixEnd_1375607 313932258973113184438313 := by
  unfold tailWord_1375607
  simp only [CollatzResearch.WordTrace]
  refine ⟨50172509127418248816581075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33448339418278832544387383 50172509127418248816581075)
  ·
    refine ⟨75258763691127373224871613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50172509127418248816581075 75258763691127373224871613)
    ·
      refine ⟨28222036384172764959326855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75258763691127373224871613 28222036384172764959326855)
      ·
        refine ⟨42333054576259147438990283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28222036384172764959326855 42333054576259147438990283)
        ·
          refine ⟨63499581864388721158485425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42333054576259147438990283 63499581864388721158485425)
          ·
            refine ⟨47624686398291540868864069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63499581864388721158485425 47624686398291540868864069)
            ·
              refine ⟨8929628699679663912912013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47624686398291540868864069 8929628699679663912912013)
              ·
                refine ⟨3348610762379873967342005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8929628699679663912912013 3348610762379873967342005)
                ·
                  refine ⟨313932258973113184438313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3348610762379873967342005 313932258973113184438313)
                  ·
                    rfl

theorem cell21_1375607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 5].length) (baseStart_1375607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1375607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1375607 prefixEnd_1375607 := by exact prefixLift 1375607
  have htrace : WordTrace (prefixWord ++ tailWord_1375607) baseStart_1375607 baseEnd_1375607 := by
    simpa [prefixWord, tailWord_1375607, baseEnd_1375607] using wordTrace_append hprefix tailTrace_1375607
  have hstable : (prefixWord ++ tailWord_1375607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375607).length < 2 ^ (prefixWord ++ tailWord_1375607).sum := by decide
  have hdescent : baseEnd_1375607 < baseStart_1375607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375624 : List Nat := [2, 1, 3, 3, 1, 3, 1, 2, 5]
def baseStart_1375624 : Nat := 118140960795 + 1375624 * 2 ^ 59
def prefixEnd_1375624 : Nat := 4983230072969 + 3 ^ 40 * 1375624 * 2
def baseEnd_1375624 : Nat := 313936138604724932654945

theorem tailTrace_1375624 : CollatzResearch.WordTrace tailWord_1375624 prefixEnd_1375624 313936138604724932654945 := by
  unfold tailWord_1375624
  simp only [CollatzResearch.WordTrace]
  refine ⟨25086564584178330359974963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33448752778904440479966617 25086564584178330359974963)
  ·
    refine ⟨37629846876267495539962445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25086564584178330359974963 37629846876267495539962445)
    ·
      refine ⟨14111192578600310827485917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37629846876267495539962445 14111192578600310827485917)
      ·
        refine ⟨5291697216975116560307219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14111192578600310827485917 5291697216975116560307219)
        ·
          refine ⟨7937545825462674840460829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5291697216975116560307219 7937545825462674840460829)
          ·
            refine ⟨2976579684548503065172811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7937545825462674840460829 2976579684548503065172811)
            ·
              refine ⟨4464869526822754597759217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2976579684548503065172811 4464869526822754597759217)
              ·
                refine ⟨3348652145117065948319413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4464869526822754597759217 3348652145117065948319413)
                ·
                  refine ⟨313936138604724932654945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3348652145117065948319413 313936138604724932654945)
                  ·
                    rfl

theorem cell21_1375624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 5].length) (baseStart_1375624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1375624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1375624 prefixEnd_1375624 := by exact prefixLift 1375624
  have htrace : WordTrace (prefixWord ++ tailWord_1375624) baseStart_1375624 baseEnd_1375624 := by
    simpa [prefixWord, tailWord_1375624, baseEnd_1375624] using wordTrace_append hprefix tailTrace_1375624
  have hstable : (prefixWord ++ tailWord_1375624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375624).length < 2 ^ (prefixWord ++ tailWord_1375624).sum := by decide
  have hdescent : baseEnd_1375624 < baseStart_1375624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375641 : List Nat := [1, 2, 1, 2, 1, 6, 2, 3, 3]
def baseStart_1375641 : Nat := 118140960795 + 1375641 * 2 ^ 59
def prefixEnd_1375641 : Nat := 4983230072969 + 3 ^ 40 * 1375641 * 2
def baseEnd_1375641 : Nat := 313940018236336680871577

theorem tailTrace_1375641 : CollatzResearch.WordTrace tailWord_1375641 prefixEnd_1375641 313940018236336680871577 := by
  unfold tailWord_1375641
  simp only [CollatzResearch.WordTrace]
  refine ⟨50173749209295072623318777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33449166139530048415545851 50173749209295072623318777)
  ·
    refine ⟨37630311906971304467489083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50173749209295072623318777 37630311906971304467489083)
    ·
      refine ⟨56445467860456956701233625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37630311906971304467489083 56445467860456956701233625)
      ·
        refine ⟨42334100895342717525925219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56445467860456956701233625 42334100895342717525925219)
        ·
          refine ⟨63501151343014076288887829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42334100895342717525925219 63501151343014076288887829)
          ·
            refine ⟨2976616469203784826041617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 63501151343014076288887829 2976616469203784826041617)
            ·
              refine ⟨2232462351902838619531213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2976616469203784826041617 2232462351902838619531213)
              ·
                refine ⟨837173381963564482324205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2232462351902838619531213 837173381963564482324205)
                ·
                  refine ⟨313940018236336680871577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 837173381963564482324205 313940018236336680871577)
                  ·
                    rfl

theorem cell21_1375641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 3, 3].length) (baseStart_1375641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1375641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1375641 prefixEnd_1375641 := by exact prefixLift 1375641
  have htrace : WordTrace (prefixWord ++ tailWord_1375641) baseStart_1375641 baseEnd_1375641 := by
    simpa [prefixWord, tailWord_1375641, baseEnd_1375641] using wordTrace_append hprefix tailTrace_1375641
  have hstable : (prefixWord ++ tailWord_1375641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375641).length < 2 ^ (prefixWord ++ tailWord_1375641).sum := by decide
  have hdescent : baseEnd_1375641 < baseStart_1375641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375683 : List Nat := [1, 1, 1, 3, 1, 1, 6, 2, 5]
def baseStart_1375683 : Nat := 118140960795 + 1375683 * 2 ^ 59
def prefixEnd_1375683 : Nat := 4983230072969 + 3 ^ 40 * 1375683 * 2
def baseEnd_1375683 : Nat := 313949603208553941171491

theorem tailTrace_1375683 : CollatzResearch.WordTrace tailWord_1375683 prefixEnd_1375683 313949603208553941171491 := by
  unfold tailWord_1375683
  simp only [CollatzResearch.WordTrace]
  refine ⟨50175281075142913796347703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33450187383428609197565135 50175281075142913796347703)
  ·
    refine ⟨75262921612714370694521555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50175281075142913796347703 75262921612714370694521555)
    ·
      refine ⟨112894382419071556041782333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75262921612714370694521555 112894382419071556041782333)
      ·
        refine ⟨42335393407151833515668375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112894382419071556041782333 42335393407151833515668375)
        ·
          refine ⟨63503090110727750273502563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42335393407151833515668375 63503090110727750273502563)
          ·
            refine ⟨95254635166091625410253845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63503090110727750273502563 95254635166091625410253845)
            ·
              refine ⟨4465061023410544941105649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 95254635166091625410253845 4465061023410544941105649)
              ·
                refine ⟨3348795767557908705829237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4465061023410544941105649 3348795767557908705829237)
                ·
                  refine ⟨313949603208553941171491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3348795767557908705829237 313949603208553941171491)
                  ·
                    rfl

theorem cell21_1375683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 5].length) (baseStart_1375683 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1375683 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1375683 prefixEnd_1375683 := by exact prefixLift 1375683
  have htrace : WordTrace (prefixWord ++ tailWord_1375683) baseStart_1375683 baseEnd_1375683 := by
    simpa [prefixWord, tailWord_1375683, baseEnd_1375683] using wordTrace_append hprefix tailTrace_1375683
  have hstable : (prefixWord ++ tailWord_1375683).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375683).length < 2 ^ (prefixWord ++ tailWord_1375683).sum := by decide
  have hdescent : baseEnd_1375683 < baseStart_1375683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375717 : List Nat := [1, 3, 1, 5, 1, 3, 1, 1, 5]
def baseStart_1375717 : Nat := 118140960795 + 1375717 * 2 ^ 59
def prefixEnd_1375717 : Nat := 4983230072969 + 3 ^ 40 * 1375717 * 2
def baseEnd_1375717 : Nat := 313957362471777437604755

theorem tailTrace_1375717 : CollatzResearch.WordTrace tailWord_1375717 prefixEnd_1375717 313957362471777437604755 := by
  unfold tailWord_1375717
  simp only [CollatzResearch.WordTrace]
  refine ⟨50176521157019737603085405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33451014104679825068723603 50176521157019737603085405)
  ·
    refine ⟨18816195433882401601157027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50176521157019737603085405 18816195433882401601157027)
    ·
      refine ⟨28224293150823602401735541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18816195433882401601157027 28224293150823602401735541)
      ·
        refine ⟨2646027482889712725162707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28224293150823602401735541 2646027482889712725162707)
        ·
          refine ⟨3969041224334569087744061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2646027482889712725162707 3969041224334569087744061)
          ·
            refine ⟨1488390459125463407904023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3969041224334569087744061 1488390459125463407904023)
            ·
              refine ⟨2232585688688195111856035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1488390459125463407904023 2232585688688195111856035)
              ·
                refine ⟨3348878533032292667784053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2232585688688195111856035 3348878533032292667784053)
                ·
                  refine ⟨313957362471777437604755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3348878533032292667784053 313957362471777437604755)
                  ·
                    rfl

theorem cell21_1375717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 5].length) (baseStart_1375717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1375717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1375717 prefixEnd_1375717 := by exact prefixLift 1375717
  have htrace : WordTrace (prefixWord ++ tailWord_1375717) baseStart_1375717 baseEnd_1375717 := by
    simpa [prefixWord, tailWord_1375717, baseEnd_1375717] using wordTrace_append hprefix tailTrace_1375717
  have hstable : (prefixWord ++ tailWord_1375717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375717).length < 2 ^ (prefixWord ++ tailWord_1375717).sum := by decide
  have hdescent : baseEnd_1375717 < baseStart_1375717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375728 : List Nat := [2, 1, 1, 1, 3, 4, 1, 8]
def baseStart_1375728 : Nat := 118140960795 + 1375728 * 2 ^ 59
def prefixEnd_1375728 : Nat := 4983230072969 + 3 ^ 40 * 1375728 * 2
def baseEnd_1375728 : Nat := 104653290940547954307133

theorem tailTrace_1375728 : CollatzResearch.WordTrace tailWord_1375728 prefixEnd_1375728 104653290940547954307133 := by
  unfold tailWord_1375728
  simp only [CollatzResearch.WordTrace]
  refine ⟨25088461179989943240867919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33451281573319924321157225 25088461179989943240867919)
  ·
    refine ⟨37632691769984914861301879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25088461179989943240867919 37632691769984914861301879)
    ·
      refine ⟨56449037654977372291952819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37632691769984914861301879 56449037654977372291952819)
      ·
        refine ⟨84673556482466058437929229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56449037654977372291952819 84673556482466058437929229)
        ·
          refine ⟨31752583680924771914223461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84673556482466058437929229 31752583680924771914223461)
          ·
            refine ⟨5953609440173394733916899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31752583680924771914223461 5953609440173394733916899)
            ·
              refine ⟨8930414160260092100875349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5953609440173394733916899 8930414160260092100875349)
              ·
                refine ⟨104653290940547954307133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8930414160260092100875349 104653290940547954307133)
                ·
                  rfl

theorem cell21_1375728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 8].length) (baseStart_1375728 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1375728 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1375728 prefixEnd_1375728 := by exact prefixLift 1375728
  have htrace : WordTrace (prefixWord ++ tailWord_1375728) baseStart_1375728 baseEnd_1375728 := by
    simpa [prefixWord, tailWord_1375728, baseEnd_1375728] using wordTrace_append hprefix tailTrace_1375728
  have hstable : (prefixWord ++ tailWord_1375728).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375728).length < 2 ^ (prefixWord ++ tailWord_1375728).sum := by decide
  have hdescent : baseEnd_1375728 < baseStart_1375728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375869 : List Nat := [1, 4, 1, 1, 4, 1, 3, 3, 3]
def baseStart_1375869 : Nat := 118140960795 + 1375869 * 2 ^ 59
def prefixEnd_1375869 : Nat := 4983230072969 + 3 ^ 40 * 1375869 * 2
def baseEnd_1375869 : Nat := 313992050942658951071111

theorem tailTrace_1375869 : CollatzResearch.WordTrace tailWord_1375869 prefixEnd_1375869 313992050942658951071111 := by
  unfold tailWord_1375869
  simp only [CollatzResearch.WordTrace]
  refine ⟨50182065052469067562618661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33454710034979378375079107 50182065052469067562618661)
  ·
    refine ⟨9409137197337950167990999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50182065052469067562618661 9409137197337950167990999)
    ·
      refine ⟨14113705796006925251986499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9409137197337950167990999 14113705796006925251986499)
      ·
        refine ⟨21170558694010387877979749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14113705796006925251986499 21170558694010387877979749)
        ·
          refine ⟨3969479755126947727121203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21170558694010387877979749 3969479755126947727121203)
          ·
            refine ⟨5954219632690421590681805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3969479755126947727121203 5954219632690421590681805)
            ·
              refine ⟨2232832362258908096505677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5954219632690421590681805 2232832362258908096505677)
              ·
                refine ⟨837312135847090536189629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2232832362258908096505677 837312135847090536189629)
                ·
                  refine ⟨313992050942658951071111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 837312135847090536189629 313992050942658951071111)
                  ·
                    rfl

theorem cell21_1375869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 3, 3].length) (baseStart_1375869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1375869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1375869 prefixEnd_1375869 := by exact prefixLift 1375869
  have htrace : WordTrace (prefixWord ++ tailWord_1375869) baseStart_1375869 baseEnd_1375869 := by
    simpa [prefixWord, tailWord_1375869, baseEnd_1375869] using wordTrace_append hprefix tailTrace_1375869
  have hstable : (prefixWord ++ tailWord_1375869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375869).length < 2 ^ (prefixWord ++ tailWord_1375869).sum := by decide
  have hdescent : baseEnd_1375869 < baseStart_1375869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375886 : List Nat := [4, 1, 1, 3, 1, 3, 3, 2, 3]
def baseStart_1375886 : Nat := 118140960795 + 1375886 * 2 ^ 59
def prefixEnd_1375886 : Nat := 4983230072969 + 3 ^ 40 * 1375886 * 2
def baseEnd_1375886 : Nat := 313995930574270699287743

theorem tailTrace_1375886 : CollatzResearch.WordTrace tailWord_1375886 prefixEnd_1375886 313995930574270699287743 := by
  unfold tailWord_1375886
  simp only [CollatzResearch.WordTrace]
  refine ⟨6272835636675934933248439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33455123395604986310658341 6272835636675934933248439)
  ·
    refine ⟨9409253455013902399872659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6272835636675934933248439 9409253455013902399872659)
    ·
      refine ⟨14113880182520853599808989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9409253455013902399872659 14113880182520853599808989)
      ·
        refine ⟨5292705068445320099928371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14113880182520853599808989 5292705068445320099928371)
        ·
          refine ⟨7939057602667980149892557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5292705068445320099928371 7939057602667980149892557)
          ·
            refine ⟨2977146601000492556209709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7939057602667980149892557 2977146601000492556209709)
            ·
              refine ⟨1116429975375184708578641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2977146601000492556209709 1116429975375184708578641)
              ·
                refine ⟨837322481531388531433981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1116429975375184708578641 837322481531388531433981)
                ·
                  refine ⟨313995930574270699287743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 837322481531388531433981 313995930574270699287743)
                  ·
                    rfl

theorem cell21_1375886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 2, 3].length) (baseStart_1375886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1375886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1375886 prefixEnd_1375886 := by exact prefixLift 1375886
  have htrace : WordTrace (prefixWord ++ tailWord_1375886) baseStart_1375886 baseEnd_1375886 := by
    simpa [prefixWord, tailWord_1375886, baseEnd_1375886] using wordTrace_append hprefix tailTrace_1375886
  have hstable : (prefixWord ++ tailWord_1375886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375886).length < 2 ^ (prefixWord ++ tailWord_1375886).sum := by decide
  have hdescent : baseEnd_1375886 < baseStart_1375886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375973 : List Nat := [1, 3, 1, 4, 1, 1, 5, 5]
def baseStart_1375973 : Nat := 118140960795 + 1375973 * 2 ^ 59
def prefixEnd_1375973 : Nat := 4983230072969 + 3 ^ 40 * 1375973 * 2
def baseEnd_1375973 : Nat := 104671928386525960445855

theorem tailTrace_1375973 : CollatzResearch.WordTrace tailWord_1375973 prefixEnd_1375973 104671928386525960445855 := by
  unfold tailWord_1375973
  simp only [CollatzResearch.WordTrace]
  refine ⟨50185858244092293324404573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33457238829394862216269715 50185858244092293324404573)
  ·
    refine ⟨18819696841534609996651715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50185858244092293324404573 18819696841534609996651715)
    ·
      refine ⟨28229545262301914994977573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18819696841534609996651715 28229545262301914994977573)
      ·
        refine ⟨5293039736681609061558295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28229545262301914994977573 5293039736681609061558295)
        ·
          refine ⟨7939559605022413592337443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5293039736681609061558295 7939559605022413592337443)
          ·
            refine ⟨11909339407533620388506165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7939559605022413592337443 11909339407533620388506165)
            ·
              refine ⟨1116500569456276911422453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11909339407533620388506165 1116500569456276911422453)
              ·
                refine ⟨104671928386525960445855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1116500569456276911422453 104671928386525960445855)
                ·
                  rfl

theorem cell21_1375973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 5].length) (baseStart_1375973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1375973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1375973 prefixEnd_1375973 := by exact prefixLift 1375973
  have htrace : WordTrace (prefixWord ++ tailWord_1375973) baseStart_1375973 baseEnd_1375973 := by
    simpa [prefixWord, tailWord_1375973, baseEnd_1375973] using wordTrace_append hprefix tailTrace_1375973
  have hstable : (prefixWord ++ tailWord_1375973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375973).length < 2 ^ (prefixWord ++ tailWord_1375973).sum := by decide
  have hdescent : baseEnd_1375973 < baseStart_1375973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376004 : List Nat := [2, 3, 2, 2, 1, 3, 2, 1, 5]
def baseStart_1376004 : Nat := 118140960795 + 1376004 * 2 ^ 59
def prefixEnd_1376004 : Nat := 4983230072969 + 3 ^ 40 * 1376004 * 2
def baseEnd_1376004 : Nat := 314022859781928716320835

theorem tailTrace_1376004 : CollatzResearch.WordTrace tailWord_1376004 prefixEnd_1376004 314022859781928716320835 := by
  unfold tailWord_1376004
  simp only [CollatzResearch.WordTrace]
  refine ⟨25093494453489992809391533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33457992604653323745855377 25093494453489992809391533)
  ·
    refine ⟨9410060420058747303521825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25093494453489992809391533 9410060420058747303521825)
    ·
      refine ⟨7057545315044060477641369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9410060420058747303521825 7057545315044060477641369)
      ·
        refine ⟨5293158986283045358231027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7057545315044060477641369 5293158986283045358231027)
        ·
          refine ⟨7939738479424568037346541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5293158986283045358231027 7939738479424568037346541)
          ·
            refine ⟨2977401929784213014004953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7939738479424568037346541 2977401929784213014004953)
            ·
              refine ⟨2233051447338159760503715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2977401929784213014004953 2233051447338159760503715)
              ·
                refine ⟨3349577171007239640755573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2233051447338159760503715 3349577171007239640755573)
                ·
                  refine ⟨314022859781928716320835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3349577171007239640755573 314022859781928716320835)
                  ·
                    rfl

theorem cell21_1376004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_1376004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1376004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1376004 prefixEnd_1376004 := by exact prefixLift 1376004
  have htrace : WordTrace (prefixWord ++ tailWord_1376004) baseStart_1376004 baseEnd_1376004 := by
    simpa [prefixWord, tailWord_1376004, baseEnd_1376004] using wordTrace_append hprefix tailTrace_1376004
  have hstable : (prefixWord ++ tailWord_1376004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376004).length < 2 ^ (prefixWord ++ tailWord_1376004).sum := by decide
  have hdescent : baseEnd_1376004 < baseStart_1376004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376032 : List Nat := [2, 1, 1, 5, 1, 1, 3, 7]
def baseStart_1376032 : Nat := 118140960795 + 1376032 * 2 ^ 59
def prefixEnd_1376032 : Nat := 4983230072969 + 3 ^ 40 * 1376032 * 2
def baseEnd_1376032 : Nat := 104676416587802296618037

theorem tailTrace_1376032 : CollatzResearch.WordTrace tailWord_1376032 prefixEnd_1376032 104676416587802296618037 := by
  unfold tailWord_1376032
  simp only [CollatzResearch.WordTrace]
  refine ⟨25094005075439273200401175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33458673433919030933868233 25094005075439273200401175)
  ·
    refine ⟨37641007613158909800601763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25094005075439273200401175 37641007613158909800601763)
    ·
      refine ⟨56461511419738364700902645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37641007613158909800601763 56461511419738364700902645)
      ·
        refine ⟨5293266695600471690709623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56461511419738364700902645 5293266695600471690709623)
        ·
          refine ⟨7939900043400707536064435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5293266695600471690709623 7939900043400707536064435)
          ·
            refine ⟨11909850065101061304096653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7939900043400707536064435 11909850065101061304096653)
            ·
              refine ⟨4466193774412897989036245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11909850065101061304096653 4466193774412897989036245)
              ·
                refine ⟨104676416587802296618037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4466193774412897989036245 104676416587802296618037)
                ·
                  rfl

theorem cell21_1376032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 7].length) (baseStart_1376032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1376032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1376032 prefixEnd_1376032 := by exact prefixLift 1376032
  have htrace : WordTrace (prefixWord ++ tailWord_1376032) baseStart_1376032 baseEnd_1376032 := by
    simpa [prefixWord, tailWord_1376032, baseEnd_1376032] using wordTrace_append hprefix tailTrace_1376032
  have hstable : (prefixWord ++ tailWord_1376032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376032).length < 2 ^ (prefixWord ++ tailWord_1376032).sum := by decide
  have hdescent : baseEnd_1376032 < baseStart_1376032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376319 : List Nat := [1, 1, 2, 2, 3, 1, 2, 9]
def baseStart_1376319 : Nat := 118140960795 + 1376319 * 2 ^ 59
def prefixEnd_1376319 : Nat := 4983230072969 + 3 ^ 40 * 1376319 * 2
def baseEnd_1376319 : Nat := 104698249024519389523397

theorem tailTrace_1376319 : CollatzResearch.WordTrace tailWord_1376319 prefixEnd_1376319 104698249024519389523397 := by
  unfold tailWord_1376319
  simp only [CollatzResearch.WordTrace]
  refine ⟨50198477900838794416500011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33465651933892529611000007 50198477900838794416500011)
  ·
    refine ⟨75297716851258191624750017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50198477900838794416500011 75297716851258191624750017)
    ·
      refine ⟨56473287638443643718562513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75297716851258191624750017 56473287638443643718562513)
      ·
        refine ⟨42354965728832732788921885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56473287638443643718562513 42354965728832732788921885)
        ·
          refine ⟨15883112148312274795845707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42354965728832732788921885 15883112148312274795845707)
          ·
            refine ⟨23824668222468412193768561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15883112148312274795845707 23824668222468412193768561)
            ·
              refine ⟨17868501166851309145326421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23824668222468412193768561 17868501166851309145326421)
              ·
                refine ⟨104698249024519389523397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17868501166851309145326421 104698249024519389523397)
                ·
                  rfl

theorem cell21_1376319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 9].length) (baseStart_1376319 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1376319 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1376319 prefixEnd_1376319 := by exact prefixLift 1376319
  have htrace : WordTrace (prefixWord ++ tailWord_1376319) baseStart_1376319 baseEnd_1376319 := by
    simpa [prefixWord, tailWord_1376319, baseEnd_1376319] using wordTrace_append hprefix tailTrace_1376319
  have hstable : (prefixWord ++ tailWord_1376319).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376319).length < 2 ^ (prefixWord ++ tailWord_1376319).sum := by decide
  have hdescent : baseEnd_1376319 < baseStart_1376319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376342 : List Nat := [5, 2, 2, 1, 1, 1, 2, 4, 3]
def baseStart_1376342 : Nat := 118140960795 + 1376342 * 2 ^ 59
def prefixEnd_1376342 : Nat := 4983230072969 + 3 ^ 40 * 1376342 * 2
def baseEnd_1376342 : Nat := 314099995986915239686811

theorem tailTrace_1376342 : CollatzResearch.WordTrace tailWord_1376342 prefixEnd_1376342 314099995986915239686811 := by
  unfold tailWord_1376342
  simp only [CollatzResearch.WordTrace]
  refine ⟨3137457298734716834036705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33466211186503646229724853 3137457298734716834036705)
  ·
    refine ⟨2353092974051037625527529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3137457298734716834036705 2353092974051037625527529)
    ·
      refine ⟨1764819730538278219145647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2353092974051037625527529 1764819730538278219145647)
      ·
        refine ⟨2647229595807417328718471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1764819730538278219145647 2647229595807417328718471)
        ·
          refine ⟨3970844393711125993077707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2647229595807417328718471 3970844393711125993077707)
          ·
            refine ⟨5956266590566688989616561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3970844393711125993077707 5956266590566688989616561)
            ·
              refine ⟨4467199942925016742212421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5956266590566688989616561 4467199942925016742212421)
              ·
                refine ⟨837599989298440639164829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4467199942925016742212421 837599989298440639164829)
                ·
                  refine ⟨314099995986915239686811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 837599989298440639164829 314099995986915239686811)
                  ·
                    rfl

theorem cell21_1376342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_1376342 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1376342 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1376342 prefixEnd_1376342 := by exact prefixLift 1376342
  have htrace : WordTrace (prefixWord ++ tailWord_1376342) baseStart_1376342 baseEnd_1376342 := by
    simpa [prefixWord, tailWord_1376342, baseEnd_1376342] using wordTrace_append hprefix tailTrace_1376342
  have hstable : (prefixWord ++ tailWord_1376342).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376342).length < 2 ^ (prefixWord ++ tailWord_1376342).sum := by decide
  have hdescent : baseEnd_1376342 < baseStart_1376342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376381 : List Nat := [1, 4, 1, 1, 3, 2, 1, 2, 6]
def baseStart_1376381 : Nat := 118140960795 + 1376381 * 2 ^ 59
def prefixEnd_1376381 : Nat := 4983230072969 + 3 ^ 40 * 1376381 * 2
def baseEnd_1376381 : Nat := 314108896318259838536731

theorem tailTrace_1376381 : CollatzResearch.WordTrace tailWord_1376381 prefixEnd_1376381 314108896318259838536731 := by
  unfold tailWord_1376381
  simp only [CollatzResearch.WordTrace]
  refine ⟨50200739226614179005256997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33467159484409452670171331 50200739226614179005256997)
  ·
    refine ⟨9412638604990158563485687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50200739226614179005256997 9412638604990158563485687)
    ·
      refine ⟨14118957907485237845228531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9412638604990158563485687 14118957907485237845228531)
      ·
        refine ⟨21178436861227856767842797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14118957907485237845228531 21178436861227856767842797)
        ·
          refine ⟨7941913822960446287941049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21178436861227856767842797 7941913822960446287941049)
          ·
            refine ⟨5956435367220334715955787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7941913822960446287941049 5956435367220334715955787)
            ·
              refine ⟨8934653050830502073933681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5956435367220334715955787 8934653050830502073933681)
              ·
                refine ⟨6700989788122876555450261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8934653050830502073933681 6700989788122876555450261)
                ·
                  refine ⟨314108896318259838536731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6700989788122876555450261 314108896318259838536731)
                  ·
                    rfl

theorem cell21_1376381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_1376381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1376381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1376381 prefixEnd_1376381 := by exact prefixLift 1376381
  have htrace : WordTrace (prefixWord ++ tailWord_1376381) baseStart_1376381 baseEnd_1376381 := by
    simpa [prefixWord, tailWord_1376381, baseEnd_1376381] using wordTrace_append hprefix tailTrace_1376381
  have hstable : (prefixWord ++ tailWord_1376381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376381).length < 2 ^ (prefixWord ++ tailWord_1376381).sum := by decide
  have hdescent : baseEnd_1376381 < baseStart_1376381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376412 : List Nat := [2, 2, 3, 2, 1, 1, 4, 6]
def baseStart_1376412 : Nat := 118140960795 + 1376412 * 2 ^ 59
def prefixEnd_1376412 : Nat := 4983230072969 + 3 ^ 40 * 1376412 * 2
def baseEnd_1376412 : Nat := 104705323646870224506667

theorem tailTrace_1376412 : CollatzResearch.WordTrace tailWord_1376412 prefixEnd_1376412 104705323646870224506667 := by
  unfold tailWord_1376412
  simp only [CollatzResearch.WordTrace]
  refine ⟨25100934944750935649817745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33467913259667914199756993 25100934944750935649817745)
  ·
    refine ⟨18825701208563201737363309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25100934944750935649817745 18825701208563201737363309)
    ·
      refine ⟨7059637953211200651511241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18825701208563201737363309 7059637953211200651511241)
      ·
        refine ⟨5294728464908400488633431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7059637953211200651511241 5294728464908400488633431)
        ·
          refine ⟨7942092697362600732950147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5294728464908400488633431 7942092697362600732950147)
          ·
            refine ⟨11913139046043901099425221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7942092697362600732950147 11913139046043901099425221)
            ·
              refine ⟨2233713571133231456142229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11913139046043901099425221 2233713571133231456142229)
              ·
                refine ⟨104705323646870224506667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2233713571133231456142229 104705323646870224506667)
                ·
                  rfl

theorem cell21_1376412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 6].length) (baseStart_1376412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1376412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1376412 prefixEnd_1376412 := by exact prefixLift 1376412
  have htrace : WordTrace (prefixWord ++ tailWord_1376412) baseStart_1376412 baseEnd_1376412 := by
    simpa [prefixWord, tailWord_1376412, baseEnd_1376412] using wordTrace_append hprefix tailTrace_1376412
  have hstable : (prefixWord ++ tailWord_1376412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376412).length < 2 ^ (prefixWord ++ tailWord_1376412).sum := by decide
  have hdescent : baseEnd_1376412 < baseStart_1376412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376415 : List Nat := [1, 1, 2, 6, 1, 1, 4, 1, 4]
def baseStart_1376415 : Nat := 118140960795 + 1376415 * 2 ^ 59
def prefixEnd_1376415 : Nat := 4983230072969 + 3 ^ 40 * 1376415 * 2
def baseEnd_1376415 : Nat := 314116655581483334969995

theorem tailTrace_1376415 : CollatzResearch.WordTrace tailWord_1376415 prefixEnd_1376415 314116655581483334969995 := by
  unfold tailWord_1376415
  simp only [CollatzResearch.WordTrace]
  refine ⟨50201979308491002811994699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33467986205660668541329799 50201979308491002811994699)
  ·
    refine ⟨75302968962736504217992049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50201979308491002811994699 75302968962736504217992049)
    ·
      refine ⟨56477226722052378163494037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75302968962736504217992049 56477226722052378163494037)
      ·
        refine ⟨2647370002596205226413783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 56477226722052378163494037 2647370002596205226413783)
        ·
          refine ⟨3971055003894307839620675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2647370002596205226413783 3971055003894307839620675)
          ·
            refine ⟨5956582505841461759431013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3971055003894307839620675 5956582505841461759431013)
            ·
              refine ⟨1116859219845274079893315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5956582505841461759431013 1116859219845274079893315)
              ·
                refine ⟨1675288829767911119839973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1116859219845274079893315 1675288829767911119839973)
                ·
                  refine ⟨314116655581483334969995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1675288829767911119839973 314116655581483334969995)
                  ·
                    rfl

theorem cell21_1376415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 1, 4].length) (baseStart_1376415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1376415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1376415 prefixEnd_1376415 := by exact prefixLift 1376415
  have htrace : WordTrace (prefixWord ++ tailWord_1376415) baseStart_1376415 baseEnd_1376415 := by
    simpa [prefixWord, tailWord_1376415, baseEnd_1376415] using wordTrace_append hprefix tailTrace_1376415
  have hstable : (prefixWord ++ tailWord_1376415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376415).length < 2 ^ (prefixWord ++ tailWord_1376415).sum := by decide
  have hdescent : baseEnd_1376415 < baseStart_1376415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376443 : List Nat := [1, 1, 1, 1, 1, 2, 6, 5, 3]
def baseStart_1376443 : Nat := 118140960795 + 1376443 * 2 ^ 59
def prefixEnd_1376443 : Nat := 4983230072969 + 3 ^ 40 * 1376443 * 2
def baseEnd_1376443 : Nat := 314123045562961508503271

theorem tailTrace_1376443 : CollatzResearch.WordTrace tailWord_1376443 prefixEnd_1376443 314123045562961508503271 := by
  unfold tailWord_1376443
  simp only [CollatzResearch.WordTrace]
  refine ⟨50203000552389563594013983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33468667034926375729342655 50203000552389563594013983)
  ·
    refine ⟨75304500828584345391020975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50203000552389563594013983 75304500828584345391020975)
    ·
      refine ⟨112956751242876518086531463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75304500828584345391020975 112956751242876518086531463)
      ·
        refine ⟨169435126864314777129797195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112956751242876518086531463 169435126864314777129797195)
        ·
          refine ⟨254152690296472165694695793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169435126864314777129797195 254152690296472165694695793)
          ·
            refine ⟨190614517722354124271021845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 254152690296472165694695793 190614517722354124271021845)
            ·
              refine ⟨8935055518235349575204149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 190614517722354124271021845 8935055518235349575204149)
              ·
                refine ⟨837661454834564022675389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8935055518235349575204149 837661454834564022675389)
                ·
                  refine ⟨314123045562961508503271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 837661454834564022675389 314123045562961508503271)
                  ·
                    rfl

theorem cell21_1376443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 5, 3].length) (baseStart_1376443 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1376443 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1376443 prefixEnd_1376443 := by exact prefixLift 1376443
  have htrace : WordTrace (prefixWord ++ tailWord_1376443) baseStart_1376443 baseEnd_1376443 := by
    simpa [prefixWord, tailWord_1376443, baseEnd_1376443] using wordTrace_append hprefix tailTrace_1376443
  have hstable : (prefixWord ++ tailWord_1376443).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376443).length < 2 ^ (prefixWord ++ tailWord_1376443).sum := by decide
  have hdescent : baseEnd_1376443 < baseStart_1376443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376533 : List Nat := [1, 3, 2, 1, 2, 1, 2, 5, 4]
def baseStart_1376533 : Nat := 118140960795 + 1376533 * 2 ^ 59
def prefixEnd_1376533 : Nat := 4983230072969 + 3 ^ 40 * 1376533 * 2
def baseEnd_1376533 : Nat := 314143584789141352003087

theorem tailTrace_1376533 : CollatzResearch.WordTrace tailWord_1376533 prefixEnd_1376533 314143584789141352003087 := by
  unfold tailWord_1376533
  simp only [CollatzResearch.WordTrace]
  refine ⟨50206283122063508964790253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33470855414709005976526835 50206283122063508964790253)
  ·
    refine ⟨18827356170773815861796345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50206283122063508964790253 18827356170773815861796345)
    ·
      refine ⟨14120517128080361896347259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18827356170773815861796345 14120517128080361896347259)
      ·
        refine ⟨21180775692120542844520889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14120517128080361896347259 21180775692120542844520889)
        ·
          refine ⟨15885581769090407133390667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21180775692120542844520889 15885581769090407133390667)
          ·
            refine ⟨23828372653635610700086001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15885581769090407133390667 23828372653635610700086001)
            ·
              refine ⟨17871279490226708025064501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23828372653635610700086001 17871279490226708025064501)
              ·
                refine ⟨1675432452208753877349797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17871279490226708025064501 1675432452208753877349797)
                ·
                  refine ⟨314143584789141352003087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1675432452208753877349797 314143584789141352003087)
                  ·
                    rfl

theorem cell21_1376533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 5, 4].length) (baseStart_1376533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1376533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1376533 prefixEnd_1376533 := by exact prefixLift 1376533
  have htrace : WordTrace (prefixWord ++ tailWord_1376533) baseStart_1376533 baseEnd_1376533 := by
    simpa [prefixWord, tailWord_1376533, baseEnd_1376533] using wordTrace_append hprefix tailTrace_1376533
  have hstable : (prefixWord ++ tailWord_1376533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376533).length < 2 ^ (prefixWord ++ tailWord_1376533).sum := by decide
  have hdescent : baseEnd_1376533 < baseStart_1376533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376547 : List Nat := [1, 1, 1, 4, 2, 2, 3, 7]
def baseStart_1376547 : Nat := 118140960795 + 1376547 * 2 ^ 59
def prefixEnd_1376547 : Nat := 4983230072969 + 3 ^ 40 * 1376547 * 2
def baseEnd_1376547 : Nat := 104715593259960146256575

theorem tailTrace_1376547 : CollatzResearch.WordTrace tailWord_1376547 prefixEnd_1376547 104715593259960146256575 := by
  unfold tailWord_1376547
  simp only [CollatzResearch.WordTrace]
  refine ⟨50206793744012789355799895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33471195829341859570533263 50206793744012789355799895)
  ·
    refine ⟨75310190616019184033699843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50206793744012789355799895 75310190616019184033699843)
    ·
      refine ⟨112965285924028776050549765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75310190616019184033699843 112965285924028776050549765)
      ·
        refine ⟨21180991110755395509478081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112965285924028776050549765 21180991110755395509478081)
        ·
          refine ⟨15885743333066546632108561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21180991110755395509478081 15885743333066546632108561)
          ·
            refine ⟨11914307499799909974081421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15885743333066546632108561 11914307499799909974081421)
            ·
              refine ⟨4467865312424966240280533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11914307499799909974081421 4467865312424966240280533)
              ·
                refine ⟨104715593259960146256575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4467865312424966240280533 104715593259960146256575)
                ·
                  rfl

theorem cell21_1376547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 7].length) (baseStart_1376547 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1376547 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1376547 prefixEnd_1376547 := by exact prefixLift 1376547
  have htrace : WordTrace (prefixWord ++ tailWord_1376547) baseStart_1376547 baseEnd_1376547 := by
    simpa [prefixWord, tailWord_1376547, baseEnd_1376547] using wordTrace_append hprefix tailTrace_1376547
  have hstable : (prefixWord ++ tailWord_1376547).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376547).length < 2 ^ (prefixWord ++ tailWord_1376547).sum := by decide
  have hdescent : baseEnd_1376547 < baseStart_1376547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376564 : List Nat := [2, 5, 1, 1, 1, 2, 9]
def baseStart_1376564 : Nat := 118140960795 + 1376564 * 2 ^ 59
def prefixEnd_1376564 : Nat := 4983230072969 + 3 ^ 40 * 1376564 * 2
def baseEnd_1376564 : Nat := 34905628823499131887373

theorem tailTrace_1376564 : CollatzResearch.WordTrace tailWord_1376564 prefixEnd_1376564 34905628823499131887373 := by
  unfold tailWord_1376564
  simp only [CollatzResearch.WordTrace]
  refine ⟨25103706892475600629584373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33471609189967467506112497 25103706892475600629584373)
  ·
    refine ⟨2353472521169587559023535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25103706892475600629584373 2353472521169587559023535)
    ·
      refine ⟨3530208781754381338535303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2353472521169587559023535 3530208781754381338535303)
      ·
        refine ⟨5295313172631572007802955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3530208781754381338535303 5295313172631572007802955)
        ·
          refine ⟨7942969758947358011704433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5295313172631572007802955 7942969758947358011704433)
          ·
            refine ⟨5957227319210518508778325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7942969758947358011704433 5957227319210518508778325)
            ·
              refine ⟨34905628823499131887373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5957227319210518508778325 34905628823499131887373)
              ·
                rfl

theorem cell21_1376564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 9].length) (baseStart_1376564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1376564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1376564 prefixEnd_1376564 := by exact prefixLift 1376564
  have htrace : WordTrace (prefixWord ++ tailWord_1376564) baseStart_1376564 baseEnd_1376564 := by
    simpa [prefixWord, tailWord_1376564, baseEnd_1376564] using wordTrace_append hprefix tailTrace_1376564
  have hstable : (prefixWord ++ tailWord_1376564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376564).length < 2 ^ (prefixWord ++ tailWord_1376564).sum := by decide
  have hdescent : baseEnd_1376564 < baseStart_1376564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376626 : List Nat := [3, 2, 1, 2, 1, 4, 2, 2, 4]
def baseStart_1376626 : Nat := 118140960795 + 1376626 * 2 ^ 59
def prefixEnd_1376626 : Nat := 4983230072969 + 3 ^ 40 * 1376626 * 2
def baseEnd_1376626 : Nat := 314164808656193856952897

theorem tailTrace_1376626 : CollatzResearch.WordTrace tailWord_1376626 prefixEnd_1376626 314164808656193856952897 := by
  unfold tailWord_1376626
  simp only [CollatzResearch.WordTrace]
  refine ⟨12552418777681646461981433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33473116740484390565283821 12552418777681646461981433)
  ·
    refine ⟨9414314083261234846486075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12552418777681646461981433 9414314083261234846486075)
    ·
      refine ⟨14121471124891852269729113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9414314083261234846486075 14121471124891852269729113)
      ·
        refine ⟨10591103343668889202296835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14121471124891852269729113 10591103343668889202296835)
        ·
          refine ⟨15886655015503333803445253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10591103343668889202296835 15886655015503333803445253)
          ·
            refine ⟨2978747815406875088145985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15886655015503333803445253 2978747815406875088145985)
            ·
              refine ⟨2234060861555156316109489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2978747815406875088145985 2234060861555156316109489)
              ·
                refine ⟨1675545646166367237082117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2234060861555156316109489 1675545646166367237082117)
                ·
                  refine ⟨314164808656193856952897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1675545646166367237082117 314164808656193856952897)
                  ·
                    rfl

theorem cell21_1376626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_1376626 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1376626 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1376626 prefixEnd_1376626 := by exact prefixLift 1376626
  have htrace : WordTrace (prefixWord ++ tailWord_1376626) baseStart_1376626 baseEnd_1376626 := by
    simpa [prefixWord, tailWord_1376626, baseEnd_1376626] using wordTrace_append hprefix tailTrace_1376626
  have hstable : (prefixWord ++ tailWord_1376626).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376626).length < 2 ^ (prefixWord ++ tailWord_1376626).sum := by decide
  have hdescent : baseEnd_1376626 < baseStart_1376626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376629 : List Nat := [1, 3, 4, 1, 2, 1, 4, 2, 3]
def baseStart_1376629 : Nat := 118140960795 + 1376629 * 2 ^ 59
def prefixEnd_1376629 : Nat := 4983230072969 + 3 ^ 40 * 1376629 * 2
def baseEnd_1376629 : Nat := 314165493297066518402891

theorem tailTrace_1376629 : CollatzResearch.WordTrace tailWord_1376629 prefixEnd_1376629 314165493297066518402891 := by
  unfold tailWord_1376629
  simp only [CollatzResearch.WordTrace]
  refine ⟨50209784529715717360284941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33473189686477144906856627 50209784529715717360284941)
  ·
    refine ⟨18828669198643394010106853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50209784529715717360284941 18828669198643394010106853)
    ·
      refine ⟨3530375474745636376895035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18828669198643394010106853 3530375474745636376895035)
      ·
        refine ⟨5295563212118454565342553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3530375474745636376895035 5295563212118454565342553)
        ·
          refine ⟨3971672409088840924006915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5295563212118454565342553 3971672409088840924006915)
          ·
            refine ⟨5957508613633261386010373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3971672409088840924006915 5957508613633261386010373)
            ·
              refine ⟨1117032865056236509876945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5957508613633261386010373 1117032865056236509876945)
              ·
                refine ⟨837774648792177382407709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1117032865056236509876945 837774648792177382407709)
                ·
                  refine ⟨314165493297066518402891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 837774648792177382407709 314165493297066518402891)
                  ·
                    rfl

theorem cell21_1376629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 2, 3].length) (baseStart_1376629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1376629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1376629 prefixEnd_1376629 := by exact prefixLift 1376629
  have htrace : WordTrace (prefixWord ++ tailWord_1376629) baseStart_1376629 baseEnd_1376629 := by
    simpa [prefixWord, tailWord_1376629, baseEnd_1376629] using wordTrace_append hprefix tailTrace_1376629
  have hstable : (prefixWord ++ tailWord_1376629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376629).length < 2 ^ (prefixWord ++ tailWord_1376629).sum := by decide
  have hdescent : baseEnd_1376629 < baseStart_1376629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376716 : List Nat := [2, 2, 1, 4, 3, 1, 1, 7]
def baseStart_1376716 : Nat := 118140960795 + 1376716 * 2 ^ 59
def prefixEnd_1376716 : Nat := 4983230072969 + 3 ^ 40 * 1376716 * 2
def baseEnd_1376716 : Nat := 104728449294124566817571

theorem tailTrace_1376716 : CollatzResearch.WordTrace tailWord_1376716 prefixEnd_1376716 104728449294124566817571 := by
  unfold tailWord_1376716
  simp only [CollatzResearch.WordTrace]
  refine ⟨25106478840200265609351001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33475305120267020812468001 25106478840200265609351001)
  ·
    refine ⟨18829859130150199207013251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25106478840200265609351001 18829859130150199207013251)
    ·
      refine ⟨28244788695225298810519877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18829859130150199207013251 28244788695225298810519877)
      ·
        refine ⟨5295897880354743526972477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28244788695225298810519877 5295897880354743526972477)
        ·
          refine ⟨1985961705133028822614679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5295897880354743526972477 1985961705133028822614679)
          ·
            refine ⟨2978942557699543233922019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1985961705133028822614679 2978942557699543233922019)
            ·
              refine ⟨4468413836549314850883029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2978942557699543233922019 4468413836549314850883029)
              ·
                refine ⟨104728449294124566817571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4468413836549314850883029 104728449294124566817571)
                ·
                  rfl

theorem cell21_1376716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 7].length) (baseStart_1376716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1376716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1376716 prefixEnd_1376716 := by exact prefixLift 1376716
  have htrace : WordTrace (prefixWord ++ tailWord_1376716) baseStart_1376716 baseEnd_1376716 := by
    simpa [prefixWord, tailWord_1376716, baseEnd_1376716] using wordTrace_append hprefix tailTrace_1376716
  have hstable : (prefixWord ++ tailWord_1376716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376716).length < 2 ^ (prefixWord ++ tailWord_1376716).sum := by decide
  have hdescent : baseEnd_1376716 < baseStart_1376716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376722 : List Nat := [3, 2, 2, 4, 1, 2, 1, 3, 3]
def baseStart_1376722 : Nat := 118140960795 + 1376722 * 2 ^ 59
def prefixEnd_1376722 : Nat := 4983230072969 + 3 ^ 40 * 1376722 * 2
def baseEnd_1376722 : Nat := 314186717164119023352701

theorem tailTrace_1376722 : CollatzResearch.WordTrace tailWord_1376722 prefixEnd_1376722 314186717164119023352701 := by
  unfold tailWord_1376722
  simp only [CollatzResearch.WordTrace]
  refine ⟨12553294129594698560855105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33475451012252529495613613 12553294129594698560855105)
  ·
    refine ⟨9414970597196023920641329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12553294129594698560855105 9414970597196023920641329)
    ·
      refine ⟨7061227947897017940480997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9414970597196023920641329 7061227947897017940480997)
      ·
        refine ⟨1323980240230690863840187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7061227947897017940480997 1323980240230690863840187)
        ·
          refine ⟨1985970360346036295760281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1323980240230690863840187 1985970360346036295760281)
          ·
            refine ⟨1489477770259527221820211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1985970360346036295760281 1489477770259527221820211)
            ·
              refine ⟨2234216655389290832730317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1489477770259527221820211 2234216655389290832730317)
              ·
                refine ⟨837831245770984062273869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2234216655389290832730317 837831245770984062273869)
                ·
                  refine ⟨314186717164119023352701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 837831245770984062273869 314186717164119023352701)
                  ·
                    rfl

theorem cell21_1376722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 3, 3].length) (baseStart_1376722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1376722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1376722 prefixEnd_1376722 := by exact prefixLift 1376722
  have htrace : WordTrace (prefixWord ++ tailWord_1376722) baseStart_1376722 baseEnd_1376722 := by
    simpa [prefixWord, tailWord_1376722, baseEnd_1376722] using wordTrace_append hprefix tailTrace_1376722
  have hstable : (prefixWord ++ tailWord_1376722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376722).length < 2 ^ (prefixWord ++ tailWord_1376722).sum := by decide
  have hdescent : baseEnd_1376722 < baseStart_1376722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376896 : List Nat := [2, 1, 1, 2, 1, 5, 1, 2, 6]
def baseStart_1376896 : Nat := 118140960795 + 1376896 * 2 ^ 59
def prefixEnd_1376896 : Nat := 4983230072969 + 3 ^ 40 * 1376896 * 2
def baseEnd_1376896 : Nat := 314226426334733387452345

theorem tailTrace_1376896 : CollatzResearch.WordTrace tailWord_1376896 prefixEnd_1376896 314226426334733387452345 := by
  unfold tailWord_1376896
  simp only [CollatzResearch.WordTrace]
  refine ⟨25109761409874210980127271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33479681879832281306836361 25109761409874210980127271)
  ·
    refine ⟨37664642114811316470190907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25109761409874210980127271 37664642114811316470190907)
    ·
      refine ⟨56496963172216974705286361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37664642114811316470190907 56496963172216974705286361)
      ·
        refine ⟨42372722379162731028964771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56496963172216974705286361 42372722379162731028964771)
        ·
          refine ⟨63559083568744096543447157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42372722379162731028964771 63559083568744096543447157)
          ·
            refine ⟨5958664084569759050948171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63559083568744096543447157 5958664084569759050948171)
            ·
              refine ⟨8937996126854638576422257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5958664084569759050948171 8937996126854638576422257)
              ·
                refine ⟨6703497095140978932316693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8937996126854638576422257 6703497095140978932316693)
                ·
                  refine ⟨314226426334733387452345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6703497095140978932316693 314226426334733387452345)
                  ·
                    rfl

theorem cell21_1376896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 6].length) (baseStart_1376896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1376896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1376896 prefixEnd_1376896 := by exact prefixLift 1376896
  have htrace : WordTrace (prefixWord ++ tailWord_1376896) baseStart_1376896 baseEnd_1376896 := by
    simpa [prefixWord, tailWord_1376896, baseEnd_1376896] using wordTrace_append hprefix tailTrace_1376896
  have hstable : (prefixWord ++ tailWord_1376896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376896).length < 2 ^ (prefixWord ++ tailWord_1376896).sum := by decide
  have hdescent : baseEnd_1376896 < baseStart_1376896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376899 : List Nat := [1, 1, 1, 3, 3, 1, 5, 3, 3]
def baseStart_1376899 : Nat := 118140960795 + 1376899 * 2 ^ 59
def prefixEnd_1376899 : Nat := 4983230072969 + 3 ^ 40 * 1376899 * 2
def baseEnd_1376899 : Nat := 314227110975606048902339

theorem tailTrace_1376899 : CollatzResearch.WordTrace tailWord_1376899 prefixEnd_1376899 314227110975606048902339 := by
  unfold tailWord_1376899
  simp only [CollatzResearch.WordTrace]
  refine ⟨50219632238737553472613751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33479754825825035648409167 50219632238737553472613751)
  ·
    refine ⟨75329448358106330208920627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50219632238737553472613751 75329448358106330208920627)
    ·
      refine ⟨112994172537159495313380941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75329448358106330208920627 112994172537159495313380941)
      ·
        refine ⟨42372814701434810742517853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112994172537159495313380941 42372814701434810742517853)
        ·
          refine ⟨15889805513038054028444195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42372814701434810742517853 15889805513038054028444195)
          ·
            refine ⟨23834708269557081042666293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15889805513038054028444195 23834708269557081042666293)
            ·
              refine ⟨2234503900270976347749965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23834708269557081042666293 2234503900270976347749965)
              ·
                refine ⟨837938962601616130406237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2234503900270976347749965 837938962601616130406237)
                ·
                  refine ⟨314227110975606048902339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 837938962601616130406237 314227110975606048902339)
                  ·
                    rfl

theorem cell21_1376899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 3, 3].length) (baseStart_1376899 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1376899 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1376899 prefixEnd_1376899 := by exact prefixLift 1376899
  have htrace : WordTrace (prefixWord ++ tailWord_1376899) baseStart_1376899 baseEnd_1376899 := by
    simpa [prefixWord, tailWord_1376899, baseEnd_1376899] using wordTrace_append hprefix tailTrace_1376899
  have hstable : (prefixWord ++ tailWord_1376899).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376899).length < 2 ^ (prefixWord ++ tailWord_1376899).sum := by decide
  have hdescent : baseEnd_1376899 < baseStart_1376899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376916 : List Nat := [2, 4, 2, 2, 1, 3, 1, 1, 5]
def baseStart_1376916 : Nat := 118140960795 + 1376916 * 2 ^ 59
def prefixEnd_1376916 : Nat := 4983230072969 + 3 ^ 40 * 1376916 * 2
def baseEnd_1376916 : Nat := 314230990607217797118971

theorem tailTrace_1376916 : CollatzResearch.WordTrace tailWord_1376916 prefixEnd_1376916 314230990607217797118971 := by
  unfold tailWord_1376916
  simp only [CollatzResearch.WordTrace]
  refine ⟨25110126139837982687991301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33480168186450643583988401 25110126139837982687991301)
  ·
    refine ⟨4708148651219621753998369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25110126139837982687991301 4708148651219621753998369)
    ·
      refine ⟨3531111488414716315498777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4708148651219621753998369 3531111488414716315498777)
      ·
        refine ⟨2648333616311037236624083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3531111488414716315498777 2648333616311037236624083)
        ·
          refine ⟨3972500424466555854936125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2648333616311037236624083 3972500424466555854936125)
          ·
            refine ⟨1489687659174958445601047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3972500424466555854936125 1489687659174958445601047)
            ·
              refine ⟨2234531488762437668401571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1489687659174958445601047 2234531488762437668401571)
              ·
                refine ⟨3351797233143656502602357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2234531488762437668401571 3351797233143656502602357)
                ·
                  refine ⟨314230990607217797118971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3351797233143656502602357 314230990607217797118971)
                  ·
                    rfl

theorem cell21_1376916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_1376916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1376916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1376916 prefixEnd_1376916 := by exact prefixLift 1376916
  have htrace : WordTrace (prefixWord ++ tailWord_1376916) baseStart_1376916 baseEnd_1376916 := by
    simpa [prefixWord, tailWord_1376916, baseEnd_1376916] using wordTrace_append hprefix tailTrace_1376916
  have hstable : (prefixWord ++ tailWord_1376916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376916).length < 2 ^ (prefixWord ++ tailWord_1376916).sum := by decide
  have hdescent : baseEnd_1376916 < baseStart_1376916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376961 : List Nat := [1, 2, 6, 2, 2, 8]
def baseStart_1376961 : Nat := 118140960795 + 1376961 * 2 ^ 59
def prefixEnd_1376961 : Nat := 4983230072969 + 3 ^ 40 * 1376961 * 2
def baseEnd_1376961 : Nat := 11638565193344730328477

theorem tailTrace_1376961 : CollatzResearch.WordTrace tailWord_1376961 prefixEnd_1376961 11638565193344730328477 := by
  unfold tailWord_1376961
  simp only [CollatzResearch.WordTrace]
  refine ⟨50221893564512938061370737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33481262376341958707580491 50221893564512938061370737)
  ·
    refine ⟨37666420173384703546028053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50221893564512938061370737 37666420173384703546028053)
    ·
      refine ⟨1765613445627407978720065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 37666420173384703546028053 1765613445627407978720065)
      ·
        refine ⟨1324210084220555984040049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1765613445627407978720065 1324210084220555984040049)
        ·
          refine ⟨993157563165416988030037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1324210084220555984040049 993157563165416988030037)
          ·
            refine ⟨11638565193344730328477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 993157563165416988030037 11638565193344730328477)
            ·
              rfl

theorem cell21_1376961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 8].length) (baseStart_1376961 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1376961 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1376961 prefixEnd_1376961 := by exact prefixLift 1376961
  have htrace : WordTrace (prefixWord ++ tailWord_1376961) baseStart_1376961 baseEnd_1376961 := by
    simpa [prefixWord, tailWord_1376961, baseEnd_1376961] using wordTrace_append hprefix tailTrace_1376961
  have hstable : (prefixWord ++ tailWord_1376961).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376961).length < 2 ^ (prefixWord ++ tailWord_1376961).sum := by decide
  have hdescent : baseEnd_1376961 < baseStart_1376961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377034 : List Nat := [3, 1, 2, 2, 1, 2, 4, 1, 5]
def baseStart_1377034 : Nat := 118140960795 + 1377034 * 2 ^ 59
def prefixEnd_1377034 : Nat := 4983230072969 + 3 ^ 40 * 1377034 * 2
def baseEnd_1377034 : Nat := 314257919814875814152063

theorem tailTrace_1377034 : CollatzResearch.WordTrace tailWord_1377034 prefixEnd_1377034 314257919814875814152063 := by
  unfold tailWord_1377034
  simp only [CollatzResearch.WordTrace]
  refine ⟨12556139023312117882194539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33483037395498981019185437 12556139023312117882194539)
  ·
    refine ⟨18834208534968176823291809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12556139023312117882194539 18834208534968176823291809)
    ·
      refine ⟨14125656401226132617468857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18834208534968176823291809 14125656401226132617468857)
      ·
        refine ⟨10594242300919599463101643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14125656401226132617468857 10594242300919599463101643)
        ·
          refine ⟨15891363451379399194652465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10594242300919599463101643 15891363451379399194652465)
          ·
            refine ⟨11918522588534549395989349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15891363451379399194652465 11918522588534549395989349)
            ·
              refine ⟨2234722985350228011748003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11918522588534549395989349 2234722985350228011748003)
              ·
                refine ⟨3352084478025342017622005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2234722985350228011748003 3352084478025342017622005)
                ·
                  refine ⟨314257919814875814152063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3352084478025342017622005 314257919814875814152063)
                  ·
                    rfl

theorem cell21_1377034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 5].length) (baseStart_1377034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1377034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1377034 prefixEnd_1377034 := by exact prefixLift 1377034
  have htrace : WordTrace (prefixWord ++ tailWord_1377034) baseStart_1377034 baseEnd_1377034 := by
    simpa [prefixWord, tailWord_1377034, baseEnd_1377034] using wordTrace_append hprefix tailTrace_1377034
  have hstable : (prefixWord ++ tailWord_1377034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377034).length < 2 ^ (prefixWord ++ tailWord_1377034).sum := by decide
  have hdescent : baseEnd_1377034 < baseStart_1377034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377085 : List Nat := [1, 4, 1, 4, 2, 1, 3, 2, 3]
def baseStart_1377085 : Nat := 118140960795 + 1377085 * 2 ^ 59
def prefixEnd_1377085 : Nat := 4983230072969 + 3 ^ 40 * 1377085 * 2
def baseEnd_1377085 : Nat := 314269558709711058801959

theorem tailTrace_1377085 : CollatzResearch.WordTrace tailWord_1377085 prefixEnd_1377085 314269558709711058801959 := by
  unfold tailWord_1377085
  simp only [CollatzResearch.WordTrace]
  refine ⟨50226416216063707238884709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33484277477375804825923139 50226416216063707238884709)
  ·
    refine ⟨9417453040511945107290883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50226416216063707238884709 9417453040511945107290883)
    ·
      refine ⟨14126179560767917660936325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9417453040511945107290883 14126179560767917660936325)
      ·
        refine ⟨2648658667643984561425561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14126179560767917660936325 2648658667643984561425561)
        ·
          refine ⟨1986494000732988421069171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2648658667643984561425561 1986494000732988421069171)
          ·
            refine ⟨2979741001099482631603757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1986494000732988421069171 2979741001099482631603757)
            ·
              refine ⟨1117402875412305986851409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2979741001099482631603757 1117402875412305986851409)
              ·
                refine ⟨838052156559229490138557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1117402875412305986851409 838052156559229490138557)
                ·
                  refine ⟨314269558709711058801959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 838052156559229490138557 314269558709711058801959)
                  ·
                    rfl

theorem cell21_1377085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 2, 3].length) (baseStart_1377085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1377085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1377085 prefixEnd_1377085 := by exact prefixLift 1377085
  have htrace : WordTrace (prefixWord ++ tailWord_1377085) baseStart_1377085 baseEnd_1377085 := by
    simpa [prefixWord, tailWord_1377085, baseEnd_1377085] using wordTrace_append hprefix tailTrace_1377085
  have hstable : (prefixWord ++ tailWord_1377085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377085).length < 2 ^ (prefixWord ++ tailWord_1377085).sum := by decide
  have hdescent : baseEnd_1377085 < baseStart_1377085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377093 : List Nat := [1, 3, 1, 1, 1, 2, 2, 5, 5]
def baseStart_1377093 : Nat := 118140960795 + 1377093 * 2 ^ 59
def prefixEnd_1377093 : Nat := 4983230072969 + 3 ^ 40 * 1377093 * 2
def baseEnd_1377093 : Nat := 314271384418704822668609

theorem tailTrace_1377093 : CollatzResearch.WordTrace tailWord_1377093 prefixEnd_1377093 314271384418704822668609 := by
  unfold tailWord_1377093
  simp only [CollatzResearch.WordTrace]
  refine ⟨50226708000034724605175933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33484472000023149736783955 50226708000034724605175933)
  ·
    refine ⟨18835015500013021726940975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50226708000034724605175933 18835015500013021726940975)
    ·
      refine ⟨28252523250019532590411463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18835015500013021726940975 28252523250019532590411463)
      ·
        refine ⟨42378784875029298885617195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28252523250019532590411463 42378784875029298885617195)
        ·
          refine ⟨63568177312543948328425793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42378784875029298885617195 63568177312543948328425793)
          ·
            refine ⟨47676132984407961246319345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63568177312543948328425793 47676132984407961246319345)
            ·
              refine ⟨35757099738305970934739509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47676132984407961246319345 35757099738305970934739509)
              ·
                refine ⟨3352228100466184775131829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35757099738305970934739509 3352228100466184775131829)
                ·
                  refine ⟨314271384418704822668609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3352228100466184775131829 314271384418704822668609)
                  ·
                    rfl

theorem cell21_1377093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_1377093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1377093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1377093 prefixEnd_1377093 := by exact prefixLift 1377093
  have htrace : WordTrace (prefixWord ++ tailWord_1377093) baseStart_1377093 baseEnd_1377093 := by
    simpa [prefixWord, tailWord_1377093, baseEnd_1377093] using wordTrace_append hprefix tailTrace_1377093
  have hstable : (prefixWord ++ tailWord_1377093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377093).length < 2 ^ (prefixWord ++ tailWord_1377093).sum := by decide
  have hdescent : baseEnd_1377093 < baseStart_1377093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377141 : List Nat := [1, 3, 4, 1, 1, 2, 1, 4, 4]
def baseStart_1377141 : Nat := 118140960795 + 1377141 * 2 ^ 59
def prefixEnd_1377141 : Nat := 4983230072969 + 3 ^ 40 * 1377141 * 2
def baseEnd_1377141 : Nat := 314282338672667405868511

theorem tailTrace_1377141 : CollatzResearch.WordTrace tailWord_1377141 prefixEnd_1377141 314282338672667405868511 := by
  unfold tailWord_1377141
  simp only [CollatzResearch.WordTrace]
  refine ⟨50228458703860828802923277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33485639135907219201948851 50228458703860828802923277)
  ·
    refine ⟨18835672013947810801096229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50228458703860828802923277 18835672013947810801096229)
    ·
      refine ⟨3531688502615214525205543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18835672013947810801096229 3531688502615214525205543)
      ·
        refine ⟨5297532753922821787808315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3531688502615214525205543 5297532753922821787808315)
        ·
          refine ⟨7946299130884232681712473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5297532753922821787808315 7946299130884232681712473)
          ·
            refine ⟨5959724348163174511284355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7946299130884232681712473 5959724348163174511284355)
            ·
              refine ⟨8939586522244761766926533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5959724348163174511284355 8939586522244761766926533)
              ·
                refine ⟨1676172472920892831298725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8939586522244761766926533 1676172472920892831298725)
                ·
                  refine ⟨314282338672667405868511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1676172472920892831298725 314282338672667405868511)
                  ·
                    rfl

theorem cell21_1377141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 4, 4].length) (baseStart_1377141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1377141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1377141 prefixEnd_1377141 := by exact prefixLift 1377141
  have htrace : WordTrace (prefixWord ++ tailWord_1377141) baseStart_1377141 baseEnd_1377141 := by
    simpa [prefixWord, tailWord_1377141, baseEnd_1377141] using wordTrace_append hprefix tailTrace_1377141
  have hstable : (prefixWord ++ tailWord_1377141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377141).length < 2 ^ (prefixWord ++ tailWord_1377141).sum := by decide
  have hdescent : baseEnd_1377141 < baseStart_1377141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377172 : List Nat := [2, 4, 2, 1, 1, 1, 5, 5]
def baseStart_1377172 : Nat := 118140960795 + 1377172 * 2 ^ 59
def prefixEnd_1377172 : Nat := 4983230072969 + 3 ^ 40 * 1377172 * 2
def baseEnd_1377172 : Nat := 104763137765006080283927

theorem tailTrace_1377172 : CollatzResearch.WordTrace tailWord_1377172 prefixEnd_1377172 104763137765006080283927 := by
  unfold tailWord_1377172
  simp only [CollatzResearch.WordTrace]
  refine ⟨25114794683374260548650885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33486392911165680731534513 25114794683374260548650885)
  ·
    refine ⟨4709024003132673852872041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25114794683374260548650885 4709024003132673852872041)
    ·
      refine ⟨3531768002349505389654031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4709024003132673852872041 3531768002349505389654031)
      ·
        refine ⟨5297652003524258084481047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3531768002349505389654031 5297652003524258084481047)
        ·
          refine ⟨7946478005286387126721571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5297652003524258084481047 7946478005286387126721571)
          ·
            refine ⟨11919717007929580690082357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7946478005286387126721571 11919717007929580690082357)
            ·
              refine ⟨1117473469493398189695221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11919717007929580690082357 1117473469493398189695221)
              ·
                refine ⟨104763137765006080283927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1117473469493398189695221 104763137765006080283927)
                ·
                  rfl

theorem cell21_1377172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 5].length) (baseStart_1377172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1377172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1377172 prefixEnd_1377172 := by exact prefixLift 1377172
  have htrace : WordTrace (prefixWord ++ tailWord_1377172) baseStart_1377172 baseEnd_1377172 := by
    simpa [prefixWord, tailWord_1377172, baseEnd_1377172] using wordTrace_append hprefix tailTrace_1377172
  have hstable : (prefixWord ++ tailWord_1377172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377172).length < 2 ^ (prefixWord ++ tailWord_1377172).sum := by decide
  have hdescent : baseEnd_1377172 < baseStart_1377172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377231 : List Nat := [1, 1, 2, 1, 1, 6, 4, 5]
def baseStart_1377231 : Nat := 118140960795 + 1377231 * 2 ^ 59
def prefixEnd_1377231 : Nat := 4983230072969 + 3 ^ 40 * 1377231 * 2
def baseEnd_1377231 : Nat := 104767625966282416456109

theorem tailTrace_1377231 : CollatzResearch.WordTrace tailWord_1377231 prefixEnd_1377231 104767625966282416456109 := by
  unfold tailWord_1377231
  simp only [CollatzResearch.WordTrace]
  refine ⟨50231741273534774173699547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33487827515689849449133031 50231741273534774173699547)
  ·
    refine ⟨75347611910302161260549321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50231741273534774173699547 75347611910302161260549321)
    ·
      refine ⟨56510708932726620945411991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75347611910302161260549321 56510708932726620945411991)
      ·
        refine ⟨84766063399089931418117987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56510708932726620945411991 84766063399089931418117987)
        ·
          refine ⟨127149095098634897127176981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84766063399089931418117987 127149095098634897127176981)
          ·
            refine ⟨5960113832748510802836421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 127149095098634897127176981 5960113832748510802836421)
            ·
              refine ⟨1117521343640345775531829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5960113832748510802836421 1117521343640345775531829)
              ·
                refine ⟨104767625966282416456109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1117521343640345775531829 104767625966282416456109)
                ·
                  rfl

theorem cell21_1377231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 5].length) (baseStart_1377231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1377231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1377231 prefixEnd_1377231 := by exact prefixLift 1377231
  have htrace : WordTrace (prefixWord ++ tailWord_1377231) baseStart_1377231 baseEnd_1377231 := by
    simpa [prefixWord, tailWord_1377231, baseEnd_1377231] using wordTrace_append hprefix tailTrace_1377231
  have hstable : (prefixWord ++ tailWord_1377231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377231).length < 2 ^ (prefixWord ++ tailWord_1377231).sum := by decide
  have hdescent : baseEnd_1377231 < baseStart_1377231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377237 : List Nat := [1, 3, 2, 3, 4, 1, 1, 3, 3]
def baseStart_1377237 : Nat := 118140960795 + 1377237 * 2 ^ 59
def prefixEnd_1377237 : Nat := 4983230072969 + 3 ^ 40 * 1377237 * 2
def baseEnd_1377237 : Nat := 314304247180592572268315

theorem tailTrace_1377237 : CollatzResearch.WordTrace tailWord_1377237 prefixEnd_1377237 314304247180592572268315 := by
  unfold tailWord_1377237
  simp only [CollatzResearch.WordTrace]
  refine ⟨50231960111513037198417965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33487973407675358132278643 50231960111513037198417965)
  ·
    refine ⟨18836985041817388949406737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50231960111513037198417965 18836985041817388949406737)
    ·
      refine ⟨14127738781363041712055053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18836985041817388949406737 14127738781363041712055053)
      ·
        refine ⟨5297902043011140642020645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14127738781363041712055053 5297902043011140642020645)
        ·
          refine ⟨993356633064588870378871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5297902043011140642020645 993356633064588870378871)
          ·
            refine ⟨1490034949596883305568307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 993356633064588870378871 1490034949596883305568307)
            ·
              refine ⟨2235052424395324958352461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1490034949596883305568307 2235052424395324958352461)
              ·
                refine ⟨838144659148246859382173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2235052424395324958352461 838144659148246859382173)
                ·
                  refine ⟨314304247180592572268315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 838144659148246859382173 314304247180592572268315)
                  ·
                    rfl

theorem cell21_1377237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 3, 3].length) (baseStart_1377237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1377237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1377237 prefixEnd_1377237 := by exact prefixLift 1377237
  have htrace : WordTrace (prefixWord ++ tailWord_1377237) baseStart_1377237 baseEnd_1377237 := by
    simpa [prefixWord, tailWord_1377237, baseEnd_1377237] using wordTrace_append hprefix tailTrace_1377237
  have hstable : (prefixWord ++ tailWord_1377237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377237).length < 2 ^ (prefixWord ++ tailWord_1377237).sum := by decide
  have hdescent : baseEnd_1377237 < baseStart_1377237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377335 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 8]
def baseStart_1377335 : Nat := 118140960795 + 1377335 * 2 ^ 59
def prefixEnd_1377335 : Nat := 4983230072969 + 3 ^ 40 * 1377335 * 2
def baseEnd_1377335 : Nat := 314326612115766179634781

theorem tailTrace_1377335 : CollatzResearch.WordTrace tailWord_1377335 prefixEnd_1377335 314326612115766179634781 := by
  unfold tailWord_1377335
  simp only [CollatzResearch.WordTrace]
  refine ⟨50235534465157999935485459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33490356310105333290323639 50235534465157999935485459)
  ·
    refine ⟨75353301697736999903228189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50235534465157999935485459 75353301697736999903228189)
    ·
      refine ⟨28257488136651374963710571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75353301697736999903228189 28257488136651374963710571)
      ·
        refine ⟨42386232204977062445565857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28257488136651374963710571 42386232204977062445565857)
        ·
          refine ⟨31789674153732796834174393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42386232204977062445565857 31789674153732796834174393)
          ·
            refine ⟨23842255615299597625630795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31789674153732796834174393 23842255615299597625630795)
            ·
              refine ⟨35763383422949396438446193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23842255615299597625630795 35763383422949396438446193)
              ·
                refine ⟨26822537567212047328834645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35763383422949396438446193 26822537567212047328834645)
                ·
                  refine ⟨314326612115766179634781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26822537567212047328834645 314326612115766179634781)
                  ·
                    rfl

theorem cell21_1377335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 8].length) (baseStart_1377335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1377335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1377335 prefixEnd_1377335 := by exact prefixLift 1377335
  have htrace : WordTrace (prefixWord ++ tailWord_1377335) baseStart_1377335 baseEnd_1377335 := by
    simpa [prefixWord, tailWord_1377335, baseEnd_1377335] using wordTrace_append hprefix tailTrace_1377335
  have hstable : (prefixWord ++ tailWord_1377335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377335).length < 2 ^ (prefixWord ++ tailWord_1377335).sum := by decide
  have hdescent : baseEnd_1377335 < baseStart_1377335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377386 : List Nat := [3, 1, 3, 2, 2, 2, 3, 1, 4]
def baseStart_1377386 : Nat := 118140960795 + 1377386 * 2 ^ 59
def prefixEnd_1377386 : Nat := 4983230072969 + 3 ^ 40 * 1377386 * 2
def baseEnd_1377386 : Nat := 314338251010601424284677

theorem tailTrace_1377386 : CollatzResearch.WordTrace tailWord_1377386 prefixEnd_1377386 314338251010601424284677 := by
  unfold tailWord_1377386
  simp only [CollatzResearch.WordTrace]
  refine ⟨12559348646993308911398003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33491596391982157097061341 12559348646993308911398003)
  ·
    refine ⟨18839022970489963367097005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12559348646993308911398003 18839022970489963367097005)
    ·
      refine ⟨7064633613933736262661377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18839022970489963367097005 7064633613933736262661377)
      ·
        refine ⟨5298475210450302196996033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7064633613933736262661377 5298475210450302196996033)
        ·
          refine ⟨3973856407837726647747025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5298475210450302196996033 3973856407837726647747025)
          ·
            refine ⟨2980392305878294985810269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3973856407837726647747025 2980392305878294985810269)
            ·
              refine ⟨1117647114704360619678851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2980392305878294985810269 1117647114704360619678851)
              ·
                refine ⟨1676470672056540929518277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1117647114704360619678851 1676470672056540929518277)
                ·
                  refine ⟨314338251010601424284677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1676470672056540929518277 314338251010601424284677)
                  ·
                    rfl

theorem cell21_1377386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 1, 4].length) (baseStart_1377386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1377386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1377386 prefixEnd_1377386 := by exact prefixLift 1377386
  have htrace : WordTrace (prefixWord ++ tailWord_1377386) baseStart_1377386 baseEnd_1377386 := by
    simpa [prefixWord, tailWord_1377386, baseEnd_1377386] using wordTrace_append hprefix tailTrace_1377386
  have hstable : (prefixWord ++ tailWord_1377386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377386).length < 2 ^ (prefixWord ++ tailWord_1377386).sum := by decide
  have hdescent : baseEnd_1377386 < baseStart_1377386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377411 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 8]
def baseStart_1377411 : Nat := 118140960795 + 1377411 * 2 ^ 59
def prefixEnd_1377411 : Nat := 4983230072969 + 3 ^ 40 * 1377411 * 2
def baseEnd_1377411 : Nat := 314343956351206936367959

theorem tailTrace_1377411 : CollatzResearch.WordTrace tailWord_1377411 prefixEnd_1377411 314343956351206936367959 := by
  unfold tailWord_1377411
  simp only [CollatzResearch.WordTrace]
  refine ⟨50238306412882664915252087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33492204275255109943501391 50238306412882664915252087)
  ·
    refine ⟨75357459619323997372878131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50238306412882664915252087 75357459619323997372878131)
    ·
      refine ⟨113036189428985996059317197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75357459619323997372878131 113036189428985996059317197)
      ·
        refine ⟨42388571035869748522243949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113036189428985996059317197 42388571035869748522243949)
        ·
          refine ⟨15895714138451155695841481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42388571035869748522243949 15895714138451155695841481)
          ·
            refine ⟨11921785603838366771881111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15895714138451155695841481 11921785603838366771881111)
            ·
              refine ⟨17882678405757550157821667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11921785603838366771881111 17882678405757550157821667)
              ·
                refine ⟨26824017608636325236732501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17882678405757550157821667 26824017608636325236732501)
                ·
                  refine ⟨314343956351206936367959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26824017608636325236732501 314343956351206936367959)
                  ·
                    rfl

theorem cell21_1377411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 8].length) (baseStart_1377411 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1377411 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1377411 prefixEnd_1377411 := by exact prefixLift 1377411
  have htrace : WordTrace (prefixWord ++ tailWord_1377411) baseStart_1377411 baseEnd_1377411 := by
    simpa [prefixWord, tailWord_1377411, baseEnd_1377411] using wordTrace_append hprefix tailTrace_1377411
  have hstable : (prefixWord ++ tailWord_1377411).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377411).length < 2 ^ (prefixWord ++ tailWord_1377411).sum := by decide
  have hdescent : baseEnd_1377411 < baseStart_1377411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377445 : List Nat := [1, 3, 1, 2, 1, 4, 4, 1, 4]
def baseStart_1377445 : Nat := 118140960795 + 1377445 * 2 ^ 59
def prefixEnd_1377445 : Nat := 4983230072969 + 3 ^ 40 * 1377445 * 2
def baseEnd_1377445 : Nat := 314351715614430432801223

theorem tailTrace_1377445 : CollatzResearch.WordTrace tailWord_1377445 prefixEnd_1377445 314351715614430432801223 := by
  unfold tailWord_1377445
  simp only [CollatzResearch.WordTrace]
  refine ⟨50239546494759488721989789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33493030996506325814659859 50239546494759488721989789)
  ·
    refine ⟨18839829935534808270746171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50239546494759488721989789 18839829935534808270746171)
    ·
      refine ⟨28259744903302212406119257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18839829935534808270746171 28259744903302212406119257)
      ·
        refine ⟨21194808677476659304589443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28259744903302212406119257 21194808677476659304589443)
        ·
          refine ⟨31792213016214988956884165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21194808677476659304589443 31792213016214988956884165)
          ·
            refine ⟨5961039940540310429415781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31792213016214988956884165 5961039940540310429415781)
            ·
              refine ⟨1117694988851308205515459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5961039940540310429415781 1117694988851308205515459)
              ·
                refine ⟨1676542483276962308273189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1117694988851308205515459 1676542483276962308273189)
                ·
                  refine ⟨314351715614430432801223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1676542483276962308273189 314351715614430432801223)
                  ·
                    rfl

theorem cell21_1377445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 1, 4].length) (baseStart_1377445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1377445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1377445 prefixEnd_1377445 := by exact prefixLift 1377445
  have htrace : WordTrace (prefixWord ++ tailWord_1377445) baseStart_1377445 baseEnd_1377445 := by
    simpa [prefixWord, tailWord_1377445, baseEnd_1377445] using wordTrace_append hprefix tailTrace_1377445
  have hstable : (prefixWord ++ tailWord_1377445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377445).length < 2 ^ (prefixWord ++ tailWord_1377445).sum := by decide
  have hdescent : baseEnd_1377445 < baseStart_1377445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377504 : List Nat := [2, 1, 1, 3, 1, 4, 2, 3, 4]
def baseStart_1377504 : Nat := 118140960795 + 1377504 * 2 ^ 59
def prefixEnd_1377504 : Nat := 4983230072969 + 3 ^ 40 * 1377504 * 2
def baseEnd_1377504 : Nat := 314365180218259441317769

theorem tailTrace_1377504 : CollatzResearch.WordTrace tailWord_1377504 prefixEnd_1377504 314365180218259441317769 := by
  unfold tailWord_1377504
  simp only [CollatzResearch.WordTrace]
  refine ⟨25120849200772870899193783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33494465601030494532258377 25120849200772870899193783)
  ·
    refine ⟨37681273801159306348790675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25120849200772870899193783 37681273801159306348790675)
    ·
      refine ⟨56521910701738959523186013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37681273801159306348790675 56521910701738959523186013)
      ·
        refine ⟨21195716513152109821194755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56521910701738959523186013 21195716513152109821194755)
        ·
          refine ⟨31793574769728164731792133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21195716513152109821194755 31793574769728164731792133)
          ·
            refine ⟨5961295269324030887211025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31793574769728164731792133 5961295269324030887211025)
            ·
              refine ⟨4470971451993023165408269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5961295269324030887211025 4470971451993023165408269)
              ·
                refine ⟨1676614294497383687028101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4470971451993023165408269 1676614294497383687028101)
                ·
                  refine ⟨314365180218259441317769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1676614294497383687028101 314365180218259441317769)
                  ·
                    rfl

theorem cell21_1377504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 3, 4].length) (baseStart_1377504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1377504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1377504 prefixEnd_1377504 := by exact prefixLift 1377504
  have htrace : WordTrace (prefixWord ++ tailWord_1377504) baseStart_1377504 baseEnd_1377504 := by
    simpa [prefixWord, tailWord_1377504, baseEnd_1377504] using wordTrace_append hprefix tailTrace_1377504
  have hstable : (prefixWord ++ tailWord_1377504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377504).length < 2 ^ (prefixWord ++ tailWord_1377504).sum := by decide
  have hdescent : baseEnd_1377504 < baseStart_1377504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377518 : List Nat := [4, 1, 2, 1, 1, 1, 2, 9]
def baseStart_1377518 : Nat := 118140960795 + 1377518 * 2 ^ 59
def prefixEnd_1377518 : Nat := 4983230072969 + 3 ^ 40 * 1377518 * 2
def baseEnd_1377518 : Nat := 104789458402999509361469

theorem tailTrace_1377518 : CollatzResearch.WordTrace tailWord_1377518 prefixEnd_1377518 104789458402999509361469 := by
  unfold tailWord_1377518
  simp only [CollatzResearch.WordTrace]
  refine ⟨6280276127936877773674651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33494806015663348126264805 6280276127936877773674651)
  ·
    refine ⟨9420414191905316660511977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6280276127936877773674651 9420414191905316660511977)
    ·
      refine ⟨7065310643928987495383983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9420414191905316660511977 7065310643928987495383983)
      ·
        refine ⟨10597965965893481243075975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7065310643928987495383983 10597965965893481243075975)
        ·
          refine ⟨15896948948840221864613963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10597965965893481243075975 15896948948840221864613963)
          ·
            refine ⟨23845423423260332796920945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15896948948840221864613963 23845423423260332796920945)
            ·
              refine ⟨17884067567445249597690709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23845423423260332796920945 17884067567445249597690709)
              ·
                refine ⟨104789458402999509361469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17884067567445249597690709 104789458402999509361469)
                ·
                  rfl

theorem cell21_1377518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_1377518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1377518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1377518 prefixEnd_1377518 := by exact prefixLift 1377518
  have htrace : WordTrace (prefixWord ++ tailWord_1377518) baseStart_1377518 baseEnd_1377518 := by
    simpa [prefixWord, tailWord_1377518, baseEnd_1377518] using wordTrace_append hprefix tailTrace_1377518
  have hstable : (prefixWord ++ tailWord_1377518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377518).length < 2 ^ (prefixWord ++ tailWord_1377518).sum := by decide
  have hdescent : baseEnd_1377518 < baseStart_1377518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377662 : List Nat := [4, 2, 3, 2, 2, 1, 1, 6]
def baseStart_1377662 : Nat := 118140960795 + 1377662 * 2 ^ 59
def prefixEnd_1377662 : Nat := 4983230072969 + 3 ^ 40 * 1377662 * 2
def baseEnd_1377662 : Nat := 104800412656962092561371

theorem tailTrace_1377662 : CollatzResearch.WordTrace tailWord_1377662 prefixEnd_1377662 104800412656962092561371 := by
  unfold tailWord_1377662
  simp only [CollatzResearch.WordTrace]
  refine ⟨6280932641871666847829905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33498307423315556521759493 6280932641871666847829905)
  ·
    refine ⟨4710699481403750135872429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6280932641871666847829905 4710699481403750135872429)
    ·
      refine ⟨1766512305526406300952161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4710699481403750135872429 1766512305526406300952161)
      ·
        refine ⟨1324884229144804725714121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1766512305526406300952161 1324884229144804725714121)
        ·
          refine ⟨993663171858603544285591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1324884229144804725714121 993663171858603544285591)
          ·
            refine ⟨1490494757787905316428387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 993663171858603544285591 1490494757787905316428387)
            ·
              refine ⟨2235742136681857974642581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1490494757787905316428387 2235742136681857974642581)
              ·
                refine ⟨104800412656962092561371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2235742136681857974642581 104800412656962092561371)
                ·
                  rfl

theorem cell21_1377662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 6].length) (baseStart_1377662 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1377662 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1377662 prefixEnd_1377662 := by exact prefixLift 1377662
  have htrace : WordTrace (prefixWord ++ tailWord_1377662) baseStart_1377662 baseEnd_1377662 := by
    simpa [prefixWord, tailWord_1377662, baseEnd_1377662] using wordTrace_append hprefix tailTrace_1377662
  have hstable : (prefixWord ++ tailWord_1377662).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377662).length < 2 ^ (prefixWord ++ tailWord_1377662).sum := by decide
  have hdescent : baseEnd_1377662 < baseStart_1377662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377777 : List Nat := [1, 2, 2, 2, 3, 2, 3, 1, 5]
def baseStart_1377777 : Nat := 118140960795 + 1377777 * 2 ^ 59
def prefixEnd_1377777 : Nat := 4983230072969 + 3 ^ 40 * 1377777 * 2
def baseEnd_1377777 : Nat := 314427482537671633267211

theorem tailTrace_1377777 : CollatzResearch.WordTrace tailWord_1377777 prefixEnd_1377777 314427482537671633267211 := by
  unfold tailWord_1377777
  simp only [CollatzResearch.WordTrace]
  refine ⟨50251655529556709423075585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33501103686371139615383723 50251655529556709423075585)
  ·
    refine ⟨37688741647167532067306689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50251655529556709423075585 37688741647167532067306689)
    ·
      refine ⟨28266556235375649050480017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37688741647167532067306689 28266556235375649050480017)
      ·
        refine ⟨21199917176531736787860013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28266556235375649050480017 21199917176531736787860013)
        ·
          refine ⟨7949968941199401295447505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21199917176531736787860013 7949968941199401295447505)
          ·
            refine ⟨5962476705899550971585629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7949968941199401295447505 5962476705899550971585629)
            ·
              refine ⟨2235928764712331614344611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5962476705899550971585629 2235928764712331614344611)
              ·
                refine ⟨3353893147068497421516917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2235928764712331614344611 3353893147068497421516917)
                ·
                  refine ⟨314427482537671633267211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3353893147068497421516917 314427482537671633267211)
                  ·
                    rfl

theorem cell21_1377777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 5].length) (baseStart_1377777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1377777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1377777 prefixEnd_1377777 := by exact prefixLift 1377777
  have htrace : WordTrace (prefixWord ++ tailWord_1377777) baseStart_1377777 baseEnd_1377777 := by
    simpa [prefixWord, tailWord_1377777, baseEnd_1377777] using wordTrace_append hprefix tailTrace_1377777
  have hstable : (prefixWord ++ tailWord_1377777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377777).length < 2 ^ (prefixWord ++ tailWord_1377777).sum := by decide
  have hdescent : baseEnd_1377777 < baseStart_1377777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377884 : List Nat := [2, 2, 4, 1, 2, 2, 1, 1, 6]
def baseStart_1377884 : Nat := 118140960795 + 1377884 * 2 ^ 59
def prefixEnd_1377884 : Nat := 4983230072969 + 3 ^ 40 * 1377884 * 2
def baseEnd_1377884 : Nat := 314451901395463224983659

theorem tailTrace_1377884 : CollatzResearch.WordTrace tailWord_1377884 prefixEnd_1377884 314451901395463224983659 := by
  unfold tailWord_1377884
  simp only [CollatzResearch.WordTrace]
  refine ⟨25127779070084533348610353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33503705426779377798147137 25127779070084533348610353)
  ·
    refine ⟨18845834302563400011457765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25127779070084533348610353 18845834302563400011457765)
    ·
      refine ⟨3533593931730637502148331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18845834302563400011457765 3533593931730637502148331)
      ·
        refine ⟨5300390897595956253222497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3533593931730637502148331 5300390897595956253222497)
        ·
          refine ⟨3975293173196967189916873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5300390897595956253222497 3975293173196967189916873)
          ·
            refine ⟨2981469879897725392437655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3975293173196967189916873 2981469879897725392437655)
            ·
              refine ⟨4472204819846588088656483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2981469879897725392437655 4472204819846588088656483)
              ·
                refine ⟨6708307229769882132984725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4472204819846588088656483 6708307229769882132984725)
                ·
                  refine ⟨314451901395463224983659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6708307229769882132984725 314451901395463224983659)
                  ·
                    rfl

theorem cell21_1377884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 6].length) (baseStart_1377884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1377884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1377884 prefixEnd_1377884 := by exact prefixLift 1377884
  have htrace : WordTrace (prefixWord ++ tailWord_1377884) baseStart_1377884 baseEnd_1377884 := by
    simpa [prefixWord, tailWord_1377884, baseEnd_1377884] using wordTrace_append hprefix tailTrace_1377884
  have hstable : (prefixWord ++ tailWord_1377884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377884).length < 2 ^ (prefixWord ++ tailWord_1377884).sum := by decide
  have hdescent : baseEnd_1377884 < baseStart_1377884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377943 : List Nat := [1, 1, 3, 3, 2, 2, 2, 1, 6]
def baseStart_1377943 : Nat := 118140960795 + 1377943 * 2 ^ 59
def prefixEnd_1377943 : Nat := 4983230072969 + 3 ^ 40 * 1377943 * 2
def baseEnd_1377943 : Nat := 314465365999292233500205

theorem tailTrace_1377943 : CollatzResearch.WordTrace tailWord_1377943 prefixEnd_1377943 314465365999292233500205 := by
  unfold tailWord_1377943
  simp only [CollatzResearch.WordTrace]
  refine ⟨50257710046955319773618483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33505140031303546515745655 50257710046955319773618483)
  ·
    refine ⟨75386565070432979660427725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50257710046955319773618483 75386565070432979660427725)
    ·
      refine ⟨28269961901412367372660397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75386565070432979660427725 28269961901412367372660397)
      ·
        refine ⟨10601235713029637764747649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28269961901412367372660397 10601235713029637764747649)
        ·
          refine ⟨7950926784772228323560737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10601235713029637764747649 7950926784772228323560737)
          ·
            refine ⟨5963195088579171242670553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7950926784772228323560737 5963195088579171242670553)
            ·
              refine ⟨4472396316434378432002915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5963195088579171242670553 4472396316434378432002915)
              ·
                refine ⟨6708594474651567648004373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4472396316434378432002915 6708594474651567648004373)
                ·
                  refine ⟨314465365999292233500205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6708594474651567648004373 314465365999292233500205)
                  ·
                    rfl

theorem cell21_1377943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 6].length) (baseStart_1377943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1377943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1377943 prefixEnd_1377943 := by exact prefixLift 1377943
  have htrace : WordTrace (prefixWord ++ tailWord_1377943) baseStart_1377943 baseEnd_1377943 := by
    simpa [prefixWord, tailWord_1377943, baseEnd_1377943] using wordTrace_append hprefix tailTrace_1377943
  have hstable : (prefixWord ++ tailWord_1377943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377943).length < 2 ^ (prefixWord ++ tailWord_1377943).sum := by decide
  have hdescent : baseEnd_1377943 < baseStart_1377943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377957 : List Nat := [1, 3, 1, 2, 1, 2, 3, 8]
def baseStart_1377957 : Nat := 118140960795 + 1377957 * 2 ^ 59
def prefixEnd_1377957 : Nat := 4983230072969 + 3 ^ 40 * 1377957 * 2
def baseEnd_1377957 : Nat := 104822853663343773422281

theorem tailTrace_1377957 : CollatzResearch.WordTrace tailWord_1377957 prefixEnd_1377957 104822853663343773422281 := by
  unfold tailWord_1377957
  simp only [CollatzResearch.WordTrace]
  refine ⟨50258220668904600164628125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33505480445936400109752083 50258220668904600164628125)
  ·
    refine ⟨18846832750839225061735547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50258220668904600164628125 18846832750839225061735547)
    ·
      refine ⟨28270249126258837592603321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18846832750839225061735547 28270249126258837592603321)
      ·
        refine ⟨21202686844694128194452491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28270249126258837592603321 21202686844694128194452491)
        ·
          refine ⟨31804030267041192291678737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21202686844694128194452491 31804030267041192291678737)
          ·
            refine ⟨23853022700280894218759053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31804030267041192291678737 23853022700280894218759053)
            ·
              refine ⟨8944883512605335332034645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23853022700280894218759053 8944883512605335332034645)
              ·
                refine ⟨104822853663343773422281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8944883512605335332034645 104822853663343773422281)
                ·
                  rfl

theorem cell21_1377957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 8].length) (baseStart_1377957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1377957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1377957 prefixEnd_1377957 := by exact prefixLift 1377957
  have htrace : WordTrace (prefixWord ++ tailWord_1377957) baseStart_1377957 baseEnd_1377957 := by
    simpa [prefixWord, tailWord_1377957, baseEnd_1377957] using wordTrace_append hprefix tailTrace_1377957
  have hstable : (prefixWord ++ tailWord_1377957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377957).length < 2 ^ (prefixWord ++ tailWord_1377957).sum := by decide
  have hdescent : baseEnd_1377957 < baseStart_1377957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377997 : List Nat := [1, 6, 2, 1, 1, 3, 2, 2, 3]
def baseStart_1377997 : Nat := 118140960795 + 1377997 * 2 ^ 59
def prefixEnd_1377997 : Nat := 4983230072969 + 3 ^ 40 * 1377997 * 2
def baseEnd_1377997 : Nat := 314477689535000139600095

theorem tailTrace_1377997 : CollatzResearch.WordTrace tailWord_1377997 prefixEnd_1377997 314477689535000139600095 := by
  unfold tailWord_1377997
  simp only [CollatzResearch.WordTrace]
  refine ⟨50259679588759686996084245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33506453059173124664056163 50259679588759686996084245)
  ·
    refine ⟨2355922480723110327941449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 50259679588759686996084245 2355922480723110327941449)
    ·
      refine ⟨1766941860542332745956087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2355922480723110327941449 1766941860542332745956087)
      ·
        refine ⟨2650412790813499118934131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1766941860542332745956087 2650412790813499118934131)
        ·
          refine ⟨3975619186220248678401197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2650412790813499118934131 3975619186220248678401197)
          ·
            refine ⟨1490857194832593254400449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3975619186220248678401197 1490857194832593254400449)
            ·
              refine ⟨1118142896124444940800337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1490857194832593254400449 1118142896124444940800337)
              ·
                refine ⟨838607172093333705600253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1118142896124444940800337 838607172093333705600253)
                ·
                  refine ⟨314477689535000139600095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 838607172093333705600253 314477689535000139600095)
                  ·
                    rfl

theorem cell21_1377997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_1377997 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1377997 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1377997 prefixEnd_1377997 := by exact prefixLift 1377997
  have htrace : WordTrace (prefixWord ++ tailWord_1377997) baseStart_1377997 baseEnd_1377997 := by
    simpa [prefixWord, tailWord_1377997, baseEnd_1377997] using wordTrace_append hprefix tailTrace_1377997
  have hstable : (prefixWord ++ tailWord_1377997).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377997).length < 2 ^ (prefixWord ++ tailWord_1377997).sum := by decide
  have hdescent : baseEnd_1377997 < baseStart_1377997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378050 : List Nat := [3, 4, 1, 1, 1, 1, 10]
def baseStart_1378050 : Nat := 118140960795 + 1378050 * 2 ^ 59
def prefixEnd_1378050 : Nat := 4983230072969 + 3 ^ 40 * 1378050 * 2
def baseEnd_1378050 : Nat := 34943309428564869468517

theorem tailTrace_1378050 : CollatzResearch.WordTrace tailWord_1378050 prefixEnd_1378050 34943309428564869468517 := by
  unfold tailWord_1378050
  simp only [CollatzResearch.WordTrace]
  refine ⟨12565403164391919261940901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33507741771711784698509069 12565403164391919261940901)
  ·
    refine ⟨2356013093323484861613919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12565403164391919261940901 2356013093323484861613919)
    ·
      refine ⟨3534019639985227292420879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2356013093323484861613919 3534019639985227292420879)
      ·
        refine ⟨5301029459977840938631319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3534019639985227292420879 5301029459977840938631319)
        ·
          refine ⟨7951544189966761407946979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5301029459977840938631319 7951544189966761407946979)
          ·
            refine ⟨11927316284950142111920469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7951544189966761407946979 11927316284950142111920469)
            ·
              refine ⟨34943309428564869468517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11927316284950142111920469 34943309428564869468517)
              ·
                rfl

theorem cell21_1378050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 10].length) (baseStart_1378050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1378050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1378050 prefixEnd_1378050 := by exact prefixLift 1378050
  have htrace : WordTrace (prefixWord ++ tailWord_1378050) baseStart_1378050 baseEnd_1378050 := by
    simpa [prefixWord, tailWord_1378050, baseEnd_1378050] using wordTrace_append hprefix tailTrace_1378050
  have hstable : (prefixWord ++ tailWord_1378050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378050).length < 2 ^ (prefixWord ++ tailWord_1378050).sum := by decide
  have hdescent : baseEnd_1378050 < baseStart_1378050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378098 : List Nat := [3, 2, 1, 1, 3, 2, 3, 3, 3]
def baseStart_1378098 : Nat := 118140960795 + 1378098 * 2 ^ 59
def prefixEnd_1378098 : Nat := 4983230072969 + 3 ^ 40 * 1378098 * 2
def baseEnd_1378098 : Nat := 314500739111046408416555

theorem tailTrace_1378098 : CollatzResearch.WordTrace tailWord_1378098 prefixEnd_1378098 314500739111046408416555 := by
  unfold tailWord_1378098
  simp only [CollatzResearch.WordTrace]
  refine ⟨12565840840348445311377737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33508908907595854163673965 12565840840348445311377737)
  ·
    refine ⟨9424380630261333983533303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12565840840348445311377737 9424380630261333983533303)
    ·
      refine ⟨14136570945392000975299955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9424380630261333983533303 14136570945392000975299955)
      ·
        refine ⟨21204856418088001462949933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14136570945392000975299955 21204856418088001462949933)
        ·
          refine ⟨7951821156783000548606225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21204856418088001462949933 7951821156783000548606225)
          ·
            refine ⟨5963865867587250411454669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7951821156783000548606225 5963865867587250411454669)
            ·
              refine ⟨2236449700345218904295501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5963865867587250411454669 2236449700345218904295501)
              ·
                refine ⟨838668637629457089110813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2236449700345218904295501 838668637629457089110813)
                ·
                  refine ⟨314500739111046408416555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 838668637629457089110813 314500739111046408416555)
                  ·
                    rfl

theorem cell21_1378098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 3, 3].length) (baseStart_1378098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1378098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1378098 prefixEnd_1378098 := by exact prefixLift 1378098
  have htrace : WordTrace (prefixWord ++ tailWord_1378098) baseStart_1378098 baseEnd_1378098 := by
    simpa [prefixWord, tailWord_1378098, baseEnd_1378098] using wordTrace_append hprefix tailTrace_1378098
  have hstable : (prefixWord ++ tailWord_1378098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378098).length < 2 ^ (prefixWord ++ tailWord_1378098).sum := by decide
  have hdescent : baseEnd_1378098 < baseStart_1378098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378129 : List Nat := [1, 2, 2, 1, 5, 3, 2, 1, 4]
def baseStart_1378129 : Nat := 118140960795 + 1378129 * 2 ^ 59
def prefixEnd_1378129 : Nat := 4983230072969 + 3 ^ 40 * 1378129 * 2
def baseEnd_1378129 : Nat := 314507813733397243399825

theorem tailTrace_1378129 : CollatzResearch.WordTrace tailWord_1378129 prefixEnd_1378129 314507813733397243399825 := by
  unfold tailWord_1378129
  simp only [CollatzResearch.WordTrace]
  refine ⟨50264494024281473539889441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33509662682854315693259627 50264494024281473539889441)
  ·
    refine ⟨37698370518211105154917081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50264494024281473539889441 37698370518211105154917081)
    ·
      refine ⟨28273777888658328866187811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37698370518211105154917081 28273777888658328866187811)
      ·
        refine ⟨42410666832987493299281717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28273777888658328866187811 42410666832987493299281717)
        ·
          refine ⟨3976000015592577496807661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42410666832987493299281717 3976000015592577496807661)
          ·
            refine ⟨1491000005847216561302873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3976000015592577496807661 1491000005847216561302873)
            ·
              refine ⟨1118250004385412420977155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1491000005847216561302873 1118250004385412420977155)
              ·
                refine ⟨1677375006578118631465733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1118250004385412420977155 1677375006578118631465733)
                ·
                  refine ⟨314507813733397243399825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1677375006578118631465733 314507813733397243399825)
                  ·
                    rfl

theorem cell21_1378129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 1, 4].length) (baseStart_1378129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1378129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1378129 prefixEnd_1378129 := by exact prefixLift 1378129
  have htrace : WordTrace (prefixWord ++ tailWord_1378129) baseStart_1378129 baseEnd_1378129 := by
    simpa [prefixWord, tailWord_1378129, baseEnd_1378129] using wordTrace_append hprefix tailTrace_1378129
  have hstable : (prefixWord ++ tailWord_1378129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378129).length < 2 ^ (prefixWord ++ tailWord_1378129).sum := by decide
  have hdescent : baseEnd_1378129 < baseStart_1378129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378222 : List Nat := [4, 1, 5, 1, 1, 1, 1, 1, 6]
def baseStart_1378222 : Nat := 118140960795 + 1378222 * 2 ^ 59
def prefixEnd_1378222 : Nat := 4983230072969 + 3 ^ 40 * 1378222 * 2
def baseEnd_1378222 : Nat := 314529037600449748349635

theorem tailTrace_1378222 : CollatzResearch.WordTrace tailWord_1378222 prefixEnd_1378222 314529037600449748349635 := by
  unfold tailWord_1378222
  simp only [CollatzResearch.WordTrace]
  refine ⟨6283485751618068802878115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33511924008629700282016613 6283485751618068802878115)
  ·
    refine ⟨9425228627427103204317173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6283485751618068802878115 9425228627427103204317173)
    ·
      refine ⟨883615183821290925404735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9425228627427103204317173 883615183821290925404735)
      ·
        refine ⟨1325422775731936388107103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 883615183821290925404735 1325422775731936388107103)
        ·
          refine ⟨1988134163597904582160655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1325422775731936388107103 1988134163597904582160655)
          ·
            refine ⟨2982201245396856873240983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1988134163597904582160655 2982201245396856873240983)
            ·
              refine ⟨4473301868095285309861475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2982201245396856873240983 4473301868095285309861475)
              ·
                refine ⟨6709952802142927964792213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4473301868095285309861475 6709952802142927964792213)
                ·
                  refine ⟨314529037600449748349635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6709952802142927964792213 314529037600449748349635)
                  ·
                    rfl

theorem cell21_1378222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 6].length) (baseStart_1378222 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1378222 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1378222 prefixEnd_1378222 := by exact prefixLift 1378222
  have htrace : WordTrace (prefixWord ++ tailWord_1378222) baseStart_1378222 baseEnd_1378222 := by
    simpa [prefixWord, tailWord_1378222, baseEnd_1378222] using wordTrace_append hprefix tailTrace_1378222
  have hstable : (prefixWord ++ tailWord_1378222).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378222).length < 2 ^ (prefixWord ++ tailWord_1378222).sum := by decide
  have hdescent : baseEnd_1378222 < baseStart_1378222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378233 : List Nat := [1, 2, 1, 4, 2, 1, 1, 6, 3]
def baseStart_1378233 : Nat := 118140960795 + 1378233 * 2 ^ 59
def prefixEnd_1378233 : Nat := 4983230072969 + 3 ^ 40 * 1378233 * 2
def baseEnd_1378233 : Nat := 314531547950316173666279

theorem tailTrace_1378233 : CollatzResearch.WordTrace tailWord_1378233 prefixEnd_1378233 314531547950316173666279 := by
  unfold tailWord_1378233
  simp only [CollatzResearch.WordTrace]
  refine ⟨50268287215904699301675353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33512191477269799534450235 50268287215904699301675353)
  ·
    refine ⟨37701215411928524476256515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50268287215904699301675353 37701215411928524476256515)
    ·
      refine ⟨56551823117892786714384773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37701215411928524476256515 56551823117892786714384773)
      ·
        refine ⟨10603466834604897508947145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56551823117892786714384773 10603466834604897508947145)
        ·
          refine ⟨7952600125953673131710359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10603466834604897508947145 7952600125953673131710359)
          ·
            refine ⟨11928900188930509697565539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7952600125953673131710359 11928900188930509697565539)
            ·
              refine ⟨17893350283395764546348309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11928900188930509697565539 17893350283395764546348309)
              ·
                refine ⟨838750794534176463110077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17893350283395764546348309 838750794534176463110077)
                ·
                  refine ⟨314531547950316173666279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 838750794534176463110077 314531547950316173666279)
                  ·
                    rfl

theorem cell21_1378233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 6, 3].length) (baseStart_1378233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1378233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1378233 prefixEnd_1378233 := by exact prefixLift 1378233
  have htrace : WordTrace (prefixWord ++ tailWord_1378233) baseStart_1378233 baseEnd_1378233 := by
    simpa [prefixWord, tailWord_1378233, baseEnd_1378233] using wordTrace_append hprefix tailTrace_1378233
  have hstable : (prefixWord ++ tailWord_1378233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378233).length < 2 ^ (prefixWord ++ tailWord_1378233).sum := by decide
  have hdescent : baseEnd_1378233 < baseStart_1378233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378337 : List Nat := [1, 2, 3, 2, 4, 9]
def baseStart_1378337 : Nat := 118140960795 + 1378337 * 2 ^ 59
def prefixEnd_1378337 : Nat := 4983230072969 + 3 ^ 40 * 1378337 * 2
def baseEnd_1378337 : Nat := 11650195635823522367879

theorem tailTrace_1378337 : CollatzResearch.WordTrace tailWord_1378337 prefixEnd_1378337 11650195635823522367879 := by
  unfold tailWord_1378337
  simp only [CollatzResearch.WordTrace]
  refine ⟨50272080407527925063461265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33514720271685283375640843 50272080407527925063461265)
  ·
    refine ⟨37704060305645943797595949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50272080407527925063461265 37704060305645943797595949)
    ·
      refine ⟨14139022614617228924098481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37704060305645943797595949 14139022614617228924098481)
      ·
        refine ⟨10604266960962921693073861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14139022614617228924098481 10604266960962921693073861)
        ·
          refine ⟨1988300055180547817451349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10604266960962921693073861 1988300055180547817451349)
          ·
            refine ⟨11650195635823522367879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1988300055180547817451349 11650195635823522367879)
            ·
              rfl

theorem cell21_1378337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 9].length) (baseStart_1378337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1378337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1378337 prefixEnd_1378337 := by exact prefixLift 1378337
  have htrace : WordTrace (prefixWord ++ tailWord_1378337) baseStart_1378337 baseEnd_1378337 := by
    simpa [prefixWord, tailWord_1378337, baseEnd_1378337] using wordTrace_append hprefix tailTrace_1378337
  have hstable : (prefixWord ++ tailWord_1378337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378337).length < 2 ^ (prefixWord ++ tailWord_1378337).sum := by decide
  have hdescent : baseEnd_1378337 < baseStart_1378337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378343 : List Nat := [1, 1, 7, 1, 2, 1, 1, 4, 3]
def baseStart_1378343 : Nat := 118140960795 + 1378343 * 2 ^ 59
def prefixEnd_1378343 : Nat := 4983230072969 + 3 ^ 40 * 1378343 * 2
def baseEnd_1378343 : Nat := 314556651448980426832721

theorem tailTrace_1378343 : CollatzResearch.WordTrace tailWord_1378343 prefixEnd_1378343 314556651448980426832721 := by
  unfold tailWord_1378343
  simp only [CollatzResearch.WordTrace]
  refine ⟨50272299245506188088179683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33514866163670792058786455 50272299245506188088179683)
  ·
    refine ⟨75408448868259282132269525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50272299245506188088179683 75408448868259282132269525)
    ·
      refine ⟨1767385520349826924975067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 75408448868259282132269525 1767385520349826924975067)
      ·
        refine ⟨2651078280524740387462601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1767385520349826924975067 2651078280524740387462601)
        ·
          refine ⟨1988308710393555290596951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2651078280524740387462601 1988308710393555290596951)
          ·
            refine ⟨2982463065590332935895427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1988308710393555290596951 2982463065590332935895427)
            ·
              refine ⟨4473694598385499403843141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2982463065590332935895427 4473694598385499403843141)
              ·
                refine ⟨838817737197281138220589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4473694598385499403843141 838817737197281138220589)
                ·
                  refine ⟨314556651448980426832721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 838817737197281138220589 314556651448980426832721)
                  ·
                    rfl

theorem cell21_1378343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 4, 3].length) (baseStart_1378343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1378343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1378343 prefixEnd_1378343 := by exact prefixLift 1378343
  have htrace : WordTrace (prefixWord ++ tailWord_1378343) baseStart_1378343 baseEnd_1378343 := by
    simpa [prefixWord, tailWord_1378343, baseEnd_1378343] using wordTrace_append hprefix tailTrace_1378343
  have hstable : (prefixWord ++ tailWord_1378343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378343).length < 2 ^ (prefixWord ++ tailWord_1378343).sum := by decide
  have hdescent : baseEnd_1378343 < baseStart_1378343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378354 : List Nat := [3, 2, 1, 1, 2, 5, 1, 6]
def baseStart_1378354 : Nat := 118140960795 + 1378354 * 2 ^ 59
def prefixEnd_1378354 : Nat := 4983230072969 + 3 ^ 40 * 1378354 * 2
def baseEnd_1378354 : Nat := 104853053932948950716455

theorem tailTrace_1378354 : CollatzResearch.WordTrace tailWord_1378354 prefixEnd_1378354 104853053932948950716455 := by
  unfold tailWord_1378354
  simp only [CollatzResearch.WordTrace]
  refine ⟨12568175112116584241707529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33515133632310891311220077 12568175112116584241707529)
  ·
    refine ⟨9426131334087438181280647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12568175112116584241707529 9426131334087438181280647)
    ·
      refine ⟨14139197001131157271920971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9426131334087438181280647 14139197001131157271920971)
      ·
        refine ⟨21208795501696735907881457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14139197001131157271920971 21208795501696735907881457)
        ·
          refine ⟨15906596626272551930911093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21208795501696735907881457 15906596626272551930911093)
          ·
            refine ⟨1491243433713051743522915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15906596626272551930911093 1491243433713051743522915)
            ·
              refine ⟨2236865150569577615284373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1491243433713051743522915 2236865150569577615284373)
              ·
                refine ⟨104853053932948950716455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2236865150569577615284373 104853053932948950716455)
                ·
                  rfl

theorem cell21_1378354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 6].length) (baseStart_1378354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1378354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1378354 prefixEnd_1378354 := by exact prefixLift 1378354
  have htrace : WordTrace (prefixWord ++ tailWord_1378354) baseStart_1378354 baseEnd_1378354 := by
    simpa [prefixWord, tailWord_1378354, baseEnd_1378354] using wordTrace_append hprefix tailTrace_1378354
  have hstable : (prefixWord ++ tailWord_1378354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378354).length < 2 ^ (prefixWord ++ tailWord_1378354).sum := by decide
  have hdescent : baseEnd_1378354 < baseStart_1378354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378368 : List Nat := [2, 1, 1, 2, 2, 5, 1, 2, 5]
def baseStart_1378368 : Nat := 118140960795 + 1378368 * 2 ^ 59
def prefixEnd_1378368 : Nat := 4983230072969 + 3 ^ 40 * 1378368 * 2
def baseEnd_1378368 : Nat := 314562356789585938916003

theorem tailTrace_1378368 : CollatzResearch.WordTrace tailWord_1378368 prefixEnd_1378368 314562356789585938916003 := by
  unfold tailWord_1378368
  simp only [CollatzResearch.WordTrace]
  refine ⟨25136605535207808678919879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33515474046943744905226505 25136605535207808678919879)
  ·
    refine ⟨37704908302811713018379819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25136605535207808678919879 37704908302811713018379819)
    ·
      refine ⟨56557362454217569527569729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37704908302811713018379819 56557362454217569527569729)
      ·
        refine ⟨42418021840663177145677297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56557362454217569527569729 42418021840663177145677297)
        ·
          refine ⟨31813516380497382859257973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42418021840663177145677297 31813516380497382859257973)
          ·
            refine ⟨2982517160671629643055435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31813516380497382859257973 2982517160671629643055435)
            ·
              refine ⟨4473775741007444464583153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2982517160671629643055435 4473775741007444464583153)
              ·
                refine ⟨3355331805755583348437365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4473775741007444464583153 3355331805755583348437365)
                ·
                  refine ⟨314562356789585938916003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3355331805755583348437365 314562356789585938916003)
                  ·
                    rfl

theorem cell21_1378368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 5].length) (baseStart_1378368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1378368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1378368 prefixEnd_1378368 := by exact prefixLift 1378368
  have htrace : WordTrace (prefixWord ++ tailWord_1378368) baseStart_1378368 baseEnd_1378368 := by
    simpa [prefixWord, tailWord_1378368, baseEnd_1378368] using wordTrace_append hprefix tailTrace_1378368
  have hstable : (prefixWord ++ tailWord_1378368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378368).length < 2 ^ (prefixWord ++ tailWord_1378368).sum := by decide
  have hdescent : baseEnd_1378368 < baseStart_1378368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378402 : List Nat := [3, 3, 2, 2, 2, 1, 2, 1, 5]
def baseStart_1378402 : Nat := 118140960795 + 1378402 * 2 ^ 59
def prefixEnd_1378402 : Nat := 4983230072969 + 3 ^ 40 * 1378402 * 2
def baseEnd_1378402 : Nat := 314570116052809435349267

theorem tailTrace_1378402 : CollatzResearch.WordTrace tailWord_1378402 prefixEnd_1378402 314570116052809435349267 := by
  unfold tailWord_1378402
  simp only [CollatzResearch.WordTrace]
  refine ⟨12568612788073110291144365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33516300768194960776384973 12568612788073110291144365)
  ·
    refine ⟨4713229795527416359179137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12568612788073110291144365 4713229795527416359179137)
    ·
      refine ⟨3534922346645562269384353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4713229795527416359179137 3534922346645562269384353)
      ·
        refine ⟨2651191759984171702038265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3534922346645562269384353 2651191759984171702038265)
        ·
          refine ⟨1988393819988128776528699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2651191759984171702038265 1988393819988128776528699)
          ·
            refine ⟨2982590729982193164793049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1988393819988128776528699 2982590729982193164793049)
            ·
              refine ⟨2236943047486644873594787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2982590729982193164793049 2236943047486644873594787)
              ·
                refine ⟨3355414571229967310392181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2236943047486644873594787 3355414571229967310392181)
                ·
                  refine ⟨314570116052809435349267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3355414571229967310392181 314570116052809435349267)
                  ·
                    rfl

theorem cell21_1378402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_1378402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1378402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1378402 prefixEnd_1378402 := by exact prefixLift 1378402
  have htrace : WordTrace (prefixWord ++ tailWord_1378402) baseStart_1378402 baseEnd_1378402 := by
    simpa [prefixWord, tailWord_1378402, baseEnd_1378402] using wordTrace_append hprefix tailTrace_1378402
  have hstable : (prefixWord ++ tailWord_1378402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378402).length < 2 ^ (prefixWord ++ tailWord_1378402).sum := by decide
  have hdescent : baseEnd_1378402 < baseStart_1378402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378413 : List Nat := [1, 5, 1, 1, 2, 1, 2, 8]
def baseStart_1378413 : Nat := 118140960795 + 1378413 * 2 ^ 59
def prefixEnd_1378413 : Nat := 4983230072969 + 3 ^ 40 * 1378413 * 2
def baseEnd_1378413 : Nat := 104857542134225286888637

theorem tailTrace_1378413 : CollatzResearch.WordTrace tailWord_1378413 prefixEnd_1378413 104857542134225286888637 := by
  unfold tailWord_1378413
  simp only [CollatzResearch.WordTrace]
  refine ⟨50274852355252590043227893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33516568236835060028818595 50274852355252590043227893)
  ·
    refine ⟨4713267408304930316552615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50274852355252590043227893 4713267408304930316552615)
    ·
      refine ⟨7069901112457395474828923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4713267408304930316552615 7069901112457395474828923)
      ·
        refine ⟨10604851668686093212243385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7069901112457395474828923 10604851668686093212243385)
        ·
          refine ⟨7953638751514569909182539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10604851668686093212243385 7953638751514569909182539)
          ·
            refine ⟨11930458127271854863773809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7953638751514569909182539 11930458127271854863773809)
            ·
              refine ⟨8947843595453891147830357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11930458127271854863773809 8947843595453891147830357)
              ·
                refine ⟨104857542134225286888637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8947843595453891147830357 104857542134225286888637)
                ·
                  rfl

theorem cell21_1378413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 8].length) (baseStart_1378413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1378413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1378413 prefixEnd_1378413 := by exact prefixLift 1378413
  have htrace : WordTrace (prefixWord ++ tailWord_1378413) baseStart_1378413 baseEnd_1378413 := by
    simpa [prefixWord, tailWord_1378413, baseEnd_1378413] using wordTrace_append hprefix tailTrace_1378413
  have hstable : (prefixWord ++ tailWord_1378413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378413).length < 2 ^ (prefixWord ++ tailWord_1378413).sum := by decide
  have hdescent : baseEnd_1378413 < baseStart_1378413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378416 : List Nat := [2, 1, 1, 1, 5, 3, 3, 1, 4]
def baseStart_1378416 : Nat := 118140960795 + 1378416 * 2 ^ 59
def prefixEnd_1378416 : Nat := 4983230072969 + 3 ^ 40 * 1378416 * 2
def baseEnd_1378416 : Nat := 314573311043548522115905

theorem tailTrace_1378416 : CollatzResearch.WordTrace tailWord_1378416 prefixEnd_1378416 314573311043548522115905 := by
  unfold tailWord_1378416
  simp only [CollatzResearch.WordTrace]
  refine ⟨25137480887120860777793551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33516641182827814370391401 25137480887120860777793551)
  ·
    refine ⟨37706221330681291166690327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25137480887120860777793551 37706221330681291166690327)
    ·
      refine ⟨56559331996021936750035491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37706221330681291166690327 56559331996021936750035491)
      ·
        refine ⟨84838997994032905125053237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56559331996021936750035491 84838997994032905125053237)
        ·
          refine ⟨7953656061940584855473741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84838997994032905125053237 7953656061940584855473741)
          ·
            refine ⟨2982621023227719320802653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7953656061940584855473741 2982621023227719320802653)
            ·
              refine ⟨1118482883710394745300995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2982621023227719320802653 1118482883710394745300995)
              ·
                refine ⟨1677724325565592117951493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1118482883710394745300995 1677724325565592117951493)
                ·
                  refine ⟨314573311043548522115905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1677724325565592117951493 314573311043548522115905)
                  ·
                    rfl

theorem cell21_1378416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 1, 4].length) (baseStart_1378416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1378416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1378416 prefixEnd_1378416 := by exact prefixLift 1378416
  have htrace : WordTrace (prefixWord ++ tailWord_1378416) baseStart_1378416 baseEnd_1378416 := by
    simpa [prefixWord, tailWord_1378416, baseEnd_1378416] using wordTrace_append hprefix tailTrace_1378416
  have hstable : (prefixWord ++ tailWord_1378416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378416).length < 2 ^ (prefixWord ++ tailWord_1378416).sum := by decide
  have hdescent : baseEnd_1378416 < baseStart_1378416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378461 : List Nat := [1, 4, 2, 1, 1, 5, 1, 1, 5]
def baseStart_1378461 : Nat := 118140960795 + 1378461 * 2 ^ 59
def prefixEnd_1378461 : Nat := 4983230072969 + 3 ^ 40 * 1378461 * 2
def baseEnd_1378461 : Nat := 314583580656638443865813

theorem tailTrace_1378461 : CollatzResearch.WordTrace tailWord_1378461 prefixEnd_1378461 314583580656638443865813 := by
  unfold tailWord_1378461
  simp only [CollatzResearch.WordTrace]
  refine ⟨50276603059078694240975237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33517735372719129493983491 50276603059078694240975237)
  ·
    refine ⟨9426863073577255170182857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50276603059078694240975237 9426863073577255170182857)
    ·
      refine ⟨7070147305182941377637143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9426863073577255170182857 7070147305182941377637143)
      ·
        refine ⟨10605220957774412066455715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7070147305182941377637143 10605220957774412066455715)
        ·
          refine ⟨15907831436661618099683573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10605220957774412066455715 15907831436661618099683573)
          ·
            refine ⟨1491359197187026696845335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15907831436661618099683573 1491359197187026696845335)
            ·
              refine ⟨2237038795780540045268003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1491359197187026696845335 2237038795780540045268003)
              ·
                refine ⟨3355558193670810067902005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2237038795780540045268003 3355558193670810067902005)
                ·
                  refine ⟨314583580656638443865813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3355558193670810067902005 314583580656638443865813)
                  ·
                    rfl

theorem cell21_1378461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_1378461 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1378461 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1378461 prefixEnd_1378461 := by exact prefixLift 1378461
  have htrace : WordTrace (prefixWord ++ tailWord_1378461) baseStart_1378461 baseEnd_1378461 := by
    simpa [prefixWord, tailWord_1378461, baseEnd_1378461] using wordTrace_append hprefix tailTrace_1378461
  have hstable : (prefixWord ++ tailWord_1378461).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378461).length < 2 ^ (prefixWord ++ tailWord_1378461).sum := by decide
  have hdescent : baseEnd_1378461 < baseStart_1378461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378568 : List Nat := [2, 1, 3, 2, 3, 3, 1, 2, 4]
def baseStart_1378568 : Nat := 118140960795 + 1378568 * 2 ^ 59
def prefixEnd_1378568 : Nat := 4983230072969 + 3 ^ 40 * 1378568 * 2
def baseEnd_1378568 : Nat := 314607999514430035582261

theorem tailTrace_1378568 : CollatzResearch.WordTrace tailWord_1378568 prefixEnd_1378568 314607999514430035582261 := by
  unfold tailWord_1378568
  simp only [CollatzResearch.WordTrace]
  refine ⟨25140252834845525757560179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33520337113127367676746905 25140252834845525757560179)
  ·
    refine ⟨37710379252268288636340269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25140252834845525757560179 37710379252268288636340269)
    ·
      refine ⟨14141392219600608238627601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37710379252268288636340269 14141392219600608238627601)
      ·
        refine ⟨10606044164700456178970701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14141392219600608238627601 10606044164700456178970701)
        ·
          refine ⟨3977266561762671067114013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10606044164700456178970701 3977266561762671067114013)
          ·
            refine ⟨1491474960661001650167755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3977266561762671067114013 1491474960661001650167755)
            ·
              refine ⟨2237212440991502475251633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1491474960661001650167755 2237212440991502475251633)
              ·
                refine ⟨1677909330743626856438725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2237212440991502475251633 1677909330743626856438725)
                ·
                  refine ⟨314607999514430035582261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1677909330743626856438725 314607999514430035582261)
                  ·
                    rfl

theorem cell21_1378568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 2, 4].length) (baseStart_1378568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1378568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1378568 prefixEnd_1378568 := by exact prefixLift 1378568
  have htrace : WordTrace (prefixWord ++ tailWord_1378568) baseStart_1378568 baseEnd_1378568 := by
    simpa [prefixWord, tailWord_1378568, baseEnd_1378568] using wordTrace_append hprefix tailTrace_1378568
  have hstable : (prefixWord ++ tailWord_1378568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378568).length < 2 ^ (prefixWord ++ tailWord_1378568).sum := by decide
  have hdescent : baseEnd_1378568 < baseStart_1378568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378596 : List Nat := [2, 3, 1, 3, 1, 2, 2, 2, 5]
def baseStart_1378596 : Nat := 118140960795 + 1378596 * 2 ^ 59
def prefixEnd_1378596 : Nat := 4983230072969 + 3 ^ 40 * 1378596 * 2
def baseEnd_1378596 : Nat := 314614389495908209115537

theorem tailTrace_1378596 : CollatzResearch.WordTrace tailWord_1378596 prefixEnd_1378596 314614389495908209115537 := by
  unfold tailWord_1378596
  simp only [CollatzResearch.WordTrace]
  refine ⟨25140763456794806148569821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33521017942393074864759761 25140763456794806148569821)
  ·
    refine ⟨9427786296298052305713683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25140763456794806148569821 9427786296298052305713683)
    ·
      refine ⟨14141679444447078458570525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9427786296298052305713683 14141679444447078458570525)
      ·
        refine ⟨5303129791667654421963947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14141679444447078458570525 5303129791667654421963947)
        ·
          refine ⟨7954694687501481632945921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5303129791667654421963947 7954694687501481632945921)
          ·
            refine ⟨5966021015626111224709441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7954694687501481632945921 5966021015626111224709441)
            ·
              refine ⟨4474515761719583418532081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5966021015626111224709441 4474515761719583418532081)
              ·
                refine ⟨3355886821289687563899061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4474515761719583418532081 3355886821289687563899061)
                ·
                  refine ⟨314614389495908209115537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3355886821289687563899061 314614389495908209115537)
                  ·
                    rfl

theorem cell21_1378596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_1378596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1378596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1378596 prefixEnd_1378596 := by exact prefixLift 1378596
  have htrace : WordTrace (prefixWord ++ tailWord_1378596) baseStart_1378596 baseEnd_1378596 := by
    simpa [prefixWord, tailWord_1378596, baseEnd_1378596] using wordTrace_append hprefix tailTrace_1378596
  have hstable : (prefixWord ++ tailWord_1378596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378596).length < 2 ^ (prefixWord ++ tailWord_1378596).sum := by decide
  have hdescent : baseEnd_1378596 < baseStart_1378596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378641 : List Nat := [1, 2, 2, 1, 4, 3, 2, 6]
def baseStart_1378641 : Nat := 118140960795 + 1378641 * 2 ^ 59
def prefixEnd_1378641 : Nat := 4983230072969 + 3 ^ 40 * 1378641 * 2
def baseEnd_1378641 : Nat := 104874886369666043621815

theorem tailTrace_1378641 : CollatzResearch.WordTrace tailWord_1378641 prefixEnd_1378641 104874886369666043621815 := by
  unfold tailWord_1378641
  simp only [CollatzResearch.WordTrace]
  refine ⟨50283168198426584982527777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33522112132284389988351851 50283168198426584982527777)
  ·
    refine ⟨37712376148819938736895833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50283168198426584982527777 37712376148819938736895833)
    ·
      refine ⟨28284282111614954052671875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37712376148819938736895833 28284282111614954052671875)
      ·
        refine ⟨42426423167422431079007813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28284282111614954052671875 42426423167422431079007813)
        ·
          refine ⟨7954954343891705827313965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42426423167422431079007813 7954954343891705827313965)
          ·
            refine ⟨2983107878959389685242737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7954954343891705827313965 2983107878959389685242737)
            ·
              refine ⟨2237330909219542263932053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2983107878959389685242737 2237330909219542263932053)
              ·
                refine ⟨104874886369666043621815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2237330909219542263932053 104874886369666043621815)
                ·
                  rfl

theorem cell21_1378641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 6].length) (baseStart_1378641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1378641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1378641 prefixEnd_1378641 := by exact prefixLift 1378641
  have htrace : WordTrace (prefixWord ++ tailWord_1378641) baseStart_1378641 baseEnd_1378641 := by
    simpa [prefixWord, tailWord_1378641, baseEnd_1378641] using wordTrace_append hprefix tailTrace_1378641
  have hstable : (prefixWord ++ tailWord_1378641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378641).length < 2 ^ (prefixWord ++ tailWord_1378641).sum := by decide
  have hdescent : baseEnd_1378641 < baseStart_1378641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378644 : List Nat := [2, 4, 1, 1, 2, 2, 4, 1, 4]
def baseStart_1378644 : Nat := 118140960795 + 1378644 * 2 ^ 59
def prefixEnd_1378644 : Nat := 4983230072969 + 3 ^ 40 * 1378644 * 2
def baseEnd_1378644 : Nat := 314625343749870792315439

theorem tailTrace_1378644 : CollatzResearch.WordTrace tailWord_1378644 prefixEnd_1378644 314625343749870792315439 := by
  unfold tailWord_1378644
  simp only [CollatzResearch.WordTrace]
  refine ⟨25141638808707858247443493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33522185078277144329924657 25141638808707858247443493)
  ·
    refine ⟨4714057276632723421395655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25141638808707858247443493 4714057276632723421395655)
    ·
      refine ⟨7071085914949085132093483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4714057276632723421395655 7071085914949085132093483)
      ·
        refine ⟨10606628872423627698140225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7071085914949085132093483 10606628872423627698140225)
        ·
          refine ⟨7954971654317720773605169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10606628872423627698140225 7954971654317720773605169)
          ·
            refine ⟨5966228740738290580203877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7954971654317720773605169 5966228740738290580203877)
            ·
              refine ⟨1118667888888429483788227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5966228740738290580203877 1118667888888429483788227)
              ·
                refine ⟨1678001833332644225682341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1118667888888429483788227 1678001833332644225682341)
                ·
                  refine ⟨314625343749870792315439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1678001833332644225682341 314625343749870792315439)
                  ·
                    rfl

theorem cell21_1378644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_1378644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1378644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1378644 prefixEnd_1378644 := by exact prefixLift 1378644
  have htrace : WordTrace (prefixWord ++ tailWord_1378644) baseStart_1378644 baseEnd_1378644 := by
    simpa [prefixWord, tailWord_1378644, baseEnd_1378644] using wordTrace_append hprefix tailTrace_1378644
  have hstable : (prefixWord ++ tailWord_1378644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378644).length < 2 ^ (prefixWord ++ tailWord_1378644).sum := by decide
  have hdescent : baseEnd_1378644 < baseStart_1378644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378655 : List Nat := [1, 1, 2, 3, 1, 2, 2, 4, 5]
def baseStart_1378655 : Nat := 118140960795 + 1378655 * 2 ^ 59
def prefixEnd_1378655 : Nat := 4983230072969 + 3 ^ 40 * 1378655 * 2
def baseEnd_1378655 : Nat := 314627854099737217632083

theorem tailTrace_1378655 : CollatzResearch.WordTrace tailWord_1378655 prefixEnd_1378655 314627854099737217632083 := by
  unfold tailWord_1378655
  simp only [CollatzResearch.WordTrace]
  refine ⟨50283678820375865373537419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33522452546917243582358279 50283678820375865373537419)
  ·
    refine ⟨75425518230563798060306129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50283678820375865373537419 75425518230563798060306129)
    ·
      refine ⟨56569138672922848545229597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75425518230563798060306129 56569138672922848545229597)
      ·
        refine ⟨21213427002346068204461099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56569138672922848545229597 21213427002346068204461099)
        ·
          refine ⟨31820140503519102306691649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21213427002346068204461099 31820140503519102306691649)
          ·
            refine ⟨23865105377639326730018737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31820140503519102306691649 23865105377639326730018737)
            ·
              refine ⟨17898829033229495047514053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23865105377639326730018737 17898829033229495047514053)
              ·
                refine ⟨3356030443730530321408885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17898829033229495047514053 3356030443730530321408885)
                ·
                  refine ⟨314627854099737217632083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3356030443730530321408885 314627854099737217632083)
                  ·
                    rfl

theorem cell21_1378655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 5].length) (baseStart_1378655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1378655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1378655 prefixEnd_1378655 := by exact prefixLift 1378655
  have htrace : WordTrace (prefixWord ++ tailWord_1378655) baseStart_1378655 baseEnd_1378655 := by
    simpa [prefixWord, tailWord_1378655, baseEnd_1378655] using wordTrace_append hprefix tailTrace_1378655
  have hstable : (prefixWord ++ tailWord_1378655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378655).length < 2 ^ (prefixWord ++ tailWord_1378655).sum := by decide
  have hdescent : baseEnd_1378655 < baseStart_1378655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378748 : List Nat := [2, 2, 2, 4, 1, 1, 1, 3, 5]
def baseStart_1378748 : Nat := 118140960795 + 1378748 * 2 ^ 59
def prefixEnd_1378748 : Nat := 4983230072969 + 3 ^ 40 * 1378748 * 2
def baseEnd_1378748 : Nat := 314649077966789722581893

theorem tailTrace_1378748 : CollatzResearch.WordTrace tailWord_1378748 prefixEnd_1378748 314649077966789722581893 := by
  unfold tailWord_1378748
  simp only [CollatzResearch.WordTrace]
  refine ⟨25143535404519471128336449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33524713872692628171115265 25143535404519471128336449)
  ·
    refine ⟨18857651553389603346252337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25143535404519471128336449 18857651553389603346252337)
    ·
      refine ⟨14143238665042202509689253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18857651553389603346252337 14143238665042202509689253)
      ·
        refine ⟨2651857249695412970566735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14143238665042202509689253 2651857249695412970566735)
        ·
          refine ⟨3977785874543119455850103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2651857249695412970566735 3977785874543119455850103)
          ·
            refine ⟨5966678811814679183775155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3977785874543119455850103 5966678811814679183775155)
            ·
              refine ⟨8950018217722018775662733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5966678811814679183775155 8950018217722018775662733)
              ·
                refine ⟨3356256831645757040873525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8950018217722018775662733 3356256831645757040873525)
                ·
                  refine ⟨314649077966789722581893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3356256831645757040873525 314649077966789722581893)
                  ·
                    rfl

theorem cell21_1378748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 5].length) (baseStart_1378748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1378748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1378748 prefixEnd_1378748 := by exact prefixLift 1378748
  have htrace : WordTrace (prefixWord ++ tailWord_1378748) baseStart_1378748 baseEnd_1378748 := by
    simpa [prefixWord, tailWord_1378748, baseEnd_1378748] using wordTrace_append hprefix tailTrace_1378748
  have hstable : (prefixWord ++ tailWord_1378748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378748).length < 2 ^ (prefixWord ++ tailWord_1378748).sum := by decide
  have hdescent : baseEnd_1378748 < baseStart_1378748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378858 : List Nat := [3, 1, 4, 1, 1, 2, 4, 2, 3]
def baseStart_1378858 : Nat := 118140960795 + 1378858 * 2 ^ 59
def prefixEnd_1378858 : Nat := 4983230072969 + 3 ^ 40 * 1378858 * 2
def baseEnd_1378858 : Nat := 314674181465453975748335

theorem tailTrace_1378858 : CollatzResearch.WordTrace tailWord_1378858 prefixEnd_1378858 314674181465453975748335 := by
  unfold tailWord_1378858
  simp only [CollatzResearch.WordTrace]
  refine ⟨12572770709660107760794307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33527388559093620695451485 12572770709660107760794307)
  ·
    refine ⟨18859156064490161641191461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12572770709660107760794307 18859156064490161641191461)
    ·
      refine ⟨3536091762091905307723399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18859156064490161641191461 3536091762091905307723399)
      ·
        refine ⟨5304137643137857961585099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3536091762091905307723399 5304137643137857961585099)
        ·
          refine ⟨7956206464706786942377649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5304137643137857961585099 7956206464706786942377649)
          ·
            refine ⟨5967154848530090206783237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7956206464706786942377649 5967154848530090206783237)
            ·
              refine ⟨1118841534099391913771857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5967154848530090206783237 1118841534099391913771857)
              ·
                refine ⟨839131150574543935328893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1118841534099391913771857 839131150574543935328893)
                ·
                  refine ⟨314674181465453975748335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 839131150574543935328893 314674181465453975748335)
                  ·
                    rfl

theorem cell21_1378858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 2, 3].length) (baseStart_1378858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1378858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1378858 prefixEnd_1378858 := by exact prefixLift 1378858
  have htrace : WordTrace (prefixWord ++ tailWord_1378858) baseStart_1378858 baseEnd_1378858 := by
    simpa [prefixWord, tailWord_1378858, baseEnd_1378858] using wordTrace_append hprefix tailTrace_1378858
  have hstable : (prefixWord ++ tailWord_1378858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378858).length < 2 ^ (prefixWord ++ tailWord_1378858).sum := by decide
  have hdescent : baseEnd_1378858 < baseStart_1378858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378861 : List Nat := [1, 5, 4, 1, 2, 1, 1, 6]
def baseStart_1378861 : Nat := 118140960795 + 1378861 * 2 ^ 59
def prefixEnd_1378861 : Nat := 4983230072969 + 3 ^ 40 * 1378861 * 2
def baseEnd_1378861 : Nat := 104891622035442212399443

theorem tailTrace_1378861 : CollatzResearch.WordTrace tailWord_1378861 prefixEnd_1378861 104891622035442212399443 := by
  unfold tailWord_1378861
  simp only [CollatzResearch.WordTrace]
  refine ⟨50291192257629562555536437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33527461505086375037024291 50291192257629562555536437)
  ·
    refine ⟨4714799274152771489581541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50291192257629562555536437 4714799274152771489581541)
    ·
      refine ⟨884024863903644654296539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4714799274152771489581541 884024863903644654296539)
      ·
        refine ⟨1326037295855466981444809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 884024863903644654296539 1326037295855466981444809)
        ·
          refine ⟨994527971891600236083607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1326037295855466981444809 994527971891600236083607)
          ·
            refine ⟨1491791957837400354125411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 994527971891600236083607 1491791957837400354125411)
            ·
              refine ⟨2237687936756100531188117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1491791957837400354125411 2237687936756100531188117)
              ·
                refine ⟨104891622035442212399443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2237687936756100531188117 104891622035442212399443)
                ·
                  rfl

theorem cell21_1378861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 6].length) (baseStart_1378861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1378861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1378861 prefixEnd_1378861 := by exact prefixLift 1378861
  have htrace : WordTrace (prefixWord ++ tailWord_1378861) baseStart_1378861 baseEnd_1378861 := by
    simpa [prefixWord, tailWord_1378861, baseEnd_1378861] using wordTrace_append hprefix tailTrace_1378861
  have hstable : (prefixWord ++ tailWord_1378861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378861).length < 2 ^ (prefixWord ++ tailWord_1378861).sum := by decide
  have hdescent : baseEnd_1378861 < baseStart_1378861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379004 : List Nat := [2, 2, 2, 3, 1, 1, 1, 9]
def baseStart_1379004 : Nat := 118140960795 + 1379004 * 2 ^ 59
def prefixEnd_1379004 : Nat := 4983230072969 + 3 ^ 40 * 1379004 * 2
def baseEnd_1379004 : Nat := 104902500218196722104901

theorem tailTrace_1379004 : CollatzResearch.WordTrace tailWord_1379004 prefixEnd_1379004 104902500218196722104901 := by
  unfold tailWord_1379004
  simp only [CollatzResearch.WordTrace]
  refine ⟨25148203948055748988996033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33530938597407665318661377 25148203948055748988996033)
  ·
    refine ⟨18861152961041811741747025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25148203948055748988996033 18861152961041811741747025)
    ·
      refine ⟨14145864720781358806310269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18861152961041811741747025 14145864720781358806310269)
      ·
        refine ⟨5304699270293009552366351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14145864720781358806310269 5304699270293009552366351)
        ·
          refine ⟨7957048905439514328549527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5304699270293009552366351 7957048905439514328549527)
          ·
            refine ⟨11935573358159271492824291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7957048905439514328549527 11935573358159271492824291)
            ·
              refine ⟨17903360037238907239236437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11935573358159271492824291 17903360037238907239236437)
              ·
                refine ⟨104902500218196722104901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17903360037238907239236437 104902500218196722104901)
                ·
                  rfl

theorem cell21_1379004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 9].length) (baseStart_1379004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1379004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1379004 prefixEnd_1379004 := by exact prefixLift 1379004
  have htrace : WordTrace (prefixWord ++ tailWord_1379004) baseStart_1379004 baseEnd_1379004 := by
    simpa [prefixWord, tailWord_1379004, baseEnd_1379004] using wordTrace_append hprefix tailTrace_1379004
  have hstable : (prefixWord ++ tailWord_1379004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379004).length < 2 ^ (prefixWord ++ tailWord_1379004).sum := by decide
  have hdescent : baseEnd_1379004 < baseStart_1379004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379021 : List Nat := [1, 6, 2, 1, 11]
def baseStart_1379021 : Nat := 118140960795 + 1379021 * 2 ^ 59
def prefixEnd_1379021 : Nat := 4983230072969 + 3 ^ 40 * 1379021 * 2
def baseEnd_1379021 : Nat := 3885325682545702648535

theorem tailTrace_1379021 : CollatzResearch.WordTrace tailWord_1379021 prefixEnd_1379021 3885325682545702648535 := by
  unfold tailWord_1379021
  simp only [CollatzResearch.WordTrace]
  refine ⟨50297027937049909881360917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33531351958033273254240611 50297027937049909881360917)
  ·
    refine ⟨2357673184549214525688793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 50297027937049909881360917 2357673184549214525688793)
    ·
      refine ⟨1768254888411910894266595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2357673184549214525688793 1768254888411910894266595)
      ·
        refine ⟨2652382332617866341399893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1768254888411910894266595 2652382332617866341399893)
        ·
          refine ⟨3885325682545702648535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2652382332617866341399893 3885325682545702648535)
          ·
            rfl

theorem cell21_1379021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 11].length) (baseStart_1379021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1379021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1379021 prefixEnd_1379021 := by exact prefixLift 1379021
  have htrace : WordTrace (prefixWord ++ tailWord_1379021) baseStart_1379021 baseEnd_1379021 := by
    simpa [prefixWord, tailWord_1379021, baseEnd_1379021] using wordTrace_append hprefix tailTrace_1379021
  have hstable : (prefixWord ++ tailWord_1379021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379021).length < 2 ^ (prefixWord ++ tailWord_1379021).sum := by decide
  have hdescent : baseEnd_1379021 < baseStart_1379021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379080 : List Nat := [2, 1, 3, 2, 2, 3, 8]
def baseStart_1379080 : Nat := 118140960795 + 1379080 * 2 ^ 59
def prefixEnd_1379080 : Nat := 4983230072969 + 3 ^ 40 * 1379080 * 2
def baseEnd_1379080 : Nat := 34969427210003435894209

theorem tailTrace_1379080 : CollatzResearch.WordTrace tailWord_1379080 prefixEnd_1379080 34969427210003435894209 := by
  unfold tailWord_1379080
  simp only [CollatzResearch.WordTrace]
  refine ⟨25149589921918081478879347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33532786562557441971839129 25149589921918081478879347)
  ·
    refine ⟨37724384882877122218319021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25149589921918081478879347 37724384882877122218319021)
    ·
      refine ⟨14146644331078920831869633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37724384882877122218319021 14146644331078920831869633)
      ·
        refine ⟨10609983248309190623902225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14146644331078920831869633 10609983248309190623902225)
        ·
          refine ⟨7957487436231892967926669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10609983248309190623902225 7957487436231892967926669)
          ·
            refine ⟨2984057788586959862972501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7957487436231892967926669 2984057788586959862972501)
            ·
              refine ⟨34969427210003435894209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2984057788586959862972501 34969427210003435894209)
              ·
                rfl

theorem cell21_1379080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 8].length) (baseStart_1379080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1379080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1379080 prefixEnd_1379080 := by exact prefixLift 1379080
  have htrace : WordTrace (prefixWord ++ tailWord_1379080) baseStart_1379080 baseEnd_1379080 := by
    simpa [prefixWord, tailWord_1379080, baseEnd_1379080] using wordTrace_append hprefix tailTrace_1379080
  have hstable : (prefixWord ++ tailWord_1379080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379080).length < 2 ^ (prefixWord ++ tailWord_1379080).sum := by decide
  have hdescent : baseEnd_1379080 < baseStart_1379080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379114 : List Nat := [3, 1, 4, 3, 1, 1, 1, 7]
def baseStart_1379114 : Nat := 118140960795 + 1379114 * 2 ^ 59
def prefixEnd_1379114 : Nat := 4983230072969 + 3 ^ 40 * 1379114 * 2
def baseEnd_1379114 : Nat := 104910868051084806493715

theorem tailTrace_1379114 : CollatzResearch.WordTrace tailWord_1379114 prefixEnd_1379114 104910868051084806493715 := by
  unfold tailWord_1379114
  simp only [CollatzResearch.WordTrace]
  refine ⟨12575104981428246691124099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33533613283808657842997597 12575104981428246691124099)
  ·
    refine ⟨18862657472142370036686149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12575104981428246691124099 18862657472142370036686149)
    ·
      refine ⟨3536748276026694381878653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18862657472142370036686149 3536748276026694381878653)
      ·
        refine ⟨1326280603510010393204495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3536748276026694381878653 1326280603510010393204495)
        ·
          refine ⟨1989420905265015589806743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1326280603510010393204495 1989420905265015589806743)
          ·
            refine ⟨2984131357897523384710115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1989420905265015589806743 2984131357897523384710115)
            ·
              refine ⟨4476197036846285077065173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2984131357897523384710115 4476197036846285077065173)
              ·
                refine ⟨104910868051084806493715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4476197036846285077065173 104910868051084806493715)
                ·
                  rfl

theorem cell21_1379114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 7].length) (baseStart_1379114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1379114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1379114 prefixEnd_1379114 := by exact prefixLift 1379114
  have htrace : WordTrace (prefixWord ++ tailWord_1379114) baseStart_1379114 baseEnd_1379114 := by
    simpa [prefixWord, tailWord_1379114, baseEnd_1379114] using wordTrace_append hprefix tailTrace_1379114
  have hstable : (prefixWord ++ tailWord_1379114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379114).length < 2 ^ (prefixWord ++ tailWord_1379114).sum := by decide
  have hdescent : baseEnd_1379114 < baseStart_1379114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379145 : List Nat := [1, 2, 1, 1, 2, 6, 3, 2, 3]
def baseStart_1379145 : Nat := 118140960795 + 1379145 * 2 ^ 59
def prefixEnd_1379145 : Nat := 4983230072969 + 3 ^ 40 * 1379145 * 2
def baseEnd_1379145 : Nat := 314739678775605254464415

theorem tailTrace_1379145 : CollatzResearch.WordTrace tailWord_1379145 prefixEnd_1379145 314739678775605254464415 := by
  unfold tailWord_1379145
  simp only [CollatzResearch.WordTrace]
  refine ⟨50301550588600679058874889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33534367059067119372583259 50301550588600679058874889)
  ·
    refine ⟨37726162941450509294156167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50301550588600679058874889 37726162941450509294156167)
    ·
      refine ⟨56589244412175763941234251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37726162941450509294156167 56589244412175763941234251)
      ·
        refine ⟨84883866618263645911851377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56589244412175763941234251 84883866618263645911851377)
        ·
          refine ⟨63662899963697734433888533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84883866618263645911851377 63662899963697734433888533)
          ·
            refine ⟨2984198435798331301588525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 63662899963697734433888533 2984198435798331301588525)
            ·
              refine ⟨1119074413424374238095697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2984198435798331301588525 1119074413424374238095697)
              ·
                refine ⟨839305810068280678571773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1119074413424374238095697 839305810068280678571773)
                ·
                  refine ⟨314739678775605254464415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 839305810068280678571773 314739678775605254464415)
                  ·
                    rfl

theorem cell21_1379145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 2, 3].length) (baseStart_1379145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1379145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1379145 prefixEnd_1379145 := by exact prefixLift 1379145
  have htrace : WordTrace (prefixWord ++ tailWord_1379145) baseStart_1379145 baseEnd_1379145 := by
    simpa [prefixWord, tailWord_1379145, baseEnd_1379145] using wordTrace_append hprefix tailTrace_1379145
  have hstable : (prefixWord ++ tailWord_1379145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379145).length < 2 ^ (prefixWord ++ tailWord_1379145).sum := by decide
  have hdescent : baseEnd_1379145 < baseStart_1379145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379159 : List Nat := [1, 1, 3, 2, 4, 1, 4, 1, 4]
def baseStart_1379159 : Nat := 118140960795 + 1379159 * 2 ^ 59
def prefixEnd_1379159 : Nat := 4983230072969 + 3 ^ 40 * 1379159 * 2
def baseEnd_1379159 : Nat := 314742873766344341231053

theorem tailTrace_1379159 : CollatzResearch.WordTrace tailWord_1379159 prefixEnd_1379159 314742873766344341231053 := by
  unfold tailWord_1379159
  simp only [CollatzResearch.WordTrace]
  refine ⟨50302061210549959449884531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33534707473699972966589687 50302061210549959449884531)
  ·
    refine ⟨75453091815824939174826797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50302061210549959449884531 75453091815824939174826797)
    ·
      refine ⟨28294909430934352190560049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75453091815824939174826797 28294909430934352190560049)
      ·
        refine ⟨21221182073200764142920037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28294909430934352190560049 21221182073200764142920037)
        ·
          refine ⟨3978971638725143276797507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21221182073200764142920037 3978971638725143276797507)
          ·
            refine ⟨5968457458087714915196261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3978971638725143276797507 5968457458087714915196261)
            ·
              refine ⟨1119085773391446546599299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5968457458087714915196261 1119085773391446546599299)
              ·
                refine ⟨1678628660087169819898949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1119085773391446546599299 1678628660087169819898949)
                ·
                  refine ⟨314742873766344341231053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1678628660087169819898949 314742873766344341231053)
                  ·
                    rfl

theorem cell21_1379159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 1, 4].length) (baseStart_1379159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1379159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1379159 prefixEnd_1379159 := by exact prefixLift 1379159
  have htrace : WordTrace (prefixWord ++ tailWord_1379159) baseStart_1379159 baseEnd_1379159 := by
    simpa [prefixWord, tailWord_1379159, baseEnd_1379159] using wordTrace_append hprefix tailTrace_1379159
  have hstable : (prefixWord ++ tailWord_1379159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379159).length < 2 ^ (prefixWord ++ tailWord_1379159).sum := by decide
  have hdescent : baseEnd_1379159 < baseStart_1379159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379252 : List Nat := [2, 5, 2, 1, 1, 1, 3, 2, 4]
def baseStart_1379252 : Nat := 118140960795 + 1379252 * 2 ^ 59
def prefixEnd_1379252 : Nat := 4983230072969 + 3 ^ 40 * 1379252 * 2
def baseEnd_1379252 : Nat := 314764097633396846180863

theorem tailTrace_1379252 : CollatzResearch.WordTrace tailWord_1379252 prefixEnd_1379252 314764097633396846180863 := by
  unfold tailWord_1379252
  simp only [CollatzResearch.WordTrace]
  refine ⟨25152726599606518166510005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33536968799475357555346673 25152726599606518166510005)
  ·
    refine ⟨2358068118713111078110313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25152726599606518166510005 2358068118713111078110313)
    ·
      refine ⟨1768551089034833308582735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2358068118713111078110313 1768551089034833308582735)
      ·
        refine ⟨2652826633552249962874103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1768551089034833308582735 2652826633552249962874103)
        ·
          refine ⟨3979239950328374944311155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2652826633552249962874103 3979239950328374944311155)
          ·
            refine ⟨5968859925492562416466733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3979239950328374944311155 5968859925492562416466733)
            ·
              refine ⟨2238322472059710906175025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5968859925492562416466733 2238322472059710906175025)
              ·
                refine ⟨1678741854044783179631269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2238322472059710906175025 1678741854044783179631269)
                ·
                  refine ⟨314764097633396846180863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1678741854044783179631269 314764097633396846180863)
                  ·
                    rfl

theorem cell21_1379252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_1379252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1379252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1379252 prefixEnd_1379252 := by exact prefixLift 1379252
  have htrace : WordTrace (prefixWord ++ tailWord_1379252) baseStart_1379252 baseEnd_1379252 := by
    simpa [prefixWord, tailWord_1379252, baseEnd_1379252] using wordTrace_append hprefix tailTrace_1379252
  have hstable : (prefixWord ++ tailWord_1379252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379252).length < 2 ^ (prefixWord ++ tailWord_1379252).sum := by decide
  have hdescent : baseEnd_1379252 < baseStart_1379252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379314 : List Nat := [3, 2, 1, 5, 2, 1, 1, 1, 5]
def baseStart_1379314 : Nat := 118140960795 + 1379314 * 2 ^ 59
def prefixEnd_1379314 : Nat := 4983230072969 + 3 ^ 40 * 1379314 * 2
def baseEnd_1379314 : Nat := 314778246878098516147403

theorem tailTrace_1379314 : CollatzResearch.WordTrace tailWord_1379314 prefixEnd_1379314 314778246878098516147403 := by
  unfold tailWord_1379314
  simp only [CollatzResearch.WordTrace]
  refine ⟨12576928631247105230444249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33538476349992280614517997 12576928631247105230444249)
  ·
    refine ⟨9432696473435328922833187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12576928631247105230444249 9432696473435328922833187)
    ·
      refine ⟨14149044710152993384249781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9432696473435328922833187 14149044710152993384249781)
      ·
        refine ⟨1326472941576843129773417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14149044710152993384249781 1326472941576843129773417)
        ·
          refine ⟨994854706182632347330063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1326472941576843129773417 994854706182632347330063)
          ·
            refine ⟨1492282059273948520995095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 994854706182632347330063 1492282059273948520995095)
            ·
              refine ⟨2238423088910922781492643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1492282059273948520995095 2238423088910922781492643)
              ·
                refine ⟨3357634633366384172238965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2238423088910922781492643 3357634633366384172238965)
                ·
                  refine ⟨314778246878098516147403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3357634633366384172238965 314778246878098516147403)
                  ·
                    rfl

theorem cell21_1379314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 5].length) (baseStart_1379314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1379314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1379314 prefixEnd_1379314 := by exact prefixLift 1379314
  have htrace : WordTrace (prefixWord ++ tailWord_1379314) baseStart_1379314 baseEnd_1379314 := by
    simpa [prefixWord, tailWord_1379314, baseEnd_1379314] using wordTrace_append hprefix tailTrace_1379314
  have hstable : (prefixWord ++ tailWord_1379314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379314).length < 2 ^ (prefixWord ++ tailWord_1379314).sum := by decide
  have hdescent : baseEnd_1379314 < baseStart_1379314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379384 : List Nat := [2, 1, 2, 1, 5, 1, 3, 6]
def baseStart_1379384 : Nat := 118140960795 + 1379384 * 2 ^ 59
def prefixEnd_1379384 : Nat := 4983230072969 + 3 ^ 40 * 1379384 * 2
def baseEnd_1379384 : Nat := 104931407277264649993531

theorem tailTrace_1379384 : CollatzResearch.WordTrace tailWord_1379384 prefixEnd_1379384 104931407277264649993531 := by
  unfold tailWord_1379384
  simp only [CollatzResearch.WordTrace]
  refine ⟨25155133817367411438412603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33540178423156548584550137 25155133817367411438412603)
  ·
    refine ⟨37732700726051117157618905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25155133817367411438412603 37732700726051117157618905)
    ·
      refine ⟨28299525544538337868214179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37732700726051117157618905 28299525544538337868214179)
      ·
        refine ⟨42449288316807506802321269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28299525544538337868214179 42449288316807506802321269)
        ·
          refine ⟨3979620779700703762717619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42449288316807506802321269 3979620779700703762717619)
          ·
            refine ⟨5969431169551055644076429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3979620779700703762717619 5969431169551055644076429)
            ·
              refine ⟨2238536688581645866528661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5969431169551055644076429 2238536688581645866528661)
              ·
                refine ⟨104931407277264649993531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2238536688581645866528661 104931407277264649993531)
                ·
                  rfl

theorem cell21_1379384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 6].length) (baseStart_1379384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1379384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1379384 prefixEnd_1379384 := by exact prefixLift 1379384
  have htrace : WordTrace (prefixWord ++ tailWord_1379384) baseStart_1379384 baseEnd_1379384 := by
    simpa [prefixWord, tailWord_1379384, baseEnd_1379384] using wordTrace_append hprefix tailTrace_1379384
  have hstable : (prefixWord ++ tailWord_1379384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379384).length < 2 ^ (prefixWord ++ tailWord_1379384).sum := by decide
  have hdescent : baseEnd_1379384 < baseStart_1379384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379421 : List Nat := [1, 4, 4, 1, 3, 1, 1, 2, 4]
def baseStart_1379421 : Nat := 118140960795 + 1379421 * 2 ^ 59
def prefixEnd_1379421 : Nat := 4983230072969 + 3 ^ 40 * 1379421 * 2
def baseEnd_1379421 : Nat := 314802665735890107863851

theorem tailTrace_1379421 : CollatzResearch.WordTrace tailWord_1379421 prefixEnd_1379421 314802665735890107863851 := by
  unfold tailWord_1379421
  simp only [CollatzResearch.WordTrace]
  refine ⟨50311617135600778195922117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33541078090400518797281411 50311617135600778195922117)
  ·
    refine ⟨9433428212925145911735397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50311617135600778195922117 9433428212925145911735397)
    ·
      refine ⟨1768767789923464858450387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9433428212925145911735397 1768767789923464858450387)
      ·
        refine ⟨2653151684885197287675581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1768767789923464858450387 2653151684885197287675581)
        ·
          refine ⟨994931881831948982878343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2653151684885197287675581 994931881831948982878343)
          ·
            refine ⟨1492397822747923474317515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 994931881831948982878343 1492397822747923474317515)
            ·
              refine ⟨2238596734121885211476273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1492397822747923474317515 2238596734121885211476273)
              ·
                refine ⟨1678947550591413908607205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2238596734121885211476273 1678947550591413908607205)
                ·
                  refine ⟨314802665735890107863851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1678947550591413908607205 314802665735890107863851)
                  ·
                    rfl

theorem cell21_1379421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 2, 4].length) (baseStart_1379421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1379421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1379421 prefixEnd_1379421 := by exact prefixLift 1379421
  have htrace : WordTrace (prefixWord ++ tailWord_1379421) baseStart_1379421 baseEnd_1379421 := by
    simpa [prefixWord, tailWord_1379421, baseEnd_1379421] using wordTrace_append hprefix tailTrace_1379421
  have hstable : (prefixWord ++ tailWord_1379421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379421).length < 2 ^ (prefixWord ++ tailWord_1379421).sum := by decide
  have hdescent : baseEnd_1379421 < baseStart_1379421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379429 : List Nat := [1, 3, 1, 3, 2, 1, 3, 1, 6]
def baseStart_1379429 : Nat := 118140960795 + 1379429 * 2 ^ 59
def prefixEnd_1379429 : Nat := 4983230072969 + 3 ^ 40 * 1379429 * 2
def baseEnd_1379429 : Nat := 314804491444883871730501

theorem tailTrace_1379429 : CollatzResearch.WordTrace tailWord_1379429 prefixEnd_1379429 314804491444883871730501 := by
  unfold tailWord_1379429
  simp only [CollatzResearch.WordTrace]
  refine ⟨50311908919571795562213341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33541272613047863708142227 50311908919571795562213341)
  ·
    refine ⟨18866965844839423335830003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50311908919571795562213341 18866965844839423335830003)
    ·
      refine ⟨28300448767259135003745005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18866965844839423335830003 28300448767259135003745005)
      ·
        refine ⟨10612668287722175626404377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28300448767259135003745005 10612668287722175626404377)
        ·
          refine ⟨7959501215791631719803283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10612668287722175626404377 7959501215791631719803283)
          ·
            refine ⟨11939251823687447579704925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7959501215791631719803283 11939251823687447579704925)
            ·
              refine ⟨4477219433882792842389347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11939251823687447579704925 4477219433882792842389347)
              ·
                refine ⟨6715829150824189263584021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4477219433882792842389347 6715829150824189263584021)
                ·
                  refine ⟨314804491444883871730501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6715829150824189263584021 314804491444883871730501)
                  ·
                    rfl

theorem cell21_1379429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_1379429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1379429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1379429 prefixEnd_1379429 := by exact prefixLift 1379429
  have htrace : WordTrace (prefixWord ++ tailWord_1379429) baseStart_1379429 baseEnd_1379429 := by
    simpa [prefixWord, tailWord_1379429, baseEnd_1379429] using wordTrace_append hprefix tailTrace_1379429
  have hstable : (prefixWord ++ tailWord_1379429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379429).length < 2 ^ (prefixWord ++ tailWord_1379429).sum := by decide
  have hdescent : baseEnd_1379429 < baseStart_1379429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379460 : List Nat := [2, 3, 2, 1, 2, 3, 1, 7]
def baseStart_1379460 : Nat := 118140960795 + 1379460 * 2 ^ 59
def prefixEnd_1379460 : Nat := 4983230072969 + 3 ^ 40 * 1379460 * 2
def baseEnd_1379460 : Nat := 104937188689078235571257

theorem tailTrace_1379460 : CollatzResearch.WordTrace tailWord_1379460 prefixEnd_1379460 104937188689078235571257 := by
  unfold tailWord_1379460
  simp only [CollatzResearch.WordTrace]
  refine ⟨25156519791229743928295917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33542026388306325237727889 25156519791229743928295917)
  ·
    refine ⟨9433694921711153973110969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25156519791229743928295917 9433694921711153973110969)
    ·
      refine ⟨7075271191283365479833227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9433694921711153973110969 7075271191283365479833227)
      ·
        refine ⟨10612906786925048219749841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7075271191283365479833227 10612906786925048219749841)
        ·
          refine ⟨7959680090193786164812381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10612906786925048219749841 7959680090193786164812381)
          ·
            refine ⟨2984880033822669811804643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7959680090193786164812381 2984880033822669811804643)
            ·
              refine ⟨4477320050734004717706965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2984880033822669811804643 4477320050734004717706965)
              ·
                refine ⟨104937188689078235571257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4477320050734004717706965 104937188689078235571257)
                ·
                  rfl

theorem cell21_1379460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 7].length) (baseStart_1379460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1379460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1379460 prefixEnd_1379460 := by exact prefixLift 1379460
  have htrace : WordTrace (prefixWord ++ tailWord_1379460) baseStart_1379460 baseEnd_1379460 := by
    simpa [prefixWord, tailWord_1379460, baseEnd_1379460] using wordTrace_append hprefix tailTrace_1379460
  have hstable : (prefixWord ++ tailWord_1379460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379460).length < 2 ^ (prefixWord ++ tailWord_1379460).sum := by decide
  have hdescent : baseEnd_1379460 < baseStart_1379460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379491 : List Nat := [1, 1, 1, 4, 1, 1, 1, 8, 3]
def baseStart_1379491 : Nat := 118140960795 + 1379491 * 2 ^ 59
def prefixEnd_1379491 : Nat := 4983230072969 + 3 ^ 40 * 1379491 * 2
def baseEnd_1379491 : Nat := 314818640689585541697041

theorem tailTrace_1379491 : CollatzResearch.WordTrace tailWord_1379491 prefixEnd_1379491 314818640689585541697041 := by
  unfold tailWord_1379491
  simp only [CollatzResearch.WordTrace]
  refine ⟨50314170245347180150970327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33542780163564786767313551 50314170245347180150970327)
  ·
    refine ⟨75471255368020770226455491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50314170245347180150970327 75471255368020770226455491)
    ·
      refine ⟨113206883052031155339683237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75471255368020770226455491 113206883052031155339683237)
      ·
        refine ⟨21226290572255841626190607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113206883052031155339683237 21226290572255841626190607)
        ·
          refine ⟨31839435858383762439285911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21226290572255841626190607 31839435858383762439285911)
          ·
            refine ⟨47759153787575643658928867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31839435858383762439285911 47759153787575643658928867)
            ·
              refine ⟨71638730681363465488393301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47759153787575643658928867 71638730681363465488393301)
              ·
                refine ⟨839516375172228111192109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 71638730681363465488393301 839516375172228111192109)
                ·
                  refine ⟨314818640689585541697041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 839516375172228111192109 314818640689585541697041)
                  ·
                    rfl

theorem cell21_1379491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 8, 3].length) (baseStart_1379491 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1379491 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1379491 prefixEnd_1379491 := by exact prefixLift 1379491
  have htrace : WordTrace (prefixWord ++ tailWord_1379491) baseStart_1379491 baseEnd_1379491 := by
    simpa [prefixWord, tailWord_1379491, baseEnd_1379491] using wordTrace_append hprefix tailTrace_1379491
  have hstable : (prefixWord ++ tailWord_1379491).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379491).length < 2 ^ (prefixWord ++ tailWord_1379491).sum := by decide
  have hdescent : baseEnd_1379491 < baseStart_1379491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379519 : List Nat := [1, 1, 2, 2, 2, 2, 4, 7]
def baseStart_1379519 : Nat := 118140960795 + 1379519 * 2 ^ 59
def prefixEnd_1379519 : Nat := 4983230072969 + 3 ^ 40 * 1379519 * 2
def baseEnd_1379519 : Nat := 104941676890354571743439

theorem tailTrace_1379519 : CollatzResearch.WordTrace tailWord_1379519 prefixEnd_1379519 104941676890354571743439 := by
  unfold tailWord_1379519
  simp only [CollatzResearch.WordTrace]
  refine ⟨50315191489245740932989611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33543460992830493955326407 50315191489245740932989611)
  ·
    refine ⟨75472787233868611399484417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50315191489245740932989611 75472787233868611399484417)
    ·
      refine ⟨56604590425401458549613313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75472787233868611399484417 56604590425401458549613313)
      ·
        refine ⟨42453442819051093912209985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56604590425401458549613313 42453442819051093912209985)
        ·
          refine ⟨31840082114288320434157489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42453442819051093912209985 31840082114288320434157489)
          ·
            refine ⟨23880061585716240325618117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31840082114288320434157489 23880061585716240325618117)
            ·
              refine ⟨4477511547321795061053397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23880061585716240325618117 4477511547321795061053397)
              ·
                refine ⟨104941676890354571743439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4477511547321795061053397 104941676890354571743439)
                ·
                  rfl

theorem cell21_1379519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 7].length) (baseStart_1379519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1379519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1379519 prefixEnd_1379519 := by exact prefixLift 1379519
  have htrace : WordTrace (prefixWord ++ tailWord_1379519) baseStart_1379519 baseEnd_1379519 := by
    simpa [prefixWord, tailWord_1379519, baseEnd_1379519] using wordTrace_append hprefix tailTrace_1379519
  have hstable : (prefixWord ++ tailWord_1379519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379519).length < 2 ^ (prefixWord ++ tailWord_1379519).sum := by decide
  have hdescent : baseEnd_1379519 < baseStart_1379519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379542 : List Nat := [5, 2, 1, 2, 2, 1, 1, 4, 3]
def baseStart_1379542 : Nat := 118140960795 + 1379542 * 2 ^ 59
def prefixEnd_1379542 : Nat := 4983230072969 + 3 ^ 40 * 1379542 * 2
def baseEnd_1379542 : Nat := 314830279584420786346937

theorem tailTrace_1379542 : CollatzResearch.WordTrace tailWord_1379542 prefixEnd_1379542 314830279584420786346937 := by
  unfold tailWord_1379542
  simp only [CollatzResearch.WordTrace]
  refine ⟨3144751898010150991317305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33544020245441610574051253 3144751898010150991317305)
  ·
    refine ⟨2358563923507613243487979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3144751898010150991317305 2358563923507613243487979)
    ·
      refine ⟨3537845885261419865231969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2358563923507613243487979 3537845885261419865231969)
      ·
        refine ⟨2653384413946064898923977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3537845885261419865231969 2653384413946064898923977)
        ·
          refine ⟨1990038310459548674192983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2653384413946064898923977 1990038310459548674192983)
          ·
            refine ⟨2985057465689323011289475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1990038310459548674192983 2985057465689323011289475)
            ·
              refine ⟨4477586198533984516934213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2985057465689323011289475 4477586198533984516934213)
              ·
                refine ⟨839547412225122096925165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4477586198533984516934213 839547412225122096925165)
                ·
                  refine ⟨314830279584420786346937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 839547412225122096925165 314830279584420786346937)
                  ·
                    rfl

theorem cell21_1379542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_1379542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1379542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1379542 prefixEnd_1379542 := by exact prefixLift 1379542
  have htrace : WordTrace (prefixWord ++ tailWord_1379542) baseStart_1379542 baseEnd_1379542 := by
    simpa [prefixWord, tailWord_1379542, baseEnd_1379542] using wordTrace_append hprefix tailTrace_1379542
  have hstable : (prefixWord ++ tailWord_1379542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379542).length < 2 ^ (prefixWord ++ tailWord_1379542).sum := by decide
  have hdescent : baseEnd_1379542 < baseStart_1379542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379567 : List Nat := [1, 1, 2, 1, 7, 1, 1, 2, 5]
def baseStart_1379567 : Nat := 118140960795 + 1379567 * 2 ^ 59
def prefixEnd_1379567 : Nat := 4983230072969 + 3 ^ 40 * 1379567 * 2
def baseEnd_1379567 : Nat := 314835984925026298430219

theorem tailTrace_1379567 : CollatzResearch.WordTrace tailWord_1379567 prefixEnd_1379567 314835984925026298430219 := by
  unfold tailWord_1379567
  simp only [CollatzResearch.WordTrace]
  refine ⟨50316942193071845130736955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33544628128714563420491303 50316942193071845130736955)
  ·
    refine ⟨75475413289607767696105433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50316942193071845130736955 75475413289607767696105433)
    ·
      refine ⟨56606559967205825772079075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75475413289607767696105433 56606559967205825772079075)
      ·
        refine ⟨84909839950808738658118613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56606559967205825772079075 84909839950808738658118613)
        ·
          refine ⟨1990074373847079812299655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 84909839950808738658118613 1990074373847079812299655)
          ·
            refine ⟨2985111560770619718449483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1990074373847079812299655 2985111560770619718449483)
            ·
              refine ⟨4477667341155929577674225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2985111560770619718449483 4477667341155929577674225)
              ·
                refine ⟨3358250505866947183255669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4477667341155929577674225 3358250505866947183255669)
                ·
                  refine ⟨314835984925026298430219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3358250505866947183255669 314835984925026298430219)
                  ·
                    rfl

theorem cell21_1379567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 5].length) (baseStart_1379567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1379567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1379567 prefixEnd_1379567 := by exact prefixLift 1379567
  have htrace : WordTrace (prefixWord ++ tailWord_1379567) baseStart_1379567 baseEnd_1379567 := by
    simpa [prefixWord, tailWord_1379567, baseEnd_1379567] using wordTrace_append hprefix tailTrace_1379567
  have hstable : (prefixWord ++ tailWord_1379567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379567).length < 2 ^ (prefixWord ++ tailWord_1379567).sum := by decide
  have hdescent : baseEnd_1379567 < baseStart_1379567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379595 : List Nat := [1, 1, 1, 1, 5, 4, 8]
def baseStart_1379595 : Nat := 118140960795 + 1379595 * 2 ^ 59
def prefixEnd_1379595 : Nat := 4983230072969 + 3 ^ 40 * 1379595 * 2
def baseEnd_1379595 : Nat := 34982486100722719107055

theorem tailTrace_1379595 : CollatzResearch.WordTrace tailWord_1379595 prefixEnd_1379595 34982486100722719107055 := by
  unfold tailWord_1379595
  simp only [CollatzResearch.WordTrace]
  refine ⟨50317963436970405912756239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33545308957980270608504159 50317963436970405912756239)
  ·
    refine ⟨75476945155455608869134359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50317963436970405912756239 75476945155455608869134359)
    ·
      refine ⟨113215417733183413303701539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75476945155455608869134359 113215417733183413303701539)
      ·
        refine ⟨169823126599775119955552309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113215417733183413303701539 169823126599775119955552309)
        ·
          refine ⟨15920918118728917495833029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 169823126599775119955552309 15920918118728917495833029)
          ·
            refine ⟨2985172147261672030468693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15920918118728917495833029 2985172147261672030468693)
            ·
              refine ⟨34982486100722719107055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2985172147261672030468693 34982486100722719107055)
              ·
                rfl

theorem cell21_1379595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 8].length) (baseStart_1379595 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1379595 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1379595 prefixEnd_1379595 := by exact prefixLift 1379595
  have htrace : WordTrace (prefixWord ++ tailWord_1379595) baseStart_1379595 baseEnd_1379595 := by
    simpa [prefixWord, tailWord_1379595, baseEnd_1379595] using wordTrace_append hprefix tailTrace_1379595
  have hstable : (prefixWord ++ tailWord_1379595).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379595).length < 2 ^ (prefixWord ++ tailWord_1379595).sum := by decide
  have hdescent : baseEnd_1379595 < baseStart_1379595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379598 : List Nat := [4, 1, 1, 2, 1, 3, 3, 2, 4]
def baseStart_1379598 : Nat := 118140960795 + 1379598 * 2 ^ 59
def prefixEnd_1379598 : Nat := 4983230072969 + 3 ^ 40 * 1379598 * 2
def baseEnd_1379598 : Nat := 314843059547377133413489

theorem tailTrace_1379598 : CollatzResearch.WordTrace tailWord_1379598 prefixEnd_1379598 314843059547377133413489 := by
  unfold tailWord_1379598
  simp only [CollatzResearch.WordTrace]
  refine ⟨6289759106994942178139431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33545381903973024950076965 6289759106994942178139431)
  ·
    refine ⟨9434638660492413267209147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6289759106994942178139431 9434638660492413267209147)
    ·
      refine ⟨14151957990738619900813721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9434638660492413267209147 14151957990738619900813721)
      ·
        refine ⟨10613968493053964925610291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14151957990738619900813721 10613968493053964925610291)
        ·
          refine ⟨15920952739580947388415437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10613968493053964925610291 15920952739580947388415437)
          ·
            refine ⟨5970357277342855270655789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15920952739580947388415437 5970357277342855270655789)
            ·
              refine ⟨2238883979003570726495921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5970357277342855270655789 2238883979003570726495921)
              ·
                refine ⟨1679162984252678044871941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2238883979003570726495921 1679162984252678044871941)
                ·
                  refine ⟨314843059547377133413489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1679162984252678044871941 314843059547377133413489)
                  ·
                    rfl

theorem cell21_1379598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_1379598 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1379598 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1379598 prefixEnd_1379598 := by exact prefixLift 1379598
  have htrace : WordTrace (prefixWord ++ tailWord_1379598) baseStart_1379598 baseEnd_1379598 := by
    simpa [prefixWord, tailWord_1379598, baseEnd_1379598] using wordTrace_append hprefix tailTrace_1379598
  have hstable : (prefixWord ++ tailWord_1379598).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379598).length < 2 ^ (prefixWord ++ tailWord_1379598).sum := by decide
  have hdescent : baseEnd_1379598 < baseStart_1379598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379615 : List Nat := [1, 1, 2, 4, 4, 1, 3, 1, 4]
def baseStart_1379615 : Nat := 118140960795 + 1379615 * 2 ^ 59
def prefixEnd_1379615 : Nat := 4983230072969 + 3 ^ 40 * 1379615 * 2
def baseEnd_1379615 : Nat := 314846939178988881630121

theorem tailTrace_1379615 : CollatzResearch.WordTrace tailWord_1379615 prefixEnd_1379615 314846939178988881630121 := by
  unfold tailWord_1379615
  simp only [CollatzResearch.WordTrace]
  refine ⟨50318692896897949328484299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33545795264598632885656199 50318692896897949328484299)
  ·
    refine ⟨75478039345346923992726449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50318692896897949328484299 75478039345346923992726449)
    ·
      refine ⟨56608529509010192994544837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75478039345346923992726449 56608529509010192994544837)
      ·
        refine ⟨10614099282939411186477157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56608529509010192994544837 10614099282939411186477157)
        ·
          refine ⟨1990143615551139597464467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10614099282939411186477157 1990143615551139597464467)
          ·
            refine ⟨2985215423326709396196701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1990143615551139597464467 2985215423326709396196701)
            ·
              refine ⟨1119455783747516023573763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2985215423326709396196701 1119455783747516023573763)
              ·
                refine ⟨1679183675621274035360645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1119455783747516023573763 1679183675621274035360645)
                ·
                  refine ⟨314846939178988881630121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1679183675621274035360645 314846939178988881630121)
                  ·
                    rfl

theorem cell21_1379615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 1, 4].length) (baseStart_1379615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1379615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1379615 prefixEnd_1379615 := by exact prefixLift 1379615
  have htrace : WordTrace (prefixWord ++ tailWord_1379615) baseStart_1379615 baseEnd_1379615 := by
    simpa [prefixWord, tailWord_1379615, baseEnd_1379615] using wordTrace_append hprefix tailTrace_1379615
  have hstable : (prefixWord ++ tailWord_1379615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379615).length < 2 ^ (prefixWord ++ tailWord_1379615).sum := by decide
  have hdescent : baseEnd_1379615 < baseStart_1379615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379629 : List Nat := [1, 5, 3, 1, 1, 2, 1, 7]
def baseStart_1379629 : Nat := 118140960795 + 1379629 * 2 ^ 59
def prefixEnd_1379629 : Nat := 4983230072969 + 3 ^ 40 * 1379629 * 2
def baseEnd_1379629 : Nat := 104950044723242656132253

theorem tailTrace_1379629 : CollatzResearch.WordTrace tailWord_1379629 prefixEnd_1379629 104950044723242656132253 := by
  unfold tailWord_1379629
  simp only [CollatzResearch.WordTrace]
  refine ⟨50319203518847229719493941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33546135679231486479662627 50319203518847229719493941)
  ·
    refine ⟨4717425329891927786202557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50319203518847229719493941 4717425329891927786202557)
    ·
      refine ⟨1769034498709472919825959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4717425329891927786202557 1769034498709472919825959)
      ·
        refine ⟨2653551748064209379738939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1769034498709472919825959 2653551748064209379738939)
        ·
          refine ⟨3980327622096314069608409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2653551748064209379738939 3980327622096314069608409)
          ·
            refine ⟨2985245716572235552206307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3980327622096314069608409 2985245716572235552206307)
            ·
              refine ⟨4477868574858353328309461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2985245716572235552206307 4477868574858353328309461)
              ·
                refine ⟨104950044723242656132253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4477868574858353328309461 104950044723242656132253)
                ·
                  rfl

theorem cell21_1379629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 7].length) (baseStart_1379629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1379629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1379629 prefixEnd_1379629 := by exact prefixLift 1379629
  have htrace : WordTrace (prefixWord ++ tailWord_1379629) baseStart_1379629 baseEnd_1379629 := by
    simpa [prefixWord, tailWord_1379629, baseEnd_1379629] using wordTrace_append hprefix tailTrace_1379629
  have hstable : (prefixWord ++ tailWord_1379629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379629).length < 2 ^ (prefixWord ++ tailWord_1379629).sum := by decide
  have hdescent : baseEnd_1379629 < baseStart_1379629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379671 : List Nat := [1, 1, 3, 2, 3, 2, 1, 8]
def baseStart_1379671 : Nat := 118140960795 + 1379671 * 2 ^ 59
def prefixEnd_1379671 : Nat := 4983230072969 + 3 ^ 40 * 1379671 * 2
def baseEnd_1379671 : Nat := 104953239713981742898891

theorem tailTrace_1379671 : CollatzResearch.WordTrace tailWord_1379671 prefixEnd_1379671 104953239713981742898891 := by
  unfold tailWord_1379671
  simp only [CollatzResearch.WordTrace]
  refine ⟨50320735384695070892522867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33547156923130047261681911 50320735384695070892522867)
  ·
    refine ⟨75481103077042606338784301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50320735384695070892522867 75481103077042606338784301)
    ·
      refine ⟨28305413653890977377044113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75481103077042606338784301 28305413653890977377044113)
      ·
        refine ⟨21229060240418233032783085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28305413653890977377044113 21229060240418233032783085)
        ·
          refine ⟨7960897590156837387293657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21229060240418233032783085 7960897590156837387293657)
          ·
            refine ⟨5970673192617628040470243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7960897590156837387293657 5970673192617628040470243)
            ·
              refine ⟨8956009788926442060705365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5970673192617628040470243 8956009788926442060705365)
              ·
                refine ⟨104953239713981742898891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8956009788926442060705365 104953239713981742898891)
                ·
                  rfl

theorem cell21_1379671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 8].length) (baseStart_1379671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1379671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1379671 prefixEnd_1379671 := by exact prefixLift 1379671
  have htrace : WordTrace (prefixWord ++ tailWord_1379671) baseStart_1379671 baseEnd_1379671 := by
    simpa [prefixWord, tailWord_1379671, baseEnd_1379671] using wordTrace_append hprefix tailTrace_1379671
  have hstable : (prefixWord ++ tailWord_1379671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379671).length < 2 ^ (prefixWord ++ tailWord_1379671).sum := by decide
  have hdescent : baseEnd_1379671 < baseStart_1379671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379674 : List Nat := [3, 1, 1, 2, 1, 2, 6, 1, 4]
def baseStart_1379674 : Nat := 118140960795 + 1379674 * 2 ^ 59
def prefixEnd_1379674 : Nat := 4983230072969 + 3 ^ 40 * 1379674 * 2
def baseEnd_1379674 : Nat := 314860403782817890146667

theorem tailTrace_1379674 : CollatzResearch.WordTrace tailWord_1379674 prefixEnd_1379674 314860403782817890146667 := by
  unfold tailWord_1379674
  simp only [CollatzResearch.WordTrace]
  refine ⟨12580211200921050601220519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33547229869122801603254717 12580211200921050601220519)
  ·
    refine ⟨18870316801381575901830779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12580211200921050601220519 18870316801381575901830779)
    ·
      refine ⟨28305475202072363852746169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18870316801381575901830779 28305475202072363852746169)
      ·
        refine ⟨21229106401554272889559627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28305475202072363852746169 21229106401554272889559627)
        ·
          refine ⟨31843659602331409334339441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21229106401554272889559627 31843659602331409334339441)
          ·
            refine ⟨23882744701748557000754581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31843659602331409334339441 23882744701748557000754581)
            ·
              refine ⟨1119503657894463609410371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23882744701748557000754581 1119503657894463609410371)
              ·
                refine ⟨1679255486841695414115557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1119503657894463609410371 1679255486841695414115557)
                ·
                  refine ⟨314860403782817890146667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1679255486841695414115557 314860403782817890146667)
                  ·
                    rfl

theorem cell21_1379674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 1, 4].length) (baseStart_1379674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1379674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1379674 prefixEnd_1379674 := by exact prefixLift 1379674
  have htrace : WordTrace (prefixWord ++ tailWord_1379674) baseStart_1379674 baseEnd_1379674 := by
    simpa [prefixWord, tailWord_1379674, baseEnd_1379674] using wordTrace_append hprefix tailTrace_1379674
  have hstable : (prefixWord ++ tailWord_1379674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379674).length < 2 ^ (prefixWord ++ tailWord_1379674).sum := by decide
  have hdescent : baseEnd_1379674 < baseStart_1379674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379733 : List Nat := [1, 3, 2, 1, 1, 2, 4, 3, 4]
def baseStart_1379733 : Nat := 118140960795 + 1379733 * 2 ^ 59
def prefixEnd_1379733 : Nat := 4983230072969 + 3 ^ 40 * 1379733 * 2
def baseEnd_1379733 : Nat := 314873868386646898663213

theorem tailTrace_1379733 : CollatzResearch.WordTrace tailWord_1379733 prefixEnd_1379733 314873868386646898663213 := by
  unfold tailWord_1379733
  simp only [CollatzResearch.WordTrace]
  refine ⟨50322996710470455481279853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33548664473646970320853235 50322996710470455481279853)
  ·
    refine ⟨18871123766426420805479945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50322996710470455481279853 18871123766426420805479945)
    ·
      refine ⟨14153342824819815604109959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18871123766426420805479945 14153342824819815604109959)
      ·
        refine ⟨21230014237229723406164939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14153342824819815604109959 21230014237229723406164939)
        ·
          refine ⟨31845021355844585109247409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21230014237229723406164939 31845021355844585109247409)
          ·
            refine ⟨23883766016883438831935557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31845021355844585109247409 23883766016883438831935557)
            ·
              refine ⟨4478206128165644780987917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23883766016883438831935557 4478206128165644780987917)
              ·
                refine ⟨1679327298062116792870469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4478206128165644780987917 1679327298062116792870469)
                ·
                  refine ⟨314873868386646898663213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1679327298062116792870469 314873868386646898663213)
                  ·
                    rfl

theorem cell21_1379733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 3, 4].length) (baseStart_1379733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1379733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1379733 prefixEnd_1379733 := by exact prefixLift 1379733
  have htrace : WordTrace (prefixWord ++ tailWord_1379733) baseStart_1379733 baseEnd_1379733 := by
    simpa [prefixWord, tailWord_1379733, baseEnd_1379733] using wordTrace_append hprefix tailTrace_1379733
  have hstable : (prefixWord ++ tailWord_1379733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379733).length < 2 ^ (prefixWord ++ tailWord_1379733).sum := by decide
  have hdescent : baseEnd_1379733 < baseStart_1379733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379798 : List Nat := [5, 2, 1, 1, 1, 4, 2, 5]
def baseStart_1379798 : Nat := 118140960795 + 1379798 * 2 ^ 59
def prefixEnd_1379798 : Nat := 4983230072969 + 3 ^ 40 * 1379798 * 2
def baseEnd_1379798 : Nat := 104962900757407076693249

theorem tailTrace_1379798 : CollatzResearch.WordTrace tailWord_1379798 prefixEnd_1379798 104962900757407076693249 := by
  unfold tailWord_1379798
  simp only [CollatzResearch.WordTrace]
  refine ⟨3145335465952185723899753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33550244970156647721597365 3145335465952185723899753)
  ·
    refine ⟨2359001599464139292924815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3145335465952185723899753 2359001599464139292924815)
    ·
      refine ⟨3538502399196208939387223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2359001599464139292924815 3538502399196208939387223)
      ·
        refine ⟨5307753598794313409080835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3538502399196208939387223 5307753598794313409080835)
        ·
          refine ⟨7961630398191470113621253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5307753598794313409080835 7961630398191470113621253)
          ·
            refine ⟨1492805699660900646303985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7961630398191470113621253 1492805699660900646303985)
            ·
              refine ⟨1119604274745675484727989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1492805699660900646303985 1119604274745675484727989)
              ·
                refine ⟨104962900757407076693249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1119604274745675484727989 104962900757407076693249)
                ·
                  rfl

theorem cell21_1379798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_1379798 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1379798 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1379798 prefixEnd_1379798 := by exact prefixLift 1379798
  have htrace : WordTrace (prefixWord ++ tailWord_1379798) baseStart_1379798 baseEnd_1379798 := by
    simpa [prefixWord, tailWord_1379798, baseEnd_1379798] using wordTrace_append hprefix tailTrace_1379798
  have hstable : (prefixWord ++ tailWord_1379798).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379798).length < 2 ^ (prefixWord ++ tailWord_1379798).sum := by decide
  have hdescent : baseEnd_1379798 < baseStart_1379798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379916 : List Nat := [2, 2, 1, 3, 1, 4, 3, 5]
def baseStart_1379916 : Nat := 118140960795 + 1379916 * 2 ^ 59
def prefixEnd_1379916 : Nat := 4983230072969 + 3 ^ 40 * 1379916 * 2
def baseEnd_1379916 : Nat := 104971877159959749037613

theorem tailTrace_1379916 : CollatzResearch.WordTrace tailWord_1379916 prefixEnd_1379916 104971877159959749037613 := by
  unfold tailWord_1379916
  simp only [CollatzResearch.WordTrace]
  refine ⟨25164835634403738867595801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33553114179204985156794401 25164835634403738867595801)
  ·
    refine ⟨18873626725802804150696851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25164835634403738867595801 18873626725802804150696851)
    ·
      refine ⟨28310440088704206226045277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18873626725802804150696851 28310440088704206226045277)
      ·
        refine ⟨10616415033264077334766979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28310440088704206226045277 10616415033264077334766979)
        ·
          refine ⟨15924622549896116002150469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10616415033264077334766979 15924622549896116002150469)
          ·
            refine ⟨2985866728105521750403213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15924622549896116002150469 2985866728105521750403213)
            ·
              refine ⟨1119700023039570656401205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2985866728105521750403213 1119700023039570656401205)
              ·
                refine ⟨104971877159959749037613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1119700023039570656401205 104971877159959749037613)
                ·
                  rfl

theorem cell21_1379916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 5].length) (baseStart_1379916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1379916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1379916 prefixEnd_1379916 := by exact prefixLift 1379916
  have htrace : WordTrace (prefixWord ++ tailWord_1379916) baseStart_1379916 baseEnd_1379916 := by
    simpa [prefixWord, tailWord_1379916, baseEnd_1379916] using wordTrace_append hprefix tailTrace_1379916
  have hstable : (prefixWord ++ tailWord_1379916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379916).length < 2 ^ (prefixWord ++ tailWord_1379916).sum := by decide
  have hdescent : baseEnd_1379916 < baseStart_1379916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379933 : List Nat := [1, 4, 4, 2, 1, 1, 8]
def baseStart_1379933 : Nat := 118140960795 + 1379933 * 2 ^ 59
def prefixEnd_1379933 : Nat := 4983230072969 + 3 ^ 40 * 1379933 * 2
def baseEnd_1379933 : Nat := 34991056790165666147719

theorem tailTrace_1379933 : CollatzResearch.WordTrace tailWord_1379933 prefixEnd_1379933 34991056790165666147719 := by
  unfold tailWord_1379933
  simp only [CollatzResearch.WordTrace]
  refine ⟨50330291309745889638560453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33553527539830593092373635 50330291309745889638560453)
  ·
    refine ⟨9436929620577354307230085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50330291309745889638560453 9436929620577354307230085)
    ·
      refine ⟨1769424303858253932605641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9436929620577354307230085 1769424303858253932605641)
      ·
        refine ⟨1327068227893690449454231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1769424303858253932605641 1327068227893690449454231)
        ·
          refine ⟨1990602341840535674181347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1327068227893690449454231 1990602341840535674181347)
          ·
            refine ⟨2985903512760803511272021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1990602341840535674181347 2985903512760803511272021)
            ·
              refine ⟨34991056790165666147719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2985903512760803511272021 34991056790165666147719)
              ·
                rfl

theorem cell21_1379933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 8].length) (baseStart_1379933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1379933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1379933 prefixEnd_1379933 := by exact prefixLift 1379933
  have htrace : WordTrace (prefixWord ++ tailWord_1379933) baseStart_1379933 baseEnd_1379933 := by
    simpa [prefixWord, tailWord_1379933, baseEnd_1379933] using wordTrace_append hprefix tailTrace_1379933
  have hstable : (prefixWord ++ tailWord_1379933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379933).length < 2 ^ (prefixWord ++ tailWord_1379933).sum := by decide
  have hdescent : baseEnd_1379933 < baseStart_1379933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379975 : List Nat := [1, 1, 4, 2, 1, 4, 1, 7]
def baseStart_1379975 : Nat := 118140960795 + 1379975 * 2 ^ 59
def prefixEnd_1379975 : Nat := 4983230072969 + 3 ^ 40 * 1379975 * 2
def baseEnd_1379975 : Nat := 104976365361236085209795

theorem tailTrace_1379975 : CollatzResearch.WordTrace tailWord_1379975 prefixEnd_1379975 104976365361236085209795 := by
  unfold tailWord_1379975
  simp only [CollatzResearch.WordTrace]
  refine ⟨50331823175593730811589379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33554548783729153874392919 50331823175593730811589379)
  ·
    refine ⟨75497734763390596217384069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50331823175593730811589379 75497734763390596217384069)
    ·
      refine ⟨14155825268135736790759513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75497734763390596217384069 14155825268135736790759513)
      ·
        refine ⟨10616868951101802593069635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14155825268135736790759513 10616868951101802593069635)
        ·
          refine ⟨15925303426652703889604453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10616868951101802593069635 15925303426652703889604453)
          ·
            refine ⟨2985994392497381979300835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15925303426652703889604453 2985994392497381979300835)
            ·
              refine ⟨4478991588746072968951253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2985994392497381979300835 4478991588746072968951253)
              ·
                refine ⟨104976365361236085209795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4478991588746072968951253 104976365361236085209795)
                ·
                  rfl

theorem cell21_1379975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 7].length) (baseStart_1379975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1379975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1379975 prefixEnd_1379975 := by exact prefixLift 1379975
  have htrace : WordTrace (prefixWord ++ tailWord_1379975) baseStart_1379975 baseEnd_1379975 := by
    simpa [prefixWord, tailWord_1379975, baseEnd_1379975] using wordTrace_append hprefix tailTrace_1379975
  have hstable : (prefixWord ++ tailWord_1379975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379975).length < 2 ^ (prefixWord ++ tailWord_1379975).sum := by decide
  have hdescent : baseEnd_1379975 < baseStart_1379975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379989 : List Nat := [1, 3, 2, 1, 1, 1, 1, 4, 7]
def baseStart_1379989 : Nat := 118140960795 + 1379989 * 2 ^ 59
def prefixEnd_1379989 : Nat := 4983230072969 + 3 ^ 40 * 1379989 * 2
def baseEnd_1379989 : Nat := 314932291074447342396023

theorem tailTrace_1379989 : CollatzResearch.WordTrace tailWord_1379989 prefixEnd_1379989 314932291074447342396023 := by
  unfold tailWord_1379989
  simp only [CollatzResearch.WordTrace]
  refine ⟨50332333797543011202599021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33554889198362007468399347 50332333797543011202599021)
  ·
    refine ⟨18874625174078629200974633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50332333797543011202599021 18874625174078629200974633)
    ·
      refine ⟨14155968880558971900730975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18874625174078629200974633 14155968880558971900730975)
      ·
        refine ⟨21233953320838457851096463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14155968880558971900730975 21233953320838457851096463)
        ·
          refine ⟨31850929981257686776644695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21233953320838457851096463 31850929981257686776644695)
          ·
            refine ⟨47776394971886530164967043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31850929981257686776644695 47776394971886530164967043)
            ·
              refine ⟨71664592457829795247450565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47776394971886530164967043 71664592457829795247450565)
              ·
                refine ⟨13437111085843086608896981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71664592457829795247450565 13437111085843086608896981)
                ·
                  refine ⟨314932291074447342396023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13437111085843086608896981 314932291074447342396023)
                  ·
                    rfl

theorem cell21_1379989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_1379989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1379989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1379989 prefixEnd_1379989 := by exact prefixLift 1379989
  have htrace : WordTrace (prefixWord ++ tailWord_1379989) baseStart_1379989 baseEnd_1379989 := by
    simpa [prefixWord, tailWord_1379989, baseEnd_1379989] using wordTrace_append hprefix tailTrace_1379989
  have hstable : (prefixWord ++ tailWord_1379989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379989).length < 2 ^ (prefixWord ++ tailWord_1379989).sum := by decide
  have hdescent : baseEnd_1379989 < baseStart_1379989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380082 : List Nat := [3, 2, 1, 3, 1, 1, 3, 2, 5]
def baseStart_1380082 : Nat := 118140960795 + 1380082 * 2 ^ 59
def prefixEnd_1380082 : Nat := 4983230072969 + 3 ^ 40 * 1380082 * 2
def baseEnd_1380082 : Nat := 314953514941499847345833

theorem tailTrace_1380082 : CollatzResearch.WordTrace tailWord_1380082 prefixEnd_1380082 314953514941499847345833 := by
  unfold tailWord_1380082
  simp only [CollatzResearch.WordTrace]
  refine ⟨12583931446551522021433625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33557150524137392057156333 12583931446551522021433625)
  ·
    refine ⟨9437948584913641516075219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12583931446551522021433625 9437948584913641516075219)
    ·
      refine ⟨14156922877370462274112829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9437948584913641516075219 14156922877370462274112829)
      ·
        refine ⟨5308846079013923352792311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14156922877370462274112829 5308846079013923352792311)
        ·
          refine ⟨7963269118520885029188467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5308846079013923352792311 7963269118520885029188467)
          ·
            refine ⟨11944903677781327543782701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7963269118520885029188467 11944903677781327543782701)
            ·
              refine ⟨4479338879167997828918513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11944903677781327543782701 4479338879167997828918513)
              ·
                refine ⟨3359504159375998371688885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4479338879167997828918513 3359504159375998371688885)
                ·
                  refine ⟨314953514941499847345833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3359504159375998371688885 314953514941499847345833)
                  ·
                    rfl

theorem cell21_1380082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_1380082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1380082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1380082 prefixEnd_1380082 := by exact prefixLift 1380082
  have htrace : WordTrace (prefixWord ++ tailWord_1380082) baseStart_1380082 baseEnd_1380082 := by
    simpa [prefixWord, tailWord_1380082, baseEnd_1380082] using wordTrace_append hprefix tailTrace_1380082
  have hstable : (prefixWord ++ tailWord_1380082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380082).length < 2 ^ (prefixWord ++ tailWord_1380082).sum := by decide
  have hdescent : baseEnd_1380082 < baseStart_1380082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380130 : List Nat := [3, 3, 1, 1, 2, 1, 5, 1, 4]
def baseStart_1380130 : Nat := 118140960795 + 1380130 * 2 ^ 59
def prefixEnd_1380130 : Nat := 4983230072969 + 3 ^ 40 * 1380130 * 2
def baseEnd_1380130 : Nat := 314964469195462430545735

theorem tailTrace_1380130 : CollatzResearch.WordTrace tailWord_1380130 prefixEnd_1380130 314964469195462430545735 := by
  unfold tailWord_1380130
  simp only [CollatzResearch.WordTrace]
  refine ⟨12584369122508048070870461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33558317660021461522321229 12584369122508048070870461)
  ·
    refine ⟨4719138420940518026576423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12584369122508048070870461 4719138420940518026576423)
    ·
      refine ⟨7078707631410777039864635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4719138420940518026576423 7078707631410777039864635)
      ·
        refine ⟨10618061447116165559796953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7078707631410777039864635 10618061447116165559796953)
        ·
          refine ⟨7963546085337124169847715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10618061447116165559796953 7963546085337124169847715)
          ·
            refine ⟨11945319128005686254771573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7963546085337124169847715 11945319128005686254771573)
            ·
              refine ⟨1119873668250533086384835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11945319128005686254771573 1119873668250533086384835)
              ·
                refine ⟨1679810502375799629577253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1119873668250533086384835 1679810502375799629577253)
                ·
                  refine ⟨314964469195462430545735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1679810502375799629577253 314964469195462430545735)
                  ·
                    rfl

theorem cell21_1380130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_1380130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1380130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1380130 prefixEnd_1380130 := by exact prefixLift 1380130
  have htrace : WordTrace (prefixWord ++ tailWord_1380130) baseStart_1380130 baseEnd_1380130 := by
    simpa [prefixWord, tailWord_1380130, baseEnd_1380130] using wordTrace_append hprefix tailTrace_1380130
  have hstable : (prefixWord ++ tailWord_1380130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380130).length < 2 ^ (prefixWord ++ tailWord_1380130).sum := by decide
  have hdescent : baseEnd_1380130 < baseStart_1380130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380254 : List Nat := [4, 3, 1, 3, 1, 1, 3, 5]
def baseStart_1380254 : Nat := 118140960795 + 1380254 * 2 ^ 59
def prefixEnd_1380254 : Nat := 4983230072969 + 3 ^ 40 * 1380254 * 2
def baseEnd_1380254 : Nat := 104997589228288590159605

theorem tailTrace_1380254 : CollatzResearch.WordTrace tailWord_1380254 prefixEnd_1380254 104997589228288590159605 := by
  unfold tailWord_1380254
  simp only [CollatzResearch.WordTrace]
  refine ⟨6292749892697870182624477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33561332761055307640663877 6292749892697870182624477)
  ·
    refine ⟨2359781209761701318484179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6292749892697870182624477 2359781209761701318484179)
    ·
      refine ⟨3539671814642551977726269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2359781209761701318484179 3539671814642551977726269)
      ·
        refine ⟨1327376930490956991647351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3539671814642551977726269 1327376930490956991647351)
        ·
          refine ⟨1991065395736435487471027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1327376930490956991647351 1991065395736435487471027)
          ·
            refine ⟨2986598093604653231206541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1991065395736435487471027 2986598093604653231206541)
            ·
              refine ⟨1119974285101744961702453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2986598093604653231206541 1119974285101744961702453)
              ·
                refine ⟨104997589228288590159605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1119974285101744961702453 104997589228288590159605)
                ·
                  rfl

theorem cell21_1380254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_1380254 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1380254 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1380254 prefixEnd_1380254 := by exact prefixLift 1380254
  have htrace : WordTrace (prefixWord ++ tailWord_1380254) baseStart_1380254 baseEnd_1380254 := by
    simpa [prefixWord, tailWord_1380254, baseEnd_1380254] using wordTrace_append hprefix tailTrace_1380254
  have hstable : (prefixWord ++ tailWord_1380254).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380254).length < 2 ^ (prefixWord ++ tailWord_1380254).sum := by decide
  have hdescent : baseEnd_1380254 < baseStart_1380254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380313 : List Nat := [1, 2, 1, 2, 7, 1, 2, 5]
def baseStart_1380313 : Nat := 118140960795 + 1380313 * 2 ^ 59
def prefixEnd_1380313 : Nat := 4983230072969 + 3 ^ 40 * 1380313 * 2
def baseEnd_1380313 : Nat := 105002077429564926331787

theorem tailTrace_1380313 : CollatzResearch.WordTrace tailWord_1380313 prefixEnd_1380313 105002077429564926331787 := by
  unfold tailWord_1380313
  simp only [CollatzResearch.WordTrace]
  refine ⟨50344151048369214537393593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33562767365579476358262395 50344151048369214537393593)
  ·
    refine ⟨37758113286276910903045195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50344151048369214537393593 37758113286276910903045195)
    ·
      refine ⟨56637169929415366354567793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37758113286276910903045195 56637169929415366354567793)
      ·
        refine ⟨42477877447061524765925845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56637169929415366354567793 42477877447061524765925845)
        ·
          refine ⟨995575252665504486701387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 42477877447061524765925845 995575252665504486701387)
          ·
            refine ⟨1493362878998256730052081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 995575252665504486701387 1493362878998256730052081)
            ·
              refine ⟨1120022159248692547539061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1493362878998256730052081 1120022159248692547539061)
              ·
                refine ⟨105002077429564926331787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1120022159248692547539061 105002077429564926331787)
                ·
                  rfl

theorem cell21_1380313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 5].length) (baseStart_1380313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1380313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1380313 prefixEnd_1380313 := by exact prefixLift 1380313
  have htrace : WordTrace (prefixWord ++ tailWord_1380313) baseStart_1380313 baseEnd_1380313 := by
    simpa [prefixWord, tailWord_1380313, baseEnd_1380313] using wordTrace_append hprefix tailTrace_1380313
  have hstable : (prefixWord ++ tailWord_1380313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380313).length < 2 ^ (prefixWord ++ tailWord_1380313).sum := by decide
  have hdescent : baseEnd_1380313 < baseStart_1380313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380400 : List Nat := [2, 1, 1, 1, 2, 5, 1, 4, 4]
def baseStart_1380400 : Nat := 118140960795 + 1380400 * 2 ^ 59
def prefixEnd_1380400 : Nat := 4983230072969 + 3 ^ 40 * 1380400 * 2
def baseEnd_1380400 : Nat := 315026086874001961045183

theorem tailTrace_1380400 : CollatzResearch.WordTrace tailWord_1380400 prefixEnd_1380400 315026086874001961045183 := by
  unfold tailWord_1380400
  simp only [CollatzResearch.WordTrace]
  refine ⟨25173662099527014197905327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33564882799369352263873769 25173662099527014197905327)
  ·
    refine ⟨37760493149290521296857991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25173662099527014197905327 37760493149290521296857991)
    ·
      refine ⟨56640739723935781945286987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37760493149290521296857991 56640739723935781945286987)
      ·
        refine ⟨84961109585903672917930481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56640739723935781945286987 84961109585903672917930481)
        ·
          refine ⟨63720832189427754688447861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84961109585903672917930481 63720832189427754688447861)
          ·
            refine ⟨5973828017758852002041987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63720832189427754688447861 5973828017758852002041987)
            ·
              refine ⟨8960742026638278003062981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5973828017758852002041987 8960742026638278003062981)
              ·
                refine ⟨1680139129994677125574309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8960742026638278003062981 1680139129994677125574309)
                ·
                  refine ⟨315026086874001961045183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1680139129994677125574309 315026086874001961045183)
                  ·
                    rfl

theorem cell21_1380400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 4, 4].length) (baseStart_1380400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1380400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1380400 prefixEnd_1380400 := by exact prefixLift 1380400
  have htrace : WordTrace (prefixWord ++ tailWord_1380400) baseStart_1380400 baseEnd_1380400 := by
    simpa [prefixWord, tailWord_1380400, baseEnd_1380400] using wordTrace_append hprefix tailTrace_1380400
  have hstable : (prefixWord ++ tailWord_1380400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380400).length < 2 ^ (prefixWord ++ tailWord_1380400).sum := by decide
  have hdescent : baseEnd_1380400 < baseStart_1380400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380403 : List Nat := [1, 1, 1, 2, 4, 1, 6, 2, 3]
def baseStart_1380403 : Nat := 118140960795 + 1380403 * 2 ^ 59
def prefixEnd_1380403 : Nat := 4983230072969 + 3 ^ 40 * 1380403 * 2
def baseEnd_1380403 : Nat := 315026771514874622495177

theorem tailTrace_1380403 : CollatzResearch.WordTrace tailWord_1380403 prefixEnd_1380403 315026771514874622495177 := by
  unfold tailWord_1380403
  simp only [CollatzResearch.WordTrace]
  refine ⟨50347433618043159908169863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33564955745362106605446575 50347433618043159908169863)
  ·
    refine ⟨75521150427064739862254795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50347433618043159908169863 75521150427064739862254795)
    ·
      refine ⟨113281725640597109793382193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75521150427064739862254795 113281725640597109793382193)
      ·
        refine ⟨84961294230447832345036645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113281725640597109793382193 84961294230447832345036645)
        ·
          refine ⟨15930242668208968564694371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84961294230447832345036645 15930242668208968564694371)
          ·
            refine ⟨23895364002313452847041557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15930242668208968564694371 23895364002313452847041557)
            ·
              refine ⟨1120095187608443102205073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23895364002313452847041557 1120095187608443102205073)
              ·
                refine ⟨840071390706332326653805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1120095187608443102205073 840071390706332326653805)
                ·
                  refine ⟨315026771514874622495177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 840071390706332326653805 315026771514874622495177)
                  ·
                    rfl

theorem cell21_1380403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 2, 3].length) (baseStart_1380403 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1380403 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1380403 prefixEnd_1380403 := by exact prefixLift 1380403
  have htrace : WordTrace (prefixWord ++ tailWord_1380403) baseStart_1380403 baseEnd_1380403 := by
    simpa [prefixWord, tailWord_1380403, baseEnd_1380403] using wordTrace_append hprefix tailTrace_1380403
  have hstable : (prefixWord ++ tailWord_1380403).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380403).length < 2 ^ (prefixWord ++ tailWord_1380403).sum := by decide
  have hdescent : baseEnd_1380403 < baseStart_1380403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380417 : List Nat := [1, 2, 5, 1, 2, 1, 2, 3, 4]
def baseStart_1380417 : Nat := 118140960795 + 1380417 * 2 ^ 59
def prefixEnd_1380417 : Nat := 4983230072969 + 3 ^ 40 * 1380417 * 2
def baseEnd_1380417 : Nat := 315029966505613709261815

theorem tailTrace_1380417 : CollatzResearch.WordTrace tailWord_1380417 prefixEnd_1380417 315029966505613709261815 := by
  unfold tailWord_1380417
  simp only [CollatzResearch.WordTrace]
  refine ⟨50347944239992440299179505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33565296159994960199453003 50347944239992440299179505)
  ·
    refine ⟨37760958179994330224384629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50347944239992440299179505 37760958179994330224384629)
    ·
      refine ⟨3540089829374468458536059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37760958179994330224384629 3540089829374468458536059)
      ·
        refine ⟨5310134744061702687804089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3540089829374468458536059 5310134744061702687804089)
        ·
          refine ⟨3982601058046277015853067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5310134744061702687804089 3982601058046277015853067)
          ·
            refine ⟨5973901587069415523779601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3982601058046277015853067 5973901587069415523779601)
            ·
              refine ⟨4480426190302061642834701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5973901587069415523779601 4480426190302061642834701)
              ·
                refine ⟨1680159821363273116063013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4480426190302061642834701 1680159821363273116063013)
                ·
                  refine ⟨315029966505613709261815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1680159821363273116063013 315029966505613709261815)
                  ·
                    rfl

theorem cell21_1380417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 3, 4].length) (baseStart_1380417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1380417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1380417 prefixEnd_1380417 := by exact prefixLift 1380417
  have htrace : WordTrace (prefixWord ++ tailWord_1380417) baseStart_1380417 baseEnd_1380417 := by
    simpa [prefixWord, tailWord_1380417, baseEnd_1380417] using wordTrace_append hprefix tailTrace_1380417
  have hstable : (prefixWord ++ tailWord_1380417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380417).length < 2 ^ (prefixWord ++ tailWord_1380417).sum := by decide
  have hdescent : baseEnd_1380417 < baseStart_1380417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380462 : List Nat := [4, 1, 2, 2, 1, 1, 4, 1, 5]
def baseStart_1380462 : Nat := 118140960795 + 1380462 * 2 ^ 59
def prefixEnd_1380462 : Nat := 4983230072969 + 3 ^ 40 * 1380462 * 2
def baseEnd_1380462 : Nat := 315040236118703631011723

theorem tailTrace_1380462 : CollatzResearch.WordTrace tailWord_1380462 prefixEnd_1380462 315040236118703631011723 := by
  unfold tailWord_1380462
  simp only [CollatzResearch.WordTrace]
  refine ⟨6293698190603676623070955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33566390349886275323045093 6293698190603676623070955)
  ·
    refine ⟨9440547285905514934606433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6293698190603676623070955 9440547285905514934606433)
    ·
      refine ⟨7080410464429136200954825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9440547285905514934606433 7080410464429136200954825)
      ·
        refine ⟨5310307848321852150716119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7080410464429136200954825 5310307848321852150716119)
        ·
          refine ⟨7965461772482778226074179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5310307848321852150716119 7965461772482778226074179)
          ·
            refine ⟨11948192658724167339111269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7965461772482778226074179 11948192658724167339111269)
            ·
              refine ⟨2240286123510781376083363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11948192658724167339111269 2240286123510781376083363)
              ·
                refine ⟨3360429185266172064125045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2240286123510781376083363 3360429185266172064125045)
                ·
                  refine ⟨315040236118703631011723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3360429185266172064125045 315040236118703631011723)
                  ·
                    rfl

theorem cell21_1380462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_1380462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1380462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1380462 prefixEnd_1380462 := by exact prefixLift 1380462
  have htrace : WordTrace (prefixWord ++ tailWord_1380462) baseStart_1380462 baseEnd_1380462 := by
    simpa [prefixWord, tailWord_1380462, baseEnd_1380462] using wordTrace_append hprefix tailTrace_1380462
  have hstable : (prefixWord ++ tailWord_1380462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380462).length < 2 ^ (prefixWord ++ tailWord_1380462).sum := by decide
  have hdescent : baseEnd_1380462 < baseStart_1380462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380583 : List Nat := [1, 1, 5, 3, 1, 1, 3, 6]
def baseStart_1380583 : Nat := 118140960795 + 1380583 * 2 ^ 59
def prefixEnd_1380583 : Nat := 4983230072969 + 3 ^ 40 * 1380583 * 2
def baseEnd_1380583 : Nat := 105022616655744769831603

theorem tailTrace_1380583 : CollatzResearch.WordTrace tailWord_1380583 prefixEnd_1380583 105022616655744769831603 := by
  unfold tailWord_1380583
  simp only [CollatzResearch.WordTrace]
  refine ⟨50353998757391050649722403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33569332504927367099814935 50353998757391050649722403)
  ·
    refine ⟨75530998136086575974583605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50353998757391050649722403 75530998136086575974583605)
    ·
      refine ⟨7081031075258116497617213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75530998136086575974583605 7081031075258116497617213)
      ·
        refine ⟨2655386653221793686606455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7081031075258116497617213 2655386653221793686606455)
        ·
          refine ⟨3983079979832690529909683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2655386653221793686606455 3983079979832690529909683)
          ·
            refine ⟨5974619969749035794864525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3983079979832690529909683 5974619969749035794864525)
            ·
              refine ⟨2240482488655888423074197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5974619969749035794864525 2240482488655888423074197)
              ·
                refine ⟨105022616655744769831603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2240482488655888423074197 105022616655744769831603)
                ·
                  rfl

theorem cell21_1380583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 6].length) (baseStart_1380583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1380583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1380583 prefixEnd_1380583 := by exact prefixLift 1380583
  have htrace : WordTrace (prefixWord ++ tailWord_1380583) baseStart_1380583 baseEnd_1380583 := by
    simpa [prefixWord, tailWord_1380583, baseEnd_1380583] using wordTrace_append hprefix tailTrace_1380583
  have hstable : (prefixWord ++ tailWord_1380583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380583).length < 2 ^ (prefixWord ++ tailWord_1380583).sum := by decide
  have hdescent : baseEnd_1380583 < baseStart_1380583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380611 : List Nat := [1, 1, 1, 3, 2, 3, 2, 2, 6]
def baseStart_1380611 : Nat := 118140960795 + 1380611 * 2 ^ 59
def prefixEnd_1380611 : Nat := 4983230072969 + 3 ^ 40 * 1380611 * 2
def baseEnd_1380611 : Nat := 315074239948712483028085

theorem tailTrace_1380611 : CollatzResearch.WordTrace tailWord_1380611 prefixEnd_1380611 315074239948712483028085 := by
  unfold tailWord_1380611
  simp only [CollatzResearch.WordTrace]
  refine ⟨50355020001289611431741687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33570013334193074287827791 50355020001289611431741687)
  ·
    refine ⟨75532530001934417147612531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50355020001289611431741687 75532530001934417147612531)
    ·
      refine ⟨113298795002901625721418797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75532530001934417147612531 113298795002901625721418797)
      ·
        refine ⟨42487048126088109645532049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113298795002901625721418797 42487048126088109645532049)
        ·
          refine ⟨31865286094566082234149037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42487048126088109645532049 31865286094566082234149037)
          ·
            refine ⟨11949482285462280837805889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31865286094566082234149037 11949482285462280837805889)
            ·
              refine ⟨8962111714096710628354417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11949482285462280837805889 8962111714096710628354417)
              ·
                refine ⟨6721583785572532971265813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8962111714096710628354417 6721583785572532971265813)
                ·
                  refine ⟨315074239948712483028085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6721583785572532971265813 315074239948712483028085)
                  ·
                    rfl

theorem cell21_1380611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 6].length) (baseStart_1380611 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1380611 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1380611 prefixEnd_1380611 := by exact prefixLift 1380611
  have htrace : WordTrace (prefixWord ++ tailWord_1380611) baseStart_1380611 baseEnd_1380611 := by
    simpa [prefixWord, tailWord_1380611, baseEnd_1380611] using wordTrace_append hprefix tailTrace_1380611
  have hstable : (prefixWord ++ tailWord_1380611).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380611).length < 2 ^ (prefixWord ++ tailWord_1380611).sum := by decide
  have hdescent : baseEnd_1380611 < baseStart_1380611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380656 : List Nat := [2, 1, 1, 1, 2, 2, 2, 3, 7]
def baseStart_1380656 : Nat := 118140960795 + 1380656 * 2 ^ 59
def prefixEnd_1380656 : Nat := 4983230072969 + 3 ^ 40 * 1380656 * 2
def baseEnd_1380656 : Nat := 315084509561802404777993

theorem tailTrace_1380656 : CollatzResearch.WordTrace tailWord_1380656 prefixEnd_1380656 315084509561802404777993 := by
  unfold tailWord_1380656
  simp only [CollatzResearch.WordTrace]
  refine ⟨25178330643063292058564911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33571107524084389411419881 25178330643063292058564911)
  ·
    refine ⟨37767495964594938087847367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25178330643063292058564911 37767495964594938087847367)
    ·
      refine ⟨56651243946892407131771051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37767495964594938087847367 56651243946892407131771051)
      ·
        refine ⟨84976865920338610697656577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56651243946892407131771051 84976865920338610697656577)
        ·
          refine ⟨63732649440253958023242433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84976865920338610697656577 63732649440253958023242433)
          ·
            refine ⟨47799487080190468517431825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63732649440253958023242433 47799487080190468517431825)
            ·
              refine ⟨35849615310142851388073869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47799487080190468517431825 35849615310142851388073869)
              ·
                refine ⟨13443605741303569270527701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35849615310142851388073869 13443605741303569270527701)
                ·
                  refine ⟨315084509561802404777993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13443605741303569270527701 315084509561802404777993)
                  ·
                    rfl

theorem cell21_1380656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 7].length) (baseStart_1380656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1380656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1380656 prefixEnd_1380656 := by exact prefixLift 1380656
  have htrace : WordTrace (prefixWord ++ tailWord_1380656) baseStart_1380656 baseEnd_1380656 := by
    simpa [prefixWord, tailWord_1380656, baseEnd_1380656] using wordTrace_append hprefix tailTrace_1380656
  have hstable : (prefixWord ++ tailWord_1380656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380656).length < 2 ^ (prefixWord ++ tailWord_1380656).sum := by decide
  have hdescent : baseEnd_1380656 < baseStart_1380656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380676 : List Nat := [2, 3, 4, 1, 2, 2, 7]
def baseStart_1380676 : Nat := 118140960795 + 1380676 * 2 ^ 59
def prefixEnd_1380676 : Nat := 4983230072969 + 3 ^ 40 * 1380676 * 2
def baseEnd_1380676 : Nat := 35009897092698534938291

theorem tailTrace_1380676 : CollatzResearch.WordTrace tailWord_1380676 prefixEnd_1380676 35009897092698534938291 := by
  unfold tailWord_1380676
  simp only [CollatzResearch.WordTrace]
  refine ⟨25178695373027063766428941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33571593830702751688571921 25178695373027063766428941)
  ·
    refine ⟨9442010764885148912410853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25178695373027063766428941 9442010764885148912410853)
    ·
      refine ⟨1770377018415965421077035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9442010764885148912410853 1770377018415965421077035)
      ·
        refine ⟨2655565527623948131615553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1770377018415965421077035 2655565527623948131615553)
        ·
          refine ⟨1991674145717961098711665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2655565527623948131615553 1991674145717961098711665)
          ·
            refine ⟨1493755609288470824033749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1991674145717961098711665 1493755609288470824033749)
            ·
              refine ⟨35009897092698534938291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1493755609288470824033749 35009897092698534938291)
              ·
                rfl

theorem cell21_1380676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 7].length) (baseStart_1380676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1380676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1380676 prefixEnd_1380676 := by exact prefixLift 1380676
  have htrace : WordTrace (prefixWord ++ tailWord_1380676) baseStart_1380676 baseEnd_1380676 := by
    simpa [prefixWord, tailWord_1380676, baseEnd_1380676] using wordTrace_append hprefix tailTrace_1380676
  have hstable : (prefixWord ++ tailWord_1380676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380676).length < 2 ^ (prefixWord ++ tailWord_1380676).sum := by decide
  have hdescent : baseEnd_1380676 < baseStart_1380676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380690 : List Nat := [3, 2, 2, 1, 1, 1, 2, 6, 3]
def baseStart_1380690 : Nat := 118140960795 + 1380690 * 2 ^ 59
def prefixEnd_1380690 : Nat := 4983230072969 + 3 ^ 40 * 1380690 * 2
def baseEnd_1380690 : Nat := 315092268825025901211257

theorem tailTrace_1380690 : CollatzResearch.WordTrace tailWord_1380690 prefixEnd_1380690 315092268825025901211257 := by
  unfold tailWord_1380690
  simp only [CollatzResearch.WordTrace]
  refine ⟨12589475342000851980966881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33571934245335605282578349 12589475342000851980966881)
  ·
    refine ⟨9442106506500638985725161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12589475342000851980966881 9442106506500638985725161)
    ·
      refine ⟨7081579879875479239293871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9442106506500638985725161 7081579879875479239293871)
      ·
        refine ⟨10622369819813218858940807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7081579879875479239293871 10622369819813218858940807)
        ·
          refine ⟨15933554729719828288411211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10622369819813218858940807 15933554729719828288411211)
          ·
            refine ⟨23900332094579742432616817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15933554729719828288411211 23900332094579742432616817)
            ·
              refine ⟨17925249070934806824462613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23900332094579742432616817 17925249070934806824462613)
              ·
                refine ⟨840246050200069069896685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17925249070934806824462613 840246050200069069896685)
                ·
                  refine ⟨315092268825025901211257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 840246050200069069896685 315092268825025901211257)
                  ·
                    rfl

theorem cell21_1380690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 6, 3].length) (baseStart_1380690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1380690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1380690 prefixEnd_1380690 := by exact prefixLift 1380690
  have htrace : WordTrace (prefixWord ++ tailWord_1380690) baseStart_1380690 baseEnd_1380690 := by
    simpa [prefixWord, tailWord_1380690, baseEnd_1380690] using wordTrace_append hprefix tailTrace_1380690
  have hstable : (prefixWord ++ tailWord_1380690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380690).length < 2 ^ (prefixWord ++ tailWord_1380690).sum := by decide
  have hdescent : baseEnd_1380690 < baseStart_1380690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380732 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 9]
def baseStart_1380732 : Nat := 118140960795 + 1380732 * 2 ^ 59
def prefixEnd_1380732 : Nat := 4983230072969 + 3 ^ 40 * 1380732 * 2
def baseEnd_1380732 : Nat := 315101853797243161511171

theorem tailTrace_1380732 : CollatzResearch.WordTrace tailWord_1380732 prefixEnd_1380732 315101853797243161511171 := by
  unfold tailWord_1380732
  simp only [CollatzResearch.WordTrace]
  refine ⟨25179716616925624548448225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33572955489234166064597633 25179716616925624548448225)
  ·
    refine ⟨18884787462694218411336169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25179716616925624548448225 18884787462694218411336169)
    ·
      refine ⟨14163590597020663808502127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18884787462694218411336169 14163590597020663808502127)
      ·
        refine ⟨21245385895530995712753191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14163590597020663808502127 21245385895530995712753191)
        ·
          refine ⟨31868078843296493569129787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21245385895530995712753191 31868078843296493569129787)
          ·
            refine ⟨47802118264944740353694681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31868078843296493569129787 47802118264944740353694681)
            ·
              refine ⟨35851588698708555265271011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47802118264944740353694681 35851588698708555265271011)
              ·
                refine ⟨53777383048062832897906517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35851588698708555265271011 53777383048062832897906517)
                ·
                  refine ⟨315101853797243161511171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 53777383048062832897906517 315101853797243161511171)
                  ·
                    rfl

theorem cell21_1380732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_1380732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1380732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1380732 prefixEnd_1380732 := by exact prefixLift 1380732
  have htrace : WordTrace (prefixWord ++ tailWord_1380732) baseStart_1380732 baseEnd_1380732 := by
    simpa [prefixWord, tailWord_1380732, baseEnd_1380732] using wordTrace_append hprefix tailTrace_1380732
  have hstable : (prefixWord ++ tailWord_1380732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380732).length < 2 ^ (prefixWord ++ tailWord_1380732).sum := by decide
  have hdescent : baseEnd_1380732 < baseStart_1380732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380766 : List Nat := [4, 3, 1, 2, 1, 1, 1, 1, 7]
def baseStart_1380766 : Nat := 118140960795 + 1380766 * 2 ^ 59
def prefixEnd_1380766 : Nat := 4983230072969 + 3 ^ 40 * 1380766 * 2
def baseEnd_1380766 : Nat := 315109613060466657944435

theorem tailTrace_1380766 : CollatzResearch.WordTrace tailWord_1380766 prefixEnd_1380766 315109613060466657944435 := by
  unfold tailWord_1380766
  simp only [CollatzResearch.WordTrace]
  refine ⟨6295084164466009112954269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33573782210485381935756101 6295084164466009112954269)
  ·
    refine ⟨2360656561674753417357851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6295084164466009112954269 2360656561674753417357851)
    ·
      refine ⟨3540984842512130126036777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2360656561674753417357851 3540984842512130126036777)
      ·
        refine ⟨2655738631884097594527583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3540984842512130126036777 2655738631884097594527583)
        ·
          refine ⟨3983607947826146391791375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2655738631884097594527583 3983607947826146391791375)
          ·
            refine ⟨5975411921739219587687063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3983607947826146391791375 5975411921739219587687063)
            ·
              refine ⟨8963117882608829381530595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5975411921739219587687063 8963117882608829381530595)
              ·
                refine ⟨13444676823913244072295893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8963117882608829381530595 13444676823913244072295893)
                ·
                  refine ⟨315109613060466657944435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13444676823913244072295893 315109613060466657944435)
                  ·
                    rfl

theorem cell21_1380766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_1380766 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1380766 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1380766 prefixEnd_1380766 := by exact prefixLift 1380766
  have htrace : WordTrace (prefixWord ++ tailWord_1380766) baseStart_1380766 baseEnd_1380766 := by
    simpa [prefixWord, tailWord_1380766, baseEnd_1380766] using wordTrace_append hprefix tailTrace_1380766
  have hstable : (prefixWord ++ tailWord_1380766).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380766).length < 2 ^ (prefixWord ++ tailWord_1380766).sum := by decide
  have hdescent : baseEnd_1380766 < baseStart_1380766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380777 : List Nat := [1, 2, 1, 1, 1, 1, 3, 11]
def baseStart_1380777 : Nat := 118140960795 + 1380777 * 2 ^ 59
def prefixEnd_1380777 : Nat := 4983230072969 + 3 ^ 40 * 1380777 * 2
def baseEnd_1380777 : Nat := 105037374470111027753693

theorem tailTrace_1380777 : CollatzResearch.WordTrace tailWord_1380777 prefixEnd_1380777 105037374470111027753693 := by
  unfold tailWord_1380777
  simp only [CollatzResearch.WordTrace]
  refine ⟨50361074518688221782284585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33574049679125481188189723 50361074518688221782284585)
  ·
    refine ⟨37770805889016166336713439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50361074518688221782284585 37770805889016166336713439)
    ·
      refine ⟨56656208833524249505070159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37770805889016166336713439 56656208833524249505070159)
      ·
        refine ⟨84984313250286374257605239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56656208833524249505070159 84984313250286374257605239)
        ·
          refine ⟨127476469875429561386407859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84984313250286374257605239 127476469875429561386407859)
          ·
            refine ⟨191214704813144342079611789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127476469875429561386407859 191214704813144342079611789)
            ·
              refine ⟨71705514304929128279854421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191214704813144342079611789 71705514304929128279854421)
              ·
                refine ⟨105037374470111027753693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 71705514304929128279854421 105037374470111027753693)
                ·
                  rfl

theorem cell21_1380777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 11].length) (baseStart_1380777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1380777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1380777 prefixEnd_1380777 := by exact prefixLift 1380777
  have htrace : WordTrace (prefixWord ++ tailWord_1380777) baseStart_1380777 baseEnd_1380777 := by
    simpa [prefixWord, tailWord_1380777, baseEnd_1380777] using wordTrace_append hprefix tailTrace_1380777
  have hstable : (prefixWord ++ tailWord_1380777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380777).length < 2 ^ (prefixWord ++ tailWord_1380777).sum := by decide
  have hdescent : baseEnd_1380777 < baseStart_1380777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380797 : List Nat := [1, 4, 1, 2, 2, 4, 1, 2, 4]
def baseStart_1380797 : Nat := 118140960795 + 1380797 * 2 ^ 59
def prefixEnd_1380797 : Nat := 4983230072969 + 3 ^ 40 * 1380797 * 2
def baseEnd_1380797 : Nat := 315116687682817492927705

theorem tailTrace_1380797 : CollatzResearch.WordTrace tailWord_1380797 prefixEnd_1380797 315116687682817492927705 := by
  unfold tailWord_1380797
  simp only [CollatzResearch.WordTrace]
  refine ⟨50361803978615765198012645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33574535985743843465341763 50361803978615765198012645)
  ·
    refine ⟨9442838245990455974627371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50361803978615765198012645 9442838245990455974627371)
    ·
      refine ⟨14164257368985683961941057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9442838245990455974627371 14164257368985683961941057)
      ·
        refine ⟨10623193026739262971455793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14164257368985683961941057 10623193026739262971455793)
        ·
          refine ⟨7967394770054447228591845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10623193026739262971455793 7967394770054447228591845)
          ·
            refine ⟨1493886519385208855360971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7967394770054447228591845 1493886519385208855360971)
            ·
              refine ⟨2240829779077813283041457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1493886519385208855360971 2240829779077813283041457)
              ·
                refine ⟨1680622334308359962281093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2240829779077813283041457 1680622334308359962281093)
                ·
                  refine ⟨315116687682817492927705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1680622334308359962281093 315116687682817492927705)
                  ·
                    rfl

theorem cell21_1380797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_1380797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1380797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1380797 prefixEnd_1380797 := by exact prefixLift 1380797
  have htrace : WordTrace (prefixWord ++ tailWord_1380797) baseStart_1380797 baseEnd_1380797 := by
    simpa [prefixWord, tailWord_1380797, baseEnd_1380797] using wordTrace_append hprefix tailTrace_1380797
  have hstable : (prefixWord ++ tailWord_1380797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380797).length < 2 ^ (prefixWord ++ tailWord_1380797).sum := by decide
  have hdescent : baseEnd_1380797 < baseStart_1380797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380834 : List Nat := [3, 3, 3, 2, 2, 1, 1, 3, 3]
def baseStart_1380834 : Nat := 118140960795 + 1380834 * 2 ^ 59
def prefixEnd_1380834 : Nat := 4983230072969 + 3 ^ 40 * 1380834 * 2
def baseEnd_1380834 : Nat := 315125131586913650810963

theorem tailTrace_1380834 : CollatzResearch.WordTrace tailWord_1380834 prefixEnd_1380834 315125131586913650810963 := by
  unfold tailWord_1380834
  simp only [CollatzResearch.WordTrace]
  refine ⟨12590788369870430129277389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33575435652987813678073037 12590788369870430129277389)
  ·
    refine ⟨4721545638701411298479021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12590788369870430129277389 4721545638701411298479021)
    ·
      refine ⟨1770579614513029236929633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4721545638701411298479021 1770579614513029236929633)
      ·
        refine ⟨1327934710884771927697225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1770579614513029236929633 1327934710884771927697225)
        ·
          refine ⟨995951033163578945772919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1327934710884771927697225 995951033163578945772919)
          ·
            refine ⟨1493926549745368418659379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 995951033163578945772919 1493926549745368418659379)
            ·
              refine ⟨2240889824618052627989069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1493926549745368418659379 2240889824618052627989069)
              ·
                refine ⟨840333684231769735495901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2240889824618052627989069 840333684231769735495901)
                ·
                  refine ⟨315125131586913650810963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 840333684231769735495901 315125131586913650810963)
                  ·
                    rfl

theorem cell21_1380834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_1380834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1380834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1380834 prefixEnd_1380834 := by exact prefixLift 1380834
  have htrace : WordTrace (prefixWord ++ tailWord_1380834) baseStart_1380834 baseEnd_1380834 := by
    simpa [prefixWord, tailWord_1380834, baseEnd_1380834] using wordTrace_append hprefix tailTrace_1380834
  have hstable : (prefixWord ++ tailWord_1380834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380834).length < 2 ^ (prefixWord ++ tailWord_1380834).sum := by decide
  have hdescent : baseEnd_1380834 < baseStart_1380834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380839 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 8]
def baseStart_1380839 : Nat := 118140960795 + 1380839 * 2 ^ 59
def prefixEnd_1380839 : Nat := 4983230072969 + 3 ^ 40 * 1380839 * 2
def baseEnd_1380839 : Nat := 315126272655034753227619

theorem tailTrace_1380839 : CollatzResearch.WordTrace tailWord_1380839 prefixEnd_1380839 315126272655034753227619 := by
  unfold tailWord_1380839
  simp only [CollatzResearch.WordTrace]
  refine ⟨50363335844463606371041571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33575557229642404247361047 50363335844463606371041571)
  ·
    refine ⟨75545003766695409556562357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50363335844463606371041571 75545003766695409556562357)
    ·
      refine ⟨7082344103127694645927721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75545003766695409556562357 7082344103127694645927721)
      ·
        refine ⟨5311758077345770984445791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7082344103127694645927721 5311758077345770984445791)
        ·
          refine ⟨7967637116018656476668687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5311758077345770984445791 7967637116018656476668687)
          ·
            refine ⟨11951455674027984715003031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7967637116018656476668687 11951455674027984715003031)
            ·
              refine ⟨17927183511041977072504547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11951455674027984715003031 17927183511041977072504547)
              ·
                refine ⟨26890775266562965608756821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17927183511041977072504547 26890775266562965608756821)
                ·
                  refine ⟨315126272655034753227619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26890775266562965608756821 315126272655034753227619)
                  ·
                    rfl

theorem cell21_1380839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 8].length) (baseStart_1380839 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1380839 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1380839 prefixEnd_1380839 := by exact prefixLift 1380839
  have htrace : WordTrace (prefixWord ++ tailWord_1380839) baseStart_1380839 baseEnd_1380839 := by
    simpa [prefixWord, tailWord_1380839, baseEnd_1380839] using wordTrace_append hprefix tailTrace_1380839
  have hstable : (prefixWord ++ tailWord_1380839).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380839).length < 2 ^ (prefixWord ++ tailWord_1380839).sum := by decide
  have hdescent : baseEnd_1380839 < baseStart_1380839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381087 : List Nat := [1, 1, 2, 3, 2, 5, 2, 2, 3]
def baseStart_1381087 : Nat := 118140960795 + 1381087 * 2 ^ 59
def prefixEnd_1381087 : Nat := 4983230072969 + 3 ^ 40 * 1381087 * 2
def baseEnd_1381087 : Nat := 315182869633841433093779

theorem tailTrace_1381087 : CollatzResearch.WordTrace tailWord_1381087 prefixEnd_1381087 315182869633841433093779 := by
  unfold tailWord_1381087
  simp only [CollatzResearch.WordTrace]
  refine ⟨50372381147565144726069515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33581587431710096484046343 50372381147565144726069515)
  ·
    refine ⟨75558571721347717089104273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50372381147565144726069515 75558571721347717089104273)
    ·
      refine ⟨56668928791010787816828205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75558571721347717089104273 56668928791010787816828205)
      ·
        refine ⟨21250848296629045431310577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56668928791010787816828205 21250848296629045431310577)
        ·
          refine ⟨15938136222471784073482933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21250848296629045431310577 15938136222471784073482933)
          ·
            refine ⟨1494200270856729756889025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15938136222471784073482933 1494200270856729756889025)
            ·
              refine ⟨1120650203142547317666769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1494200270856729756889025 1120650203142547317666769)
              ·
                refine ⟨840487652356910488250077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1120650203142547317666769 840487652356910488250077)
                ·
                  refine ⟨315182869633841433093779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 840487652356910488250077 315182869633841433093779)
                  ·
                    rfl

theorem cell21_1381087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 2, 3].length) (baseStart_1381087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1381087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1381087 prefixEnd_1381087 := by exact prefixLift 1381087
  have htrace : WordTrace (prefixWord ++ tailWord_1381087) baseStart_1381087 baseEnd_1381087 := by
    simpa [prefixWord, tailWord_1381087, baseEnd_1381087] using wordTrace_append hprefix tailTrace_1381087
  have hstable : (prefixWord ++ tailWord_1381087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381087).length < 2 ^ (prefixWord ++ tailWord_1381087).sum := by decide
  have hdescent : baseEnd_1381087 < baseStart_1381087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381112 : List Nat := [2, 1, 2, 1, 1, 2, 5, 2, 5]
def baseStart_1381112 : Nat := 118140960795 + 1381112 * 2 ^ 59
def prefixEnd_1381112 : Nat := 4983230072969 + 3 ^ 40 * 1381112 * 2
def baseEnd_1381112 : Nat := 315188574974446945177061

theorem tailTrace_1381112 : CollatzResearch.WordTrace tailWord_1381112 prefixEnd_1381112 315188574974446945177061 := by
  unfold tailWord_1381112
  simp only [CollatzResearch.WordTrace]
  refine ⟨25186646486237286997864795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33582195314983049330486393 25186646486237286997864795)
  ·
    refine ⟨37779969729355930496797193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25186646486237286997864795 37779969729355930496797193)
    ·
      refine ⟨28334977297016947872597895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37779969729355930496797193 28334977297016947872597895)
      ·
        refine ⟨42502465945525421808896843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28334977297016947872597895 42502465945525421808896843)
        ·
          refine ⟨63753698918288132713345265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42502465945525421808896843 63753698918288132713345265)
          ·
            refine ⟨47815274188716099535008949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63753698918288132713345265 47815274188716099535008949)
            ·
              refine ⟨4482681955192134331407089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47815274188716099535008949 4482681955192134331407089)
              ·
                refine ⟨3362011466394100748555317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4482681955192134331407089 3362011466394100748555317)
                ·
                  refine ⟨315188574974446945177061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3362011466394100748555317 315188574974446945177061)
                  ·
                    rfl

theorem cell21_1381112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 5].length) (baseStart_1381112 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1381112 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1381112 prefixEnd_1381112 := by exact prefixLift 1381112
  have htrace : WordTrace (prefixWord ++ tailWord_1381112) baseStart_1381112 baseEnd_1381112 := by
    simpa [prefixWord, tailWord_1381112, baseEnd_1381112] using wordTrace_append hprefix tailTrace_1381112
  have hstable : (prefixWord ++ tailWord_1381112).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381112).length < 2 ^ (prefixWord ++ tailWord_1381112).sum := by decide
  have hdescent : baseEnd_1381112 < baseStart_1381112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381129 : List Nat := [1, 2, 1, 1, 3, 2, 3, 5, 3]
def baseStart_1381129 : Nat := 118140960795 + 1381129 * 2 ^ 59
def prefixEnd_1381129 : Nat := 4983230072969 + 3 ^ 40 * 1381129 * 2
def baseEnd_1381129 : Nat := 315192454606058693393693

theorem tailTrace_1381129 : CollatzResearch.WordTrace tailWord_1381129 prefixEnd_1381129 315192454606058693393693 := by
  unfold tailWord_1381129
  simp only [CollatzResearch.WordTrace]
  refine ⟨50373913013412985899098441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33582608675608657266065627 50373913013412985899098441)
  ·
    refine ⟨37780434760059739424323831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50373913013412985899098441 37780434760059739424323831)
    ·
      refine ⟨56670652140089609136485747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37780434760059739424323831 56670652140089609136485747)
      ·
        refine ⟨85005978210134413704728621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56670652140089609136485747 85005978210134413704728621)
        ·
          refine ⟨31877241828800405139273233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85005978210134413704728621 31877241828800405139273233)
          ·
            refine ⟨23907931371600303854454925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31877241828800405139273233 23907931371600303854454925)
            ·
              refine ⟨8965474264350113945420597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23907931371600303854454925 8965474264350113945420597)
              ·
                refine ⟨840513212282823182383181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8965474264350113945420597 840513212282823182383181)
                ·
                  refine ⟨315192454606058693393693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 840513212282823182383181 315192454606058693393693)
                  ·
                    rfl

theorem cell21_1381129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 5, 3].length) (baseStart_1381129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1381129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1381129 prefixEnd_1381129 := by exact prefixLift 1381129
  have htrace : WordTrace (prefixWord ++ tailWord_1381129) baseStart_1381129 baseEnd_1381129 := by
    simpa [prefixWord, tailWord_1381129, baseEnd_1381129] using wordTrace_append hprefix tailTrace_1381129
  have hstable : (prefixWord ++ tailWord_1381129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381129).length < 2 ^ (prefixWord ++ tailWord_1381129).sum := by decide
  have hdescent : baseEnd_1381129 < baseStart_1381129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381157 : List Nat := [1, 3, 1, 2, 3, 1, 2, 8]
def baseStart_1381157 : Nat := 118140960795 + 1381157 * 2 ^ 59
def prefixEnd_1381157 : Nat := 4983230072969 + 3 ^ 40 * 1381157 * 2
def baseEnd_1381157 : Nat := 105066281529178955642323

theorem tailTrace_1381157 : CollatzResearch.WordTrace tailWord_1381157 prefixEnd_1381157 105066281529178955642323 := by
  unfold tailWord_1381157
  simp only [CollatzResearch.WordTrace]
  refine ⟨50374934257311546681117725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33583289504874364454078483 50374934257311546681117725)
  ·
    refine ⟨18890600346491830005419147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50374934257311546681117725 18890600346491830005419147)
    ·
      refine ⟨28335900519737745008128721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18890600346491830005419147 28335900519737745008128721)
      ·
        refine ⟨21251925389803308756096541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28335900519737745008128721 21251925389803308756096541)
        ·
          refine ⟨7969472021176240783536203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21251925389803308756096541 7969472021176240783536203)
          ·
            refine ⟨11954208031764361175304305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7969472021176240783536203 11954208031764361175304305)
            ·
              refine ⟨8965656023823270881478229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11954208031764361175304305 8965656023823270881478229)
              ·
                refine ⟨105066281529178955642323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8965656023823270881478229 105066281529178955642323)
                ·
                  rfl

theorem cell21_1381157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 8].length) (baseStart_1381157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1381157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1381157 prefixEnd_1381157 := by exact prefixLift 1381157
  have htrace : WordTrace (prefixWord ++ tailWord_1381157) baseStart_1381157 baseEnd_1381157 := by
    simpa [prefixWord, tailWord_1381157, baseEnd_1381157] using wordTrace_append hprefix tailTrace_1381157
  have hstable : (prefixWord ++ tailWord_1381157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381157).length < 2 ^ (prefixWord ++ tailWord_1381157).sum := by decide
  have hdescent : baseEnd_1381157 < baseStart_1381157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381233 : List Nat := [1, 2, 2, 2, 1, 4, 2, 7]
def baseStart_1381233 : Nat := 118140960795 + 1381233 * 2 ^ 59
def prefixEnd_1381233 : Nat := 4983230072969 + 3 ^ 40 * 1381233 * 2
def baseEnd_1381233 : Nat := 105072062940992541220049

theorem tailTrace_1381233 : CollatzResearch.WordTrace tailWord_1381233 prefixEnd_1381233 105072062940992541220049 := by
  unfold tailWord_1381233
  simp only [CollatzResearch.WordTrace]
  refine ⟨50377706205036211660884353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33585137470024141107256235 50377706205036211660884353)
  ·
    refine ⟨37783279653777158745663265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50377706205036211660884353 37783279653777158745663265)
    ·
      refine ⟨28337459740332869059247449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37783279653777158745663265 28337459740332869059247449)
      ·
        refine ⟨21253094805249651794435587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28337459740332869059247449 21253094805249651794435587)
        ·
          refine ⟨31879642207874477691653381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21253094805249651794435587 31879642207874477691653381)
          ·
            refine ⟨5977432913976464567185009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31879642207874477691653381 5977432913976464567185009)
            ·
              refine ⟨4483074685482348425388757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5977432913976464567185009 4483074685482348425388757)
              ·
                refine ⟨105072062940992541220049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4483074685482348425388757 105072062940992541220049)
                ·
                  rfl

theorem cell21_1381233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 7].length) (baseStart_1381233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1381233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1381233 prefixEnd_1381233 := by exact prefixLift 1381233
  have htrace : WordTrace (prefixWord ++ tailWord_1381233) baseStart_1381233 baseEnd_1381233 := by
    simpa [prefixWord, tailWord_1381233, baseEnd_1381233] using wordTrace_append hprefix tailTrace_1381233
  have hstable : (prefixWord ++ tailWord_1381233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381233).length < 2 ^ (prefixWord ++ tailWord_1381233).sum := by decide
  have hdescent : baseEnd_1381233 < baseStart_1381233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381270 : List Nat := [5, 3, 1, 1, 1, 1, 2, 3, 4]
def baseStart_1381270 : Nat := 118140960795 + 1381270 * 2 ^ 59
def prefixEnd_1381270 : Nat := 4983230072969 + 3 ^ 40 * 1381270 * 2
def baseEnd_1381270 : Nat := 315224632727073781543405

theorem tailTrace_1381270 : CollatzResearch.WordTrace tailWord_1381270 prefixEnd_1381270 315224632727073781543405 := by
  unfold tailWord_1381270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3148690981618885436248829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33586037137268111319987509 3148690981618885436248829)
  ·
    refine ⟨1180759118107082038593311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3148690981618885436248829 1180759118107082038593311)
    ·
      refine ⟨1771138677160623057889967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1180759118107082038593311 1771138677160623057889967)
      ·
        refine ⟨2656708015740934586834951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1771138677160623057889967 2656708015740934586834951)
        ·
          refine ⟨3985062023611401880252427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2656708015740934586834951 3985062023611401880252427)
          ·
            refine ⟨5977593035417102820378641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3985062023611401880252427 5977593035417102820378641)
            ·
              refine ⟨4483194776562827115283981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5977593035417102820378641 4483194776562827115283981)
              ·
                refine ⟨1681198041211060168231493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4483194776562827115283981 1681198041211060168231493)
                ·
                  refine ⟨315224632727073781543405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1681198041211060168231493 315224632727073781543405)
                  ·
                    rfl

theorem cell21_1381270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_1381270 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1381270 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1381270 prefixEnd_1381270 := by exact prefixLift 1381270
  have htrace : WordTrace (prefixWord ++ tailWord_1381270) baseStart_1381270 baseEnd_1381270 := by
    simpa [prefixWord, tailWord_1381270, baseEnd_1381270] using wordTrace_append hprefix tailTrace_1381270
  have hstable : (prefixWord ++ tailWord_1381270).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381270).length < 2 ^ (prefixWord ++ tailWord_1381270).sum := by decide
  have hdescent : baseEnd_1381270 < baseStart_1381270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381281 : List Nat := [1, 2, 3, 4, 1, 2, 1, 2, 5]
def baseStart_1381281 : Nat := 118140960795 + 1381281 * 2 ^ 59
def prefixEnd_1381281 : Nat := 4983230072969 + 3 ^ 40 * 1381281 * 2
def baseEnd_1381281 : Nat := 315227143076940206860049

theorem tailTrace_1381281 : CollatzResearch.WordTrace tailWord_1381281 prefixEnd_1381281 315227143076940206860049 := by
  unfold tailWord_1381281
  simp only [CollatzResearch.WordTrace]
  refine ⟨50379456908862315858631697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33586304605908210572421131 50379456908862315858631697)
  ·
    refine ⟨37784592681646736893973773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50379456908862315858631697 37784592681646736893973773)
    ·
      refine ⟨14169222255617526335240165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37784592681646736893973773 14169222255617526335240165)
      ·
        refine ⟨2656729172928286187857531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14169222255617526335240165 2656729172928286187857531)
        ·
          refine ⟨3985093759392429281786297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2656729172928286187857531 3985093759392429281786297)
          ·
            refine ⟨2988820319544321961339723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3985093759392429281786297 2988820319544321961339723)
            ·
              refine ⟨4483230479316482942009585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2988820319544321961339723 4483230479316482942009585)
              ·
                refine ⟨3362422859487362206507189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4483230479316482942009585 3362422859487362206507189)
                ·
                  refine ⟨315227143076940206860049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3362422859487362206507189 315227143076940206860049)
                  ·
                    rfl

theorem cell21_1381281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 5].length) (baseStart_1381281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1381281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1381281 prefixEnd_1381281 := by exact prefixLift 1381281
  have htrace : WordTrace (prefixWord ++ tailWord_1381281) baseStart_1381281 baseEnd_1381281 := by
    simpa [prefixWord, tailWord_1381281, baseEnd_1381281] using wordTrace_append hprefix tailTrace_1381281
  have hstable : (prefixWord ++ tailWord_1381281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381281).length < 2 ^ (prefixWord ++ tailWord_1381281).sum := by decide
  have hdescent : baseEnd_1381281 < baseStart_1381281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381312 : List Nat := [2, 1, 1, 2, 3, 5, 1, 2, 4]
def baseStart_1381312 : Nat := 118140960795 + 1381312 * 2 ^ 59
def prefixEnd_1381312 : Nat := 4983230072969 + 3 ^ 40 * 1381312 * 2
def baseEnd_1381312 : Nat := 315234217699291041843319

theorem tailTrace_1381312 : CollatzResearch.WordTrace tailWord_1381312 prefixEnd_1381312 315234217699291041843319 := by
  unfold tailWord_1381312
  simp only [CollatzResearch.WordTrace]
  refine ⟨25190293785875004076505095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33587058381166672102006793 25190293785875004076505095)
  ·
    refine ⟨37785440678812506114757643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25190293785875004076505095 37785440678812506114757643)
    ·
      refine ⟨56678161018218759172136465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37785440678812506114757643 56678161018218759172136465)
      ·
        refine ⟨42508620763664069379102349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56678161018218759172136465 42508620763664069379102349)
        ·
          refine ⟨15940732786374026017163381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42508620763664069379102349 15940732786374026017163381)
          ·
            refine ⟨1494443698722564939109067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15940732786374026017163381 1494443698722564939109067)
            ·
              refine ⟨2241665548083847408663601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1494443698722564939109067 2241665548083847408663601)
              ·
                refine ⟨1681249161062885556497701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2241665548083847408663601 1681249161062885556497701)
                ·
                  refine ⟨315234217699291041843319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1681249161062885556497701 315234217699291041843319)
                  ·
                    rfl

theorem cell21_1381312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 2, 4].length) (baseStart_1381312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1381312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1381312 prefixEnd_1381312 := by exact prefixLift 1381312
  have htrace : WordTrace (prefixWord ++ tailWord_1381312) baseStart_1381312 baseEnd_1381312 := by
    simpa [prefixWord, tailWord_1381312, baseEnd_1381312] using wordTrace_append hprefix tailTrace_1381312
  have hstable : (prefixWord ++ tailWord_1381312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381312).length < 2 ^ (prefixWord ++ tailWord_1381312).sum := by decide
  have hdescent : baseEnd_1381312 < baseStart_1381312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381343 : List Nat := [1, 1, 2, 3, 5, 2, 2, 5]
def baseStart_1381343 : Nat := 118140960795 + 1381343 * 2 ^ 59
def prefixEnd_1381343 : Nat := 4983230072969 + 3 ^ 40 * 1381343 * 2
def baseEnd_1381343 : Nat := 105080430773880625608863

theorem tailTrace_1381343 : CollatzResearch.WordTrace tailWord_1381343 prefixEnd_1381343 105080430773880625608863 := by
  unfold tailWord_1381343
  simp only [CollatzResearch.WordTrace]
  refine ⟨50381718234637700447388683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33587812156425133631592455 50381718234637700447388683)
  ·
    refine ⟨75572577351956550671083025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50381718234637700447388683 75572577351956550671083025)
    ·
      refine ⟨56679433013967413003312269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75572577351956550671083025 56679433013967413003312269)
      ·
        refine ⟨21254787380237779876242101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56679433013967413003312269 21254787380237779876242101)
        ·
          refine ⟨1992636316897291863397697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21254787380237779876242101 1992636316897291863397697)
          ·
            refine ⟨1494477237672968897548273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1992636316897291863397697 1494477237672968897548273)
            ·
              refine ⟨1120857928254726673161205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1494477237672968897548273 1120857928254726673161205)
              ·
                refine ⟨105080430773880625608863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1120857928254726673161205 105080430773880625608863)
                ·
                  rfl

theorem cell21_1381343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 5].length) (baseStart_1381343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1381343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1381343 prefixEnd_1381343 := by exact prefixLift 1381343
  have htrace : WordTrace (prefixWord ++ tailWord_1381343) baseStart_1381343 baseEnd_1381343 := by
    simpa [prefixWord, tailWord_1381343, baseEnd_1381343] using wordTrace_append hprefix tailTrace_1381343
  have hstable : (prefixWord ++ tailWord_1381343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381343).length < 2 ^ (prefixWord ++ tailWord_1381343).sum := by decide
  have hdescent : baseEnd_1381343 < baseStart_1381343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381388 : List Nat := [2, 2, 1, 2, 3, 2, 4, 1, 4]
def baseStart_1381388 : Nat := 118140960795 + 1381388 * 2 ^ 59
def prefixEnd_1381388 : Nat := 4983230072969 + 3 ^ 40 * 1381388 * 2
def baseEnd_1381388 : Nat := 315251561934731798576497

theorem tailTrace_1381388 : CollatzResearch.WordTrace tailWord_1381388 prefixEnd_1381388 315251561934731798576497 := by
  unfold tailWord_1381388
  simp only [CollatzResearch.WordTrace]
  refine ⟨25191679759737336566388409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33588906346316448755184545 25191679759737336566388409)
  ·
    refine ⟨18893759819803002424791307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25191679759737336566388409 18893759819803002424791307)
    ·
      refine ⟨28340639729704503637186961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18893759819803002424791307 28340639729704503637186961)
      ·
        refine ⟨21255479797278377727890221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28340639729704503637186961 21255479797278377727890221)
        ·
          refine ⟨7970804923979391647958833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21255479797278377727890221 7970804923979391647958833)
          ·
            refine ⟨5978103692984543735969125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7970804923979391647958833 5978103692984543735969125)
            ·
              refine ⟨1120894442434601950494211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5978103692984543735969125 1120894442434601950494211)
              ·
                refine ⟨1681341663651902925741317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1120894442434601950494211 1681341663651902925741317)
                ·
                  refine ⟨315251561934731798576497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1681341663651902925741317 315251561934731798576497)
                  ·
                    rfl

theorem cell21_1381388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 1, 4].length) (baseStart_1381388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1381388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1381388 prefixEnd_1381388 := by exact prefixLift 1381388
  have htrace : WordTrace (prefixWord ++ tailWord_1381388) baseStart_1381388 baseEnd_1381388 := by
    simpa [prefixWord, tailWord_1381388, baseEnd_1381388] using wordTrace_append hprefix tailTrace_1381388
  have hstable : (prefixWord ++ tailWord_1381388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381388).length < 2 ^ (prefixWord ++ tailWord_1381388).sum := by decide
  have hdescent : baseEnd_1381388 < baseStart_1381388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381447 : List Nat := [1, 1, 4, 1, 3, 2, 2, 3, 4]
def baseStart_1381447 : Nat := 118140960795 + 1381447 * 2 ^ 59
def prefixEnd_1381447 : Nat := 4983230072969 + 3 ^ 40 * 1381447 * 2
def baseEnd_1381447 : Nat := 315265026538560807093043

theorem tailTrace_1381447 : CollatzResearch.WordTrace tailWord_1381447 prefixEnd_1381447 315265026538560807093043 := by
  unfold tailWord_1381447
  simp only [CollatzResearch.WordTrace]
  refine ⟨50385511426260926209174595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33590340950840617472783063 50385511426260926209174595)
  ·
    refine ⟨75578267139391389313761893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50385511426260926209174595 75578267139391389313761893)
    ·
      refine ⟨14170925088635885496330355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75578267139391389313761893 14170925088635885496330355)
      ·
        refine ⟨21256387632953828244495533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14170925088635885496330355 21256387632953828244495533)
        ·
          refine ⟨7971145362357685591685825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21256387632953828244495533 7971145362357685591685825)
          ·
            refine ⟨5978359021768264193764369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7971145362357685591685825 5978359021768264193764369)
            ·
              refine ⟨4483769266326198145323277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5978359021768264193764369 4483769266326198145323277)
              ·
                refine ⟨1681413474872324304496229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4483769266326198145323277 1681413474872324304496229)
                ·
                  refine ⟨315265026538560807093043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1681413474872324304496229 315265026538560807093043)
                  ·
                    rfl

theorem cell21_1381447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 3, 4].length) (baseStart_1381447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1381447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1381447 prefixEnd_1381447 := by exact prefixLift 1381447
  have htrace : WordTrace (prefixWord ++ tailWord_1381447) baseStart_1381447 baseEnd_1381447 := by
    simpa [prefixWord, tailWord_1381447, baseEnd_1381447] using wordTrace_append hprefix tailTrace_1381447
  have hstable : (prefixWord ++ tailWord_1381447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381447).length < 2 ^ (prefixWord ++ tailWord_1381447).sum := by decide
  have hdescent : baseEnd_1381447 < baseStart_1381447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381475 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 9]
def baseStart_1381475 : Nat := 118140960795 + 1381475 * 2 ^ 59
def prefixEnd_1381475 : Nat := 4983230072969 + 3 ^ 40 * 1381475 * 2
def baseEnd_1381475 : Nat := 315271416520038980626319

theorem tailTrace_1381475 : CollatzResearch.WordTrace tailWord_1381475 prefixEnd_1381475 315271416520038980626319 := by
  unfold tailWord_1381475
  simp only [CollatzResearch.WordTrace]
  refine ⟨50386532670159486991193879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33591021780106324660795919 50386532670159486991193879)
  ·
    refine ⟨75579799005239230486790819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50386532670159486991193879 75579799005239230486790819)
    ·
      refine ⟨113369698507858845730186229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75579799005239230486790819 113369698507858845730186229)
      ·
        refine ⟨10628409235111766787204959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113369698507858845730186229 10628409235111766787204959)
        ·
          refine ⟨15942613852667650180807439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10628409235111766787204959 15942613852667650180807439)
          ·
            refine ⟨23913920779001475271211159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15942613852667650180807439 23913920779001475271211159)
            ·
              refine ⟨35870881168502212906816739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23913920779001475271211159 35870881168502212906816739)
              ·
                refine ⟨53806321752753319360225109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35870881168502212906816739 53806321752753319360225109)
                ·
                  refine ⟨315271416520038980626319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 53806321752753319360225109 315271416520038980626319)
                  ·
                    rfl

theorem cell21_1381475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 9].length) (baseStart_1381475 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1381475 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1381475 prefixEnd_1381475 := by exact prefixLift 1381475
  have htrace : WordTrace (prefixWord ++ tailWord_1381475) baseStart_1381475 baseEnd_1381475 := by
    simpa [prefixWord, tailWord_1381475, baseEnd_1381475] using wordTrace_append hprefix tailTrace_1381475
  have hstable : (prefixWord ++ tailWord_1381475).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381475).length < 2 ^ (prefixWord ++ tailWord_1381475).sum := by decide
  have hdescent : baseEnd_1381475 < baseStart_1381475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381512 : List Nat := [2, 1, 3, 4, 3, 1, 2, 5]
def baseStart_1381512 : Nat := 118140960795 + 1381512 * 2 ^ 59
def prefixEnd_1381512 : Nat := 4983230072969 + 3 ^ 40 * 1381512 * 2
def baseEnd_1381512 : Nat := 105093286808045046169859

theorem tailTrace_1381512 : CollatzResearch.WordTrace tailWord_1381512 prefixEnd_1381512 105093286808045046169859 := by
  unfold tailWord_1381512
  simp only [CollatzResearch.WordTrace]
  refine ⟨25193941085512721155145395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33591921447350294873527193 25193941085512721155145395)
  ·
    refine ⟨37790911628269081732718093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25193941085512721155145395 37790911628269081732718093)
    ·
      refine ⟨14171591860600905649769285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37790911628269081732718093 14171591860600905649769285)
      ·
        refine ⟨2657173473862669809331741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14171591860600905649769285 2657173473862669809331741)
        ·
          refine ⟨996440052698501178499403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2657173473862669809331741 996440052698501178499403)
          ·
            refine ⟨1494660079047751767749105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 996440052698501178499403 1494660079047751767749105)
            ·
              refine ⟨1120995059285813825811829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1494660079047751767749105 1120995059285813825811829)
              ·
                refine ⟨105093286808045046169859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1120995059285813825811829 105093286808045046169859)
                ·
                  rfl

theorem cell21_1381512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 5].length) (baseStart_1381512 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1381512 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1381512 prefixEnd_1381512 := by exact prefixLift 1381512
  have htrace : WordTrace (prefixWord ++ tailWord_1381512) baseStart_1381512 baseEnd_1381512 := by
    simpa [prefixWord, tailWord_1381512, baseEnd_1381512] using wordTrace_append hprefix tailTrace_1381512
  have hstable : (prefixWord ++ tailWord_1381512).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381512).length < 2 ^ (prefixWord ++ tailWord_1381512).sum := by decide
  have hdescent : baseEnd_1381512 < baseStart_1381512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381543 : List Nat := [1, 1, 6, 2, 1, 2, 3, 2, 3]
def baseStart_1381543 : Nat := 118140960795 + 1381543 * 2 ^ 59
def prefixEnd_1381543 : Nat := 4983230072969 + 3 ^ 40 * 1381543 * 2
def baseEnd_1381543 : Nat := 315286935046485973492847

theorem tailTrace_1381543 : CollatzResearch.WordTrace tailWord_1381543 prefixEnd_1381543 315286935046485973492847 := by
  unfold tailWord_1381543
  simp only [CollatzResearch.WordTrace]
  refine ⟨50389012833913134604669283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33592675222608756403112855 50389012833913134604669283)
  ·
    refine ⟨75583519250869701907003925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50389012833913134604669283 75583519250869701907003925)
    ·
      refine ⟨3542977464884517276890809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 75583519250869701907003925 3542977464884517276890809)
      ·
        refine ⟨2657233098663387957668107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3542977464884517276890809 2657233098663387957668107)
        ·
          refine ⟨3985849647995081936502161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2657233098663387957668107 3985849647995081936502161)
          ·
            refine ⟨2989387235996311452376621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3985849647995081936502161 2989387235996311452376621)
            ·
              refine ⟨1121020213498616794641233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2989387235996311452376621 1121020213498616794641233)
              ·
                refine ⟨840765160123962595980925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1121020213498616794641233 840765160123962595980925)
                ·
                  refine ⟨315286935046485973492847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 840765160123962595980925 315286935046485973492847)
                  ·
                    rfl

theorem cell21_1381543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 2, 3].length) (baseStart_1381543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1381543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1381543 prefixEnd_1381543 := by exact prefixLift 1381543
  have htrace : WordTrace (prefixWord ++ tailWord_1381543) baseStart_1381543 baseEnd_1381543 := by
    simpa [prefixWord, tailWord_1381543, baseEnd_1381543] using wordTrace_append hprefix tailTrace_1381543
  have hstable : (prefixWord ++ tailWord_1381543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381543).length < 2 ^ (prefixWord ++ tailWord_1381543).sum := by decide
  have hdescent : baseEnd_1381543 < baseStart_1381543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381650 : List Nat := [3, 2, 4, 2, 1, 2, 1, 2, 4]
def baseStart_1381650 : Nat := 118140960795 + 1381650 * 2 ^ 59
def prefixEnd_1381650 : Nat := 4983230072969 + 3 ^ 40 * 1381650 * 2
def baseEnd_1381650 : Nat := 315311353904277565209295

theorem tailTrace_1381650 : CollatzResearch.WordTrace tailWord_1381650 prefixEnd_1381650 315311353904277565209295 := by
  unfold tailWord_1381650
  simp only [CollatzResearch.WordTrace]
  refine ⟨12598228861131372969703601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33595276963016994585876269 12598228861131372969703601)
  ·
    refine ⟨9448671645848529727277701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12598228861131372969703601 9448671645848529727277701)
    ·
      refine ⟨1771625933596599323864569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9448671645848529727277701 1771625933596599323864569)
      ·
        refine ⟨1328719450197449492898427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1771625933596599323864569 1328719450197449492898427)
        ·
          refine ⟨1993079175296174239347641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1328719450197449492898427 1993079175296174239347641)
          ·
            refine ⟨1494809381472130679510731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1993079175296174239347641 1494809381472130679510731)
            ·
              refine ⟨2242214072208196019266097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1494809381472130679510731 2242214072208196019266097)
              ·
                refine ⟨1681660554156147014449573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2242214072208196019266097 1681660554156147014449573)
                ·
                  refine ⟨315311353904277565209295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1681660554156147014449573 315311353904277565209295)
                  ·
                    rfl

theorem cell21_1381650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_1381650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1381650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1381650 prefixEnd_1381650 := by exact prefixLift 1381650
  have htrace : WordTrace (prefixWord ++ tailWord_1381650) baseStart_1381650 baseEnd_1381650 := by
    simpa [prefixWord, tailWord_1381650, baseEnd_1381650] using wordTrace_append hprefix tailTrace_1381650
  have hstable : (prefixWord ++ tailWord_1381650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381650).length < 2 ^ (prefixWord ++ tailWord_1381650).sum := by decide
  have hdescent : baseEnd_1381650 < baseStart_1381650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381661 : List Nat := [1, 4, 2, 3, 1, 2, 2, 1, 5]
def baseStart_1381661 : Nat := 118140960795 + 1381661 * 2 ^ 59
def prefixEnd_1381661 : Nat := 4983230072969 + 3 ^ 40 * 1381661 * 2
def baseEnd_1381661 : Nat := 315313864254143990525939

theorem tailTrace_1381661 : CollatzResearch.WordTrace tailWord_1381661 prefixEnd_1381661 315313864254143990525939 := by
  unfold tailWord_1381661
  simp only [CollatzResearch.WordTrace]
  refine ⟨50393316647485640757464837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33595544431657093838309891 50393316647485640757464837)
  ·
    refine ⟨9448746871403557642024657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50393316647485640757464837 9448746871403557642024657)
    ·
      refine ⟨7086560153552668231518493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9448746871403557642024657 7086560153552668231518493)
      ·
        refine ⟨2657460057582250586819435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7086560153552668231518493 2657460057582250586819435)
        ·
          refine ⟨3986190086373375880229153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2657460057582250586819435 3986190086373375880229153)
          ·
            refine ⟨2989642564780031910171865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3986190086373375880229153 2989642564780031910171865)
            ·
              refine ⟨2242231923585023932628899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2989642564780031910171865 2242231923585023932628899)
              ·
                refine ⟨3363347885377535898943349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2242231923585023932628899 3363347885377535898943349)
                ·
                  refine ⟨315313864254143990525939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3363347885377535898943349 315313864254143990525939)
                  ·
                    rfl

theorem cell21_1381661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_1381661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1381661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1381661 prefixEnd_1381661 := by exact prefixLift 1381661
  have htrace : WordTrace (prefixWord ++ tailWord_1381661) baseStart_1381661 baseEnd_1381661 := by
    simpa [prefixWord, tailWord_1381661, baseEnd_1381661] using wordTrace_append hprefix tailTrace_1381661
  have hstable : (prefixWord ++ tailWord_1381661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381661).length < 2 ^ (prefixWord ++ tailWord_1381661).sum := by decide
  have hdescent : baseEnd_1381661 < baseStart_1381661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381813 : List Nat := [1, 3, 3, 2, 2, 1, 1, 5, 3]
def baseStart_1381813 : Nat := 118140960795 + 1381813 * 2 ^ 59
def prefixEnd_1381813 : Nat := 4983230072969 + 3 ^ 40 * 1381813 * 2
def baseEnd_1381813 : Nat := 315348552725025503992295

theorem tailTrace_1381813 : CollatzResearch.WordTrace tailWord_1381813 prefixEnd_1381813 315348552725025503992295 := by
  unfold tailWord_1381813
  simp only [CollatzResearch.WordTrace]
  refine ⟨50398860542934970716998093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33599240361956647144665395 50398860542934970716998093)
  ·
    refine ⟨18899572703600614018874285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50398860542934970716998093 18899572703600614018874285)
    ·
      refine ⟨7087339763850230257077857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18899572703600614018874285 7087339763850230257077857)
      ·
        refine ⟨5315504822887672692808393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7087339763850230257077857 5315504822887672692808393)
        ·
          refine ⟨3986628617165754519606295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5315504822887672692808393 3986628617165754519606295)
          ·
            refine ⟨5979942925748631779409443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3986628617165754519606295 5979942925748631779409443)
            ·
              refine ⟨8969914388622947669114165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5979942925748631779409443 8969914388622947669114165)
              ·
                refine ⟨840929473933401343979453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8969914388622947669114165 840929473933401343979453)
                ·
                  refine ⟨315348552725025503992295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 840929473933401343979453 315348552725025503992295)
                  ·
                    rfl

theorem cell21_1381813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 5, 3].length) (baseStart_1381813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1381813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1381813 prefixEnd_1381813 := by exact prefixLift 1381813
  have htrace : WordTrace (prefixWord ++ tailWord_1381813) baseStart_1381813 baseEnd_1381813 := by
    simpa [prefixWord, tailWord_1381813, baseEnd_1381813] using wordTrace_append hprefix tailTrace_1381813
  have hstable : (prefixWord ++ tailWord_1381813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381813).length < 2 ^ (prefixWord ++ tailWord_1381813).sum := by decide
  have hdescent : baseEnd_1381813 < baseStart_1381813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381855 : List Nat := [1, 1, 2, 3, 3, 1, 1, 4, 5]
def baseStart_1381855 : Nat := 118140960795 + 1381855 * 2 ^ 59
def prefixEnd_1381855 : Nat := 4983230072969 + 3 ^ 40 * 1381855 * 2
def baseEnd_1381855 : Nat := 315358137697242764292209

theorem tailTrace_1381855 : CollatzResearch.WordTrace tailWord_1381855 prefixEnd_1381855 315358137697242764292209 := by
  unfold tailWord_1381855
  simp only [CollatzResearch.WordTrace]
  refine ⟨50400392408782811890027019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33600261605855207926684679 50400392408782811890027019)
  ·
    refine ⟨75600588613174217835040529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50400392408782811890027019 75600588613174217835040529)
    ·
      refine ⟨56700441459880663376280397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75600588613174217835040529 56700441459880663376280397)
      ·
        refine ⟨21262665547455248766105149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56700441459880663376280397 21262665547455248766105149)
        ·
          refine ⟨7973499580295718287289431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21262665547455248766105149 7973499580295718287289431)
          ·
            refine ⟨11960249370443577430934147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7973499580295718287289431 11960249370443577430934147)
            ·
              refine ⟨17940374055665366146401221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11960249370443577430934147 17940374055665366146401221)
              ·
                refine ⟨3363820135437256152450229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17940374055665366146401221 3363820135437256152450229)
                ·
                  refine ⟨315358137697242764292209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3363820135437256152450229 315358137697242764292209)
                  ·
                    rfl

theorem cell21_1381855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 5].length) (baseStart_1381855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1381855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1381855 prefixEnd_1381855 := by exact prefixLift 1381855
  have htrace : WordTrace (prefixWord ++ tailWord_1381855) baseStart_1381855 baseEnd_1381855 := by
    simpa [prefixWord, tailWord_1381855, baseEnd_1381855] using wordTrace_append hprefix tailTrace_1381855
  have hstable : (prefixWord ++ tailWord_1381855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381855).length < 2 ^ (prefixWord ++ tailWord_1381855).sum := by decide
  have hdescent : baseEnd_1381855 < baseStart_1381855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381889 : List Nat := [1, 2, 4, 1, 4, 2, 1, 1, 5]
def baseStart_1381889 : Nat := 118140960795 + 1381889 * 2 ^ 59
def prefixEnd_1381889 : Nat := 4983230072969 + 3 ^ 40 * 1381889 * 2
def baseEnd_1381889 : Nat := 315365896960466260725473

theorem tailTrace_1381889 : CollatzResearch.WordTrace tailWord_1381889 prefixEnd_1381889 315365896960466260725473 := by
  unfold tailWord_1381889
  simp only [CollatzResearch.WordTrace]
  refine ⟨50401632490659635696764721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33601088327106423797843147 50401632490659635696764721)
  ·
    refine ⟨37801224367994726772573541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50401632490659635696764721 37801224367994726772573541)
    ·
      refine ⟨7087729568999011269857539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37801224367994726772573541 7087729568999011269857539)
      ·
        refine ⟨10631594353498516904786309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7087729568999011269857539 10631594353498516904786309)
        ·
          refine ⟨1993423941280971919647433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10631594353498516904786309 1993423941280971919647433)
          ·
            refine ⟨1495067955960728939735575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1993423941280971919647433 1495067955960728939735575)
            ·
              refine ⟨2242601933941093409603363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1495067955960728939735575 2242601933941093409603363)
              ·
                refine ⟨3363902900911640114405045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2242601933941093409603363 3363902900911640114405045)
                ·
                  refine ⟨315365896960466260725473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3363902900911640114405045 315365896960466260725473)
                  ·
                    rfl

theorem cell21_1381889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 5].length) (baseStart_1381889 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1381889 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1381889 prefixEnd_1381889 := by exact prefixLift 1381889
  have htrace : WordTrace (prefixWord ++ tailWord_1381889) baseStart_1381889 baseEnd_1381889 := by
    simpa [prefixWord, tailWord_1381889, baseEnd_1381889] using wordTrace_append hprefix tailTrace_1381889
  have hstable : (prefixWord ++ tailWord_1381889).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381889).length < 2 ^ (prefixWord ++ tailWord_1381889).sum := by decide
  have hdescent : baseEnd_1381889 < baseStart_1381889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381962 : List Nat := [3, 1, 2, 1, 1, 3, 1, 5, 4]
def baseStart_1381962 : Nat := 118140960795 + 1381962 * 2 ^ 59
def prefixEnd_1381962 : Nat := 4983230072969 + 3 ^ 40 * 1381962 * 2
def baseEnd_1381962 : Nat := 315382556555034356008657

theorem tailTrace_1381962 : CollatzResearch.WordTrace tailWord_1381962 prefixEnd_1381962 315382556555034356008657 := by
  unfold tailWord_1381962
  simp only [CollatzResearch.WordTrace]
  refine ⟨12601073754848792291043035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33602863346263446109448093 12601073754848792291043035)
  ·
    refine ⟨18901610632273188436564553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12601073754848792291043035 18901610632273188436564553)
    ·
      refine ⟨14176207974204891327423415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18901610632273188436564553 14176207974204891327423415)
      ·
        refine ⟨21264311961307336991135123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14176207974204891327423415 21264311961307336991135123)
        ·
          refine ⟨31896467941961005486702685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21264311961307336991135123 31896467941961005486702685)
          ·
            refine ⟨11961175478235377057513507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31896467941961005486702685 11961175478235377057513507)
            ·
              refine ⟨17941763217353065586270261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11961175478235377057513507 17941763217353065586270261)
              ·
                refine ⟨1682040301626849898712837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17941763217353065586270261 1682040301626849898712837)
                ·
                  refine ⟨315382556555034356008657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1682040301626849898712837 315382556555034356008657)
                  ·
                    rfl

theorem cell21_1381962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 5, 4].length) (baseStart_1381962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1381962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1381962 prefixEnd_1381962 := by exact prefixLift 1381962
  have htrace : WordTrace (prefixWord ++ tailWord_1381962) baseStart_1381962 baseEnd_1381962 := by
    simpa [prefixWord, tailWord_1381962, baseEnd_1381962] using wordTrace_append hprefix tailTrace_1381962
  have hstable : (prefixWord ++ tailWord_1381962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381962).length < 2 ^ (prefixWord ++ tailWord_1381962).sum := by decide
  have hdescent : baseEnd_1381962 < baseStart_1381962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381965 : List Nat := [1, 6, 1, 1, 3, 1, 1, 2, 5]
def baseStart_1381965 : Nat := 118140960795 + 1381965 * 2 ^ 59
def prefixEnd_1381965 : Nat := 4983230072969 + 3 ^ 40 * 1381965 * 2
def baseEnd_1381965 : Nat := 315383241195907017458651

theorem tailTrace_1381965 : CollatzResearch.WordTrace tailWord_1381965 prefixEnd_1381965 315383241195907017458651 := by
  unfold tailWord_1381965
  simp only [CollatzResearch.WordTrace]
  refine ⟨50404404438384300676531349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33602936292256200451020899 50404404438384300676531349)
  ·
    refine ⟨2362706458049264094212407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 50404404438384300676531349 2362706458049264094212407)
    ·
      refine ⟨3544059687073896141318611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2362706458049264094212407 3544059687073896141318611)
      ·
        refine ⟨5316089530610844211977917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3544059687073896141318611 5316089530610844211977917)
        ·
          refine ⟨1993533573979066579491719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5316089530610844211977917 1993533573979066579491719)
          ·
            refine ⟨2990300360968599869237579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1993533573979066579491719 2990300360968599869237579)
            ·
              refine ⟨4485450541452899803856369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2990300360968599869237579 4485450541452899803856369)
              ·
                refine ⟨3364087906089674852892277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4485450541452899803856369 3364087906089674852892277)
                ·
                  refine ⟨315383241195907017458651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3364087906089674852892277 315383241195907017458651)
                  ·
                    rfl

theorem cell21_1381965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_1381965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1381965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1381965 prefixEnd_1381965 := by exact prefixLift 1381965
  have htrace : WordTrace (prefixWord ++ tailWord_1381965) baseStart_1381965 baseEnd_1381965 := by
    simpa [prefixWord, tailWord_1381965, baseEnd_1381965] using wordTrace_append hprefix tailTrace_1381965
  have hstable : (prefixWord ++ tailWord_1381965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381965).length < 2 ^ (prefixWord ++ tailWord_1381965).sum := by decide
  have hdescent : baseEnd_1381965 < baseStart_1381965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382052 : List Nat := [2, 3, 1, 2, 2, 2, 9]
def baseStart_1382052 : Nat := 118140960795 + 1382052 * 2 ^ 59
def prefixEnd_1382052 : Nat := 4983230072969 + 3 ^ 40 * 1382052 * 2
def baseEnd_1382052 : Nat := 35044788420134911056497

theorem tailTrace_1382052 : CollatzResearch.WordTrace tailWord_1382052 prefixEnd_1382052 35044788420134911056497 := by
  unfold tailWord_1382052
  simp only [CollatzResearch.WordTrace]
  refine ⟨25203788794534557267474205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33605051726046076356632273 25203788794534557267474205)
  ·
    refine ⟨9451420797950458975302827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25203788794534557267474205 9451420797950458975302827)
    ·
      refine ⟨14177131196925688462954241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9451420797950458975302827 14177131196925688462954241)
      ·
        refine ⟨10632848397694266347215681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14177131196925688462954241 10632848397694266347215681)
        ·
          refine ⟨7974636298270699760411761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10632848397694266347215681 7974636298270699760411761)
          ·
            refine ⟨5980977223703024820308821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7974636298270699760411761 5980977223703024820308821)
            ·
              refine ⟨35044788420134911056497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5980977223703024820308821 35044788420134911056497)
              ·
                rfl

theorem cell21_1382052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 9].length) (baseStart_1382052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1382052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1382052 prefixEnd_1382052 := by exact prefixLift 1382052
  have htrace : WordTrace (prefixWord ++ tailWord_1382052) baseStart_1382052 baseEnd_1382052 := by
    simpa [prefixWord, tailWord_1382052, baseEnd_1382052] using wordTrace_append hprefix tailTrace_1382052
  have hstable : (prefixWord ++ tailWord_1382052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382052).length < 2 ^ (prefixWord ++ tailWord_1382052).sum := by decide
  have hdescent : baseEnd_1382052 < baseStart_1382052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382176 : List Nat := [2, 1, 1, 5, 1, 1, 1, 6, 3]
def baseStart_1382176 : Nat := 118140960795 + 1382176 * 2 ^ 59
def prefixEnd_1382176 : Nat := 4983230072969 + 3 ^ 40 * 1382176 * 2
def baseEnd_1382176 : Nat := 315431394270617539441553

theorem tailTrace_1382176 : CollatzResearch.WordTrace tailWord_1382176 prefixEnd_1382176 315431394270617539441553 := by
  unfold tailWord_1382176
  simp only [CollatzResearch.WordTrace]
  refine ⟨25206050120309941856231191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33608066827079922474974921 25206050120309941856231191)
  ·
    refine ⟨37809075180464912784346787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25206050120309941856231191 37809075180464912784346787)
    ·
      refine ⟨56713612770697369176520181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37809075180464912784346787 56713612770697369176520181)
      ·
        refine ⟨5316901197252878360298767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56713612770697369176520181 5316901197252878360298767)
        ·
          refine ⟨7975351795879317540448151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5316901197252878360298767 7975351795879317540448151)
          ·
            refine ⟨11963027693818976310672227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7975351795879317540448151 11963027693818976310672227)
            ·
              refine ⟨17944541540728464466008341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11963027693818976310672227 17944541540728464466008341)
              ·
                refine ⟨841150384721646771844141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17944541540728464466008341 841150384721646771844141)
                ·
                  refine ⟨315431394270617539441553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 841150384721646771844141 315431394270617539441553)
                  ·
                    rfl

theorem cell21_1382176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 6, 3].length) (baseStart_1382176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1382176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1382176 prefixEnd_1382176 := by exact prefixLift 1382176
  have htrace : WordTrace (prefixWord ++ tailWord_1382176) baseStart_1382176 baseEnd_1382176 := by
    simpa [prefixWord, tailWord_1382176, baseEnd_1382176] using wordTrace_append hprefix tailTrace_1382176
  have hstable : (prefixWord ++ tailWord_1382176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382176).length < 2 ^ (prefixWord ++ tailWord_1382176).sum := by decide
  have hdescent : baseEnd_1382176 < baseStart_1382176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382221 : List Nat := [1, 6, 1, 2, 1, 1, 9]
def baseStart_1382221 : Nat := 118140960795 + 1382221 * 2 ^ 59
def prefixEnd_1382221 : Nat := 4983230072969 + 3 ^ 40 * 1382221 * 2
def baseEnd_1382221 : Nat := 35049073764856384576829

theorem tailTrace_1382221 : CollatzResearch.WordTrace tailWord_1382221 prefixEnd_1382221 35049073764856384576829 := by
  unfold tailWord_1382221
  simp only [CollatzResearch.WordTrace]
  refine ⟨50413741525456856397850517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33609161016971237598567011 50413741525456856397850517)
  ·
    refine ⟨2363144134005790143649243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 50413741525456856397850517 2363144134005790143649243)
    ·
      refine ⟨3544716201008685215473865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2363144134005790143649243 3544716201008685215473865)
      ·
        refine ⟨2658537150756513911605399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3544716201008685215473865 2658537150756513911605399)
        ·
          refine ⟨3987805726134770867408099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2658537150756513911605399 3987805726134770867408099)
          ·
            refine ⟨5981708589202156301112149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3987805726134770867408099 5981708589202156301112149)
            ·
              refine ⟨35049073764856384576829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5981708589202156301112149 35049073764856384576829)
              ·
                rfl

theorem cell21_1382221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 9].length) (baseStart_1382221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1382221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1382221 prefixEnd_1382221 := by exact prefixLift 1382221
  have htrace : WordTrace (prefixWord ++ tailWord_1382221) baseStart_1382221 baseEnd_1382221 := by
    simpa [prefixWord, tailWord_1382221, baseEnd_1382221] using wordTrace_append hprefix tailTrace_1382221
  have hstable : (prefixWord ++ tailWord_1382221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382221).length < 2 ^ (prefixWord ++ tailWord_1382221).sum := by decide
  have hdescent : baseEnd_1382221 < baseStart_1382221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382280 : List Nat := [2, 1, 3, 3, 3, 9]
def baseStart_1382280 : Nat := 118140960795 + 1382280 * 2 ^ 59
def prefixEnd_1382280 : Nat := 4983230072969 + 3 ^ 40 * 1382280 * 2
def baseEnd_1382280 : Nat := 11683523277316165544741

theorem tailTrace_1382280 : CollatzResearch.WordTrace tailWord_1382280 prefixEnd_1382280 11683523277316165544741 := by
  unfold tailWord_1382280
  simp only [CollatzResearch.WordTrace]
  refine ⟨25207946716121554737124147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33610595621495406316165529 25207946716121554737124147)
  ·
    refine ⟨37811920074182332105686221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25207946716121554737124147 37811920074182332105686221)
    ·
      refine ⟨14179470027818374539632333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37811920074182332105686221 14179470027818374539632333)
      ·
        refine ⟨5317301260431890452362125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14179470027818374539632333 5317301260431890452362125)
        ·
          refine ⟨1993987972661958919635797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5317301260431890452362125 1993987972661958919635797)
          ·
            refine ⟨11683523277316165544741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1993987972661958919635797 11683523277316165544741)
            ·
              rfl

theorem cell21_1382280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 9].length) (baseStart_1382280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1382280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1382280 prefixEnd_1382280 := by exact prefixLift 1382280
  have htrace : WordTrace (prefixWord ++ tailWord_1382280) baseStart_1382280 baseEnd_1382280 := by
    simpa [prefixWord, tailWord_1382280, baseEnd_1382280] using wordTrace_append hprefix tailTrace_1382280
  have hstable : (prefixWord ++ tailWord_1382280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382280).length < 2 ^ (prefixWord ++ tailWord_1382280).sum := by decide
  have hdescent : baseEnd_1382280 < baseStart_1382280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382286 : List Nat := [4, 1, 1, 5, 1, 1, 1, 4, 3]
def baseStart_1382286 : Nat := 118140960795 + 1382286 * 2 ^ 59
def prefixEnd_1382286 : Nat := 4983230072969 + 3 ^ 40 * 1382286 * 2
def baseEnd_1382286 : Nat := 315456497769281792607995

theorem tailTrace_1382286 : CollatzResearch.WordTrace tailWord_1382286 prefixEnd_1382286 315456497769281792607995 := by
  unfold tailWord_1382286
  simp only [CollatzResearch.WordTrace]
  refine ⟨6302014033777671562370839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33610741513480914999311141 6302014033777671562370839)
  ·
    refine ⟨9453021050666507343556259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6302014033777671562370839 9453021050666507343556259)
    ·
      refine ⟨14179531575999761015334389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9453021050666507343556259 14179531575999761015334389)
      ·
        refine ⟨1329331085249977595187599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14179531575999761015334389 1329331085249977595187599)
        ·
          refine ⟨1993996627874966392781399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1329331085249977595187599 1993996627874966392781399)
          ·
            refine ⟨2990994941812449589172099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1993996627874966392781399 2990994941812449589172099)
            ·
              refine ⟨4486492412718674383758149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2990994941812449589172099 4486492412718674383758149)
              ·
                refine ⟨841217327384751446954653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4486492412718674383758149 841217327384751446954653)
                ·
                  refine ⟨315456497769281792607995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 841217327384751446954653 315456497769281792607995)
                  ·
                    rfl

theorem cell21_1382286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 4, 3].length) (baseStart_1382286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1382286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1382286 prefixEnd_1382286 := by exact prefixLift 1382286
  have htrace : WordTrace (prefixWord ++ tailWord_1382286) baseStart_1382286 baseEnd_1382286 := by
    simpa [prefixWord, tailWord_1382286, baseEnd_1382286] using wordTrace_append hprefix tailTrace_1382286
  have hstable : (prefixWord ++ tailWord_1382286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382286).length < 2 ^ (prefixWord ++ tailWord_1382286).sum := by decide
  have hdescent : baseEnd_1382286 < baseStart_1382286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382311 : List Nat := [1, 1, 6, 1, 2, 1, 1, 1, 7]
def baseStart_1382311 : Nat := 118140960795 + 1382311 * 2 ^ 59
def prefixEnd_1382311 : Nat := 4983230072969 + 3 ^ 40 * 1382311 * 2
def baseEnd_1382311 : Nat := 315462203109887304691277

theorem tailTrace_1382311 : CollatzResearch.WordTrace tailWord_1382311 prefixEnd_1382311 315462203109887304691277 := by
  unfold tailWord_1382311
  simp only [CollatzResearch.WordTrace]
  refine ⟨50417024095130801768626787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33611349396753867845751191 50417024095130801768626787)
  ·
    refine ⟨75625536142696202652940181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50417024095130801768626787 75625536142696202652940181)
    ·
      refine ⟨3544947006688884499356571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 75625536142696202652940181 3544947006688884499356571)
      ·
        refine ⟨5317420510033326749034857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3544947006688884499356571 5317420510033326749034857)
        ·
          refine ⟨3988065382524995061776143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5317420510033326749034857 3988065382524995061776143)
          ·
            refine ⟨5982098073787492592664215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3988065382524995061776143 5982098073787492592664215)
            ·
              refine ⟨8973147110681238888996323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5982098073787492592664215 8973147110681238888996323)
              ·
                refine ⟨13459720666021858333494485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8973147110681238888996323 13459720666021858333494485)
                ·
                  refine ⟨315462203109887304691277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13459720666021858333494485 315462203109887304691277)
                  ·
                    rfl

theorem cell21_1382311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 7].length) (baseStart_1382311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1382311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1382311 prefixEnd_1382311 := by exact prefixLift 1382311
  have htrace : WordTrace (prefixWord ++ tailWord_1382311) baseStart_1382311 baseEnd_1382311 := by
    simpa [prefixWord, tailWord_1382311, baseEnd_1382311] using wordTrace_append hprefix tailTrace_1382311
  have hstable : (prefixWord ++ tailWord_1382311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382311).length < 2 ^ (prefixWord ++ tailWord_1382311).sum := by decide
  have hdescent : baseEnd_1382311 < baseStart_1382311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382328 : List Nat := [2, 1, 2, 1, 2, 3, 4, 3, 3]
def baseStart_1382328 : Nat := 118140960795 + 1382328 * 2 ^ 59
def prefixEnd_1382328 : Nat := 4983230072969 + 3 ^ 40 * 1382328 * 2
def baseEnd_1382328 : Nat := 315466082741499052907909

theorem tailTrace_1382328 : CollatzResearch.WordTrace tailWord_1382328 prefixEnd_1382328 315466082741499052907909 := by
  unfold tailWord_1382328
  simp only [CollatzResearch.WordTrace]
  refine ⟨25208822068034606835997819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33611762757379475781330425 25208822068034606835997819)
  ·
    refine ⟨37813233102051910253996729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25208822068034606835997819 37813233102051910253996729)
    ·
      refine ⟨28359924826538932690497547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37813233102051910253996729 28359924826538932690497547)
      ·
        refine ⟨42539887239808399035746321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28359924826538932690497547 42539887239808399035746321)
        ·
          refine ⟨31904915429856299276809741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42539887239808399035746321 31904915429856299276809741)
          ·
            refine ⟨11964343286196112228803653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31904915429856299276809741 11964343286196112228803653)
            ·
              refine ⟨2243314366161771042900685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11964343286196112228803653 2243314366161771042900685)
              ·
                refine ⟨841242887310664141087757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2243314366161771042900685 841242887310664141087757)
                ·
                  refine ⟨315466082741499052907909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 841242887310664141087757 315466082741499052907909)
                  ·
                    rfl

theorem cell21_1382328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 3, 3].length) (baseStart_1382328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1382328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1382328 prefixEnd_1382328 := by exact prefixLift 1382328
  have htrace : WordTrace (prefixWord ++ tailWord_1382328) baseStart_1382328 baseEnd_1382328 := by
    simpa [prefixWord, tailWord_1382328, baseEnd_1382328] using wordTrace_append hprefix tailTrace_1382328
  have hstable : (prefixWord ++ tailWord_1382328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382328).length < 2 ^ (prefixWord ++ tailWord_1382328).sum := by decide
  have hdescent : baseEnd_1382328 < baseStart_1382328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382356 : List Nat := [2, 4, 1, 2, 1, 1, 2, 8]
def baseStart_1382356 : Nat := 118140960795 + 1382356 * 2 ^ 59
def prefixEnd_1382356 : Nat := 4983230072969 + 3 ^ 40 * 1382356 * 2
def baseEnd_1382356 : Nat := 105157490907659075480395

theorem tailTrace_1382356 : CollatzResearch.WordTrace tailWord_1382356 prefixEnd_1382356 105157490907659075480395 := by
  unfold tailWord_1382356
  simp only [CollatzResearch.WordTrace]
  refine ⟨25209332689983887227007461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33612443586645182969343281 25209332689983887227007461)
  ·
    refine ⟨4726749879371978855063899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25209332689983887227007461 4726749879371978855063899)
    ·
      refine ⟨7090124819057968282595849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4726749879371978855063899 7090124819057968282595849)
      ·
        refine ⟨5317593614293476211946887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7090124819057968282595849 5317593614293476211946887)
        ·
          refine ⟨7976390421440214317920331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5317593614293476211946887 7976390421440214317920331)
          ·
            refine ⟨11964585632160321476880497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7976390421440214317920331 11964585632160321476880497)
            ·
              refine ⟨8973439224120241107660373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11964585632160321476880497 8973439224120241107660373)
              ·
                refine ⟨105157490907659075480395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8973439224120241107660373 105157490907659075480395)
                ·
                  rfl

theorem cell21_1382356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 8].length) (baseStart_1382356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1382356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1382356 prefixEnd_1382356 := by exact prefixLift 1382356
  have htrace : WordTrace (prefixWord ++ tailWord_1382356) baseStart_1382356 baseEnd_1382356 := by
    simpa [prefixWord, tailWord_1382356, baseEnd_1382356] using wordTrace_append hprefix tailTrace_1382356
  have hstable : (prefixWord ++ tailWord_1382356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382356).length < 2 ^ (prefixWord ++ tailWord_1382356).sum := by decide
  have hdescent : baseEnd_1382356 < baseStart_1382356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382390 : List Nat := [5, 1, 1, 1, 5, 1, 7]
def baseStart_1382390 : Nat := 118140960795 + 1382390 * 2 ^ 59
def prefixEnd_1382390 : Nat := 4983230072969 + 3 ^ 40 * 1382390 * 2
def baseEnd_1382390 : Nat := 35053359109577858097161

theorem tailTrace_1382390 : CollatzResearch.WordTrace tailWord_1382390 prefixEnd_1382390 35053359109577858097161 := by
  unfold tailWord_1382390
  simp only [CollatzResearch.WordTrace]
  refine ⟨3151244091365287391297039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33613270307896398840501749 3151244091365287391297039)
  ·
    refine ⟨4726866137047931086945559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3151244091365287391297039 4726866137047931086945559)
    ·
      refine ⟨7090299205571896630418339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4726866137047931086945559 7090299205571896630418339)
      ·
        refine ⟨10635448808357844945627509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7090299205571896630418339 10635448808357844945627509)
        ·
          refine ⟨997073325783547963652579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10635448808357844945627509 997073325783547963652579)
          ·
            refine ⟨1495609988675321945478869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 997073325783547963652579 1495609988675321945478869)
            ·
              refine ⟨35053359109577858097161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1495609988675321945478869 35053359109577858097161)
              ·
                rfl

theorem cell21_1382390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 7].length) (baseStart_1382390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1382390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1382390 prefixEnd_1382390 := by exact prefixLift 1382390
  have htrace : WordTrace (prefixWord ++ tailWord_1382390) baseStart_1382390 baseEnd_1382390 := by
    simpa [prefixWord, tailWord_1382390, baseEnd_1382390] using wordTrace_append hprefix tailTrace_1382390
  have hstable : (prefixWord ++ tailWord_1382390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382390).length < 2 ^ (prefixWord ++ tailWord_1382390).sum := by decide
  have hdescent : baseEnd_1382390 < baseStart_1382390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382401 : List Nat := [1, 2, 4, 1, 2, 1, 1, 3, 6]
def baseStart_1382401 : Nat := 118140960795 + 1382401 * 2 ^ 59
def prefixEnd_1382401 : Nat := 4983230072969 + 3 ^ 40 * 1382401 * 2
def baseEnd_1382401 : Nat := 315482742336067148191093

theorem tailTrace_1382401 : CollatzResearch.WordTrace tailWord_1382401 prefixEnd_1382401 315482742336067148191093 := by
  unfold tailWord_1382401
  simp only [CollatzResearch.WordTrace]
  refine ⟨50420306664804747139403057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33613537776536498092935371 50420306664804747139403057)
  ·
    refine ⟨37815229998603560354552293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50420306664804747139403057 37815229998603560354552293)
    ·
      refine ⟨7090355624738167566478555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37815229998603560354552293 7090355624738167566478555)
      ·
        refine ⟨10635533437107251349717833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7090355624738167566478555 10635533437107251349717833)
        ·
          refine ⟨7976650077830438512288375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10635533437107251349717833 7976650077830438512288375)
          ·
            refine ⟨11964975116745657768432563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7976650077830438512288375 11964975116745657768432563)
            ·
              refine ⟨17947462675118486652648845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11964975116745657768432563 17947462675118486652648845)
              ·
                refine ⟨6730298503169432494743317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17947462675118486652648845 6730298503169432494743317)
                ·
                  refine ⟨315482742336067148191093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6730298503169432494743317 315482742336067148191093)
                  ·
                    rfl

theorem cell21_1382401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 6].length) (baseStart_1382401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1382401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1382401 prefixEnd_1382401 := by exact prefixLift 1382401
  have htrace : WordTrace (prefixWord ++ tailWord_1382401) baseStart_1382401 baseEnd_1382401 := by
    simpa [prefixWord, tailWord_1382401, baseEnd_1382401] using wordTrace_append hprefix tailTrace_1382401
  have hstable : (prefixWord ++ tailWord_1382401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382401).length < 2 ^ (prefixWord ++ tailWord_1382401).sum := by decide
  have hdescent : baseEnd_1382401 < baseStart_1382401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382452 : List Nat := [2, 5, 1, 2, 2, 1, 2, 2, 4]
def baseStart_1382452 : Nat := 118140960795 + 1382452 * 2 ^ 59
def prefixEnd_1382452 : Nat := 4983230072969 + 3 ^ 40 * 1382452 * 2
def baseEnd_1382452 : Nat := 315494381230902392840989

theorem tailTrace_1382452 : CollatzResearch.WordTrace tailWord_1382452 prefixEnd_1382452 315494381230902392840989 := by
  unfold tailWord_1382452
  simp only [CollatzResearch.WordTrace]
  refine ⟨25211083393809991424754805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33614777858413321899673073 25211083393809991424754805)
  ·
    refine ⟨2363539068169686696070763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25211083393809991424754805 2363539068169686696070763)
    ·
      refine ⟨3545308602254530044106145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2363539068169686696070763 3545308602254530044106145)
      ·
        refine ⟨2658981451690897533079609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3545308602254530044106145 2658981451690897533079609)
        ·
          refine ⟨1994236088768173149809707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2658981451690897533079609 1994236088768173149809707)
          ·
            refine ⟨2991354133152259724714561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1994236088768173149809707 2991354133152259724714561)
            ·
              refine ⟨2243515599864194793535921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2991354133152259724714561 2243515599864194793535921)
              ·
                refine ⟨1682636699898146095151941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2243515599864194793535921 1682636699898146095151941)
                ·
                  refine ⟨315494381230902392840989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1682636699898146095151941 315494381230902392840989)
                  ·
                    rfl

theorem cell21_1382452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_1382452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1382452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1382452 prefixEnd_1382452 := by exact prefixLift 1382452
  have htrace : WordTrace (prefixWord ++ tailWord_1382452) baseStart_1382452 baseEnd_1382452 := by
    simpa [prefixWord, tailWord_1382452, baseEnd_1382452] using wordTrace_append hprefix tailTrace_1382452
  have hstable : (prefixWord ++ tailWord_1382452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382452).length < 2 ^ (prefixWord ++ tailWord_1382452).sum := by decide
  have hdescent : baseEnd_1382452 < baseStart_1382452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382542 : List Nat := [4, 1, 1, 3, 3, 2, 2, 5]
def baseStart_1382542 : Nat := 118140960795 + 1382542 * 2 ^ 59
def prefixEnd_1382542 : Nat := 4983230072969 + 3 ^ 40 * 1382542 * 2
def baseEnd_1382542 : Nat := 105171640152360745446935

theorem tailTrace_1382542 : CollatzResearch.WordTrace tailWord_1382542 prefixEnd_1382542 105171640152360745446935 := by
  unfold tailWord_1382542
  simp only [CollatzResearch.WordTrace]
  refine ⟨6303181169661741027535735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33616966238195952146857253 6303181169661741027535735)
  ·
    refine ⟨9454771754492611541303603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6303181169661741027535735 9454771754492611541303603)
    ·
      refine ⟨14182157631738917311955405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9454771754492611541303603 14182157631738917311955405)
      ·
        refine ⟨5318309111902093991983277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14182157631738917311955405 5318309111902093991983277)
        ·
          refine ⟨1994365916963285246993729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5318309111902093991983277 1994365916963285246993729)
          ·
            refine ⟨1495774437722463935245297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1994365916963285246993729 1495774437722463935245297)
            ·
              refine ⟨1121830828291847951433973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1495774437722463935245297 1121830828291847951433973)
              ·
                refine ⟨105171640152360745446935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1121830828291847951433973 105171640152360745446935)
                ·
                  rfl

theorem cell21_1382542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_1382542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1382542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1382542 prefixEnd_1382542 := by exact prefixLift 1382542
  have htrace : WordTrace (prefixWord ++ tailWord_1382542) baseStart_1382542 baseEnd_1382542 := by
    simpa [prefixWord, tailWord_1382542, baseEnd_1382542] using wordTrace_append hprefix tailTrace_1382542
  have hstable : (prefixWord ++ tailWord_1382542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382542).length < 2 ^ (prefixWord ++ tailWord_1382542).sum := by decide
  have hdescent : baseEnd_1382542 < baseStart_1382542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382615 : List Nat := [1, 1, 3, 2, 1, 2, 1, 7, 3]
def baseStart_1382615 : Nat := 118140960795 + 1382615 * 2 ^ 59
def prefixEnd_1382615 : Nat := 4983230072969 + 3 ^ 40 * 1382615 * 2
def baseEnd_1382615 : Nat := 315531580051650331623989

theorem tailTrace_1382615 : CollatzResearch.WordTrace tailWord_1382615 prefixEnd_1382615 315531580051650331623989 := by
  unfold tailWord_1382615
  simp only [CollatzResearch.WordTrace]
  refine ⟨50428111886029461687693299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33618741257352974458462199 50428111886029461687693299)
  ·
    refine ⟨75642167829044192531539949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50428111886029461687693299 75642167829044192531539949)
    ·
      refine ⟨28365812935891572199327481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75642167829044192531539949 28365812935891572199327481)
      ·
        refine ⟨21274359701918679149495611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28365812935891572199327481 21274359701918679149495611)
        ·
          refine ⟨31911539552878018724243417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21274359701918679149495611 31911539552878018724243417)
          ·
            refine ⟨23933654664658514043182563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31911539552878018724243417 23933654664658514043182563)
            ·
              refine ⟨35900481996987771064773845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23933654664658514043182563 35900481996987771064773845)
              ·
                refine ⟨841417546804400884330637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 35900481996987771064773845 841417546804400884330637)
                ·
                  refine ⟨315531580051650331623989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 841417546804400884330637 315531580051650331623989)
                  ·
                    rfl

theorem cell21_1382615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 7, 3].length) (baseStart_1382615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1382615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1382615 prefixEnd_1382615 := by exact prefixLift 1382615
  have htrace : WordTrace (prefixWord ++ tailWord_1382615) baseStart_1382615 baseEnd_1382615 := by
    simpa [prefixWord, tailWord_1382615, baseEnd_1382615] using wordTrace_append hprefix tailTrace_1382615
  have hstable : (prefixWord ++ tailWord_1382615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382615).length < 2 ^ (prefixWord ++ tailWord_1382615).sum := by decide
  have hdescent : baseEnd_1382615 < baseStart_1382615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382632 : List Nat := [2, 1, 4, 1, 2, 3, 1, 4, 3]
def baseStart_1382632 : Nat := 118140960795 + 1382632 * 2 ^ 59
def prefixEnd_1382632 : Nat := 4983230072969 + 3 ^ 40 * 1382632 * 2
def baseEnd_1382632 : Nat := 315535459683262079840621

theorem tailTrace_1382632 : CollatzResearch.WordTrace tailWord_1382632 prefixEnd_1382632 315535459683262079840621 := by
  unfold tailWord_1382632
  simp only [CollatzResearch.WordTrace]
  refine ⟨25214365963483936795531075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33619154617978582394041433 25214365963483936795531075)
  ·
    refine ⟨37821548945225905193296613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25214365963483936795531075 37821548945225905193296613)
    ·
      refine ⟨7091540427229857223743115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37821548945225905193296613 7091540427229857223743115)
      ·
        refine ⟨10637310640844785835614673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7091540427229857223743115 10637310640844785835614673)
        ·
          refine ⟨7977982980633589376711005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10637310640844785835614673 7977982980633589376711005)
          ·
            refine ⟨2991743617737596016266627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7977982980633589376711005 2991743617737596016266627)
            ·
              refine ⟨4487615426606394024399941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2991743617737596016266627 4487615426606394024399941)
              ·
                refine ⟨841427892488698879574989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4487615426606394024399941 841427892488698879574989)
                ·
                  refine ⟨315535459683262079840621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 841427892488698879574989 315535459683262079840621)
                  ·
                    rfl

theorem cell21_1382632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 4, 3].length) (baseStart_1382632 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1382632 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1382632 prefixEnd_1382632 := by exact prefixLift 1382632
  have htrace : WordTrace (prefixWord ++ tailWord_1382632) baseStart_1382632 baseEnd_1382632 := by
    simpa [prefixWord, tailWord_1382632, baseEnd_1382632] using wordTrace_append hprefix tailTrace_1382632
  have hstable : (prefixWord ++ tailWord_1382632).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382632).length < 2 ^ (prefixWord ++ tailWord_1382632).sum := by decide
  have hdescent : baseEnd_1382632 < baseStart_1382632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382646 : List Nat := [5, 1, 1, 1, 1, 1, 4, 3, 4]
def baseStart_1382646 : Nat := 118140960795 + 1382646 * 2 ^ 59
def prefixEnd_1382646 : Nat := 4983230072969 + 3 ^ 40 * 1382646 * 2
def baseEnd_1382646 : Nat := 315538654674001166607259

theorem tailTrace_1382646 : CollatzResearch.WordTrace tailWord_1382646 prefixEnd_1382646 315538654674001166607259 := by
  unfold tailWord_1382646
  simp only [CollatzResearch.WordTrace]
  refine ⟨3151827659307322123879487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33619495032611435988047861 3151827659307322123879487)
  ·
    refine ⟨4727741488960983185819231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3151827659307322123879487 4727741488960983185819231)
    ·
      refine ⟨7091612233441474778728847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4727741488960983185819231 7091612233441474778728847)
      ·
        refine ⟨10637418350162212168093271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7091612233441474778728847 10637418350162212168093271)
        ·
          refine ⟨15956127525243318252139907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10637418350162212168093271 15956127525243318252139907)
          ·
            refine ⟨23934191287864977378209861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15956127525243318252139907 23934191287864977378209861)
            ·
              refine ⟨4487660866474683258414349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23934191287864977378209861 4487660866474683258414349)
              ·
                refine ⟨1682872824928006221905381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4487660866474683258414349 1682872824928006221905381)
                ·
                  refine ⟨315538654674001166607259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1682872824928006221905381 315538654674001166607259)
                  ·
                    rfl

theorem cell21_1382646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_1382646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1382646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1382646 prefixEnd_1382646 := by exact prefixLift 1382646
  have htrace : WordTrace (prefixWord ++ tailWord_1382646) baseStart_1382646 baseEnd_1382646 := by
    simpa [prefixWord, tailWord_1382646, baseEnd_1382646] using wordTrace_append hprefix tailTrace_1382646
  have hstable : (prefixWord ++ tailWord_1382646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382646).length < 2 ^ (prefixWord ++ tailWord_1382646).sum := by decide
  have hdescent : baseEnd_1382646 < baseStart_1382646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382691 : List Nat := [1, 1, 1, 4, 2, 2, 1, 6, 3]
def baseStart_1382691 : Nat := 118140960795 + 1382691 * 2 ^ 59
def prefixEnd_1382691 : Nat := 4983230072969 + 3 ^ 40 * 1382691 * 2
def baseEnd_1382691 : Nat := 315548924287091088357167

theorem tailTrace_1382691 : CollatzResearch.WordTrace tailWord_1382691 prefixEnd_1382691 315548924287091088357167 := by
  unfold tailWord_1382691
  simp only [CollatzResearch.WordTrace]
  refine ⟨50430883833754126667459927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33620589222502751111639951 50430883833754126667459927)
  ·
    refine ⟨75646325750631190001189891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50430883833754126667459927 75646325750631190001189891)
    ·
      refine ⟨113469488625946785001784837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75646325750631190001189891 113469488625946785001784837)
      ·
        refine ⟨21275529117365022187834657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113469488625946785001784837 21275529117365022187834657)
        ·
          refine ⟨15956646838023766640875993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21275529117365022187834657 15956646838023766640875993)
          ·
            refine ⟨11967485128517824980656995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15956646838023766640875993 11967485128517824980656995)
            ·
              refine ⟨17951227692776737470985493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11967485128517824980656995 17951227692776737470985493)
              ·
                refine ⟨841463798098909568952445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17951227692776737470985493 841463798098909568952445)
                ·
                  refine ⟨315548924287091088357167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 841463798098909568952445 315548924287091088357167)
                  ·
                    rfl

theorem cell21_1382691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 6, 3].length) (baseStart_1382691 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1382691 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1382691 prefixEnd_1382691 := by exact prefixLift 1382691
  have htrace : WordTrace (prefixWord ++ tailWord_1382691) baseStart_1382691 baseEnd_1382691 := by
    simpa [prefixWord, tailWord_1382691, baseEnd_1382691] using wordTrace_append hprefix tailTrace_1382691
  have hstable : (prefixWord ++ tailWord_1382691).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382691).length < 2 ^ (prefixWord ++ tailWord_1382691).sum := by decide
  have hdescent : baseEnd_1382691 < baseStart_1382691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382719 : List Nat := [1, 1, 2, 2, 4, 1, 3, 7]
def baseStart_1382719 : Nat := 118140960795 + 1382719 * 2 ^ 59
def prefixEnd_1382719 : Nat := 4983230072969 + 3 ^ 40 * 1382719 * 2
def baseEnd_1382719 : Nat := 105185104756189753963481

theorem tailTrace_1382719 : CollatzResearch.WordTrace tailWord_1382719 prefixEnd_1382719 105185104756189753963481 := by
  unfold tailWord_1382719
  simp only [CollatzResearch.WordTrace]
  refine ⟨50431905077652687449479211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33621270051768458299652807 50431905077652687449479211)
  ·
    refine ⟨75647857616479031174218817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50431905077652687449479211 75647857616479031174218817)
    ·
      refine ⟨56735893212359273380664113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75647857616479031174218817 56735893212359273380664113)
      ·
        refine ⟨42551919909269455035498085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56735893212359273380664113 42551919909269455035498085)
        ·
          refine ⟨7978484982988022819155891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42551919909269455035498085 7978484982988022819155891)
          ·
            refine ⟨11967727474482034228733837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7978484982988022819155891 11967727474482034228733837)
            ·
              refine ⟨4487897802930762835775189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11967727474482034228733837 4487897802930762835775189)
              ·
                refine ⟨105185104756189753963481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4487897802930762835775189 105185104756189753963481)
                ·
                  rfl

theorem cell21_1382719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 7].length) (baseStart_1382719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1382719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1382719 prefixEnd_1382719 := by exact prefixLift 1382719
  have htrace : WordTrace (prefixWord ++ tailWord_1382719) baseStart_1382719 baseEnd_1382719 := by
    simpa [prefixWord, tailWord_1382719, baseEnd_1382719] using wordTrace_append hprefix tailTrace_1382719
  have hstable : (prefixWord ++ tailWord_1382719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382719).length < 2 ^ (prefixWord ++ tailWord_1382719).sum := by decide
  have hdescent : baseEnd_1382719 < baseStart_1382719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382798 : List Nat := [4, 1, 1, 4, 1, 1, 1, 4, 4]
def baseStart_1382798 : Nat := 118140960795 + 1382798 * 2 ^ 59
def prefixEnd_1382798 : Nat := 4983230072969 + 3 ^ 40 * 1382798 * 2
def baseEnd_1382798 : Nat := 315573343144882680073615

theorem tailTrace_1382798 : CollatzResearch.WordTrace tailWord_1382798 prefixEnd_1382798 315573343144882680073615 := by
  unfold tailWord_1382798
  simp only [CollatzResearch.WordTrace]
  refine ⟨6304348305545810492700631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33623190962910989294403365 6304348305545810492700631)
  ·
    refine ⟨9456522458318715739050947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6304348305545810492700631 9456522458318715739050947)
    ·
      refine ⟨14184783687478073608576421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9456522458318715739050947 14184783687478073608576421)
      ·
        refine ⟨2659646941402138801608079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14184783687478073608576421 2659646941402138801608079)
        ·
          refine ⟨3989470412103208202412119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2659646941402138801608079 3989470412103208202412119)
          ·
            refine ⟨5984205618154812303618179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3989470412103208202412119 5984205618154812303618179)
            ·
              refine ⟨8976308427232218455427269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5984205618154812303618179 8976308427232218455427269)
              ·
                refine ⟨1683057830106040960392613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8976308427232218455427269 1683057830106040960392613)
                ·
                  refine ⟨315573343144882680073615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1683057830106040960392613 315573343144882680073615)
                  ·
                    rfl

theorem cell21_1382798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_1382798 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1382798 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1382798 prefixEnd_1382798 := by exact prefixLift 1382798
  have htrace : WordTrace (prefixWord ++ tailWord_1382798) baseStart_1382798 baseEnd_1382798 := by
    simpa [prefixWord, tailWord_1382798, baseEnd_1382798] using wordTrace_append hprefix tailTrace_1382798
  have hstable : (prefixWord ++ tailWord_1382798).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382798).length < 2 ^ (prefixWord ++ tailWord_1382798).sum := by decide
  have hdescent : baseEnd_1382798 < baseStart_1382798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382840 : List Nat := [2, 1, 2, 1, 2, 2, 1, 4, 6]
def baseStart_1382840 : Nat := 118140960795 + 1382840 * 2 ^ 59
def prefixEnd_1382840 : Nat := 4983230072969 + 3 ^ 40 * 1382840 * 2
def baseEnd_1382840 : Nat := 315582928117099940373529

theorem tailTrace_1382840 : CollatzResearch.WordTrace tailWord_1382840 prefixEnd_1382840 315582928117099940373529 := by
  unfold tailWord_1382840
  simp only [CollatzResearch.WordTrace]
  refine ⟨25218159155107162557316987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33624212206809550076422649 25218159155107162557316987)
  ·
    refine ⟨37827238732660743835975481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25218159155107162557316987 37827238732660743835975481)
    ·
      refine ⟨28370429049495557876981611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37827238732660743835975481 28370429049495557876981611)
      ·
        refine ⟨42555643574243336815472417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28370429049495557876981611 42555643574243336815472417)
        ·
          refine ⟨31916732680682502611604313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42555643574243336815472417 31916732680682502611604313)
          ·
            refine ⟨23937549510511876958703235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31916732680682502611604313 23937549510511876958703235)
            ·
              refine ⟨35906324265767815438054853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23937549510511876958703235 35906324265767815438054853)
              ·
                refine ⟨6732435799831465394635285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35906324265767815438054853 6732435799831465394635285)
                ·
                  refine ⟨315582928117099940373529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6732435799831465394635285 315582928117099940373529)
                  ·
                    rfl

theorem cell21_1382840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 6].length) (baseStart_1382840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1382840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1382840 prefixEnd_1382840 := by exact prefixLift 1382840
  have htrace : WordTrace (prefixWord ++ tailWord_1382840) baseStart_1382840 baseEnd_1382840 := by
    simpa [prefixWord, tailWord_1382840, baseEnd_1382840] using wordTrace_append hprefix tailTrace_1382840
  have hstable : (prefixWord ++ tailWord_1382840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382840).length < 2 ^ (prefixWord ++ tailWord_1382840).sum := by decide
  have hdescent : baseEnd_1382840 < baseStart_1382840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382849 : List Nat := [1, 2, 7, 1, 1, 2, 1, 2, 4]
def baseStart_1382849 : Nat := 118140960795 + 1382849 * 2 ^ 59
def prefixEnd_1382849 : Nat := 4983230072969 + 3 ^ 40 * 1382849 * 2
def baseEnd_1382849 : Nat := 315584982039717924723511

theorem tailTrace_1382849 : CollatzResearch.WordTrace tailWord_1382849 prefixEnd_1382849 315584982039717924723511 := by
  unfold tailWord_1382849
  simp only [CollatzResearch.WordTrace]
  refine ⟨50436646567181719651711601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33624431044787813101141067 50436646567181719651711601)
  ·
    refine ⟨37827484925386289738783701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50436646567181719651711601 37827484925386289738783701)
    ·
      refine ⟨886581677938741165752743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 37827484925386289738783701 886581677938741165752743)
      ·
        refine ⟨1329872516908111748629115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 886581677938741165752743 1329872516908111748629115)
        ·
          refine ⟨1994808775362167622943673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1329872516908111748629115 1994808775362167622943673)
          ·
            refine ⟨1496106581521625717207755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1994808775362167622943673 1496106581521625717207755)
            ·
              refine ⟨2244159872282438575811633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1496106581521625717207755 2244159872282438575811633)
              ·
                refine ⟨1683119904211828931858725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2244159872282438575811633 1683119904211828931858725)
                ·
                  refine ⟨315584982039717924723511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1683119904211828931858725 315584982039717924723511)
                  ·
                    rfl

theorem cell21_1382849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 2, 4].length) (baseStart_1382849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1382849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1382849 prefixEnd_1382849 := by exact prefixLift 1382849
  have htrace : WordTrace (prefixWord ++ tailWord_1382849) baseStart_1382849 baseEnd_1382849 := by
    simpa [prefixWord, tailWord_1382849, baseEnd_1382849] using wordTrace_append hprefix tailTrace_1382849
  have hstable : (prefixWord ++ tailWord_1382849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382849).length < 2 ^ (prefixWord ++ tailWord_1382849).sum := by decide
  have hdescent : baseEnd_1382849 < baseStart_1382849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382857 : List Nat := [1, 2, 1, 1, 2, 1, 7, 2, 4]
def baseStart_1382857 : Nat := 118140960795 + 1382857 * 2 ^ 59
def prefixEnd_1382857 : Nat := 4983230072969 + 3 ^ 40 * 1382857 * 2
def baseEnd_1382857 : Nat := 315586807748711688590161

theorem tailTrace_1382857 : CollatzResearch.WordTrace tailWord_1382857 prefixEnd_1382857 315586807748711688590161 := by
  unfold tailWord_1382857
  simp only [CollatzResearch.WordTrace]
  refine ⟨50436938351152737018002825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33624625567435158012001883 50436938351152737018002825)
  ·
    refine ⟨37827703763364552763502119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50436938351152737018002825 37827703763364552763502119)
    ·
      refine ⟨56741555645046829145253179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37827703763364552763502119 56741555645046829145253179)
      ·
        refine ⟨85112333467570243717879769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56741555645046829145253179 85112333467570243717879769)
        ·
          refine ⟨63834250100677682788409827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85112333467570243717879769 63834250100677682788409827)
          ·
            refine ⟨95751375151016524182614741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63834250100677682788409827 95751375151016524182614741)
            ·
              refine ⟨2244172855101949785530033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 95751375151016524182614741 2244172855101949785530033)
              ·
                refine ⟨1683129641326462339147525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2244172855101949785530033 1683129641326462339147525)
                ·
                  refine ⟨315586807748711688590161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1683129641326462339147525 315586807748711688590161)
                  ·
                    rfl

theorem cell21_1382857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 2, 4].length) (baseStart_1382857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1382857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1382857 prefixEnd_1382857 := by exact prefixLift 1382857
  have htrace : WordTrace (prefixWord ++ tailWord_1382857) baseStart_1382857 baseEnd_1382857 := by
    simpa [prefixWord, tailWord_1382857, baseEnd_1382857] using wordTrace_append hprefix tailTrace_1382857
  have hstable : (prefixWord ++ tailWord_1382857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382857).length < 2 ^ (prefixWord ++ tailWord_1382857).sum := by decide
  have hdescent : baseEnd_1382857 < baseStart_1382857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382874 : List Nat := [3, 1, 1, 2, 3, 1, 5, 1, 4]
def baseStart_1382874 : Nat := 118140960795 + 1382874 * 2 ^ 59
def prefixEnd_1382874 : Nat := 4983230072969 + 3 ^ 40 * 1382874 * 2
def baseEnd_1382874 : Nat := 315590687380323436806793

theorem tailTrace_1382874 : CollatzResearch.WordTrace tailWord_1382874 prefixEnd_1382874 315590687380323436806793 := by
  unfold tailWord_1382874
  simp only [CollatzResearch.WordTrace]
  refine ⟨12609389598022787230342919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33625038928060765947581117 12609389598022787230342919)
  ·
    refine ⟨18914084397034180845514379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12609389598022787230342919 18914084397034180845514379)
    ·
      refine ⟨28371126595551271268271569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18914084397034180845514379 28371126595551271268271569)
      ·
        refine ⟨21278344946663453451203677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28371126595551271268271569 21278344946663453451203677)
        ·
          refine ⟨7979379354998795044201379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21278344946663453451203677 7979379354998795044201379)
          ·
            refine ⟨11969069032498192566302069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7979379354998795044201379 11969069032498192566302069)
            ·
              refine ⟨1122100221796705553090819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11969069032498192566302069 1122100221796705553090819)
              ·
                refine ⟨1683150332695058329636229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1122100221796705553090819 1683150332695058329636229)
                ·
                  refine ⟨315590687380323436806793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1683150332695058329636229 315590687380323436806793)
                  ·
                    rfl

theorem cell21_1382874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 1, 4].length) (baseStart_1382874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1382874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1382874 prefixEnd_1382874 := by exact prefixLift 1382874
  have htrace : WordTrace (prefixWord ++ tailWord_1382874) baseStart_1382874 baseEnd_1382874 := by
    simpa [prefixWord, tailWord_1382874, baseEnd_1382874] using wordTrace_append hprefix tailTrace_1382874
  have hstable : (prefixWord ++ tailWord_1382874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382874).length < 2 ^ (prefixWord ++ tailWord_1382874).sum := by decide
  have hdescent : baseEnd_1382874 < baseStart_1382874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382888 : List Nat := [2, 1, 4, 1, 1, 3, 4, 5]
def baseStart_1382888 : Nat := 118140960795 + 1382888 * 2 ^ 59
def prefixEnd_1382888 : Nat := 4983230072969 + 3 ^ 40 * 1382888 * 2
def baseEnd_1382888 : Nat := 105197960790354174524477

theorem tailTrace_1382888 : CollatzResearch.WordTrace tailWord_1382888 prefixEnd_1382888 105197960790354174524477 := by
  unfold tailWord_1382888
  simp only [CollatzResearch.WordTrace]
  refine ⟨25219034507020214656190659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33625379342693619541587545 25219034507020214656190659)
  ·
    refine ⟨37828551760530321984285989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25219034507020214656190659 37828551760530321984285989)
    ·
      refine ⟨7092853455099435372053623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37828551760530321984285989 7092853455099435372053623)
      ·
        refine ⟨10639280182649153058080435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7092853455099435372053623 10639280182649153058080435)
        ·
          refine ⟨15958920273973729587120653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10639280182649153058080435 15958920273973729587120653)
          ·
            refine ⟨5984595102740148595170245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15958920273973729587120653 5984595102740148595170245)
            ·
              refine ⟨1122111581763777861594421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5984595102740148595170245 1122111581763777861594421)
              ·
                refine ⟨105197960790354174524477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1122111581763777861594421 105197960790354174524477)
                ·
                  rfl

theorem cell21_1382888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 5].length) (baseStart_1382888 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1382888 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1382888 prefixEnd_1382888 := by exact prefixLift 1382888
  have htrace : WordTrace (prefixWord ++ tailWord_1382888) baseStart_1382888 baseEnd_1382888 := by
    simpa [prefixWord, tailWord_1382888, baseEnd_1382888] using wordTrace_append hprefix tailTrace_1382888
  have hstable : (prefixWord ++ tailWord_1382888).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382888).length < 2 ^ (prefixWord ++ tailWord_1382888).sum := by decide
  have hdescent : baseEnd_1382888 < baseStart_1382888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382925 : List Nat := [1, 7, 1, 1, 1, 3, 2, 1, 4]
def baseStart_1382925 : Nat := 118140960795 + 1382925 * 2 ^ 59
def prefixEnd_1382925 : Nat := 4983230072969 + 3 ^ 40 * 1382925 * 2
def baseEnd_1382925 : Nat := 315602326275158681456689

theorem tailTrace_1382925 : CollatzResearch.WordTrace tailWord_1382925 prefixEnd_1382925 315602326275158681456689 := by
  unfold tailWord_1382925
  simp only [CollatzResearch.WordTrace]
  refine ⟨50439418514906384631478229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33626279009937589754318819 50439418514906384631478229)
  ·
    refine ⟨1182173871443118389800271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 50439418514906384631478229 1182173871443118389800271)
    ·
      refine ⟨1773260807164677584700407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1182173871443118389800271 1773260807164677584700407)
      ·
        refine ⟨2659891210747016377050611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1773260807164677584700407 2659891210747016377050611)
        ·
          refine ⟨3989836816120524565575917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2659891210747016377050611 3989836816120524565575917)
          ·
            refine ⟨1496188806045196712090969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3989836816120524565575917 1496188806045196712090969)
            ·
              refine ⟨1122141604533897534068227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1496188806045196712090969 1122141604533897534068227)
              ·
                refine ⟨1683212406800846301102341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1122141604533897534068227 1683212406800846301102341)
                ·
                  refine ⟨315602326275158681456689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1683212406800846301102341 315602326275158681456689)
                  ·
                    rfl

theorem cell21_1382925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_1382925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1382925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1382925 prefixEnd_1382925 := by exact prefixLift 1382925
  have htrace : WordTrace (prefixWord ++ tailWord_1382925) baseStart_1382925 baseEnd_1382925 := by
    simpa [prefixWord, tailWord_1382925, baseEnd_1382925] using wordTrace_append hprefix tailTrace_1382925
  have hstable : (prefixWord ++ tailWord_1382925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382925).length < 2 ^ (prefixWord ++ tailWord_1382925).sum := by decide
  have hdescent : baseEnd_1382925 < baseStart_1382925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382933 : List Nat := [1, 3, 2, 1, 3, 1, 3, 3, 4]
def baseStart_1382933 : Nat := 118140960795 + 1382933 * 2 ^ 59
def prefixEnd_1382933 : Nat := 4983230072969 + 3 ^ 40 * 1382933 * 2
def baseEnd_1382933 : Nat := 315604151984152445323339

theorem tailTrace_1382933 : CollatzResearch.WordTrace tailWord_1382933 prefixEnd_1382933 315604151984152445323339 := by
  unfold tailWord_1382933
  simp only [CollatzResearch.WordTrace]
  refine ⟨50439710298877401997769453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33626473532584934665179635 50439710298877401997769453)
  ·
    refine ⟨18914891362079025749163545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50439710298877401997769453 18914891362079025749163545)
    ·
      refine ⟨14186168521559269311872659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18914891362079025749163545 14186168521559269311872659)
      ·
        refine ⟨21279252782338903967808989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14186168521559269311872659 21279252782338903967808989)
        ·
          refine ⟨7979719793377088987928371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21279252782338903967808989 7979719793377088987928371)
          ·
            refine ⟨11969579690065633481892557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7979719793377088987928371 11969579690065633481892557)
            ·
              refine ⟨4488592383774612555709709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11969579690065633481892557 4488592383774612555709709)
              ·
                refine ⟨1683222143915479708391141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4488592383774612555709709 1683222143915479708391141)
                ·
                  refine ⟨315604151984152445323339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1683222143915479708391141 315604151984152445323339)
                  ·
                    rfl

theorem cell21_1382933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 3, 4].length) (baseStart_1382933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1382933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1382933 prefixEnd_1382933 := by exact prefixLift 1382933
  have htrace : WordTrace (prefixWord ++ tailWord_1382933) baseStart_1382933 baseEnd_1382933 := by
    simpa [prefixWord, tailWord_1382933, baseEnd_1382933] using wordTrace_append hprefix tailTrace_1382933
  have hstable : (prefixWord ++ tailWord_1382933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382933).length < 2 ^ (prefixWord ++ tailWord_1382933).sum := by decide
  have hdescent : baseEnd_1382933 < baseStart_1382933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382947 : List Nat := [1, 1, 1, 4, 4, 1, 2, 7]
def baseStart_1382947 : Nat := 118140960795 + 1382947 * 2 ^ 59
def prefixEnd_1382947 : Nat := 4983230072969 + 3 ^ 40 * 1382947 * 2
def baseEnd_1382947 : Nat := 105202448991630510696659

theorem tailTrace_1382947 : CollatzResearch.WordTrace tailWord_1382947 prefixEnd_1382947 105202448991630510696659 := by
  unfold tailWord_1382947
  simp only [CollatzResearch.WordTrace]
  refine ⟨50440220920826682388779095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33626813947217788259186063 50440220920826682388779095)
  ·
    refine ⟨75660331381240023583168643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50440220920826682388779095 75660331381240023583168643)
    ·
      refine ⟨113490497071860035374752965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75660331381240023583168643 113490497071860035374752965)
      ·
        refine ⟨21279468200973756632766181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113490497071860035374752965 21279468200973756632766181)
        ·
          refine ⟨3989900287682579368643659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21279468200973756632766181 3989900287682579368643659)
          ·
            refine ⟨5984850431523869052965489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3989900287682579368643659 5984850431523869052965489)
            ·
              refine ⟨4488637823642901789724117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5984850431523869052965489 4488637823642901789724117)
              ·
                refine ⟨105202448991630510696659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4488637823642901789724117 105202448991630510696659)
                ·
                  rfl

theorem cell21_1382947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 7].length) (baseStart_1382947 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1382947 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1382947 prefixEnd_1382947 := by exact prefixLift 1382947
  have htrace : WordTrace (prefixWord ++ tailWord_1382947) baseStart_1382947 baseEnd_1382947 := by
    simpa [prefixWord, tailWord_1382947, baseEnd_1382947] using wordTrace_append hprefix tailTrace_1382947
  have hstable : (prefixWord ++ tailWord_1382947).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382947).length < 2 ^ (prefixWord ++ tailWord_1382947).sum := by decide
  have hdescent : baseEnd_1382947 < baseStart_1382947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382964 : List Nat := [2, 5, 1, 3, 10]
def baseStart_1382964 : Nat := 118140960795 + 1382964 * 2 ^ 59
def prefixEnd_1382964 : Nat := 4983230072969 + 3 ^ 40 * 1382964 * 2
def baseEnd_1382964 : Nat := 3896434896376583707489

theorem tailTrace_1382964 : CollatzResearch.WordTrace tailWord_1382964 prefixEnd_1382964 3896434896376583707489 := by
  unfold tailWord_1382964
  simp only [CollatzResearch.WordTrace]
  refine ⟨25220420480882547146073973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33627227307843396194765297 25220420480882547146073973)
  ·
    refine ⟨2364414420082738794944435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25220420480882547146073973 2364414420082738794944435)
    ·
      refine ⟨3546621630124108192416653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2364414420082738794944435 3546621630124108192416653)
      ·
        refine ⟨1329983111296540572156245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3546621630124108192416653 1329983111296540572156245)
        ·
          refine ⟨3896434896376583707489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1329983111296540572156245 3896434896376583707489)
          ·
            rfl

theorem cell21_1382964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 10].length) (baseStart_1382964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1382964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1382964 prefixEnd_1382964 := by exact prefixLift 1382964
  have htrace : WordTrace (prefixWord ++ tailWord_1382964) baseStart_1382964 baseEnd_1382964 := by
    simpa [prefixWord, tailWord_1382964, baseEnd_1382964] using wordTrace_append hprefix tailTrace_1382964
  have hstable : (prefixWord ++ tailWord_1382964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382964).length < 2 ^ (prefixWord ++ tailWord_1382964).sum := by decide
  have hdescent : baseEnd_1382964 < baseStart_1382964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383054 : List Nat := [4, 1, 1, 3, 1, 1, 1, 4, 5]
def baseStart_1383054 : Nat := 118140960795 + 1383054 * 2 ^ 59
def prefixEnd_1383054 : Nat := 4983230072969 + 3 ^ 40 * 1383054 * 2
def baseEnd_1383054 : Nat := 315631765832683123806425

theorem tailTrace_1383054 : CollatzResearch.WordTrace tailWord_1383054 prefixEnd_1383054 315631765832683123806425 := by
  unfold tailWord_1383054
  simp only [CollatzResearch.WordTrace]
  refine ⟨6305515441429879957865527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33629415687626026441949477 6305515441429879957865527)
  ·
    refine ⟨9458273162144819936798291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6305515441429879957865527 9458273162144819936798291)
    ·
      refine ⟨14187409743217229905197437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9458273162144819936798291 14187409743217229905197437)
      ·
        refine ⟨5320278653706461214449039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14187409743217229905197437 5320278653706461214449039)
        ·
          refine ⟨7980417980559691821673559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5320278653706461214449039 7980417980559691821673559)
          ·
            refine ⟨11970626970839537732510339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7980417980559691821673559 11970626970839537732510339)
            ·
              refine ⟨17955940456259306598765509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11970626970839537732510339 17955940456259306598765509)
              ·
                refine ⟨3366738835548619987268533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17955940456259306598765509 3366738835548619987268533)
                ·
                  refine ⟨315631765832683123806425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3366738835548619987268533 315631765832683123806425)
                  ·
                    rfl

theorem cell21_1383054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_1383054 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1383054 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1383054 prefixEnd_1383054 := by exact prefixLift 1383054
  have htrace : WordTrace (prefixWord ++ tailWord_1383054) baseStart_1383054 baseEnd_1383054 := by
    simpa [prefixWord, tailWord_1383054, baseEnd_1383054] using wordTrace_append hprefix tailTrace_1383054
  have hstable : (prefixWord ++ tailWord_1383054).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383054).length < 2 ^ (prefixWord ++ tailWord_1383054).sum := by decide
  have hdescent : baseEnd_1383054 < baseStart_1383054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383085 : List Nat := [1, 5, 2, 1, 1, 2, 2, 1, 6]
def baseStart_1383085 : Nat := 118140960795 + 1383085 * 2 ^ 59
def prefixEnd_1383085 : Nat := 4983230072969 + 3 ^ 40 * 1383085 * 2
def baseEnd_1383085 : Nat := 315638840455033958789695

theorem tailTrace_1383085 : CollatzResearch.WordTrace tailWord_1383085 prefixEnd_1383085 315638840455033958789695 := by
  unfold tailWord_1383085
  simp only [CollatzResearch.WordTrace]
  refine ⟨50445254194326731957302709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33630169462884487971535139 50445254194326731957302709)
  ·
    refine ⟨4729242580718131120997129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50445254194326731957302709 4729242580718131120997129)
    ·
      refine ⟨3546931935538598340747847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4729242580718131120997129 3546931935538598340747847)
      ·
        refine ⟨5320397903307897511121771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3546931935538598340747847 5320397903307897511121771)
        ·
          refine ⟨7980596854961846266682657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5320397903307897511121771 7980596854961846266682657)
          ·
            refine ⟨5985447641221384700011993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7980596854961846266682657 5985447641221384700011993)
            ·
              refine ⟨4489085730916038525008995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5985447641221384700011993 4489085730916038525008995)
              ·
                refine ⟨6733628596374057787513493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4489085730916038525008995 6733628596374057787513493)
                ·
                  refine ⟨315638840455033958789695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6733628596374057787513493 315638840455033958789695)
                  ·
                    rfl

theorem cell21_1383085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_1383085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1383085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1383085 prefixEnd_1383085 := by exact prefixLift 1383085
  have htrace : WordTrace (prefixWord ++ tailWord_1383085) baseStart_1383085 baseEnd_1383085 := by
    simpa [prefixWord, tailWord_1383085, baseEnd_1383085] using wordTrace_append hprefix tailTrace_1383085
  have hstable : (prefixWord ++ tailWord_1383085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383085).length < 2 ^ (prefixWord ++ tailWord_1383085).sum := by decide
  have hdescent : baseEnd_1383085 < baseStart_1383085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383189 : List Nat := [1, 3, 2, 1, 2, 2, 1, 2, 7]
def baseStart_1383189 : Nat := 118140960795 + 1383189 * 2 ^ 59
def prefixEnd_1383189 : Nat := 4983230072969 + 3 ^ 40 * 1383189 * 2
def baseEnd_1383189 : Nat := 315662574671952889056149

theorem tailTrace_1383189 : CollatzResearch.WordTrace tailWord_1383189 prefixEnd_1383189 315662574671952889056149 := by
  unfold tailWord_1383189
  simp only [CollatzResearch.WordTrace]
  refine ⟨50449047385949957719088621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33632698257299971812725747 50449047385949957719088621)
  ·
    refine ⟨18918392769731234144658233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50449047385949957719088621 18918392769731234144658233)
    ·
      refine ⟨14188794577298425608493675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18918392769731234144658233 14188794577298425608493675)
      ·
        refine ⟨21283191865947638412740513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14188794577298425608493675 21283191865947638412740513)
        ·
          refine ⟨15962393899460728809555385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21283191865947638412740513 15962393899460728809555385)
          ·
            refine ⟨11971795424595546607166539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15962393899460728809555385 11971795424595546607166539)
            ·
              refine ⟨17957693136893319910749809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11971795424595546607166539 17957693136893319910749809)
              ·
                refine ⟨13468269852669989933062357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17957693136893319910749809 13468269852669989933062357)
                ·
                  refine ⟨315662574671952889056149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13468269852669989933062357 315662574671952889056149)
                  ·
                    rfl

theorem cell21_1383189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_1383189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1383189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1383189 prefixEnd_1383189 := by exact prefixLift 1383189
  have htrace : WordTrace (prefixWord ++ tailWord_1383189) baseStart_1383189 baseEnd_1383189 := by
    simpa [prefixWord, tailWord_1383189, baseEnd_1383189] using wordTrace_append hprefix tailTrace_1383189
  have hstable : (prefixWord ++ tailWord_1383189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383189).length < 2 ^ (prefixWord ++ tailWord_1383189).sum := by decide
  have hdescent : baseEnd_1383189 < baseStart_1383189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383265 : List Nat := [1, 2, 3, 1, 1, 1, 2, 5, 5]
def baseStart_1383265 : Nat := 118140960795 + 1383265 * 2 ^ 59
def prefixEnd_1383265 : Nat := 4983230072969 + 3 ^ 40 * 1383265 * 2
def baseEnd_1383265 : Nat := 315679918907393645789327

theorem tailTrace_1383265 : CollatzResearch.WordTrace tailWord_1383265 prefixEnd_1383265 315679918907393645789327 := by
  unfold tailWord_1383265
  simp only [CollatzResearch.WordTrace]
  refine ⟨50451819333674622698855249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33634546222449748465903499 50451819333674622698855249)
  ·
    refine ⟨37838864500255967024141437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50451819333674622698855249 37838864500255967024141437)
    ·
      refine ⟨14189574187595987634053039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37838864500255967024141437 14189574187595987634053039)
      ·
        refine ⟨21284361281393981451079559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14189574187595987634053039 21284361281393981451079559)
        ·
          refine ⟨31926541922090972176619339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21284361281393981451079559 31926541922090972176619339)
          ·
            refine ⟨47889812883136458264929009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31926541922090972176619339 47889812883136458264929009)
            ·
              refine ⟨35917359662352343698696757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47889812883136458264929009 35917359662352343698696757)
              ·
                refine ⟨3367252468345532221752821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35917359662352343698696757 3367252468345532221752821)
                ·
                  refine ⟨315679918907393645789327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3367252468345532221752821 315679918907393645789327)
                  ·
                    rfl

theorem cell21_1383265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 5].length) (baseStart_1383265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1383265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1383265 prefixEnd_1383265 := by exact prefixLift 1383265
  have htrace : WordTrace (prefixWord ++ tailWord_1383265) baseStart_1383265 baseEnd_1383265 := by
    simpa [prefixWord, tailWord_1383265, baseEnd_1383265] using wordTrace_append hprefix tailTrace_1383265
  have hstable : (prefixWord ++ tailWord_1383265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383265).length < 2 ^ (prefixWord ++ tailWord_1383265).sum := by decide
  have hdescent : baseEnd_1383265 < baseStart_1383265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383310 : List Nat := [4, 1, 1, 15]
def baseStart_1383310 : Nat := 118140960795 + 1383310 * 2 ^ 59
def prefixEnd_1383310 : Nat := 4983230072969 + 3 ^ 40 * 1383310 * 2
def baseEnd_1383310 : Nat := 1299136578273594928145

theorem tailTrace_1383310 : CollatzResearch.WordTrace tailWord_1383310 prefixEnd_1383310 1299136578273594928145 := by
  unfold tailWord_1383310
  simp only [CollatzResearch.WordTrace]
  refine ⟨6306682577313949423030423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33635640412341063589495589 6306682577313949423030423)
  ·
    refine ⟨9460023865970924134545635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6306682577313949423030423 9460023865970924134545635)
    ·
      refine ⟨14190035798956386201818453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9460023865970924134545635 14190035798956386201818453)
      ·
        refine ⟨1299136578273594928145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 14190035798956386201818453 1299136578273594928145)
        ·
          rfl

theorem cell21_1383310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 15].length) (baseStart_1383310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1383310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1383310 prefixEnd_1383310 := by exact prefixLift 1383310
  have htrace : WordTrace (prefixWord ++ tailWord_1383310) baseStart_1383310 baseEnd_1383310 := by
    simpa [prefixWord, tailWord_1383310, baseEnd_1383310] using wordTrace_append hprefix tailTrace_1383310
  have hstable : (prefixWord ++ tailWord_1383310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383310).length < 2 ^ (prefixWord ++ tailWord_1383310).sum := by decide
  have hdescent : baseEnd_1383310 < baseStart_1383310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383327 : List Nat := [1, 1, 2, 5, 2, 1, 3, 6]
def baseStart_1383327 : Nat := 118140960795 + 1383327 * 2 ^ 59
def prefixEnd_1383327 : Nat := 4983230072969 + 3 ^ 40 * 1383327 * 2
def baseEnd_1383327 : Nat := 105231356050698438585289

theorem tailTrace_1383327 : CollatzResearch.WordTrace tailWord_1383327 prefixEnd_1383327 105231356050698438585289 := by
  unfold tailWord_1383327
  simp only [CollatzResearch.WordTrace]
  refine ⟨50454080659450007287612235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33636053772966671525074823 50454080659450007287612235)
  ·
    refine ⟨75681120989175010931418353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50454080659450007287612235 75681120989175010931418353)
    ·
      refine ⟨56760840741881258198563765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75681120989175010931418353 56760840741881258198563765)
      ·
        refine ⟨5321328819551367956115353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56760840741881258198563765 5321328819551367956115353)
        ·
          refine ⟨3990996614663525967086515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5321328819551367956115353 3990996614663525967086515)
          ·
            refine ⟨5986494921995288950629773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3990996614663525967086515 5986494921995288950629773)
            ·
              refine ⟨2244935595748233356486165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5986494921995288950629773 2244935595748233356486165)
              ·
                refine ⟨105231356050698438585289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2244935595748233356486165 105231356050698438585289)
                ·
                  rfl

theorem cell21_1383327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 6].length) (baseStart_1383327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1383327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1383327 prefixEnd_1383327 := by exact prefixLift 1383327
  have htrace : WordTrace (prefixWord ++ tailWord_1383327) baseStart_1383327 baseEnd_1383327 := by
    simpa [prefixWord, tailWord_1383327, baseEnd_1383327] using wordTrace_append hprefix tailTrace_1383327
  have hstable : (prefixWord ++ tailWord_1383327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383327).length < 2 ^ (prefixWord ++ tailWord_1383327).sum := by decide
  have hdescent : baseEnd_1383327 < baseStart_1383327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383364 : List Nat := [2, 3, 3, 3, 2, 1, 1, 2, 4]
def baseStart_1383364 : Nat := 118140960795 + 1383364 * 2 ^ 59
def prefixEnd_1383364 : Nat := 4983230072969 + 3 ^ 40 * 1383364 * 2
def baseEnd_1383364 : Nat := 315702512056191473639125

theorem tailTrace_1383364 : CollatzResearch.WordTrace tailWord_1383364 prefixEnd_1383364 315702512056191473639125 := by
  unfold tailWord_1383364
  simp only [CollatzResearch.WordTrace]
  refine ⟨25227715080157981303354573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33636953440210641737806097 25227715080157981303354573)
  ·
    refine ⟨9460393155059242988757965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25227715080157981303354573 9460393155059242988757965)
    ·
      refine ⟨3547647433147216120784237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9460393155059242988757965 3547647433147216120784237)
      ·
        refine ⟨1330367787430206045294089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3547647433147216120784237 1330367787430206045294089)
        ·
          refine ⟨997775840572654533970567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1330367787430206045294089 997775840572654533970567)
          ·
            refine ⟨1496663760858981800955851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 997775840572654533970567 1496663760858981800955851)
            ·
              refine ⟨2244995641288472701433777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1496663760858981800955851 2244995641288472701433777)
              ·
                refine ⟨1683746730966354526075333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2244995641288472701433777 1683746730966354526075333)
                ·
                  refine ⟨315702512056191473639125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1683746730966354526075333 315702512056191473639125)
                  ·
                    rfl

theorem cell21_1383364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 2, 4].length) (baseStart_1383364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1383364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1383364 prefixEnd_1383364 := by exact prefixLift 1383364
  have htrace : WordTrace (prefixWord ++ tailWord_1383364) baseStart_1383364 baseEnd_1383364 := by
    simpa [prefixWord, tailWord_1383364, baseEnd_1383364] using wordTrace_append hprefix tailTrace_1383364
  have hstable : (prefixWord ++ tailWord_1383364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383364).length < 2 ^ (prefixWord ++ tailWord_1383364).sum := by decide
  have hdescent : baseEnd_1383364 < baseStart_1383364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383372 : List Nat := [2, 2, 1, 4, 1, 1, 3, 1, 6]
def baseStart_1383372 : Nat := 118140960795 + 1383372 * 2 ^ 59
def prefixEnd_1383372 : Nat := 4983230072969 + 3 ^ 40 * 1383372 * 2
def baseEnd_1383372 : Nat := 315704337765185237505775

theorem tailTrace_1383372 : CollatzResearch.WordTrace tailWord_1383372 prefixEnd_1383372 315704337765185237505775 := by
  unfold tailWord_1383372
  simp only [CollatzResearch.WordTrace]
  refine ⟨25227860972143489986500185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33637147962857986648666913 25227860972143489986500185)
  ·
    refine ⟨18920895729107617489875139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25227860972143489986500185 18920895729107617489875139)
    ·
      refine ⟨28381343593661426234812709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18920895729107617489875139 28381343593661426234812709)
      ·
        refine ⟨5321501923811517419027383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28381343593661426234812709 5321501923811517419027383)
        ·
          refine ⟨7982252885717276128541075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5321501923811517419027383 7982252885717276128541075)
          ·
            refine ⟨11973379328575914192811613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7982252885717276128541075 11973379328575914192811613)
            ·
              refine ⟨4490017248215967822304355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11973379328575914192811613 4490017248215967822304355)
              ·
                refine ⟨6735025872323951733456533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4490017248215967822304355 6735025872323951733456533)
                ·
                  refine ⟨315704337765185237505775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6735025872323951733456533 315704337765185237505775)
                  ·
                    rfl

theorem cell21_1383372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_1383372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1383372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1383372 prefixEnd_1383372 := by exact prefixLift 1383372
  have htrace : WordTrace (prefixWord ++ tailWord_1383372) baseStart_1383372 baseEnd_1383372 := by
    simpa [prefixWord, tailWord_1383372, baseEnd_1383372] using wordTrace_append hprefix tailTrace_1383372
  have hstable : (prefixWord ++ tailWord_1383372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383372).length < 2 ^ (prefixWord ++ tailWord_1383372).sum := by decide
  have hdescent : baseEnd_1383372 < baseStart_1383372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383426 : List Nat := [3, 4, 1, 3, 1, 1, 3, 2, 3]
def baseStart_1383426 : Nat := 118140960795 + 1383426 * 2 ^ 59
def prefixEnd_1383426 : Nat := 4983230072969 + 3 ^ 40 * 1383426 * 2
def baseEnd_1383426 : Nat := 315716661300893143605665

theorem tailTrace_1383426 : CollatzResearch.WordTrace tailWord_1383426 prefixEnd_1383426 315716661300893143605665 := by
  unfold tailWord_1383426
  simp only [CollatzResearch.WordTrace]
  refine ⟨12614422871522836798866533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33638460990727564796977421 12614422871522836798866533)
  ·
    refine ⟨2365204288410531899787475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12614422871522836798866533 2365204288410531899787475)
    ·
      refine ⟨3547806432615797849681213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2365204288410531899787475 3547806432615797849681213)
      ·
        refine ⟨1330427412230924193630455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3547806432615797849681213 1330427412230924193630455)
        ·
          refine ⟨1995641118346386290445683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1330427412230924193630455 1995641118346386290445683)
          ·
            refine ⟨2993461677519579435668525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1995641118346386290445683 2993461677519579435668525)
            ·
              refine ⟨1122548129069842288375697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2993461677519579435668525 1122548129069842288375697)
              ·
                refine ⟨841911096802381716281773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1122548129069842288375697 841911096802381716281773)
                ·
                  refine ⟨315716661300893143605665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 841911096802381716281773 315716661300893143605665)
                  ·
                    rfl

theorem cell21_1383426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_1383426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1383426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1383426 prefixEnd_1383426 := by exact prefixLift 1383426
  have htrace : WordTrace (prefixWord ++ tailWord_1383426) baseStart_1383426 baseEnd_1383426 := by
    simpa [prefixWord, tailWord_1383426, baseEnd_1383426] using wordTrace_append hprefix tailTrace_1383426
  have hstable : (prefixWord ++ tailWord_1383426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383426).length < 2 ^ (prefixWord ++ tailWord_1383426).sum := by decide
  have hdescent : baseEnd_1383426 < baseStart_1383426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383434 : List Nat := [3, 1, 2, 2, 3, 1, 3, 1, 5]
def baseStart_1383434 : Nat := 118140960795 + 1383434 * 2 ^ 59
def prefixEnd_1383434 : Nat := 4983230072969 + 3 ^ 40 * 1383434 * 2
def baseEnd_1383434 : Nat := 315718487009886907472315

theorem tailTrace_1383434 : CollatzResearch.WordTrace tailWord_1383434 prefixEnd_1383434 315718487009886907472315 := by
  unfold tailWord_1383434
  simp only [CollatzResearch.WordTrace]
  refine ⟨12614495817515591140439339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33638655513374909707838237 12614495817515591140439339)
  ·
    refine ⟨18921743726273386710659009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12614495817515591140439339 18921743726273386710659009)
    ·
      refine ⟨14191307794705040032994257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18921743726273386710659009 14191307794705040032994257)
      ·
        refine ⟨10643480846028780024745693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14191307794705040032994257 10643480846028780024745693)
        ·
          refine ⟨3991305317260792509279635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10643480846028780024745693 3991305317260792509279635)
          ·
            refine ⟨5986957975891188763919453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3991305317260792509279635 5986957975891188763919453)
            ·
              refine ⟨2245109240959195786469795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5986957975891188763919453 2245109240959195786469795)
              ·
                refine ⟨3367663861438793679704693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2245109240959195786469795 3367663861438793679704693)
                ·
                  refine ⟨315718487009886907472315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3367663861438793679704693 315718487009886907472315)
                  ·
                    rfl

theorem cell21_1383434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 5].length) (baseStart_1383434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1383434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1383434 prefixEnd_1383434 := by exact prefixLift 1383434
  have htrace : WordTrace (prefixWord ++ tailWord_1383434) baseStart_1383434 baseEnd_1383434 := by
    simpa [prefixWord, tailWord_1383434, baseEnd_1383434] using wordTrace_append hprefix tailTrace_1383434
  have hstable : (prefixWord ++ tailWord_1383434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383434).length < 2 ^ (prefixWord ++ tailWord_1383434).sum := by decide
  have hdescent : baseEnd_1383434 < baseStart_1383434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383527 : List Nat := [1, 1, 5, 1, 1, 4, 2, 3, 3]
def baseStart_1383527 : Nat := 118140960795 + 1383527 * 2 ^ 59
def prefixEnd_1383527 : Nat := 4983230072969 + 3 ^ 40 * 1383527 * 2
def baseEnd_1383527 : Nat := 315739710876939412422125

theorem tailTrace_1383527 : CollatzResearch.WordTrace tailWord_1383527 prefixEnd_1383527 315739710876939412422125 := by
  unfold tailWord_1383527
  simp only [CollatzResearch.WordTrace]
  refine ⟨50461375258725441444892835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33640916839150294296595223 50461375258725441444892835)
  ·
    refine ⟨75692062888088162167339253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50461375258725441444892835 75692062888088162167339253)
    ·
      refine ⟨7096130895758265203188055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75692062888088162167339253 7096130895758265203188055)
      ·
        refine ⟨10644196343637397804782083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7096130895758265203188055 10644196343637397804782083)
        ·
          refine ⟨15966294515456096707173125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10644196343637397804782083 15966294515456096707173125)
          ·
            refine ⟨2993680221648018132594961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15966294515456096707173125 2993680221648018132594961)
            ·
              refine ⟨2245260166236013599446221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2993680221648018132594961 2245260166236013599446221)
              ·
                refine ⟨841972562338505099792333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2245260166236013599446221 841972562338505099792333)
                ·
                  refine ⟨315739710876939412422125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 841972562338505099792333 315739710876939412422125)
                  ·
                    rfl

theorem cell21_1383527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 3, 3].length) (baseStart_1383527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1383527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1383527 prefixEnd_1383527 := by exact prefixLift 1383527
  have htrace : WordTrace (prefixWord ++ tailWord_1383527) baseStart_1383527 baseEnd_1383527 := by
    simpa [prefixWord, tailWord_1383527, baseEnd_1383527] using wordTrace_append hprefix tailTrace_1383527
  have hstable : (prefixWord ++ tailWord_1383527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383527).length < 2 ^ (prefixWord ++ tailWord_1383527).sum := by decide
  have hdescent : baseEnd_1383527 < baseStart_1383527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383538 : List Nat := [3, 2, 1, 2, 2, 1, 10]
def baseStart_1383538 : Nat := 118140960795 + 1383538 * 2 ^ 59
def prefixEnd_1383538 : Nat := 4983230072969 + 3 ^ 40 * 1383538 * 2
def baseEnd_1383538 : Nat := 35082469025200648637641

theorem tailTrace_1383538 : CollatzResearch.WordTrace tailWord_1383538 prefixEnd_1383538 35082469025200648637641 := by
  unfold tailWord_1383538
  simp only [CollatzResearch.WordTrace]
  refine ⟨12615444115421397580885817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33641184307790393549028845 12615444115421397580885817)
  ·
    refine ⟨9461583086566048185664363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12615444115421397580885817 9461583086566048185664363)
    ·
      refine ⟨14192374629849072278496545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9461583086566048185664363 14192374629849072278496545)
      ·
        refine ⟨10644280972386804208872409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14192374629849072278496545 10644280972386804208872409)
        ·
          refine ⟨7983210729290103156654307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10644280972386804208872409 7983210729290103156654307)
          ·
            refine ⟨11974816093935154734981461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7983210729290103156654307 11974816093935154734981461)
            ·
              refine ⟨35082469025200648637641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11974816093935154734981461 35082469025200648637641)
              ·
                rfl

theorem cell21_1383538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 10].length) (baseStart_1383538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1383538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1383538 prefixEnd_1383538 := by exact prefixLift 1383538
  have htrace : WordTrace (prefixWord ++ tailWord_1383538) baseStart_1383538 baseEnd_1383538 := by
    simpa [prefixWord, tailWord_1383538, baseEnd_1383538] using wordTrace_append hprefix tailTrace_1383538
  have hstable : (prefixWord ++ tailWord_1383538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383538).length < 2 ^ (prefixWord ++ tailWord_1383538).sum := by decide
  have hdescent : baseEnd_1383538 < baseStart_1383538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383710 : List Nat := [4, 3, 2, 1, 2, 1, 1, 1, 6]
def baseStart_1383710 : Nat := 118140960795 + 1383710 * 2 ^ 59
def prefixEnd_1383710 : Nat := 4983230072969 + 3 ^ 40 * 1383710 * 2
def baseEnd_1383710 : Nat := 315781473970171760871751

theorem tailTrace_1383710 : CollatzResearch.WordTrace tailWord_1383710 prefixEnd_1383710 315781473970171760871751 := by
  unfold tailWord_1383710
  simp only [CollatzResearch.WordTrace]
  refine ⟨6308506227132807962350573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33645366544708309132536389 6308506227132807962350573)
  ·
    refine ⟨2365689835174802985881465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6308506227132807962350573 2365689835174802985881465)
    ·
      refine ⟨1774267376381102239411099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2365689835174802985881465 1774267376381102239411099)
      ·
        refine ⟨2661401064571653359116649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1774267376381102239411099 2661401064571653359116649)
        ·
          refine ⟨1996050798428740019337487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2661401064571653359116649 1996050798428740019337487)
          ·
            refine ⟨2994076197643110029006231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1996050798428740019337487 2994076197643110029006231)
            ·
              refine ⟨4491114296464665043509347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2994076197643110029006231 4491114296464665043509347)
              ·
                refine ⟨6736671444696997565264021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4491114296464665043509347 6736671444696997565264021)
                ·
                  refine ⟨315781473970171760871751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6736671444696997565264021 315781473970171760871751)
                  ·
                    rfl

theorem cell21_1383710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_1383710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1383710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1383710 prefixEnd_1383710 := by exact prefixLift 1383710
  have htrace : WordTrace (prefixWord ++ tailWord_1383710) baseStart_1383710 baseEnd_1383710 := by
    simpa [prefixWord, tailWord_1383710, baseEnd_1383710] using wordTrace_append hprefix tailTrace_1383710
  have hstable : (prefixWord ++ tailWord_1383710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383710).length < 2 ^ (prefixWord ++ tailWord_1383710).sum := by decide
  have hdescent : baseEnd_1383710 < baseStart_1383710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383741 : List Nat := [1, 4, 1, 5, 1, 2, 2, 5]
def baseStart_1383741 : Nat := 118140960795 + 1383741 * 2 ^ 59
def prefixEnd_1383741 : Nat := 4983230072969 + 3 ^ 40 * 1383741 * 2
def baseEnd_1383741 : Nat := 105262849530840865285007

theorem tailTrace_1383741 : CollatzResearch.WordTrace tailWord_1383741 prefixEnd_1383741 105262849530840865285007 := by
  unfold tailWord_1383741
  simp only [CollatzResearch.WordTrace]
  refine ⟨50469180479950155993183077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33646120319966770662122051 50469180479950155993183077)
  ·
    refine ⟨9462971339990654248721827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50469180479950155993183077 9462971339990654248721827)
    ·
      refine ⟨14194457009985981373082741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9462971339990654248721827 14194457009985981373082741)
      ·
        refine ⟨1330730344686185753726507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14194457009985981373082741 1330730344686185753726507)
        ·
          refine ⟨1996095517029278630589761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1330730344686185753726507 1996095517029278630589761)
          ·
            refine ⟨1497071637771958972942321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1996095517029278630589761 1497071637771958972942321)
            ·
              refine ⟨1122803728328969229706741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1497071637771958972942321 1122803728328969229706741)
              ·
                refine ⟨105262849530840865285007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1122803728328969229706741 105262849530840865285007)
                ·
                  rfl

theorem cell21_1383741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 5].length) (baseStart_1383741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1383741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1383741 prefixEnd_1383741 := by exact prefixLift 1383741
  have htrace : WordTrace (prefixWord ++ tailWord_1383741) baseStart_1383741 baseEnd_1383741 := by
    simpa [prefixWord, tailWord_1383741, baseEnd_1383741] using wordTrace_append hprefix tailTrace_1383741
  have hstable : (prefixWord ++ tailWord_1383741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383741).length < 2 ^ (prefixWord ++ tailWord_1383741).sum := by decide
  have hdescent : baseEnd_1383741 < baseStart_1383741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383783 : List Nat := [1, 1, 5, 1, 4, 1, 2, 6]
def baseStart_1383783 : Nat := 118140960795 + 1383783 * 2 ^ 59
def prefixEnd_1383783 : Nat := 4983230072969 + 3 ^ 40 * 1383783 * 2
def baseEnd_1383783 : Nat := 105266044521579952051645

theorem tailTrace_1383783 : CollatzResearch.WordTrace tailWord_1383783 prefixEnd_1383783 105266044521579952051645 := by
  unfold tailWord_1383783
  simp only [CollatzResearch.WordTrace]
  refine ⟨50470712345797997166212003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33647141563865331444141335 50470712345797997166212003)
  ·
    refine ⟨75706068518696995749318005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50470712345797997166212003 75706068518696995749318005)
    ·
      refine ⟨7097443923627843351498563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75706068518696995749318005 7097443923627843351498563)
      ·
        refine ⟨10646165885441765027247845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7097443923627843351498563 10646165885441765027247845)
        ·
          refine ⟨1996156103520330942608971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10646165885441765027247845 1996156103520330942608971)
          ·
            refine ⟨2994234155280496413913457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1996156103520330942608971 2994234155280496413913457)
            ·
              refine ⟨2245675616460372310435093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2994234155280496413913457 2245675616460372310435093)
              ·
                refine ⟨105266044521579952051645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2245675616460372310435093 105266044521579952051645)
                ·
                  rfl

theorem cell21_1383783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 6].length) (baseStart_1383783 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1383783 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1383783 prefixEnd_1383783 := by exact prefixLift 1383783
  have htrace : WordTrace (prefixWord ++ tailWord_1383783) baseStart_1383783 baseEnd_1383783 := by
    simpa [prefixWord, tailWord_1383783, baseEnd_1383783] using wordTrace_append hprefix tailTrace_1383783
  have hstable : (prefixWord ++ tailWord_1383783).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383783).length < 2 ^ (prefixWord ++ tailWord_1383783).sum := by decide
  have hdescent : baseEnd_1383783 < baseStart_1383783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383918 : List Nat := [4, 1, 2, 1, 2, 1, 3, 7]
def baseStart_1383918 : Nat := 118140960795 + 1383918 * 2 ^ 59
def prefixEnd_1383918 : Nat := 4983230072969 + 3 ^ 40 * 1383918 * 2
def baseEnd_1383918 : Nat := 105276314134669873801553

theorem tailTrace_1383918 : CollatzResearch.WordTrace tailWord_1383918 prefixEnd_1383918 105276314134669873801553 := by
  unfold tailWord_1383918
  simp only [CollatzResearch.WordTrace]
  refine ⟨6309454525038614402797051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33650424133539276814917605 6309454525038614402797051)
  ·
    refine ⟨9464181787557921604195577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6309454525038614402797051 9464181787557921604195577)
    ·
      refine ⟨7098136340668441203146683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9464181787557921604195577 7098136340668441203146683)
      ·
        refine ⟨10647204511002661804720025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7098136340668441203146683 10647204511002661804720025)
        ·
          refine ⟨7985403383251996353540019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10647204511002661804720025 7985403383251996353540019)
          ·
            refine ⟨11978105074877994530310029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7985403383251996353540019 11978105074877994530310029)
            ·
              refine ⟨4491789403079247948866261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11978105074877994530310029 4491789403079247948866261)
              ·
                refine ⟨105276314134669873801553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4491789403079247948866261 105276314134669873801553)
                ·
                  rfl

theorem cell21_1383918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_1383918 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1383918 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1383918 prefixEnd_1383918 := by exact prefixLift 1383918
  have htrace : WordTrace (prefixWord ++ tailWord_1383918) baseStart_1383918 baseEnd_1383918 := by
    simpa [prefixWord, tailWord_1383918, baseEnd_1383918] using wordTrace_append hprefix tailTrace_1383918
  have hstable : (prefixWord ++ tailWord_1383918).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383918).length < 2 ^ (prefixWord ++ tailWord_1383918).sum := by decide
  have hdescent : baseEnd_1383918 < baseStart_1383918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383932 : List Nat := [2, 2, 2, 1, 2, 1, 2, 2, 7]
def baseStart_1383932 : Nat := 118140960795 + 1383932 * 2 ^ 59
def prefixEnd_1383932 : Nat := 4983230072969 + 3 ^ 40 * 1383932 * 2
def baseEnd_1383932 : Nat := 315832137394748708171297

theorem tailTrace_1383932 : CollatzResearch.WordTrace tailWord_1383932 prefixEnd_1383932 315832137394748708171297 := by
  unfold tailWord_1383932
  simp only [CollatzResearch.WordTrace]
  refine ⟨25238073411129097806693025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33650764548172130408924033 25238073411129097806693025)
  ·
    refine ⟨18928555058346823355019769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25238073411129097806693025 18928555058346823355019769)
    ·
      refine ⟨14196416293760117516264827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18928555058346823355019769 14196416293760117516264827)
      ·
        refine ⟨21294624440640176274397241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14196416293760117516264827 21294624440640176274397241)
        ·
          refine ⟨15970968330480132205797931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21294624440640176274397241 15970968330480132205797931)
          ·
            refine ⟨23956452495720198308696897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15970968330480132205797931 23956452495720198308696897)
            ·
              refine ⟨17967339371790148731522673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23956452495720198308696897 17967339371790148731522673)
              ·
                refine ⟨13475504528842611548642005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17967339371790148731522673 13475504528842611548642005)
                ·
                  refine ⟨315832137394748708171297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13475504528842611548642005 315832137394748708171297)
                  ·
                    rfl

theorem cell21_1383932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_1383932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1383932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1383932 prefixEnd_1383932 := by exact prefixLift 1383932
  have htrace : WordTrace (prefixWord ++ tailWord_1383932) baseStart_1383932 baseEnd_1383932 := by
    simpa [prefixWord, tailWord_1383932, baseEnd_1383932] using wordTrace_append hprefix tailTrace_1383932
  have hstable : (prefixWord ++ tailWord_1383932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383932).length < 2 ^ (prefixWord ++ tailWord_1383932).sum := by decide
  have hdescent : baseEnd_1383932 < baseStart_1383932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383997 : List Nat := [1, 4, 1, 3, 3, 1, 2, 2, 4]
def baseStart_1383997 : Nat := 118140960795 + 1383997 * 2 ^ 59
def prefixEnd_1383997 : Nat := 4983230072969 + 3 ^ 40 * 1383997 * 2
def baseEnd_1383997 : Nat := 315846971280323039587831

theorem tailTrace_1383997 : CollatzResearch.WordTrace tailWord_1383997 prefixEnd_1383997 315846971280323039587831 := by
  unfold tailWord_1383997
  simp only [CollatzResearch.WordTrace]
  refine ⟨50478517567022711714502245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33652345044681807809668163 50478517567022711714502245)
  ·
    refine ⟨9464722043816758446469171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50478517567022711714502245 9464722043816758446469171)
    ·
      refine ⟨14197083065725137669703757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9464722043816758446469171 14197083065725137669703757)
      ·
        refine ⟨5323906149646926626138909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14197083065725137669703757 5323906149646926626138909)
        ·
          refine ⟨1996464806117597484802091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5323906149646926626138909 1996464806117597484802091)
          ·
            refine ⟨2994697209176396227203137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1996464806117597484802091 2994697209176396227203137)
            ·
              refine ⟨2246022906882297170402353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2994697209176396227203137 2246022906882297170402353)
              ·
                refine ⟨1684517180161722877801765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2246022906882297170402353 1684517180161722877801765)
                ·
                  refine ⟨315846971280323039587831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1684517180161722877801765 315846971280323039587831)
                  ·
                    rfl

theorem cell21_1383997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_1383997 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1383997 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1383997 prefixEnd_1383997 := by exact prefixLift 1383997
  have htrace : WordTrace (prefixWord ++ tailWord_1383997) baseStart_1383997 baseEnd_1383997 := by
    simpa [prefixWord, tailWord_1383997, baseEnd_1383997] using wordTrace_append hprefix tailTrace_1383997
  have hstable : (prefixWord ++ tailWord_1383997).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383997).length < 2 ^ (prefixWord ++ tailWord_1383997).sum := by decide
  have hdescent : baseEnd_1383997 < baseStart_1383997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384042 : List Nat := [3, 1, 3, 2, 1, 2, 1, 5, 3]
def baseStart_1384042 : Nat := 118140960795 + 1384042 * 2 ^ 59
def prefixEnd_1384042 : Nat := 4983230072969 + 3 ^ 40 * 1384042 * 2
def baseEnd_1384042 : Nat := 315857240893412961337739

theorem tailTrace_1384042 : CollatzResearch.WordTrace tailWord_1384042 prefixEnd_1384042 315857240893412961337739 := by
  unfold tailWord_1384042
  simp only [CollatzResearch.WordTrace]
  refine ⟨12620039712964921099972595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33653439234573122933260253 12620039712964921099972595)
  ·
    refine ⟨18930059569447381649958893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12620039712964921099972595 18930059569447381649958893)
    ·
      refine ⟨7098772338542768118734585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18930059569447381649958893 7098772338542768118734585)
      ·
        refine ⟨5324079253907076089050939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7098772338542768118734585 5324079253907076089050939)
        ·
          refine ⟨7986118880860614133576409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5324079253907076089050939 7986118880860614133576409)
          ·
            refine ⟨5989589160645460600182307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7986118880860614133576409 5989589160645460600182307)
            ·
              refine ⟨8984383740968190900273461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5989589160645460600182307 8984383740968190900273461)
              ·
                refine ⟨842285975715767896900637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8984383740968190900273461 842285975715767896900637)
                ·
                  refine ⟨315857240893412961337739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 842285975715767896900637 315857240893412961337739)
                  ·
                    rfl

theorem cell21_1384042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 5, 3].length) (baseStart_1384042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1384042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1384042 prefixEnd_1384042 := by exact prefixLift 1384042
  have htrace : WordTrace (prefixWord ++ tailWord_1384042) baseStart_1384042 baseEnd_1384042 := by
    simpa [prefixWord, tailWord_1384042, baseEnd_1384042] using wordTrace_append hprefix tailTrace_1384042
  have hstable : (prefixWord ++ tailWord_1384042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384042).length < 2 ^ (prefixWord ++ tailWord_1384042).sum := by decide
  have hdescent : baseEnd_1384042 < baseStart_1384042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384087 : List Nat := [1, 1, 3, 3, 2, 4, 2, 5]
def baseStart_1384087 : Nat := 118140960795 + 1384087 * 2 ^ 59
def prefixEnd_1384087 : Nat := 4983230072969 + 3 ^ 40 * 1384087 * 2
def baseEnd_1384087 : Nat := 105289170168834294362549

theorem tailTrace_1384087 : CollatzResearch.WordTrace tailWord_1384087 prefixEnd_1384087 105289170168834294362549 := by
  unfold tailWord_1384087
  simp only [CollatzResearch.WordTrace]
  refine ⟨50481800136696657085278515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33654533424464438056852343 50481800136696657085278515)
  ·
    refine ⟨75722700205044985627917773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50481800136696657085278515 75722700205044985627917773)
    ·
      refine ⟨28396012576891869610469165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75722700205044985627917773 28396012576891869610469165)
      ·
        refine ⟨10648504716334451103925937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28396012576891869610469165 10648504716334451103925937)
        ·
          refine ⟨7986378537250838327944453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10648504716334451103925937 7986378537250838327944453)
          ·
            refine ⟨1497445975734532186489585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7986378537250838327944453 1497445975734532186489585)
            ·
              refine ⟨1123084481800899139867189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1497445975734532186489585 1123084481800899139867189)
              ·
                refine ⟨105289170168834294362549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1123084481800899139867189 105289170168834294362549)
                ·
                  rfl

theorem cell21_1384087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 5].length) (baseStart_1384087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1384087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1384087 prefixEnd_1384087 := by exact prefixLift 1384087
  have htrace : WordTrace (prefixWord ++ tailWord_1384087) baseStart_1384087 baseEnd_1384087 := by
    simpa [prefixWord, tailWord_1384087, baseEnd_1384087] using wordTrace_append hprefix tailTrace_1384087
  have hstable : (prefixWord ++ tailWord_1384087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384087).length < 2 ^ (prefixWord ++ tailWord_1384087).sum := by decide
  have hdescent : baseEnd_1384087 < baseStart_1384087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384115 : List Nat := [1, 1, 1, 2, 3, 3, 2, 4, 4]
def baseStart_1384115 : Nat := 118140960795 + 1384115 * 2 ^ 59
def prefixEnd_1384115 : Nat := 4983230072969 + 3 ^ 40 * 1384115 * 2
def baseEnd_1384115 : Nat := 315873900487981056620923

theorem tailTrace_1384115 : CollatzResearch.WordTrace tailWord_1384115 prefixEnd_1384115 315873900487981056620923 := by
  unfold tailWord_1384115
  simp only [CollatzResearch.WordTrace]
  refine ⟨50482821380595217867297799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33655214253730145244865199 50482821380595217867297799)
  ·
    refine ⟨75724232070892826800946699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50482821380595217867297799 75724232070892826800946699)
    ·
      refine ⟨113586348106339240201420049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75724232070892826800946699 113586348106339240201420049)
      ·
        refine ⟨85189761079754430151065037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113586348106339240201420049 85189761079754430151065037)
        ·
          refine ⟨31946160404907911306649389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85189761079754430151065037 31946160404907911306649389)
          ·
            refine ⟨11979810151840466739993521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31946160404907911306649389 11979810151840466739993521)
            ·
              refine ⟨8984857613880350054995141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11979810151840466739993521 8984857613880350054995141)
              ·
                refine ⟨1684660802602565635311589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8984857613880350054995141 1684660802602565635311589)
                ·
                  refine ⟨315873900487981056620923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1684660802602565635311589 315873900487981056620923)
                  ·
                    rfl

theorem cell21_1384115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 4, 4].length) (baseStart_1384115 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1384115 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1384115 prefixEnd_1384115 := by exact prefixLift 1384115
  have htrace : WordTrace (prefixWord ++ tailWord_1384115) baseStart_1384115 baseEnd_1384115 := by
    simpa [prefixWord, tailWord_1384115, baseEnd_1384115] using wordTrace_append hprefix tailTrace_1384115
  have hstable : (prefixWord ++ tailWord_1384115).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384115).length < 2 ^ (prefixWord ++ tailWord_1384115).sum := by decide
  have hdescent : baseEnd_1384115 < baseStart_1384115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384132 : List Nat := [2, 3, 3, 1, 1, 1, 3, 3, 4]
def baseStart_1384132 : Nat := 118140960795 + 1384132 * 2 ^ 59
def prefixEnd_1384132 : Nat := 4983230072969 + 3 ^ 40 * 1384132 * 2
def baseEnd_1384132 : Nat := 315877780119592804837555

theorem tailTrace_1384132 : CollatzResearch.WordTrace tailWord_1384132 prefixEnd_1384132 315877780119592804837555 := by
  unfold tailWord_1384132
  simp only [CollatzResearch.WordTrace]
  refine ⟨25241720710766814885333325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33655627614355753180444433 25241720710766814885333325)
  ·
    refine ⟨9465645266537555581999997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25241720710766814885333325 9465645266537555581999997)
    ·
      refine ⟨3549616974951583343249999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9465645266537555581999997 3549616974951583343249999)
      ·
        refine ⟨5324425462427375014874999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3549616974951583343249999 5324425462427375014874999)
        ·
          refine ⟨7986638193641062522312499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5324425462427375014874999 7986638193641062522312499)
          ·
            refine ⟨11979957290461593783468749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7986638193641062522312499 11979957290461593783468749)
            ·
              refine ⟨4492483983923097668800781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11979957290461593783468749 4492483983923097668800781)
              ·
                refine ⟨1684681493971161625800293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4492483983923097668800781 1684681493971161625800293)
                ·
                  refine ⟨315877780119592804837555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1684681493971161625800293 315877780119592804837555)
                  ·
                    rfl

theorem cell21_1384132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_1384132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1384132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1384132 prefixEnd_1384132 := by exact prefixLift 1384132
  have htrace : WordTrace (prefixWord ++ tailWord_1384132) baseStart_1384132 baseEnd_1384132 := by
    simpa [prefixWord, tailWord_1384132, baseEnd_1384132] using wordTrace_append hprefix tailTrace_1384132
  have hstable : (prefixWord ++ tailWord_1384132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384132).length < 2 ^ (prefixWord ++ tailWord_1384132).sum := by decide
  have hdescent : baseEnd_1384132 < baseStart_1384132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384146 : List Nat := [3, 2, 2, 2, 2, 1, 2, 7]
def baseStart_1384146 : Nat := 118140960795 + 1384146 * 2 ^ 59
def prefixEnd_1384146 : Nat := 4983230072969 + 3 ^ 40 * 1384146 * 2
def baseEnd_1384146 : Nat := 105293658370110630534731

theorem tailTrace_1384146 : CollatzResearch.WordTrace tailWord_1384146 prefixEnd_1384146 105293658370110630534731 := by
  unfold tailWord_1384146
  simp only [CollatzResearch.WordTrace]
  refine ⟨12620988010870727540419073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33655968028988606774450861 12620988010870727540419073)
  ·
    refine ⟨9465741008153045655314305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12620988010870727540419073 9465741008153045655314305)
    ·
      refine ⟨7099305756114784241485729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9465741008153045655314305 7099305756114784241485729)
      ·
        refine ⟨5324479317086088181114297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7099305756114784241485729 5324479317086088181114297)
        ·
          refine ⟨3993359487814566135835723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5324479317086088181114297 3993359487814566135835723)
          ·
            refine ⟨5990039231721849203753585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3993359487814566135835723 5990039231721849203753585)
            ·
              refine ⟨4492529423791386902815189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5990039231721849203753585 4492529423791386902815189)
              ·
                refine ⟨105293658370110630534731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4492529423791386902815189 105293658370110630534731)
                ·
                  rfl

theorem cell21_1384146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 7].length) (baseStart_1384146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1384146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1384146 prefixEnd_1384146 := by exact prefixLift 1384146
  have htrace : WordTrace (prefixWord ++ tailWord_1384146) baseStart_1384146 baseEnd_1384146 := by
    simpa [prefixWord, tailWord_1384146, baseEnd_1384146] using wordTrace_append hprefix tailTrace_1384146
  have hstable : (prefixWord ++ tailWord_1384146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384146).length < 2 ^ (prefixWord ++ tailWord_1384146).sum := by decide
  have hdescent : baseEnd_1384146 < baseStart_1384146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384180 : List Nat := [2, 6, 1, 1, 1, 1, 3, 6]
def baseStart_1384180 : Nat := 118140960795 + 1384180 * 2 ^ 59
def prefixEnd_1384180 : Nat := 4983230072969 + 3 ^ 40 * 1384180 * 2
def baseEnd_1384180 : Nat := 105296244791185129345819

theorem tailTrace_1384180 : CollatzResearch.WordTrace tailWord_1384180 prefixEnd_1384180 105296244791185129345819 := by
  unfold tailWord_1384180
  simp only [CollatzResearch.WordTrace]
  refine ⟨25242596062679866984206997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33656794750239822645609329 25242596062679866984206997)
  ·
    refine ⟨1183246690438118764884703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25242596062679866984206997 1183246690438118764884703)
    ·
      refine ⟨1774870035657178147327055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1183246690438118764884703 1774870035657178147327055)
      ·
        refine ⟨2662305053485767220990583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1774870035657178147327055 2662305053485767220990583)
        ·
          refine ⟨3993457580228650831485875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2662305053485767220990583 3993457580228650831485875)
          ·
            refine ⟨5990186370342976247228813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3993457580228650831485875 5990186370342976247228813)
            ·
              refine ⟨2246319888878616092710805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5990186370342976247228813 2246319888878616092710805)
              ·
                refine ⟨105296244791185129345819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2246319888878616092710805 105296244791185129345819)
                ·
                  rfl

theorem cell21_1384180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 6].length) (baseStart_1384180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1384180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1384180 prefixEnd_1384180 := by exact prefixLift 1384180
  have htrace : WordTrace (prefixWord ++ tailWord_1384180) baseStart_1384180 baseEnd_1384180 := by
    simpa [prefixWord, tailWord_1384180, baseEnd_1384180] using wordTrace_append hprefix tailTrace_1384180
  have hstable : (prefixWord ++ tailWord_1384180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384180).length < 2 ^ (prefixWord ++ tailWord_1384180).sum := by decide
  have hdescent : baseEnd_1384180 < baseStart_1384180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384191 : List Nat := [1, 1, 2, 2, 1, 3, 4, 3, 4]
def baseStart_1384191 : Nat := 118140960795 + 1384191 * 2 ^ 59
def prefixEnd_1384191 : Nat := 4983230072969 + 3 ^ 40 * 1384191 * 2
def baseEnd_1384191 : Nat := 315891244723421813354101

theorem tailTrace_1384191 : CollatzResearch.WordTrace tailWord_1384191 prefixEnd_1384191 315891244723421813354101 := by
  unfold tailWord_1384191
  simp only [CollatzResearch.WordTrace]
  refine ⟨50485593328319882847064427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33657062218879921898042951 50485593328319882847064427)
  ·
    refine ⟨75728389992479824270596641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50485593328319882847064427 75728389992479824270596641)
    ·
      refine ⟨56796292494359868202947481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75728389992479824270596641 56796292494359868202947481)
      ·
        refine ⟨42597219370769901152210611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56796292494359868202947481 42597219370769901152210611)
        ·
          refine ⟨63895829056154851728315917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42597219370769901152210611 63895829056154851728315917)
          ·
            refine ⟨23960935896058069398118469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63895829056154851728315917 23960935896058069398118469)
            ·
              refine ⟨4492675480510888012147213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23960935896058069398118469 4492675480510888012147213)
              ·
                refine ⟨1684753305191583004555205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4492675480510888012147213 1684753305191583004555205)
                ·
                  refine ⟨315891244723421813354101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1684753305191583004555205 315891244723421813354101)
                  ·
                    rfl

theorem cell21_1384191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 3, 4].length) (baseStart_1384191 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1384191 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1384191 prefixEnd_1384191 := by exact prefixLift 1384191
  have htrace : WordTrace (prefixWord ++ tailWord_1384191) baseStart_1384191 baseEnd_1384191 := by
    simpa [prefixWord, tailWord_1384191, baseEnd_1384191] using wordTrace_append hprefix tailTrace_1384191
  have hstable : (prefixWord ++ tailWord_1384191).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384191).length < 2 ^ (prefixWord ++ tailWord_1384191).sum := by decide
  have hdescent : baseEnd_1384191 < baseStart_1384191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384236 : List Nat := [2, 2, 1, 1, 1, 5, 1, 3, 5]
def baseStart_1384236 : Nat := 118140960795 + 1384236 * 2 ^ 59
def prefixEnd_1384236 : Nat := 4983230072969 + 3 ^ 40 * 1384236 * 2
def baseEnd_1384236 : Nat := 315901514336511735104009

theorem tailTrace_1384236 : CollatzResearch.WordTrace tailWord_1384236 prefixEnd_1384236 315901514336511735104009 := by
  unfold tailWord_1384236
  simp only [CollatzResearch.WordTrace]
  refine ⟨25243617306578427766226281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33658156408771237021635041 25243617306578427766226281)
  ·
    refine ⟨18932712979933820824669711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25243617306578427766226281 18932712979933820824669711)
    ·
      refine ⟨28399069469900731237004567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18932712979933820824669711 28399069469900731237004567)
      ·
        refine ⟨42598604204851096855506851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28399069469900731237004567 42598604204851096855506851)
        ·
          refine ⟨63897906307276645283260277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42598604204851096855506851 63897906307276645283260277)
          ·
            refine ⟨5990428716307185495305651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63897906307276645283260277 5990428716307185495305651)
            ·
              refine ⟨8985643074460778242958477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5990428716307185495305651 8985643074460778242958477)
              ·
                refine ⟨3369616152922791841109429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8985643074460778242958477 3369616152922791841109429)
                ·
                  refine ⟨315901514336511735104009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3369616152922791841109429 315901514336511735104009)
                  ·
                    rfl

theorem cell21_1384236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_1384236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1384236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1384236 prefixEnd_1384236 := by exact prefixLift 1384236
  have htrace : WordTrace (prefixWord ++ tailWord_1384236) baseStart_1384236 baseEnd_1384236 := by
    simpa [prefixWord, tailWord_1384236, baseEnd_1384236] using wordTrace_append hprefix tailTrace_1384236
  have hstable : (prefixWord ++ tailWord_1384236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384236).length < 2 ^ (prefixWord ++ tailWord_1384236).sum := by decide
  have hdescent : baseEnd_1384236 < baseStart_1384236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384253 : List Nat := [1, 4, 1, 4, 1, 1, 2, 2, 5]
def baseStart_1384253 : Nat := 118140960795 + 1384253 * 2 ^ 59
def prefixEnd_1384253 : Nat := 4983230072969 + 3 ^ 40 * 1384253 * 2
def baseEnd_1384253 : Nat := 315905393968123483320641

theorem tailTrace_1384253 : CollatzResearch.WordTrace tailWord_1384253 prefixEnd_1384253 315905393968123483320641 := by
  unfold tailWord_1384253
  simp only [CollatzResearch.WordTrace]
  refine ⟨50487854654095267435821413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33658569769396844957214275 50487854654095267435821413)
  ·
    refine ⟨9466472747642862644216515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50487854654095267435821413 9466472747642862644216515)
    ·
      refine ⟨14199709121464293966324773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9466472747642862644216515 14199709121464293966324773)
      ·
        refine ⟨2662445460274555118685895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14199709121464293966324773 2662445460274555118685895)
        ·
          refine ⟨3993668190411832678028843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2662445460274555118685895 3993668190411832678028843)
          ·
            refine ⟨5990502285617749017043265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3993668190411832678028843 5990502285617749017043265)
            ·
              refine ⟨4492876714213311762782449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5990502285617749017043265 4492876714213311762782449)
              ·
                refine ⟨3369657535659983822086837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4492876714213311762782449 3369657535659983822086837)
                ·
                  refine ⟨315905393968123483320641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3369657535659983822086837 315905393968123483320641)
                  ·
                    rfl

theorem cell21_1384253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_1384253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1384253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1384253 prefixEnd_1384253 := by exact prefixLift 1384253
  have htrace : WordTrace (prefixWord ++ tailWord_1384253) baseStart_1384253 baseEnd_1384253 := by
    simpa [prefixWord, tailWord_1384253, baseEnd_1384253] using wordTrace_append hprefix tailTrace_1384253
  have hstable : (prefixWord ++ tailWord_1384253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384253).length < 2 ^ (prefixWord ++ tailWord_1384253).sum := by decide
  have hdescent : baseEnd_1384253 < baseStart_1384253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384329 : List Nat := [1, 2, 1, 1, 5, 1, 2, 5, 3]
def baseStart_1384329 : Nat := 118140960795 + 1384329 * 2 ^ 59
def prefixEnd_1384329 : Nat := 4983230072969 + 3 ^ 40 * 1384329 * 2
def baseEnd_1384329 : Nat := 315922738203564240053819

theorem tailTrace_1384329 : CollatzResearch.WordTrace tailWord_1384329 prefixEnd_1384329 315922738203564240053819 := by
  unfold tailWord_1384329
  simp only [CollatzResearch.WordTrace]
  refine ⟨50490626601819932415588041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33660417734546621610392027 50490626601819932415588041)
  ·
    refine ⟨37867969951364949311691031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50490626601819932415588041 37867969951364949311691031)
    ·
      refine ⟨56801954927047423967536547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37867969951364949311691031 56801954927047423967536547)
      ·
        refine ⟨85202932390571135951304821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56801954927047423967536547 85202932390571135951304821)
        ·
          refine ⟨7987774911616043995434827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85202932390571135951304821 7987774911616043995434827)
          ·
            refine ⟨11981662367424065993152241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7987774911616043995434827 11981662367424065993152241)
            ·
              refine ⟨8986246775568049494864181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11981662367424065993152241 8986246775568049494864181)
              ·
                refine ⟨842460635209504640143517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8986246775568049494864181 842460635209504640143517)
                ·
                  refine ⟨315922738203564240053819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 842460635209504640143517 315922738203564240053819)
                  ·
                    rfl

theorem cell21_1384329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 5, 3].length) (baseStart_1384329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1384329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1384329 prefixEnd_1384329 := by exact prefixLift 1384329
  have htrace : WordTrace (prefixWord ++ tailWord_1384329) baseStart_1384329 baseEnd_1384329 := by
    simpa [prefixWord, tailWord_1384329, baseEnd_1384329] using wordTrace_append hprefix tailTrace_1384329
  have hstable : (prefixWord ++ tailWord_1384329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384329).length < 2 ^ (prefixWord ++ tailWord_1384329).sum := by decide
  have hdescent : baseEnd_1384329 < baseStart_1384329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384343 : List Nat := [1, 1, 3, 3, 1, 3, 1, 4, 4]
def baseStart_1384343 : Nat := 118140960795 + 1384343 * 2 ^ 59
def prefixEnd_1384343 : Nat := 4983230072969 + 3 ^ 40 * 1384343 * 2
def baseEnd_1384343 : Nat := 315925933194303326820457

theorem tailTrace_1384343 : CollatzResearch.WordTrace tailWord_1384343 prefixEnd_1384343 315925933194303326820457 := by
  unfold tailWord_1384343
  simp only [CollatzResearch.WordTrace]
  refine ⟨50491137223769212806597683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33660758149179475204398455 50491137223769212806597683)
  ·
    refine ⟨75736705835653819209896525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50491137223769212806597683 75736705835653819209896525)
    ·
      refine ⟨28401264688370182203711197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75736705835653819209896525 28401264688370182203711197)
      ·
        refine ⟨10650474258138818326391699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28401264688370182203711197 10650474258138818326391699)
        ·
          refine ⟨15975711387208227489587549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10650474258138818326391699 15975711387208227489587549)
          ·
            refine ⟨5990891770203085308595331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15975711387208227489587549 5990891770203085308595331)
            ·
              refine ⟨8986337655304627962892997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5990891770203085308595331 8986337655304627962892997)
              ·
                refine ⟨1684938310369617743042437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8986337655304627962892997 1684938310369617743042437)
                ·
                  refine ⟨315925933194303326820457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1684938310369617743042437 315925933194303326820457)
                  ·
                    rfl

theorem cell21_1384343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 4, 4].length) (baseStart_1384343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1384343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1384343 prefixEnd_1384343 := by exact prefixLift 1384343
  have htrace : WordTrace (prefixWord ++ tailWord_1384343) baseStart_1384343 baseEnd_1384343 := by
    simpa [prefixWord, tailWord_1384343, baseEnd_1384343] using wordTrace_append hprefix tailTrace_1384343
  have hstable : (prefixWord ++ tailWord_1384343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384343).length < 2 ^ (prefixWord ++ tailWord_1384343).sum := by decide
  have hdescent : baseEnd_1384343 < baseStart_1384343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384346 : List Nat := [3, 1, 1, 4, 2, 2, 1, 4, 3]
def baseStart_1384346 : Nat := 118140960795 + 1384346 * 2 ^ 59
def prefixEnd_1384346 : Nat := 4983230072969 + 3 ^ 40 * 1384346 * 2
def baseEnd_1384346 : Nat := 315926617835175988270451

theorem tailTrace_1384346 : CollatzResearch.WordTrace tailWord_1384346 prefixEnd_1384346 315926617835175988270451 := by
  unfold tailWord_1384346
  simp only [CollatzResearch.WordTrace]
  refine ⟨12622811660689586079739223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33660831095172229545971261 12622811660689586079739223)
  ·
    refine ⟨18934217491034379119608835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12622811660689586079739223 18934217491034379119608835)
    ·
      refine ⟨28401326236551568679413253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18934217491034379119608835 28401326236551568679413253)
      ·
        refine ⟨5325248669353419127389985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28401326236551568679413253 5325248669353419127389985)
        ·
          refine ⟨3993936502015064345542489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5325248669353419127389985 3993936502015064345542489)
          ·
            refine ⟨2995452376511298259156867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3993936502015064345542489 2995452376511298259156867)
            ·
              refine ⟨4493178564766947388735301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2995452376511298259156867 4493178564766947388735301)
              ·
                refine ⟨842470980893802635387869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4493178564766947388735301 842470980893802635387869)
                ·
                  refine ⟨315926617835175988270451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 842470980893802635387869 315926617835175988270451)
                  ·
                    rfl

theorem cell21_1384346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 4, 3].length) (baseStart_1384346 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1384346 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1384346 prefixEnd_1384346 := by exact prefixLift 1384346
  have htrace : WordTrace (prefixWord ++ tailWord_1384346) baseStart_1384346 baseEnd_1384346 := by
    simpa [prefixWord, tailWord_1384346, baseEnd_1384346] using wordTrace_append hprefix tailTrace_1384346
  have hstable : (prefixWord ++ tailWord_1384346).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384346).length < 2 ^ (prefixWord ++ tailWord_1384346).sum := by decide
  have hdescent : baseEnd_1384346 < baseStart_1384346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384405 : List Nat := [1, 3, 2, 3, 2, 2, 2, 1, 5]
def baseStart_1384405 : Nat := 118140960795 + 1384405 * 2 ^ 59
def prefixEnd_1384405 : Nat := 4983230072969 + 3 ^ 40 * 1384405 * 2
def baseEnd_1384405 : Nat := 315940082439004996786997

theorem tailTrace_1384405 : CollatzResearch.WordTrace tailWord_1384405 prefixEnd_1384405 315940082439004996786997 := by
  unfold tailWord_1384405
  simp only [CollatzResearch.WordTrace]
  refine ⟨50493398549544597395354669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33662265699696398263569779 50493398549544597395354669)
  ·
    refine ⟨18935024456079224023258001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50493398549544597395354669 18935024456079224023258001)
    ·
      refine ⟨14201268342059418017443501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18935024456079224023258001 14201268342059418017443501)
      ·
        refine ⟨5325475628272281756541313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14201268342059418017443501 5325475628272281756541313)
        ·
          refine ⟨3994106721204211317405985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5325475628272281756541313 3994106721204211317405985)
          ·
            refine ⟨2995580040903158488054489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3994106721204211317405985 2995580040903158488054489)
            ·
              refine ⟨2246685030677368866040867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2995580040903158488054489 2246685030677368866040867)
              ·
                refine ⟨3370027546016053299061301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2246685030677368866040867 3370027546016053299061301)
                ·
                  refine ⟨315940082439004996786997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3370027546016053299061301 315940082439004996786997)
                  ·
                    rfl

theorem cell21_1384405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 5].length) (baseStart_1384405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1384405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1384405 prefixEnd_1384405 := by exact prefixLift 1384405
  have htrace : WordTrace (prefixWord ++ tailWord_1384405) baseStart_1384405 baseEnd_1384405 := by
    simpa [prefixWord, tailWord_1384405, baseEnd_1384405] using wordTrace_append hprefix tailTrace_1384405
  have hstable : (prefixWord ++ tailWord_1384405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384405).length < 2 ^ (prefixWord ++ tailWord_1384405).sum := by decide
  have hdescent : baseEnd_1384405 < baseStart_1384405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384447 : List Nat := [1, 1, 2, 2, 1, 2, 1, 4, 7]
def baseStart_1384447 : Nat := 118140960795 + 1384447 * 2 ^ 59
def prefixEnd_1384447 : Nat := 4983230072969 + 3 ^ 40 * 1384447 * 2
def baseEnd_1384447 : Nat := 315949667411222257086911

theorem tailTrace_1384447 : CollatzResearch.WordTrace tailWord_1384447 prefixEnd_1384447 315949667411222257086911 := by
  unfold tailWord_1384447
  simp only [CollatzResearch.WordTrace]
  refine ⟨50494930415392438568383595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33663286943594959045589063 50494930415392438568383595)
  ·
    refine ⟨75742395623088657852575393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50494930415392438568383595 75742395623088657852575393)
    ·
      refine ⟨56806796717316493389431545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75742395623088657852575393 56806796717316493389431545)
      ·
        refine ⟨42605097537987370042073659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56806796717316493389431545 42605097537987370042073659)
        ·
          refine ⟨63907646306981055063110489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42605097537987370042073659 63907646306981055063110489)
          ·
            refine ⟨47930734730235791297332867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63907646306981055063110489 47930734730235791297332867)
            ·
              refine ⟨71896102095353686945999301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47930734730235791297332867 71896102095353686945999301)
              ·
                refine ⟨13480519142878816302374869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71896102095353686945999301 13480519142878816302374869)
                ·
                  refine ⟨315949667411222257086911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13480519142878816302374869 315949667411222257086911)
                  ·
                    rfl

theorem cell21_1384447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 7].length) (baseStart_1384447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1384447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1384447 prefixEnd_1384447 := by exact prefixLift 1384447
  have htrace : WordTrace (prefixWord ++ tailWord_1384447) baseStart_1384447 baseEnd_1384447 := by
    simpa [prefixWord, tailWord_1384447, baseEnd_1384447] using wordTrace_append hprefix tailTrace_1384447
  have hstable : (prefixWord ++ tailWord_1384447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384447).length < 2 ^ (prefixWord ++ tailWord_1384447).sum := by decide
  have hdescent : baseEnd_1384447 < baseStart_1384447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384526 : List Nat := [4, 1, 1, 1, 1, 6, 1, 6]
def baseStart_1384526 : Nat := 118140960795 + 1384526 * 2 ^ 59
def prefixEnd_1384526 : Nat := 4983230072969 + 3 ^ 40 * 1384526 * 2
def baseEnd_1384526 : Nat := 105322565429178558423361

theorem tailTrace_1384526 : CollatzResearch.WordTrace tailWord_1384526 prefixEnd_1384526 105322565429178558423361 := by
  unfold tailWord_1384526
  simp only [CollatzResearch.WordTrace]
  refine ⟨6312226472763279382563679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33665207854737490040339621 6312226472763279382563679)
  ·
    refine ⟨9468339709144919073845519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6312226472763279382563679 9468339709144919073845519)
    ·
      refine ⟨14202509563717378610768279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9468339709144919073845519 14202509563717378610768279)
      ·
        refine ⟨21303764345576067916152419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14202509563717378610768279 21303764345576067916152419)
        ·
          refine ⟨31955646518364101874228629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21303764345576067916152419 31955646518364101874228629)
          ·
            refine ⟨1497920930548317275354467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 31955646518364101874228629 1497920930548317275354467)
            ·
              refine ⟨2246881395822475913031701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1497920930548317275354467 2246881395822475913031701)
              ·
                refine ⟨105322565429178558423361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2246881395822475913031701 105322565429178558423361)
                ·
                  rfl

theorem cell21_1384526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_1384526 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1384526 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1384526 prefixEnd_1384526 := by exact prefixLift 1384526
  have htrace : WordTrace (prefixWord ++ tailWord_1384526) baseStart_1384526 baseEnd_1384526 := by
    simpa [prefixWord, tailWord_1384526, baseEnd_1384526] using wordTrace_append hprefix tailTrace_1384526
  have hstable : (prefixWord ++ tailWord_1384526).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384526).length < 2 ^ (prefixWord ++ tailWord_1384526).sum := by decide
  have hdescent : baseEnd_1384526 < baseStart_1384526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384540 : List Nat := [2, 2, 4, 1, 1, 2, 1, 1, 7]
def baseStart_1384540 : Nat := 118140960795 + 1384540 * 2 ^ 59
def prefixEnd_1384540 : Nat := 4983230072969 + 3 ^ 40 * 1384540 * 2
def baseEnd_1384540 : Nat := 315970891278274762036721

theorem tailTrace_1384540 : CollatzResearch.WordTrace tailWord_1384540 prefixEnd_1384540 315970891278274762036721 := by
  unfold tailWord_1384540
  simp only [CollatzResearch.WordTrace]
  refine ⟨25249161202027757725759537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33665548269370343634346049 25249161202027757725759537)
  ·
    refine ⟨18936870901520818294319653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25249161202027757725759537 18936870901520818294319653)
    ·
      refine ⟨3550663294035153430184935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18936870901520818294319653 3550663294035153430184935)
      ·
        refine ⟨5325994941052730145277403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3550663294035153430184935 5325994941052730145277403)
        ·
          refine ⟨7988992411579095217916105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5325994941052730145277403 7988992411579095217916105)
          ·
            refine ⟨5991744308684321413437079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7988992411579095217916105 5991744308684321413437079)
            ·
              refine ⟨8987616463026482120155619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5991744308684321413437079 8987616463026482120155619)
              ·
                refine ⟨13481424694539723180233429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8987616463026482120155619 13481424694539723180233429)
                ·
                  refine ⟨315970891278274762036721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13481424694539723180233429 315970891278274762036721)
                  ·
                    rfl

theorem cell21_1384540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_1384540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1384540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1384540 prefixEnd_1384540 := by exact prefixLift 1384540
  have htrace : WordTrace (prefixWord ++ tailWord_1384540) baseStart_1384540 baseEnd_1384540 := by
    simpa [prefixWord, tailWord_1384540, baseEnd_1384540] using wordTrace_append hprefix tailTrace_1384540
  have hstable : (prefixWord ++ tailWord_1384540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384540).length < 2 ^ (prefixWord ++ tailWord_1384540).sum := by decide
  have hdescent : baseEnd_1384540 < baseStart_1384540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384602 : List Nat := [3, 1, 1, 5, 2, 1, 1, 7]
def baseStart_1384602 : Nat := 118140960795 + 1384602 * 2 ^ 59
def prefixEnd_1384602 : Nat := 4983230072969 + 3 ^ 40 * 1384602 * 2
def baseEnd_1384602 : Nat := 105328346840992144001087

theorem tailTrace_1384602 : CollatzResearch.WordTrace tailWord_1384602 prefixEnd_1384602 105328346840992144001087 := by
  unfold tailWord_1384602
  simp only [CollatzResearch.WordTrace]
  refine ⟨12625145932457725010069015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33667055819887266693517373 12625145932457725010069015)
  ·
    refine ⟨18937718898686587515103523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12625145932457725010069015 18937718898686587515103523)
    ·
      refine ⟨28406578348029881272655285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18937718898686587515103523 28406578348029881272655285)
      ·
        refine ⟨2663116720127801369311433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28406578348029881272655285 2663116720127801369311433)
        ·
          refine ⟨1997337540095851026983575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2663116720127801369311433 1997337540095851026983575)
          ·
            refine ⟨2996006310143776540475363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1997337540095851026983575 2996006310143776540475363)
            ·
              refine ⟨4494009465215664810713045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2996006310143776540475363 4494009465215664810713045)
              ·
                refine ⟨105328346840992144001087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4494009465215664810713045 105328346840992144001087)
                ·
                  rfl

theorem cell21_1384602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 7].length) (baseStart_1384602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1384602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1384602 prefixEnd_1384602 := by exact prefixLift 1384602
  have htrace : WordTrace (prefixWord ++ tailWord_1384602) baseStart_1384602 baseEnd_1384602 := by
    simpa [prefixWord, tailWord_1384602, baseEnd_1384602] using wordTrace_append hprefix tailTrace_1384602
  have hstable : (prefixWord ++ tailWord_1384602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384602).length < 2 ^ (prefixWord ++ tailWord_1384602).sum := by decide
  have hdescent : baseEnd_1384602 < baseStart_1384602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384740 : List Nat := [2, 3, 1, 3, 1, 4, 1, 2, 4]
def baseStart_1384740 : Nat := 118140960795 + 1384740 * 2 ^ 59
def prefixEnd_1384740 : Nat := 4983230072969 + 3 ^ 40 * 1384740 * 2
def baseEnd_1384740 : Nat := 316016534003118858702979

theorem tailTrace_1384740 : CollatzResearch.WordTrace tailWord_1384740 prefixEnd_1384740 316016534003118858702979 := by
  unfold tailWord_1384740
  simp only [CollatzResearch.WordTrace]
  refine ⟨25252808501665474804399837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33670411335553966405866449 25252808501665474804399837)
  ·
    refine ⟨9469803188124553051649939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25252808501665474804399837 9469803188124553051649939)
    ·
      refine ⟨14204704782186829577474909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9469803188124553051649939 14204704782186829577474909)
      ·
        refine ⟨5326764293320061091553091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14204704782186829577474909 5326764293320061091553091)
        ·
          refine ⟨7990146439980091637329637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5326764293320061091553091 7990146439980091637329637)
          ·
            refine ⟨1498152457496267181999307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7990146439980091637329637 1498152457496267181999307)
            ·
              refine ⟨2247228686244400772998961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1498152457496267181999307 2247228686244400772998961)
              ·
                refine ⟨1685421514683300579749221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2247228686244400772998961 1685421514683300579749221)
                ·
                  refine ⟨316016534003118858702979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1685421514683300579749221 316016534003118858702979)
                  ·
                    rfl

theorem cell21_1384740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_1384740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1384740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1384740 prefixEnd_1384740 := by exact prefixLift 1384740
  have htrace : WordTrace (prefixWord ++ tailWord_1384740) baseStart_1384740 baseEnd_1384740 := by
    simpa [prefixWord, tailWord_1384740, baseEnd_1384740] using wordTrace_append hprefix tailTrace_1384740
  have hstable : (prefixWord ++ tailWord_1384740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384740).length < 2 ^ (prefixWord ++ tailWord_1384740).sum := by decide
  have hdescent : baseEnd_1384740 < baseStart_1384740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384743 : List Nat := [1, 1, 8, 1, 1, 1, 2, 1, 5]
def baseStart_1384743 : Nat := 118140960795 + 1384743 * 2 ^ 59
def prefixEnd_1384743 : Nat := 4983230072969 + 3 ^ 40 * 1384743 * 2
def baseEnd_1384743 : Nat := 316017218643991520152973

theorem tailTrace_1384743 : CollatzResearch.WordTrace tailWord_1384743 prefixEnd_1384743 316017218643991520152973 := by
  unfold tailWord_1384743
  simp only [CollatzResearch.WordTrace]
  refine ⟨50505726422320081121158883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33670484281546720747439255 50505726422320081121158883)
  ·
    refine ⟨75758589633480121681738325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50505726422320081121158883 75758589633480121681738325)
    ·
      refine ⟨887795972267345175957871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 75758589633480121681738325 887795972267345175957871)
      ·
        refine ⟨1331693958401017763936807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 887795972267345175957871 1331693958401017763936807)
        ·
          refine ⟨1997540937601526645905211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1331693958401017763936807 1997540937601526645905211)
          ·
            refine ⟨2996311406402289968857817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1997540937601526645905211 2996311406402289968857817)
            ·
              refine ⟨2247233554801717476643363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2996311406402289968857817 2247233554801717476643363)
              ·
                refine ⟨3370850332202576214965045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2247233554801717476643363 3370850332202576214965045)
                ·
                  refine ⟨316017218643991520152973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3370850332202576214965045 316017218643991520152973)
                  ·
                    rfl

theorem cell21_1384743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 5].length) (baseStart_1384743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1384743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1384743 prefixEnd_1384743 := by exact prefixLift 1384743
  have htrace : WordTrace (prefixWord ++ tailWord_1384743) baseStart_1384743 baseEnd_1384743 := by
    simpa [prefixWord, tailWord_1384743, baseEnd_1384743] using wordTrace_append hprefix tailTrace_1384743
  have hstable : (prefixWord ++ tailWord_1384743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384743).length < 2 ^ (prefixWord ++ tailWord_1384743).sum := by decide
  have hdescent : baseEnd_1384743 < baseStart_1384743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384751 : List Nat := [1, 1, 2, 1, 2, 1, 5, 3, 5]
def baseStart_1384751 : Nat := 118140960795 + 1384751 * 2 ^ 59
def prefixEnd_1384751 : Nat := 4983230072969 + 3 ^ 40 * 1384751 * 2
def baseEnd_1384751 : Nat := 316019044352985284019623

theorem tailTrace_1384751 : CollatzResearch.WordTrace tailWord_1384751 prefixEnd_1384751 316019044352985284019623 := by
  unfold tailWord_1384751
  simp only [CollatzResearch.WordTrace]
  refine ⟨50506018206291098487450107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33670678804194065658300071 50506018206291098487450107)
  ·
    refine ⟨75759027309436647731175161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50506018206291098487450107 75759027309436647731175161)
    ·
      refine ⟨56819270482077485798381371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75759027309436647731175161 56819270482077485798381371)
      ·
        refine ⟨85228905723116228697572057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56819270482077485798381371 85228905723116228697572057)
        ·
          refine ⟨63921679292337171523179043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85228905723116228697572057 63921679292337171523179043)
          ·
            refine ⟨95882518938505757284768565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63921679292337171523179043 95882518938505757284768565)
            ·
              refine ⟨8988986150484914745447053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95882518938505757284768565 8988986150484914745447053)
              ·
                refine ⟨3370869806431843029542645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8988986150484914745447053 3370869806431843029542645)
                ·
                  refine ⟨316019044352985284019623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3370869806431843029542645 316019044352985284019623)
                  ·
                    rfl

theorem cell21_1384751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 5].length) (baseStart_1384751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1384751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1384751 prefixEnd_1384751 := by exact prefixLift 1384751
  have htrace : WordTrace (prefixWord ++ tailWord_1384751) baseStart_1384751 baseEnd_1384751 := by
    simpa [prefixWord, tailWord_1384751, baseEnd_1384751] using wordTrace_append hprefix tailTrace_1384751
  have hstable : (prefixWord ++ tailWord_1384751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384751).length < 2 ^ (prefixWord ++ tailWord_1384751).sum := by decide
  have hdescent : baseEnd_1384751 < baseStart_1384751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384785 : List Nat := [1, 2, 2, 1, 4, 2, 3, 3, 3]
def baseStart_1384785 : Nat := 118140960795 + 1384785 * 2 ^ 59
def prefixEnd_1384785 : Nat := 4983230072969 + 3 ^ 40 * 1384785 * 2
def baseEnd_1384785 : Nat := 316026803616208780452887

theorem tailTrace_1384785 : CollatzResearch.WordTrace tailWord_1384785 prefixEnd_1384785 316026803616208780452887 := by
  unfold tailWord_1384785
  simp only [CollatzResearch.WordTrace]
  refine ⟨50507258288167922294187809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33671505525445281529458539 50507258288167922294187809)
  ·
    refine ⟨37880443716125941720640857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50507258288167922294187809 37880443716125941720640857)
    ·
      refine ⟨28410332787094456290480643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37880443716125941720640857 28410332787094456290480643)
      ·
        refine ⟨42615499180641684435720965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28410332787094456290480643 42615499180641684435720965)
        ·
          refine ⟨7990406096370315831697681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42615499180641684435720965 7990406096370315831697681)
          ·
            refine ⟨5992804572277736873773261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7990406096370315831697681 5992804572277736873773261)
            ·
              refine ⟨2247301714604151327664973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5992804572277736873773261 2247301714604151327664973)
              ·
                refine ⟨842738142976556747874365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2247301714604151327664973 842738142976556747874365)
                ·
                  refine ⟨316026803616208780452887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 842738142976556747874365 316026803616208780452887)
                  ·
                    rfl

theorem cell21_1384785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 3, 3].length) (baseStart_1384785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1384785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1384785 prefixEnd_1384785 := by exact prefixLift 1384785
  have htrace : WordTrace (prefixWord ++ tailWord_1384785) baseStart_1384785 baseEnd_1384785 := by
    simpa [prefixWord, tailWord_1384785, baseEnd_1384785] using wordTrace_append hprefix tailTrace_1384785
  have hstable : (prefixWord ++ tailWord_1384785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384785).length < 2 ^ (prefixWord ++ tailWord_1384785).sum := by decide
  have hdescent : baseEnd_1384785 < baseStart_1384785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384813 : List Nat := [1, 5, 1, 1, 1, 2, 4, 6]
def baseStart_1384813 : Nat := 118140960795 + 1384813 * 2 ^ 59
def prefixEnd_1384813 : Nat := 4983230072969 + 3 ^ 40 * 1384813 * 2
def baseEnd_1384813 : Nat := 105344397865895651328721

theorem tailTrace_1384813 : CollatzResearch.WordTrace tailWord_1384813 prefixEnd_1384813 105344397865895651328721 := by
  unfold tailWord_1384813
  simp only [CollatzResearch.WordTrace]
  refine ⟨50508279532066483076207093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33672186354710988717471395 50508279532066483076207093)
  ·
    refine ⟨4735151206131232788394415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50508279532066483076207093 4735151206131232788394415)
    ·
      refine ⟨7102726809196849182591623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4735151206131232788394415 7102726809196849182591623)
      ·
        refine ⟨10654090213795273773887435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7102726809196849182591623 10654090213795273773887435)
        ·
          refine ⟨15981135320692910660831153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10654090213795273773887435 15981135320692910660831153)
          ·
            refine ⟨11985851490519682995623365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15981135320692910660831153 11985851490519682995623365)
            ·
              refine ⟨2247347154472440561679381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11985851490519682995623365 2247347154472440561679381)
              ·
                refine ⟨105344397865895651328721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2247347154472440561679381 105344397865895651328721)
                ·
                  rfl

theorem cell21_1384813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 6].length) (baseStart_1384813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1384813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1384813 prefixEnd_1384813 := by exact prefixLift 1384813
  have htrace : WordTrace (prefixWord ++ tailWord_1384813) baseStart_1384813 baseEnd_1384813 := by
    simpa [prefixWord, tailWord_1384813, baseEnd_1384813] using wordTrace_append hprefix tailTrace_1384813
  have hstable : (prefixWord ++ tailWord_1384813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384813).length < 2 ^ (prefixWord ++ tailWord_1384813).sum := by decide
  have hdescent : baseEnd_1384813 < baseStart_1384813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384816 : List Nat := [2, 1, 1, 1, 4, 5, 2, 1, 4]
def baseStart_1384816 : Nat := 118140960795 + 1384816 * 2 ^ 59
def prefixEnd_1384816 : Nat := 4983230072969 + 3 ^ 40 * 1384816 * 2
def baseEnd_1384816 : Nat := 316033878238559615436157

theorem tailTrace_1384816 : CollatzResearch.WordTrace tailWord_1384816 prefixEnd_1384816 316033878238559615436157 := by
  unfold tailWord_1384816
  simp only [CollatzResearch.WordTrace]
  refine ⟨25254194475527807294283151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33672259300703743059044201 25254194475527807294283151)
  ·
    refine ⟨37881291713291710941424727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25254194475527807294283151 37881291713291710941424727)
    ·
      refine ⟨56821937569937566412137091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37881291713291710941424727 56821937569937566412137091)
      ·
        refine ⟨85232906354906349618205637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56821937569937566412137091 85232906354906349618205637)
        ·
          refine ⟨15981169941544940553413557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85232906354906349618205637 15981169941544940553413557)
          ·
            refine ⟨1498234682019838176882521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15981169941544940553413557 1498234682019838176882521)
            ·
              refine ⟨1123676011514878632661891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1498234682019838176882521 1123676011514878632661891)
              ·
                refine ⟨1685514017272317948992837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1123676011514878632661891 1685514017272317948992837)
                ·
                  refine ⟨316033878238559615436157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1685514017272317948992837 316033878238559615436157)
                  ·
                    rfl

theorem cell21_1384816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 1, 4].length) (baseStart_1384816 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1384816 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1384816 prefixEnd_1384816 := by exact prefixLift 1384816
  have htrace : WordTrace (prefixWord ++ tailWord_1384816) baseStart_1384816 baseEnd_1384816 := by
    simpa [prefixWord, tailWord_1384816, baseEnd_1384816] using wordTrace_append hprefix tailTrace_1384816
  have hstable : (prefixWord ++ tailWord_1384816).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384816).length < 2 ^ (prefixWord ++ tailWord_1384816).sum := by decide
  have hdescent : baseEnd_1384816 < baseStart_1384816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385041 : List Nat := [1, 2, 2, 1, 3, 5, 1, 6]
def baseStart_1385041 : Nat := 118140960795 + 1385041 * 2 ^ 59
def prefixEnd_1385041 : Nat := 4983230072969 + 3 ^ 40 * 1385041 * 2
def baseEnd_1385041 : Nat := 105361742101336408061899

theorem tailTrace_1385041 : CollatzResearch.WordTrace tailWord_1385041 prefixEnd_1385041 105361742101336408061899 := by
  unfold tailWord_1385041
  simp only [CollatzResearch.WordTrace]
  refine ⟨50516595375240478015506977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33677730250160318677004651 50516595375240478015506977)
  ·
    refine ⟨37887446531430358511630233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50516595375240478015506977 37887446531430358511630233)
    ·
      refine ⟨28415584898572768883722675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37887446531430358511630233 28415584898572768883722675)
      ·
        refine ⟨42623377347859153325584013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28415584898572768883722675 42623377347859153325584013)
        ·
          refine ⟨15983766505447182497094005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42623377347859153325584013 15983766505447182497094005)
          ·
            refine ⟨1498478109885673359102563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15983766505447182497094005 1498478109885673359102563)
            ·
              refine ⟨2247717164828510038653845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1498478109885673359102563 2247717164828510038653845)
              ·
                refine ⟨105361742101336408061899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2247717164828510038653845 105361742101336408061899)
                ·
                  rfl

theorem cell21_1385041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 6].length) (baseStart_1385041 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1385041 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1385041 prefixEnd_1385041 := by exact prefixLift 1385041
  have htrace : WordTrace (prefixWord ++ tailWord_1385041) baseStart_1385041 baseEnd_1385041 := by
    simpa [prefixWord, tailWord_1385041, baseEnd_1385041] using wordTrace_append hprefix tailTrace_1385041
  have hstable : (prefixWord ++ tailWord_1385041).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385041).length < 2 ^ (prefixWord ++ tailWord_1385041).sum := by decide
  have hdescent : baseEnd_1385041 < baseStart_1385041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385117 : List Nat := [1, 4, 2, 1, 1, 1, 6, 5]
def baseStart_1385117 : Nat := 118140960795 + 1385117 * 2 ^ 59
def prefixEnd_1385117 : Nat := 4983230072969 + 3 ^ 40 * 1385117 * 2
def baseEnd_1385117 : Nat := 105367523513149993639625

theorem tailTrace_1385117 : CollatzResearch.WordTrace tailWord_1385117 prefixEnd_1385117 105367523513149993639625 := by
  unfold tailWord_1385117
  simp only [CollatzResearch.WordTrace]
  refine ⟨50519367322965142995273605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33679578215310095330182403 50519367322965142995273605)
  ·
    refine ⟨9472381373055964311613801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50519367322965142995273605 9472381373055964311613801)
    ·
      refine ⟨7104286029791973233710351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9472381373055964311613801 7104286029791973233710351)
      ·
        refine ⟨10656429044687959850565527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7104286029791973233710351 10656429044687959850565527)
        ·
          refine ⟨15984643567031939775848291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10656429044687959850565527 15984643567031939775848291)
          ·
            refine ⟨23976965350547909663772437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15984643567031939775848291 23976965350547909663772437)
            ·
              refine ⟨1123920250806933265489333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23976965350547909663772437 1123920250806933265489333)
              ·
                refine ⟨105367523513149993639625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1123920250806933265489333 105367523513149993639625)
                ·
                  rfl

theorem cell21_1385117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 5].length) (baseStart_1385117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1385117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1385117 prefixEnd_1385117 := by exact prefixLift 1385117
  have htrace : WordTrace (prefixWord ++ tailWord_1385117) baseStart_1385117 baseEnd_1385117 := by
    simpa [prefixWord, tailWord_1385117, baseEnd_1385117] using wordTrace_append hprefix tailTrace_1385117
  have hstable : (prefixWord ++ tailWord_1385117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385117).length < 2 ^ (prefixWord ++ tailWord_1385117).sum := by decide
  have hdescent : baseEnd_1385117 < baseStart_1385117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385134 : List Nat := [4, 1, 4, 1, 1, 3, 7]
def baseStart_1385134 : Nat := 118140960795 + 1385134 * 2 ^ 59
def prefixEnd_1385134 : Nat := 4983230072969 + 3 ^ 40 * 1385134 * 2
def baseEnd_1385134 : Nat := 35122938907895747681723

theorem tailTrace_1385134 : CollatzResearch.WordTrace tailWord_1385134 prefixEnd_1385134 35122938907895747681723 := by
  unfold tailWord_1385134
  simp only [CollatzResearch.WordTrace]
  refine ⟨6314998420487944362330307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33679991575935703265761637 6314998420487944362330307)
  ·
    refine ⟨9472497630731916543495461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6314998420487944362330307 9472497630731916543495461)
    ·
      refine ⟨1776093305762234351905399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9472497630731916543495461 1776093305762234351905399)
      ·
        refine ⟨2664139958643351527858099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1776093305762234351905399 2664139958643351527858099)
        ·
          refine ⟨3996209937965027291787149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2664139958643351527858099 3996209937965027291787149)
          ·
            refine ⟨1498578726736885234420181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3996209937965027291787149 1498578726736885234420181)
            ·
              refine ⟨35122938907895747681723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1498578726736885234420181 35122938907895747681723)
              ·
                rfl

theorem cell21_1385134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 7].length) (baseStart_1385134 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1385134 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1385134 prefixEnd_1385134 := by exact prefixLift 1385134
  have htrace : WordTrace (prefixWord ++ tailWord_1385134) baseStart_1385134 baseEnd_1385134 := by
    simpa [prefixWord, tailWord_1385134, baseEnd_1385134] using wordTrace_append hprefix tailTrace_1385134
  have hstable : (prefixWord ++ tailWord_1385134).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385134).length < 2 ^ (prefixWord ++ tailWord_1385134).sum := by decide
  have hdescent : baseEnd_1385134 < baseStart_1385134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385176 : List Nat := [2, 1, 2, 2, 3, 2, 2, 7]
def baseStart_1385176 : Nat := 118140960795 + 1385176 * 2 ^ 59
def prefixEnd_1385176 : Nat := 4983230072969 + 3 ^ 40 * 1385176 * 2
def baseEnd_1385176 : Nat := 105372011714426329811807

theorem tailTrace_1385176 : CollatzResearch.WordTrace tailWord_1385176 prefixEnd_1385176 105372011714426329811807 := by
  unfold tailWord_1385176
  simp only [CollatzResearch.WordTrace]
  refine ⟨25260759614875698035835691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33681012819834264047780921 25260759614875698035835691)
  ·
    refine ⟨37891139422313547053753537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25260759614875698035835691 37891139422313547053753537)
    ·
      refine ⟨28418354566735160290315153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37891139422313547053753537 28418354566735160290315153)
      ·
        refine ⟨21313765925051370217736365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28418354566735160290315153 21313765925051370217736365)
        ·
          refine ⟨7992662221894263831651137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21313765925051370217736365 7992662221894263831651137)
          ·
            refine ⟨5994496666420697873738353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7992662221894263831651137 5994496666420697873738353)
            ·
              refine ⟨4495872499815523405303765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5994496666420697873738353 4495872499815523405303765)
              ·
                refine ⟨105372011714426329811807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4495872499815523405303765 105372011714426329811807)
                ·
                  rfl

theorem cell21_1385176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 7].length) (baseStart_1385176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1385176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1385176 prefixEnd_1385176 := by exact prefixLift 1385176
  have htrace : WordTrace (prefixWord ++ tailWord_1385176) baseStart_1385176 baseEnd_1385176 := by
    simpa [prefixWord, tailWord_1385176, baseEnd_1385176] using wordTrace_append hprefix tailTrace_1385176
  have hstable : (prefixWord ++ tailWord_1385176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385176).length < 2 ^ (prefixWord ++ tailWord_1385176).sum := by decide
  have hdescent : baseEnd_1385176 < baseStart_1385176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385418 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 9]
def baseStart_1385418 : Nat := 118140960795 + 1385418 * 2 ^ 59
def prefixEnd_1385418 : Nat := 4983230072969 + 3 ^ 40 * 1385418 * 2
def baseEnd_1385418 : Nat := 316171262840340346401593

theorem tailTrace_1385418 : CollatzResearch.WordTrace tailWord_1385418 prefixEnd_1385418 316171262840340346401593 := by
  unfold tailWord_1385418
  simp only [CollatzResearch.WordTrace]
  refine ⟨12632586423718667850495227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33686897129916447601320605 12632586423718667850495227)
  ·
    refine ⟨18948879635578001775742841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12632586423718667850495227 18948879635578001775742841)
    ·
      refine ⟨14211659726683501331807131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18948879635578001775742841 14211659726683501331807131)
      ·
        refine ⟨21317489590025251997710697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14211659726683501331807131 21317489590025251997710697)
        ·
          refine ⟨15988117192518938998283023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21317489590025251997710697 15988117192518938998283023)
          ·
            refine ⟨23982175788778408497424535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15988117192518938998283023 23982175788778408497424535)
            ·
              refine ⟨35973263683167612746136803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23982175788778408497424535 35973263683167612746136803)
              ·
                refine ⟨53959895524751419119205205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35973263683167612746136803 53959895524751419119205205)
                ·
                  refine ⟨316171262840340346401593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 53959895524751419119205205 316171262840340346401593)
                  ·
                    rfl

theorem cell21_1385418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_1385418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1385418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1385418 prefixEnd_1385418 := by exact prefixLift 1385418
  have htrace : WordTrace (prefixWord ++ tailWord_1385418) baseStart_1385418 baseEnd_1385418 := by
    simpa [prefixWord, tailWord_1385418, baseEnd_1385418] using wordTrace_append hprefix tailTrace_1385418
  have hstable : (prefixWord ++ tailWord_1385418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385418).length < 2 ^ (prefixWord ++ tailWord_1385418).sum := by decide
  have hdescent : baseEnd_1385418 < baseStart_1385418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385480 : List Nat := [2, 1, 3, 2, 1, 5, 7]
def baseStart_1385480 : Nat := 118140960795 + 1385480 * 2 ^ 59
def prefixEnd_1385480 : Nat := 4983230072969 + 3 ^ 40 * 1385480 * 2
def baseEnd_1385480 : Nat := 35131712453893557374237

theorem tailTrace_1385480 : CollatzResearch.WordTrace tailWord_1385480 prefixEnd_1385480 35131712453893557374237 := by
  unfold tailWord_1385480
  simp only [CollatzResearch.WordTrace]
  refine ⟨25266303510325027995368947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33688404680433370660491929 25266303510325027995368947)
  ·
    refine ⟨37899455265487541993053421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25266303510325027995368947 37899455265487541993053421)
    ·
      refine ⟨14212295724557828247395033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37899455265487541993053421 14212295724557828247395033)
      ·
        refine ⟨10659221793418371185546275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14212295724557828247395033 10659221793418371185546275)
        ·
          refine ⟨15988832690127556778319413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10659221793418371185546275 15988832690127556778319413)
          ·
            refine ⟨1498953064699458447967445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15988832690127556778319413 1498953064699458447967445)
            ·
              refine ⟨35131712453893557374237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1498953064699458447967445 35131712453893557374237)
              ·
                rfl

theorem cell21_1385480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 7].length) (baseStart_1385480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1385480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1385480 prefixEnd_1385480 := by exact prefixLift 1385480
  have htrace : WordTrace (prefixWord ++ tailWord_1385480) baseStart_1385480 baseEnd_1385480 := by
    simpa [prefixWord, tailWord_1385480, baseEnd_1385480] using wordTrace_append hprefix tailTrace_1385480
  have hstable : (prefixWord ++ tailWord_1385480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385480).length < 2 ^ (prefixWord ++ tailWord_1385480).sum := by decide
  have hdescent : baseEnd_1385480 < baseStart_1385480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385500 : List Nat := [2, 2, 3, 1, 4, 2, 2, 1, 4]
def baseStart_1385500 : Nat := 118140960795 + 1385500 * 2 ^ 59
def prefixEnd_1385500 : Nat := 4983230072969 + 3 ^ 40 * 1385500 * 2
def baseEnd_1385500 : Nat := 316189976357526426034759

theorem tailTrace_1385500 : CollatzResearch.WordTrace tailWord_1385500 prefixEnd_1385500 316189976357526426034759 := by
  unfold tailWord_1385500
  simp only [CollatzResearch.WordTrace]
  refine ⟨25266668240288799703232977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33688890987051732937643969 25266668240288799703232977)
  ·
    refine ⟨18950001180216599777424733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25266668240288799703232977 18950001180216599777424733)
    ·
      refine ⟨7106250442581224916534275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18950001180216599777424733 7106250442581224916534275)
      ·
        refine ⟨10659375663871837374801413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7106250442581224916534275 10659375663871837374801413)
        ·
          refine ⟨1998632936975969507775265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10659375663871837374801413 1998632936975969507775265)
          ·
            refine ⟨1498974702731977130831449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1998632936975969507775265 1498974702731977130831449)
            ·
              refine ⟨1124231027048982848123587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1498974702731977130831449 1124231027048982848123587)
              ·
                refine ⟨1686346540573474272185381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1124231027048982848123587 1686346540573474272185381)
                ·
                  refine ⟨316189976357526426034759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1686346540573474272185381 316189976357526426034759)
                  ·
                    rfl

theorem cell21_1385500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 1, 4].length) (baseStart_1385500 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1385500 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1385500 prefixEnd_1385500 := by exact prefixLift 1385500
  have htrace : WordTrace (prefixWord ++ tailWord_1385500) baseStart_1385500 baseEnd_1385500 := by
    simpa [prefixWord, tailWord_1385500, baseEnd_1385500] using wordTrace_append hprefix tailTrace_1385500
  have hstable : (prefixWord ++ tailWord_1385500).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385500).length < 2 ^ (prefixWord ++ tailWord_1385500).sum := by decide
  have hdescent : baseEnd_1385500 < baseStart_1385500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385556 : List Nat := [2, 4, 1, 1, 1, 1, 5, 6]
def baseStart_1385556 : Nat := 118140960795 + 1385556 * 2 ^ 59
def prefixEnd_1385556 : Nat := 4983230072969 + 3 ^ 40 * 1385556 * 2
def baseEnd_1385556 : Nat := 105400918773494257700437

theorem tailTrace_1385556 : CollatzResearch.WordTrace tailWord_1385556 prefixEnd_1385556 105400918773494257700437 := by
  unfold tailWord_1385556
  simp only [CollatzResearch.WordTrace]
  refine ⟨25267689484187360485252261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33690252645583147313669681 25267689484187360485252261)
  ·
    refine ⟨4737691778285130090984799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25267689484187360485252261 4737691778285130090984799)
    ·
      refine ⟨7106537667427695136477199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4737691778285130090984799 7106537667427695136477199)
      ·
        refine ⟨10659806501141542704715799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7106537667427695136477199 10659806501141542704715799)
        ·
          refine ⟨15989709751712314057073699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10659806501141542704715799 15989709751712314057073699)
          ·
            refine ⟨23984564627568471085610549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15989709751712314057073699 23984564627568471085610549)
            ·
              refine ⟨2248552933834544164275989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23984564627568471085610549 2248552933834544164275989)
              ·
                refine ⟨105400918773494257700437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2248552933834544164275989 105400918773494257700437)
                ·
                  rfl

theorem cell21_1385556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 6].length) (baseStart_1385556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1385556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1385556 prefixEnd_1385556 := by exact prefixLift 1385556
  have htrace : WordTrace (prefixWord ++ tailWord_1385556) baseStart_1385556 baseEnd_1385556 := by
    simpa [prefixWord, tailWord_1385556, baseEnd_1385556] using wordTrace_append hprefix tailTrace_1385556
  have hstable : (prefixWord ++ tailWord_1385556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385556).length < 2 ^ (prefixWord ++ tailWord_1385556).sum := by decide
  have hdescent : baseEnd_1385556 < baseStart_1385556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385604 : List Nat := [2, 3, 2, 1, 2, 2, 2, 4, 3]
def baseStart_1385604 : Nat := 118140960795 + 1385604 * 2 ^ 59
def prefixEnd_1385604 : Nat := 4983230072969 + 3 ^ 40 * 1385604 * 2
def baseEnd_1385604 : Nat := 316213710574445356301213

theorem tailTrace_1385604 : CollatzResearch.WordTrace tailWord_1385604 prefixEnd_1385604 316213710574445356301213 := by
  unfold tailWord_1385604
  simp only [CollatzResearch.WordTrace]
  refine ⟨25268564836100412584125933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33691419781467216778834577 25268564836100412584125933)
  ·
    refine ⟨9475711813537654719047225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25268564836100412584125933 9475711813537654719047225)
    ·
      refine ⟨7106783860153241039285419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9475711813537654719047225 7106783860153241039285419)
      ·
        refine ⟨10660175790229861558928129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7106783860153241039285419 10660175790229861558928129)
        ·
          refine ⟨7995131842672396169196097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10660175790229861558928129 7995131842672396169196097)
          ·
            refine ⟨5996348882004297126897073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7995131842672396169196097 5996348882004297126897073)
            ·
              refine ⟨4497261661503222845172805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5996348882004297126897073 4497261661503222845172805)
              ·
                refine ⟨843236561531854283469901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4497261661503222845172805 843236561531854283469901)
                ·
                  refine ⟨316213710574445356301213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 843236561531854283469901 316213710574445356301213)
                  ·
                    rfl

theorem cell21_1385604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 4, 3].length) (baseStart_1385604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1385604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1385604 prefixEnd_1385604 := by exact prefixLift 1385604
  have htrace : WordTrace (prefixWord ++ tailWord_1385604) baseStart_1385604 baseEnd_1385604 := by
    simpa [prefixWord, tailWord_1385604, baseEnd_1385604] using wordTrace_append hprefix tailTrace_1385604
  have hstable : (prefixWord ++ tailWord_1385604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385604).length < 2 ^ (prefixWord ++ tailWord_1385604).sum := by decide
  have hdescent : baseEnd_1385604 < baseStart_1385604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385663 : List Nat := [1, 1, 2, 2, 2, 2, 2, 6, 3]
def baseStart_1385663 : Nat := 118140960795 + 1385663 * 2 ^ 59
def prefixEnd_1385663 : Nat := 4983230072969 + 3 ^ 40 * 1385663 * 2
def baseEnd_1385663 : Nat := 316227175178274364817759

theorem tailTrace_1385663 : CollatzResearch.WordTrace tailWord_1385663 prefixEnd_1385663 316227175178274364817759 := by
  unfold tailWord_1385663
  simp only [CollatzResearch.WordTrace]
  refine ⟨50539281578987078244649643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33692854385991385496433095 50539281578987078244649643)
  ·
    refine ⟨75808922368480617366974465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50539281578987078244649643 75808922368480617366974465)
    ·
      refine ⟨56856691776360463025230849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75808922368480617366974465 56856691776360463025230849)
      ·
        refine ⟨42642518832270347268923137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56856691776360463025230849 42642518832270347268923137)
        ·
          refine ⟨31981889124202760451692353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42642518832270347268923137 31981889124202760451692353)
          ·
            refine ⟨23986416843152070338769265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31981889124202760451692353 23986416843152070338769265)
            ·
              refine ⟨17989812632364052754076949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23986416843152070338769265 17989812632364052754076949)
              ·
                refine ⟨843272467142064972847357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17989812632364052754076949 843272467142064972847357)
                ·
                  refine ⟨316227175178274364817759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 843272467142064972847357 316227175178274364817759)
                  ·
                    rfl

theorem cell21_1385663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 6, 3].length) (baseStart_1385663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1385663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1385663 prefixEnd_1385663 := by exact prefixLift 1385663
  have htrace : WordTrace (prefixWord ++ tailWord_1385663) baseStart_1385663 baseEnd_1385663 := by
    simpa [prefixWord, tailWord_1385663, baseEnd_1385663] using wordTrace_append hprefix tailTrace_1385663
  have hstable : (prefixWord ++ tailWord_1385663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385663).length < 2 ^ (prefixWord ++ tailWord_1385663).sum := by decide
  have hdescent : baseEnd_1385663 < baseStart_1385663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385714 : List Nat := [3, 2, 1, 3, 3, 2, 2, 2, 3]
def baseStart_1385714 : Nat := 118140960795 + 1385714 * 2 ^ 59
def prefixEnd_1385714 : Nat := 4983230072969 + 3 ^ 40 * 1385714 * 2
def baseEnd_1385714 : Nat := 316238814073109609467655

theorem tailTrace_1385714 : CollatzResearch.WordTrace tailWord_1385714 prefixEnd_1385714 316238814073109609467655 := by
  unfold tailWord_1385714
  simp only [CollatzResearch.WordTrace]
  refine ⟨12635285425450578488689049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33694094467868209303170797 12635285425450578488689049)
  ·
    refine ⟨9476464069087933866516787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12635285425450578488689049 9476464069087933866516787)
    ·
      refine ⟨14214696103631900799775181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9476464069087933866516787 14214696103631900799775181)
      ·
        refine ⟨5330511038861962799915693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14214696103631900799775181 5330511038861962799915693)
        ·
          refine ⟨1998941639573236049968385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5330511038861962799915693 1998941639573236049968385)
          ·
            refine ⟨1499206229679927037476289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1998941639573236049968385 1499206229679927037476289)
            ·
              refine ⟨1124404672259945278107217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1499206229679927037476289 1124404672259945278107217)
              ·
                refine ⟨843303504194958958580413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1124404672259945278107217 843303504194958958580413)
                ·
                  refine ⟨316238814073109609467655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 843303504194958958580413 316238814073109609467655)
                  ·
                    rfl

theorem cell21_1385714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 2, 3].length) (baseStart_1385714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1385714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1385714 prefixEnd_1385714 := by exact prefixLift 1385714
  have htrace : WordTrace (prefixWord ++ tailWord_1385714) baseStart_1385714 baseEnd_1385714 := by
    simpa [prefixWord, tailWord_1385714, baseEnd_1385714] using wordTrace_append hprefix tailTrace_1385714
  have hstable : (prefixWord ++ tailWord_1385714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385714).length < 2 ^ (prefixWord ++ tailWord_1385714).sum := by decide
  have hdescent : baseEnd_1385714 < baseStart_1385714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385722 : List Nat := [3, 1, 1, 1, 1, 4, 2, 3, 5]
def baseStart_1385722 : Nat := 118140960795 + 1385722 * 2 ^ 59
def prefixEnd_1385722 : Nat := 4983230072969 + 3 ^ 40 * 1385722 * 2
def baseEnd_1385722 : Nat := 316240639782103373334305

theorem tailTrace_1385722 : CollatzResearch.WordTrace tailWord_1385722 prefixEnd_1385722 316240639782103373334305 := by
  unfold tailWord_1385722
  simp only [CollatzResearch.WordTrace]
  refine ⟨12635358371443332830261855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33694288990515554214031613 12635358371443332830261855)
  ·
    refine ⟨18953037557164999245392783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12635358371443332830261855 18953037557164999245392783)
    ·
      refine ⟨28429556335747498868089175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18953037557164999245392783 28429556335747498868089175)
      ·
        refine ⟨42644334503621248302133763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28429556335747498868089175 42644334503621248302133763)
        ·
          refine ⟨63966501755431872453200645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42644334503621248302133763 63966501755431872453200645)
          ·
            refine ⟨11993719079143476084975121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63966501755431872453200645 11993719079143476084975121)
            ·
              refine ⟨8995289309357607063731341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11993719079143476084975121 8995289309357607063731341)
              ·
                refine ⟨3373233491009102648899253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8995289309357607063731341 3373233491009102648899253)
                ·
                  refine ⟨316240639782103373334305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3373233491009102648899253 316240639782103373334305)
                  ·
                    rfl

theorem cell21_1385722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_1385722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1385722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1385722 prefixEnd_1385722 := by exact prefixLift 1385722
  have htrace : WordTrace (prefixWord ++ tailWord_1385722) baseStart_1385722 baseEnd_1385722 := by
    simpa [prefixWord, tailWord_1385722, baseEnd_1385722] using wordTrace_append hprefix tailTrace_1385722
  have hstable : (prefixWord ++ tailWord_1385722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385722).length < 2 ^ (prefixWord ++ tailWord_1385722).sum := by decide
  have hdescent : baseEnd_1385722 < baseStart_1385722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385770 : List Nat := [3, 1, 4, 2, 1, 2, 1, 1, 6]
def baseStart_1385770 : Nat := 118140960795 + 1385770 * 2 ^ 59
def prefixEnd_1385770 : Nat := 4983230072969 + 3 ^ 40 * 1385770 * 2
def baseEnd_1385770 : Nat := 316251594036065956534207

theorem tailTrace_1385770 : CollatzResearch.WordTrace tailWord_1385770 prefixEnd_1385770 316251594036065956534207 := by
  unfold tailWord_1385770
  simp only [CollatzResearch.WordTrace]
  refine ⟨12635796047399858879698691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33695456126399623679196509 12635796047399858879698691)
  ·
    refine ⟨18953694071099788319548037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12635796047399858879698691 18953694071099788319548037)
    ·
      refine ⟨3553817638331210309915257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18953694071099788319548037 3553817638331210309915257)
      ·
        refine ⟨2665363228748407732436443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3553817638331210309915257 2665363228748407732436443)
        ·
          refine ⟨3998044843122611598654665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2665363228748407732436443 3998044843122611598654665)
          ·
            refine ⟨2998533632341958698990999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3998044843122611598654665 2998533632341958698990999)
            ·
              refine ⟨4497800448512938048486499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2998533632341958698990999 4497800448512938048486499)
              ·
                refine ⟨6746700672769407072729749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4497800448512938048486499 6746700672769407072729749)
                ·
                  refine ⟨316251594036065956534207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6746700672769407072729749 316251594036065956534207)
                  ·
                    rfl

theorem cell21_1385770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 6].length) (baseStart_1385770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1385770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1385770 prefixEnd_1385770 := by exact prefixLift 1385770
  have htrace : WordTrace (prefixWord ++ tailWord_1385770) baseStart_1385770 baseEnd_1385770 := by
    simpa [prefixWord, tailWord_1385770, baseEnd_1385770] using wordTrace_append hprefix tailTrace_1385770
  have hstable : (prefixWord ++ tailWord_1385770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385770).length < 2 ^ (prefixWord ++ tailWord_1385770).sum := by decide
  have hdescent : baseEnd_1385770 < baseStart_1385770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385773 : List Nat := [1, 5, 3, 1, 1, 1, 2, 4, 3]
def baseStart_1385773 : Nat := 118140960795 + 1385773 * 2 ^ 59
def prefixEnd_1385773 : Nat := 4983230072969 + 3 ^ 40 * 1385773 * 2
def baseEnd_1385773 : Nat := 316252278676938617984201

theorem tailTrace_1385773 : CollatzResearch.WordTrace tailWord_1385773 prefixEnd_1385773 316252278676938617984201 := by
  unfold tailWord_1385773
  simp only [CollatzResearch.WordTrace]
  refine ⟨50543293608588567031153973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33695529072392378020769315 50543293608588567031153973)
  ·
    refine ⟨4738433775805178159170685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50543293608588567031153973 4738433775805178159170685)
    ·
      refine ⟨1776912665926941809689007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4738433775805178159170685 1776912665926941809689007)
      ·
        refine ⟨2665368998890412714533511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1776912665926941809689007 2665368998890412714533511)
        ·
          refine ⟨3998053498335619071800267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2665368998890412714533511 3998053498335619071800267)
          ·
            refine ⟨5997080247503428607700401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3998053498335619071800267 5997080247503428607700401)
            ·
              refine ⟨4497810185627571455775301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5997080247503428607700401 4497810185627571455775301)
              ·
                refine ⟨843339409805169647957869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4497810185627571455775301 843339409805169647957869)
                ·
                  refine ⟨316252278676938617984201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 843339409805169647957869 316252278676938617984201)
                  ·
                    rfl

theorem cell21_1385773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_1385773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1385773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1385773 prefixEnd_1385773 := by exact prefixLift 1385773
  have htrace : WordTrace (prefixWord ++ tailWord_1385773) baseStart_1385773 baseEnd_1385773 := by
    simpa [prefixWord, tailWord_1385773, baseEnd_1385773] using wordTrace_append hprefix tailTrace_1385773
  have hstable : (prefixWord ++ tailWord_1385773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385773).length < 2 ^ (prefixWord ++ tailWord_1385773).sum := by decide
  have hdescent : baseEnd_1385773 < baseStart_1385773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385829 : List Nat := [1, 3, 1, 3, 1, 2, 2, 4, 4]
def baseStart_1385829 : Nat := 118140960795 + 1385829 * 2 ^ 59
def prefixEnd_1385829 : Nat := 4983230072969 + 3 ^ 40 * 1385829 * 2
def baseEnd_1385829 : Nat := 316265058639894965050753

theorem tailTrace_1385829 : CollatzResearch.WordTrace tailWord_1385829 prefixEnd_1385829 316265058639894965050753 := by
  unfold tailWord_1385829
  simp only [CollatzResearch.WordTrace]
  refine ⟨50545336096385688595192541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33696890730923792396795027 50545336096385688595192541)
  ·
    refine ⟨18954501036144633223197203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50545336096385688595192541 18954501036144633223197203)
    ·
      refine ⟨28431751554216949834795805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18954501036144633223197203 28431751554216949834795805)
      ·
        refine ⟨10661906832831356188048427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28431751554216949834795805 10661906832831356188048427)
        ·
          refine ⟨15992860249247034282072641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10661906832831356188048427 15992860249247034282072641)
          ·
            refine ⟨11994645186935275711554481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15992860249247034282072641 11994645186935275711554481)
            ·
              refine ⟨8995983890201456783665861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11994645186935275711554481 8995983890201456783665861)
              ·
                refine ⟨1686746979412773146937349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8995983890201456783665861 1686746979412773146937349)
                ·
                  refine ⟨316265058639894965050753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1686746979412773146937349 316265058639894965050753)
                  ·
                    rfl

theorem cell21_1385829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 4, 4].length) (baseStart_1385829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1385829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1385829 prefixEnd_1385829 := by exact prefixLift 1385829
  have htrace : WordTrace (prefixWord ++ tailWord_1385829) baseStart_1385829 baseEnd_1385829 := by
    simpa [prefixWord, tailWord_1385829, baseEnd_1385829] using wordTrace_append hprefix tailTrace_1385829
  have hstable : (prefixWord ++ tailWord_1385829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385829).length < 2 ^ (prefixWord ++ tailWord_1385829).sum := by decide
  have hdescent : baseEnd_1385829 < baseStart_1385829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385832 : List Nat := [2, 1, 4, 2, 3, 2, 1, 1, 5]
def baseStart_1385832 : Nat := 118140960795 + 1385832 * 2 ^ 59
def prefixEnd_1385832 : Nat := 4983230072969 + 3 ^ 40 * 1385832 * 2
def baseEnd_1385832 : Nat := 316265743280767626500747

theorem tailTrace_1385832 : CollatzResearch.WordTrace tailWord_1385832 prefixEnd_1385832 316265743280767626500747 := by
  unfold tailWord_1385832
  simp only [CollatzResearch.WordTrace]
  refine ⟨25272722757687410053775875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33696963676916546738367833 25272722757687410053775875)
  ·
    refine ⟨37909084136531115080663813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25272722757687410053775875 37909084136531115080663813)
    ·
      refine ⟨7107953275599584077624465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37909084136531115080663813 7107953275599584077624465)
      ·
        refine ⟨5330964956699688058218349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7107953275599584077624465 5330964956699688058218349)
        ·
          refine ⟨1999111858762383021831881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5330964956699688058218349 1999111858762383021831881)
          ·
            refine ⟨1499333894071787266373911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1999111858762383021831881 1499333894071787266373911)
            ·
              refine ⟨2249000841107680899560867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1499333894071787266373911 2249000841107680899560867)
              ·
                refine ⟨3373501261661521349341301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2249000841107680899560867 3373501261661521349341301)
                ·
                  refine ⟨316265743280767626500747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3373501261661521349341301 316265743280767626500747)
                  ·
                    rfl

theorem cell21_1385832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 5].length) (baseStart_1385832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1385832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1385832 prefixEnd_1385832 := by exact prefixLift 1385832
  have htrace : WordTrace (prefixWord ++ tailWord_1385832) baseStart_1385832 baseEnd_1385832 := by
    simpa [prefixWord, tailWord_1385832, baseEnd_1385832] using wordTrace_append hprefix tailTrace_1385832
  have hstable : (prefixWord ++ tailWord_1385832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385832).length < 2 ^ (prefixWord ++ tailWord_1385832).sum := by decide
  have hdescent : baseEnd_1385832 < baseStart_1385832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385891 : List Nat := [1, 1, 1, 4, 1, 3, 3, 4, 3]
def baseStart_1385891 : Nat := 118140960795 + 1385891 * 2 ^ 59
def prefixEnd_1385891 : Nat := 4983230072969 + 3 ^ 40 * 1385891 * 2
def baseEnd_1385891 : Nat := 316279207884596635017293

theorem tailTrace_1385891 : CollatzResearch.WordTrace tailWord_1385891 prefixEnd_1385891 316279207884596635017293 := by
  unfold tailWord_1385891
  simp only [CollatzResearch.WordTrace]
  refine ⟨50547597422161073183949527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33698398281440715455966351 50547597422161073183949527)
  ·
    refine ⟨75821396133241609775924291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50547597422161073183949527 75821396133241609775924291)
    ·
      refine ⟨113732094199862414663886437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75821396133241609775924291 113732094199862414663886437)
      ·
        refine ⟨21324767662474202749478707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113732094199862414663886437 21324767662474202749478707)
        ·
          refine ⟨31987151493711304124218061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21324767662474202749478707 31987151493711304124218061)
          ·
            refine ⟨11995181810141739046581773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31987151493711304124218061 11995181810141739046581773)
            ·
              refine ⟨4498193178803152142468165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11995181810141739046581773 4498193178803152142468165)
              ·
                refine ⟨843411221025591026712781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4498193178803152142468165 843411221025591026712781)
                ·
                  refine ⟨316279207884596635017293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 843411221025591026712781 316279207884596635017293)
                  ·
                    rfl

theorem cell21_1385891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 4, 3].length) (baseStart_1385891 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1385891 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1385891 prefixEnd_1385891 := by exact prefixLift 1385891
  have htrace : WordTrace (prefixWord ++ tailWord_1385891) baseStart_1385891 baseEnd_1385891 := by
    simpa [prefixWord, tailWord_1385891, baseEnd_1385891] using wordTrace_append hprefix tailTrace_1385891
  have hstable : (prefixWord ++ tailWord_1385891).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385891).length < 2 ^ (prefixWord ++ tailWord_1385891).sum := by decide
  have hdescent : baseEnd_1385891 < baseStart_1385891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
