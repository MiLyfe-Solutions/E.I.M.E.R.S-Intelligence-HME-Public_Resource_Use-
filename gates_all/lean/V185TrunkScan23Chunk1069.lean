import V185TrunkScan23Chunk1068

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6327982 : List Nat := [4, 1, 4, 1, 2, 1, 1, 2, 2, 3, 2]
def baseStart_6327982 : Nat := 118140960795 + 6327982 * 2 ^ 59
def prefixEnd_6327982 : Nat := 4983230072969 + 3 ^ 40 * 6327982 * 2
def baseEnd_6327982 : Nat := 3249296338999565975023147

theorem tailTrace_6327982 : CollatzResearch.WordTrace tailWord_6327982 prefixEnd_6327982 3249296338999565975023147 := by
  unfold tailWord_6327982
  simp only [CollatzResearch.WordTrace]
  refine ⟨28850058070101177766142275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153866976373872948086092133 28850058070101177766142275)
  ·
    refine ⟨43275087105151766649213413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28850058070101177766142275 43275087105151766649213413)
    ·
      refine ⟨8114078832215956246727515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43275087105151766649213413 8114078832215956246727515)
      ·
        refine ⟨12171118248323934370091273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8114078832215956246727515 12171118248323934370091273)
        ·
          refine ⟨9128338686242950777568455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12171118248323934370091273 9128338686242950777568455)
          ·
            refine ⟨13692508029364426166352683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9128338686242950777568455 13692508029364426166352683)
            ·
              refine ⟨20538762044046639249529025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13692508029364426166352683 20538762044046639249529025)
              ·
                refine ⟨15404071533034979437146769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20538762044046639249529025 15404071533034979437146769)
                ·
                  refine ⟨11553053649776234577860077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15404071533034979437146769 11553053649776234577860077)
                  ·
                    refine ⟨4332395118666087966697529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11553053649776234577860077 4332395118666087966697529)
                    ·
                      refine ⟨3249296338999565975023147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4332395118666087966697529 3249296338999565975023147)
                      ·
                        rfl

theorem cell23_6327982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_6327982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327982 prefixEnd_6327982 := by exact prefixLift 6327982
  have htrace : WordTrace (prefixWord ++ tailWord_6327982) baseStart_6327982 baseEnd_6327982 := by
    simpa [prefixWord, tailWord_6327982, baseEnd_6327982] using wordTrace_append hprefix tailTrace_6327982
  have hstable : (prefixWord ++ tailWord_6327982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327982).length < 2 ^ (prefixWord ++ tailWord_6327982).sum := by decide
  have hdescent : baseEnd_6327982 < baseStart_6327982 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327989 : List Nat := [1, 3, 3, 3, 2, 1, 3, 2, 1, 1, 3]
def baseStart_6327989 : Nat := 118140960795 + 6327989 * 2 ^ 59
def prefixEnd_6327989 : Nat := 4983230072969 + 3 ^ 40 * 6327989 * 2
def baseEnd_6327989 : Nat := 3249299933364147447635615

theorem tailTrace_6327989 : CollatzResearch.WordTrace tailWord_6327989 prefixEnd_6327989 3249299933364147447635615 := by
  unfold tailWord_6327989
  simp only [CollatzResearch.WordTrace]
  refine ⟨230800719871784062324643021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153867146581189374883095347 230800719871784062324643021)
  ·
    refine ⟨86550269951919023371741133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230800719871784062324643021 86550269951919023371741133)
    ·
      refine ⟨32456351231969633764402925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86550269951919023371741133 32456351231969633764402925)
      ·
        refine ⟨12171131711988612661651097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32456351231969633764402925 12171131711988612661651097)
        ·
          refine ⟨9128348783991459496238323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12171131711988612661651097 9128348783991459496238323)
          ·
            refine ⟨13692523175987189244357485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9128348783991459496238323 13692523175987189244357485)
            ·
              refine ⟨5134696190995195966634057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13692523175987189244357485 5134696190995195966634057)
              ·
                refine ⟨3851022143246396974975543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5134696190995195966634057 3851022143246396974975543)
                ·
                  refine ⟨5776533214869595462463315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3851022143246396974975543 5776533214869595462463315)
                  ·
                    refine ⟨8664799822304393193694973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5776533214869595462463315 8664799822304393193694973)
                    ·
                      refine ⟨3249299933364147447635615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8664799822304393193694973 3249299933364147447635615)
                      ·
                        rfl

theorem cell23_6327989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_6327989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327989 prefixEnd_6327989 := by exact prefixLift 6327989
  have htrace : WordTrace (prefixWord ++ tailWord_6327989) baseStart_6327989 baseEnd_6327989 := by
    simpa [prefixWord, tailWord_6327989, baseEnd_6327989] using wordTrace_append hprefix tailTrace_6327989
  have hstable : (prefixWord ++ tailWord_6327989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327989).length < 2 ^ (prefixWord ++ tailWord_6327989).sum := by decide
  have hdescent : baseEnd_6327989 < baseStart_6327989 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327995 : List Nat := [1, 1, 1, 1, 1, 2, 3, 8, 1, 2, 2]
def baseStart_6327995 : Nat := 118140960795 + 6327995 * 2 ^ 59
def prefixEnd_6327995 : Nat := 4983230072969 + 3 ^ 40 * 6327995 * 2
def baseEnd_6327995 : Nat := 3249303014248074424160587

theorem tailTrace_6327995 : CollatzResearch.WordTrace tailWord_6327995 prefixEnd_6327995 3249303014248074424160587 := by
  unfold tailWord_6327995
  simp only [CollatzResearch.WordTrace]
  refine ⟨230800938709762325349361439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153867292473174883566240959 230800938709762325349361439)
  ·
    refine ⟨346201408064643488024042159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230800938709762325349361439 346201408064643488024042159)
    ·
      refine ⟨519302112096965232036063239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346201408064643488024042159 519302112096965232036063239)
      ·
        refine ⟨778953168145447848054094859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 519302112096965232036063239 778953168145447848054094859)
        ·
          refine ⟨1168429752218171772081142289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 778953168145447848054094859 1168429752218171772081142289)
          ·
            refine ⟨876322314163628829060856717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1168429752218171772081142289 876322314163628829060856717)
            ·
              refine ⟨328620867811360810897821269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 876322314163628829060856717 328620867811360810897821269)
              ·
                refine ⟨3851025794664384502708843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 328620867811360810897821269 3851025794664384502708843)
                ·
                  refine ⟨5776538691996576754063265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3851025794664384502708843 5776538691996576754063265)
                  ·
                    refine ⟨4332404018997432565547449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5776538691996576754063265 4332404018997432565547449)
                    ·
                      refine ⟨3249303014248074424160587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4332404018997432565547449 3249303014248074424160587)
                      ·
                        rfl

theorem cell23_6327995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8, 1, 2, 2].length) (baseStart_6327995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327995 prefixEnd_6327995 := by exact prefixLift 6327995
  have htrace : WordTrace (prefixWord ++ tailWord_6327995) baseStart_6327995 baseEnd_6327995 := by
    simpa [prefixWord, tailWord_6327995, baseEnd_6327995] using wordTrace_append hprefix tailTrace_6327995
  have hstable : (prefixWord ++ tailWord_6327995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327995).length < 2 ^ (prefixWord ++ tailWord_6327995).sum := by decide
  have hdescent : baseEnd_6327995 < baseStart_6327995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6328012 : List Nat := [2, 2, 1, 5, 3, 1, 1, 2, 1, 1, 4]
def baseStart_6328012 : Nat := 118140960795 + 6328012 * 2 ^ 59
def prefixEnd_6328012 : Nat := 4983230072969 + 3 ^ 40 * 6328012 * 2
def baseEnd_6328012 : Nat := 3249311743419200857648009

theorem tailTrace_6328012 : CollatzResearch.WordTrace tailWord_6328012 prefixEnd_6328012 3249311743419200857648009 := by
  unfold tailWord_6328012
  simp only [CollatzResearch.WordTrace]
  refine ⟨115400779375350368626365145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153867705833800491501820193 115400779375350368626365145)
  ·
    refine ⟨86550584531512776469773859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115400779375350368626365145 86550584531512776469773859)
    ·
      refine ⟨129825876797269164704660789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86550584531512776469773859 129825876797269164704660789)
      ·
        refine ⟨12171175949743984191061949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 129825876797269164704660789 12171175949743984191061949)
        ·
          refine ⟨4564190981153994071648231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12171175949743984191061949 4564190981153994071648231)
          ·
            refine ⟨6846286471730991107472347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4564190981153994071648231 6846286471730991107472347)
            ·
              refine ⟨10269429707596486661208521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6846286471730991107472347 10269429707596486661208521)
              ·
                refine ⟨7702072280697364995906391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10269429707596486661208521 7702072280697364995906391)
                ·
                  refine ⟨11553108421046047493859587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7702072280697364995906391 11553108421046047493859587)
                  ·
                    refine ⟨17329662631569071240789381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11553108421046047493859587 17329662631569071240789381)
                    ·
                      refine ⟨3249311743419200857648009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17329662631569071240789381 3249311743419200857648009)
                      ·
                        rfl

theorem cell23_6328012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_6328012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6328012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6328012 prefixEnd_6328012 := by exact prefixLift 6328012
  have htrace : WordTrace (prefixWord ++ tailWord_6328012) baseStart_6328012 baseEnd_6328012 := by
    simpa [prefixWord, tailWord_6328012, baseEnd_6328012] using wordTrace_append hprefix tailTrace_6328012
  have hstable : (prefixWord ++ tailWord_6328012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6328012).length < 2 ^ (prefixWord ++ tailWord_6328012).sum := by decide
  have hdescent : baseEnd_6328012 < baseStart_6328012 := by decide
  rcases family_descends (prefixWord ++ tailWord_6328012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6328045 : List Nat := [1, 5, 1, 2, 1, 2, 1, 4, 2, 1, 3]
def baseStart_6328045 : Nat := 118140960795 + 6328045 * 2 ^ 59
def prefixEnd_6328045 : Nat := 4983230072969 + 3 ^ 40 * 6328045 * 2
def baseEnd_6328045 : Nat := 3249328688280799228535357

theorem tailTrace_6328045 : CollatzResearch.WordTrace tailWord_6328045 prefixEnd_6328045 3249328688280799228535357 := by
  unfold tailWord_6328045
  simp only [CollatzResearch.WordTrace]
  refine ⟨230802762359581183888681589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153868508239720789259121059 230802762359581183888681589)
  ·
    refine ⟨21637758971210735989563899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 230802762359581183888681589 21637758971210735989563899)
    ·
      refine ⟨32456638456816103984345849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21637758971210735989563899 32456638456816103984345849)
      ·
        refine ⟨24342478842612077988259387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32456638456816103984345849 24342478842612077988259387)
        ·
          refine ⟨36513718263918116982389081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24342478842612077988259387 36513718263918116982389081)
          ·
            refine ⟨27385288697938587736791811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36513718263918116982389081 27385288697938587736791811)
            ·
              refine ⟨41077933046907881605187717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27385288697938587736791811 41077933046907881605187717)
              ·
                refine ⟨7702112446295227800972697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41077933046907881605187717 7702112446295227800972697)
                ·
                  refine ⟨5776584334721420850729523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7702112446295227800972697 5776584334721420850729523)
                  ·
                    refine ⟨8664876502082131276094285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5776584334721420850729523 8664876502082131276094285)
                    ·
                      refine ⟨3249328688280799228535357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8664876502082131276094285 3249328688280799228535357)
                      ·
                        rfl

theorem cell23_6328045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_6328045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6328045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6328045 prefixEnd_6328045 := by exact prefixLift 6328045
  have htrace : WordTrace (prefixWord ++ tailWord_6328045) baseStart_6328045 baseEnd_6328045 := by
    simpa [prefixWord, tailWord_6328045, baseEnd_6328045] using wordTrace_append hprefix tailTrace_6328045
  have hstable : (prefixWord ++ tailWord_6328045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6328045).length < 2 ^ (prefixWord ++ tailWord_6328045).sum := by decide
  have hdescent : baseEnd_6328045 < baseStart_6328045 := by decide
  rcases family_descends (prefixWord ++ tailWord_6328045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6328064 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 6]
def baseStart_6328064 : Nat := 118140960795 + 6328064 * 2 ^ 59
def prefixEnd_6328064 : Nat := 4983230072969 + 3 ^ 40 * 6328064 * 2
def baseEnd_6328064 : Nat := 3249338444413234654197769

theorem tailTrace_6328064 : CollatzResearch.WordTrace tailWord_6328064 prefixEnd_6328064 3249338444413234654197769 := by
  unfold tailWord_6328064
  simp only [CollatzResearch.WordTrace]
  refine ⟨115401727673256175066811623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153868970231008233422415497 115401727673256175066811623)
  ·
    refine ⟨173102591509884262600217435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115401727673256175066811623 173102591509884262600217435)
    ·
      refine ⟨259653887264826393900326153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173102591509884262600217435 259653887264826393900326153)
      ·
        refine ⟨194740415448619795425244615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259653887264826393900326153 194740415448619795425244615)
        ·
          refine ⟨292110623172929693137866923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194740415448619795425244615 292110623172929693137866923)
          ·
            refine ⟨438165934759394539706800385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292110623172929693137866923 438165934759394539706800385)
            ·
              refine ⟨328624451069545904780100289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 438165934759394539706800385 328624451069545904780100289)
              ·
                refine ⟨246468338302159428585075217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 328624451069545904780100289 246468338302159428585075217)
                ·
                  refine ⟨184851253726619571438806413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 246468338302159428585075217 184851253726619571438806413)
                  ·
                    refine ⟨69319220147482339289552405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 184851253726619571438806413 69319220147482339289552405)
                    ·
                      refine ⟨3249338444413234654197769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69319220147482339289552405 3249338444413234654197769)
                      ·
                        rfl

theorem cell23_6328064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_6328064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6328064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6328064 prefixEnd_6328064 := by exact prefixLift 6328064
  have htrace : WordTrace (prefixWord ++ tailWord_6328064) baseStart_6328064 baseEnd_6328064 := by
    simpa [prefixWord, tailWord_6328064, baseEnd_6328064] using wordTrace_append hprefix tailTrace_6328064
  have hstable : (prefixWord ++ tailWord_6328064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6328064).length < 2 ^ (prefixWord ++ tailWord_6328064).sum := by decide
  have hdescent : baseEnd_6328064 < baseStart_6328064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6328064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6328108 : List Nat := [2, 2, 1, 1, 1, 5, 2, 4, 5]
def baseStart_6328108 : Nat := 118140960795 + 6328108 * 2 ^ 59
def prefixEnd_6328108 : Nat := 4983230072969 + 3 ^ 40 * 6328108 * 2
def baseEnd_6328108 : Nat := 361040115284670275783063

theorem tailTrace_6328108 : CollatzResearch.WordTrace tailWord_6328108 prefixEnd_6328108 361040115284670275783063 := by
  unfold tailWord_6328108
  simp only [CollatzResearch.WordTrace]
  refine ⟨115402530079176472824112489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153870040105568630432149985 115402530079176472824112489)
  ·
    refine ⟨86551897559382354618084367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115402530079176472824112489 86551897559382354618084367)
    ·
      refine ⟨129827846339073531927126551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86551897559382354618084367 129827846339073531927126551)
      ·
        refine ⟨194741769508610297890689827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129827846339073531927126551 194741769508610297890689827)
        ·
          refine ⟨292112654262915446836034741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194741769508610297890689827 292112654262915446836034741)
          ·
            refine ⟨27385561337148323140878257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 292112654262915446836034741 27385561337148323140878257)
            ·
              refine ⟨20539171002861242355658693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27385561337148323140878257 20539171002861242355658693)
              ·
                refine ⟨3851094563036482941686005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20539171002861242355658693 3851094563036482941686005)
                ·
                  refine ⟨361040115284670275783063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3851094563036482941686005 361040115284670275783063)
                  ·
                    rfl

theorem cell23_6328108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 4, 5].length) (baseStart_6328108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6328108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6328108 prefixEnd_6328108 := by exact prefixLift 6328108
  have htrace : WordTrace (prefixWord ++ tailWord_6328108) baseStart_6328108 baseEnd_6328108 := by
    simpa [prefixWord, tailWord_6328108, baseEnd_6328108] using wordTrace_append hprefix tailTrace_6328108
  have hstable : (prefixWord ++ tailWord_6328108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6328108).length < 2 ^ (prefixWord ++ tailWord_6328108).sum := by decide
  have hdescent : baseEnd_6328108 < baseStart_6328108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6328108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6328178 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 6, 2, 3]
def baseStart_6328178 : Nat := 118140960795 + 6328178 * 2 ^ 59
def prefixEnd_6328178 : Nat := 4983230072969 + 3 ^ 40 * 6328178 * 2
def baseEnd_6328178 : Nat := 3249396981207847208172245

theorem tailTrace_6328178 : CollatzResearch.WordTrace tailWord_6328178 prefixEnd_6328178 3249396981207847208172245 := by
  unfold tailWord_6328178
  simp only [CollatzResearch.WordTrace]
  refine ⟨57701903317024836900818297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153871742178732898402182125 57701903317024836900818297)
  ·
    refine ⟨43276427487768627675613723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57701903317024836900818297 43276427487768627675613723)
    ·
      refine ⟨64914641231652941513420585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43276427487768627675613723 64914641231652941513420585)
      ·
        refine ⟨48685980923739706135065439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64914641231652941513420585 48685980923739706135065439)
        ·
          refine ⟨73028971385609559202598159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48685980923739706135065439 73028971385609559202598159)
          ·
            refine ⟨109543457078414338803897239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73028971385609559202598159 109543457078414338803897239)
            ·
              refine ⟨164315185617621508205845859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109543457078414338803897239 164315185617621508205845859)
              ·
                refine ⟨246472778426432262308768789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164315185617621508205845859 246472778426432262308768789)
                ·
                  refine ⟨11553411488739012295723537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 246472778426432262308768789 11553411488739012295723537)
                  ·
                    refine ⟨8665058616554259221792653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11553411488739012295723537 8665058616554259221792653)
                    ·
                      refine ⟨3249396981207847208172245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8665058616554259221792653 3249396981207847208172245)
                      ·
                        rfl

theorem cell23_6328178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_6328178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6328178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6328178 prefixEnd_6328178 := by exact prefixLift 6328178
  have htrace : WordTrace (prefixWord ++ tailWord_6328178) baseStart_6328178 baseEnd_6328178 := by
    simpa [prefixWord, tailWord_6328178, baseEnd_6328178] using wordTrace_append hprefix tailTrace_6328178
  have hstable : (prefixWord ++ tailWord_6328178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6328178).length < 2 ^ (prefixWord ++ tailWord_6328178).sum := by decide
  have hdescent : baseEnd_6328178 < baseStart_6328178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6328178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6328195 : List Nat := [1, 1, 1, 3, 4, 3, 2, 1, 2, 2, 3]
def baseStart_6328195 : Nat := 118140960795 + 6328195 * 2 ^ 59
def prefixEnd_6328195 : Nat := 4983230072969 + 3 ^ 40 * 6328195 * 2
def baseEnd_6328195 : Nat := 3249405710378973641659667

theorem tailTrace_6328195 : CollatzResearch.WordTrace tailWord_6328195 prefixEnd_6328195 3249405710378973641659667 := by
  unfold tailWord_6328195
  simp only [CollatzResearch.WordTrace]
  refine ⟨230808233309037759506642039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153872155539358506337761359 230808233309037759506642039)
  ·
    refine ⟨346212349963556639259963059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230808233309037759506642039 346212349963556639259963059)
    ·
      refine ⟨519318524945334958889944589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346212349963556639259963059 519318524945334958889944589)
      ·
        refine ⟨194744446854500609583729221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 519318524945334958889944589 194744446854500609583729221)
        ·
          refine ⟨36514583785218864296949229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194744446854500609583729221 36514583785218864296949229)
          ·
            refine ⟨13692968919457074111355961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36514583785218864296949229 13692968919457074111355961)
            ·
              refine ⟨10269726689592805583516971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13692968919457074111355961 10269726689592805583516971)
              ·
                refine ⟨15404590034389208375275457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10269726689592805583516971 15404590034389208375275457)
                ·
                  refine ⟨11553442525791906281456593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15404590034389208375275457 11553442525791906281456593)
                  ·
                    refine ⟨8665081894343929711092445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11553442525791906281456593 8665081894343929711092445)
                    ·
                      refine ⟨3249405710378973641659667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8665081894343929711092445 3249405710378973641659667)
                      ·
                        rfl

theorem cell23_6328195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 2, 2, 3].length) (baseStart_6328195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6328195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6328195 prefixEnd_6328195 := by exact prefixLift 6328195
  have htrace : WordTrace (prefixWord ++ tailWord_6328195) baseStart_6328195 baseEnd_6328195 := by
    simpa [prefixWord, tailWord_6328195, baseEnd_6328195] using wordTrace_append hprefix tailTrace_6328195
  have hstable : (prefixWord ++ tailWord_6328195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6328195).length < 2 ^ (prefixWord ++ tailWord_6328195).sum := by decide
  have hdescent : baseEnd_6328195 < baseStart_6328195 := by decide
  rcases family_descends (prefixWord ++ tailWord_6328195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6328228 : List Nat := [2, 3, 1, 2, 1, 3, 1, 2, 3, 5]
def baseStart_6328228 : Nat := 118140960795 + 6328228 * 2 ^ 59
def prefixEnd_6328228 : Nat := 4983230072969 + 3 ^ 40 * 6328228 * 2
def baseEnd_6328228 : Nat := 1083140885080190670849005

theorem tailTrace_6328228 : CollatzResearch.WordTrace tailWord_6328228 prefixEnd_6328228 1083140885080190670849005 := by
  unfold tailWord_6328228
  simp only [CollatzResearch.WordTrace]
  refine ⟨115404718458959103071296669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153872957945278804095062225 115404718458959103071296669)
  ·
    refine ⟨43276769422109663651736251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115404718458959103071296669 43276769422109663651736251)
    ·
      refine ⟨64915154133164495477604377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43276769422109663651736251 64915154133164495477604377)
      ·
        refine ⟨48686365599873371608203283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64915154133164495477604377 48686365599873371608203283)
        ·
          refine ⟨73029548399810057412304925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48686365599873371608203283 73029548399810057412304925)
          ·
            refine ⟨27386080649928771529614347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73029548399810057412304925 27386080649928771529614347)
            ·
              refine ⟨41079120974893157294421521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27386080649928771529614347 41079120974893157294421521)
              ·
                refine ⟨30809340731169867970816141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41079120974893157294421521 30809340731169867970816141)
                ·
                  refine ⟨11553502774188700489056053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30809340731169867970816141 11553502774188700489056053)
                  ·
                    refine ⟨1083140885080190670849005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11553502774188700489056053 1083140885080190670849005)
                    ·
                      rfl

theorem cell23_6328228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_6328228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6328228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6328228 prefixEnd_6328228 := by exact prefixLift 6328228
  have htrace : WordTrace (prefixWord ++ tailWord_6328228) baseStart_6328228 baseEnd_6328228 := by
    simpa [prefixWord, tailWord_6328228, baseEnd_6328228] using wordTrace_append hprefix tailTrace_6328228
  have hstable : (prefixWord ++ tailWord_6328228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6328228).length < 2 ^ (prefixWord ++ tailWord_6328228).sum := by decide
  have hdescent : baseEnd_6328228 < baseStart_6328228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6328228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6328248 : List Nat := [2, 1, 2, 1, 2, 3, 1, 3, 3, 1, 4]
def baseStart_6328248 : Nat := 118140960795 + 6328248 * 2 ^ 59
def prefixEnd_6328248 : Nat := 4983230072969 + 3 ^ 40 * 6328248 * 2
def baseEnd_6328248 : Nat := 3249432924853661934296923

theorem tailTrace_6328248 : CollatzResearch.WordTrace tailWord_6328248 prefixEnd_6328248 3249432924853661934296923 := by
  unfold tailWord_6328248
  simp only [CollatzResearch.WordTrace]
  refine ⟨115405083188922874779160699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153873444251897166372214265 115405083188922874779160699)
  ·
    refine ⟨173107624783384312168741049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115405083188922874779160699 173107624783384312168741049)
    ·
      refine ⟨129830718587538234126555787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173107624783384312168741049 129830718587538234126555787)
      ·
        refine ⟨194746077881307351189833681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129830718587538234126555787 194746077881307351189833681)
        ·
          refine ⟨146059558410980513392375261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194746077881307351189833681 146059558410980513392375261)
          ·
            refine ⟨54772334404117692522140723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146059558410980513392375261 54772334404117692522140723)
            ·
              refine ⟨82158501606176538783211085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54772334404117692522140723 82158501606176538783211085)
              ·
                refine ⟨30809438102316202043704157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82158501606176538783211085 30809438102316202043704157)
                ·
                  refine ⟨11553539288368575766389059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30809438102316202043704157 11553539288368575766389059)
                  ·
                    refine ⟨17330308932552863649583589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11553539288368575766389059 17330308932552863649583589)
                    ·
                      refine ⟨3249432924853661934296923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17330308932552863649583589 3249432924853661934296923)
                      ·
                        rfl

theorem cell23_6328248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 3, 1, 4].length) (baseStart_6328248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6328248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6328248 prefixEnd_6328248 := by exact prefixLift 6328248
  have htrace : WordTrace (prefixWord ++ tailWord_6328248) baseStart_6328248 baseEnd_6328248 := by
    simpa [prefixWord, tailWord_6328248, baseEnd_6328248] using wordTrace_append hprefix tailTrace_6328248
  have hstable : (prefixWord ++ tailWord_6328248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6328248).length < 2 ^ (prefixWord ++ tailWord_6328248).sum := by decide
  have hdescent : baseEnd_6328248 < baseStart_6328248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6328248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6328271 : List Nat := [1, 1, 2, 1, 1, 5, 12]
def baseStart_6328271 : Nat := 118140960795 + 6328271 * 2 ^ 59
def prefixEnd_6328271 : Nat := 4983230072969 + 3 ^ 40 * 6328271 * 2
def baseEnd_6328271 : Nat := 40116601665539695608757

theorem tailTrace_6328271 : CollatzResearch.WordTrace tailWord_6328271 prefixEnd_6328271 40116601665539695608757 := by
  unfold tailWord_6328271
  simp only [CollatzResearch.WordTrace]
  refine ⟨230811005256762424486408667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153874003504508282990939111 230811005256762424486408667)
  ·
    refine ⟨346216507885143636729613001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230811005256762424486408667 346216507885143636729613001)
    ·
      refine ⟨259662380913857727547209751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346216507885143636729613001 259662380913857727547209751)
      ·
        refine ⟨389493571370786591320814627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259662380913857727547209751 389493571370786591320814627)
        ·
          refine ⟨584240357056179886981221941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389493571370786591320814627 584240357056179886981221941)
          ·
            refine ⟨54772533474016864404489557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 584240357056179886981221941 54772533474016864404489557)
            ·
              refine ⟨40116601665539695608757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 54772533474016864404489557 40116601665539695608757)
              ·
                rfl

theorem cell23_6328271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 12].length) (baseStart_6328271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6328271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6328271 prefixEnd_6328271 := by exact prefixLift 6328271
  have htrace : WordTrace (prefixWord ++ tailWord_6328271) baseStart_6328271 baseEnd_6328271 := by
    simpa [prefixWord, tailWord_6328271, baseEnd_6328271] using wordTrace_append hprefix tailTrace_6328271
  have hstable : (prefixWord ++ tailWord_6328271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6328271).length < 2 ^ (prefixWord ++ tailWord_6328271).sum := by decide
  have hdescent : baseEnd_6328271 < baseStart_6328271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6328271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6328292 : List Nat := [2, 3, 1, 1, 1, 1, 7, 1, 2, 4]
def baseStart_6328292 : Nat := 118140960795 + 6328292 * 2 ^ 59
def prefixEnd_6328292 : Nat := 4983230072969 + 3 ^ 40 * 6328292 * 2
def baseEnd_6328292 : Nat := 1083151839334153254048907

theorem tailTrace_6328292 : CollatzResearch.WordTrace tailWord_6328292 prefixEnd_6328292 1083151839334153254048907 := by
  unfold tailWord_6328292
  simp only [CollatzResearch.WordTrace]
  refine ⟨115405885594843172536461565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153874514126457563381948753 115405885594843172536461565)
  ·
    refine ⟨43277207098066189701173087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115405885594843172536461565 43277207098066189701173087)
    ·
      refine ⟨64915810647099284551759631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43277207098066189701173087 64915810647099284551759631)
      ·
        refine ⟨97373715970648926827639447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64915810647099284551759631 97373715970648926827639447)
        ·
          refine ⟨146060573955973390241459171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97373715970648926827639447 146060573955973390241459171)
          ·
            refine ⟨219090860933960085362188757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146060573955973390241459171 219090860933960085362188757)
            ·
              refine ⟨5134942053139689500676299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 219090860933960085362188757 5134942053139689500676299)
              ·
                refine ⟨7702413079709534251014449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5134942053139689500676299 7702413079709534251014449)
                ·
                  refine ⟨5776809809782150688260837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7702413079709534251014449 5776809809782150688260837)
                  ·
                    refine ⟨1083151839334153254048907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5776809809782150688260837 1083151839334153254048907)
                    ·
                      rfl

theorem cell23_6328292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 1, 2, 4].length) (baseStart_6328292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6328292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6328292 prefixEnd_6328292 := by exact prefixLift 6328292
  have htrace : WordTrace (prefixWord ++ tailWord_6328292) baseStart_6328292 baseEnd_6328292 := by
    simpa [prefixWord, tailWord_6328292, baseEnd_6328292] using wordTrace_append hprefix tailTrace_6328292
  have hstable : (prefixWord ++ tailWord_6328292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6328292).length < 2 ^ (prefixWord ++ tailWord_6328292).sum := by decide
  have hdescent : baseEnd_6328292 < baseStart_6328292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6328292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6328295 : List Nat := [1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 6]
def baseStart_6328295 : Nat := 118140960795 + 6328295 * 2 ^ 59
def prefixEnd_6328295 : Nat := 4983230072969 + 3 ^ 40 * 6328295 * 2
def baseEnd_6328295 : Nat := 3249457058444423250409207

theorem tailTrace_6328295 : CollatzResearch.WordTrace tailWord_6328295 prefixEnd_6328295 3249457058444423250409207 := by
  unfold tailWord_6328295
  simp only [CollatzResearch.WordTrace]
  refine ⟨230811880608675476585282339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153874587072450317723521559 230811880608675476585282339)
  ·
    refine ⟨346217820913013214877923509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230811880608675476585282339 346217820913013214877923509)
    ·
      refine ⟨32457920710594988894805329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 346217820913013214877923509 32457920710594988894805329)
      ·
        refine ⟨24343440532946241671103997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32457920710594988894805329 24343440532946241671103997)
        ·
          refine ⟨9128790199854840626663999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24343440532946241671103997 9128790199854840626663999)
          ·
            refine ⟨13693185299782260939995999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9128790199854840626663999 13693185299782260939995999)
            ·
              refine ⟨20539777949673391409993999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13693185299782260939995999 20539777949673391409993999)
              ·
                refine ⟨30809666924510087114990999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20539777949673391409993999 30809666924510087114990999)
                ·
                  refine ⟨46214500386765130672486499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30809666924510087114990999 46214500386765130672486499)
                  ·
                    refine ⟨69321750580147696008729749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46214500386765130672486499 69321750580147696008729749)
                    ·
                      refine ⟨3249457058444423250409207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69321750580147696008729749 3249457058444423250409207)
                      ·
                        rfl

theorem cell23_6328295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_6328295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6328295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6328295 prefixEnd_6328295 := by exact prefixLift 6328295
  have htrace : WordTrace (prefixWord ++ tailWord_6328295) baseStart_6328295 baseEnd_6328295 := by
    simpa [prefixWord, tailWord_6328295, baseEnd_6328295] using wordTrace_append hprefix tailTrace_6328295
  have hstable : (prefixWord ++ tailWord_6328295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6328295).length < 2 ^ (prefixWord ++ tailWord_6328295).sum := by decide
  have hdescent : baseEnd_6328295 < baseStart_6328295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6328295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6328302 : List Nat := [4, 1, 2, 1, 3, 1, 1, 4, 1, 2, 3]
def baseStart_6328302 : Nat := 118140960795 + 6328302 * 2 ^ 59
def prefixEnd_6328302 : Nat := 4983230072969 + 3 ^ 40 * 6328302 * 2
def baseEnd_6328302 : Nat := 3249460652809004723021675

theorem tailTrace_6328302 : CollatzResearch.WordTrace tailWord_6328302 prefixEnd_6328302 3249460652809004723021675 := by
  unfold tailWord_6328302
  simp only [CollatzResearch.WordTrace]
  refine ⟨28851516989956264597598395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153874757279766744520524773 28851516989956264597598395)
  ·
    refine ⟨43277275484934396896397593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28851516989956264597598395 43277275484934396896397593)
    ·
      refine ⟨32457956613700797672298195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43277275484934396896397593 32457956613700797672298195)
      ·
        refine ⟨48686934920551196508447293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32457956613700797672298195 48686934920551196508447293)
        ·
          refine ⟨18257600595206698690667735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48686934920551196508447293 18257600595206698690667735)
          ·
            refine ⟨27386400892810048036001603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18257600595206698690667735 27386400892810048036001603)
            ·
              refine ⟨41079601339215072054002405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27386400892810048036001603 41079601339215072054002405)
              ·
                refine ⟨7702425251102826010125451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41079601339215072054002405 7702425251102826010125451)
                ·
                  refine ⟨11553637876654239015188177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7702425251102826010125451 11553637876654239015188177)
                  ·
                    refine ⟨8665228407490679261391133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11553637876654239015188177 8665228407490679261391133)
                    ·
                      refine ⟨3249460652809004723021675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8665228407490679261391133 3249460652809004723021675)
                      ·
                        rfl

theorem cell23_6328302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_6328302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6328302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6328302 prefixEnd_6328302 := by exact prefixLift 6328302
  have htrace : WordTrace (prefixWord ++ tailWord_6328302) baseStart_6328302 baseEnd_6328302 := by
    simpa [prefixWord, tailWord_6328302, baseEnd_6328302] using wordTrace_append hprefix tailTrace_6328302
  have hstable : (prefixWord ++ tailWord_6328302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6328302).length < 2 ^ (prefixWord ++ tailWord_6328302).sum := by decide
  have hdescent : baseEnd_6328302 < baseStart_6328302 := by decide
  rcases family_descends (prefixWord ++ tailWord_6328302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6328315 : List Nat := [1, 1, 1, 1, 1, 3, 5, 2, 4, 1, 3]
def baseStart_6328315 : Nat := 118140960795 + 6328315 * 2 ^ 59
def prefixEnd_6328315 : Nat := 4983230072969 + 3 ^ 40 * 6328315 * 2
def baseEnd_6328315 : Nat := 3249467328057513172159115

theorem tailTrace_6328315 : CollatzResearch.WordTrace tailWord_6328315 prefixEnd_6328315 3249467328057513172159115 := by
  unfold tailWord_6328315
  simp only [CollatzResearch.WordTrace]
  refine ⟨230812610068603020001010399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153875073379068680000673599 230812610068603020001010399)
  ·
    refine ⟨346218915102904530001515599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230812610068603020001010399 346218915102904530001515599)
    ·
      refine ⟨519328372654356795002273399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346218915102904530001515599 519328372654356795002273399)
      ·
        refine ⟨778992558981535192503410099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 519328372654356795002273399 778992558981535192503410099)
        ·
          refine ⟨1168488838472302788755115149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 778992558981535192503410099 1168488838472302788755115149)
          ·
            refine ⟨438183314427113545783168181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1168488838472302788755115149 438183314427113545783168181)
            ·
              refine ⟨41079685727541894917172017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 438183314427113545783168181 41079685727541894917172017)
              ·
                refine ⟨30809764295656421187879013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41079685727541894917172017 30809764295656421187879013)
                ·
                  refine ⟨5776830805435578972727315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30809764295656421187879013 5776830805435578972727315)
                  ·
                    refine ⟨8665246208153368459090973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5776830805435578972727315 8665246208153368459090973)
                    ·
                      refine ⟨3249467328057513172159115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8665246208153368459090973 3249467328057513172159115)
                      ·
                        rfl

theorem cell23_6328315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 4, 1, 3].length) (baseStart_6328315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6328315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6328315 prefixEnd_6328315 := by exact prefixLift 6328315
  have htrace : WordTrace (prefixWord ++ tailWord_6328315) baseStart_6328315 baseEnd_6328315 := by
    simpa [prefixWord, tailWord_6328315, baseEnd_6328315] using wordTrace_append hprefix tailTrace_6328315
  have hstable : (prefixWord ++ tailWord_6328315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6328315).length < 2 ^ (prefixWord ++ tailWord_6328315).sum := by decide
  have hdescent : baseEnd_6328315 < baseStart_6328315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6328315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6328328 : List Nat := [2, 1, 3, 2, 1, 2, 1, 2, 2, 2, 5]
def baseStart_6328328 : Nat := 118140960795 + 6328328 * 2 ^ 59
def prefixEnd_6328328 : Nat := 4983230072969 + 3 ^ 40 * 6328328 * 2
def baseEnd_6328328 : Nat := 3249474003306021621296555

theorem tailTrace_6328328 : CollatzResearch.WordTrace tailWord_6328328 prefixEnd_6328328 3249474003306021621296555 := by
  unfold tailWord_6328328
  simp only [CollatzResearch.WordTrace]
  refine ⟨115406542108777961610616819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153875389478370615480822425 115406542108777961610616819)
  ·
    refine ⟨173109813163166942415925229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115406542108777961610616819 173109813163166942415925229)
    ·
      refine ⟨64916179936187603405971961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173109813163166942415925229 64916179936187603405971961)
      ·
        refine ⟨48687134952140702554478971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64916179936187603405971961 48687134952140702554478971)
        ·
          refine ⟨73030702428211053831718457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48687134952140702554478971 73030702428211053831718457)
          ·
            refine ⟨54773026821158290373788843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73030702428211053831718457 54773026821158290373788843)
            ·
              refine ⟨82159540231737435560683265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54773026821158290373788843 82159540231737435560683265)
              ·
                refine ⟨61619655173803076670512449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82159540231737435560683265 61619655173803076670512449)
                ·
                  refine ⟨46214741380352307502884337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61619655173803076670512449 46214741380352307502884337)
                  ·
                    refine ⟨34661056035264230627163253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46214741380352307502884337 34661056035264230627163253)
                    ·
                      refine ⟨3249474003306021621296555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34661056035264230627163253 3249474003306021621296555)
                      ·
                        rfl

theorem cell23_6328328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_6328328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6328328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6328328 prefixEnd_6328328 := by exact prefixLift 6328328
  have htrace : WordTrace (prefixWord ++ tailWord_6328328) baseStart_6328328 baseEnd_6328328 := by
    simpa [prefixWord, tailWord_6328328, baseEnd_6328328] using wordTrace_append hprefix tailTrace_6328328
  have hstable : (prefixWord ++ tailWord_6328328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6328328).length < 2 ^ (prefixWord ++ tailWord_6328328).sum := by decide
  have hdescent : baseEnd_6328328 < baseStart_6328328 := by decide
  rcases family_descends (prefixWord ++ tailWord_6328328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6328332 : List Nat := [2, 2, 1, 2, 3, 1, 2, 4, 2, 1, 3]
def baseStart_6328332 : Nat := 118140960795 + 6328332 * 2 ^ 59
def prefixEnd_6328332 : Nat := 4983230072969 + 3 ^ 40 * 6328332 * 2
def baseEnd_6328332 : Nat := 3249476057228639605646537

theorem tailTrace_6328332 : CollatzResearch.WordTrace tailWord_6328332 prefixEnd_6328332 3249476057228639605646537 := by
  unfold tailWord_6328332
  simp only [CollatzResearch.WordTrace]
  refine ⟨115406615054770715952189625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153875486739694287936252833 115406615054770715952189625)
  ·
    refine ⟨86554961291078036964142219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115406615054770715952189625 86554961291078036964142219)
    ·
      refine ⟨129832441936617055446213329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86554961291078036964142219 129832441936617055446213329)
      ·
        refine ⟨97374331452462791584659997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129832441936617055446213329 97374331452462791584659997)
        ·
          refine ⟨36515374294673546844247499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97374331452462791584659997 36515374294673546844247499)
          ·
            refine ⟨54773061442010320266371249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36515374294673546844247499 54773061442010320266371249)
            ·
              refine ⟨41079796081507740199778437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54773061442010320266371249 41079796081507740199778437)
              ·
                refine ⟨7702461765282701287458457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41079796081507740199778437 7702461765282701287458457)
                ·
                  refine ⟨5776846323962025965593843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7702461765282701287458457 5776846323962025965593843)
                  ·
                    refine ⟨8665269485943038948390765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5776846323962025965593843 8665269485943038948390765)
                    ·
                      refine ⟨3249476057228639605646537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8665269485943038948390765 3249476057228639605646537)
                      ·
                        rfl

theorem cell23_6328332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 4, 2, 1, 3].length) (baseStart_6328332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6328332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6328332 prefixEnd_6328332 := by exact prefixLift 6328332
  have htrace : WordTrace (prefixWord ++ tailWord_6328332) baseStart_6328332 baseEnd_6328332 := by
    simpa [prefixWord, tailWord_6328332, baseEnd_6328332] using wordTrace_append hprefix tailTrace_6328332
  have hstable : (prefixWord ++ tailWord_6328332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6328332).length < 2 ^ (prefixWord ++ tailWord_6328332).sum := by decide
  have hdescent : baseEnd_6328332 < baseStart_6328332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6328332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6328349 : List Nat := [1, 4, 2, 2, 2, 2, 1, 3, 2, 1, 3]
def baseStart_6328349 : Nat := 118140960795 + 6328349 * 2 ^ 59
def prefixEnd_6328349 : Nat := 4983230072969 + 3 ^ 40 * 6328349 * 2
def baseEnd_6328349 : Nat := 3249484786399766039133959

theorem tailTrace_6328349 : CollatzResearch.WordTrace tailWord_6328349 prefixEnd_6328349 3249484786399766039133959 := by
  unfold tailWord_6328349
  simp only [CollatzResearch.WordTrace]
  refine ⟨230813850150479843807748101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153875900100319895871832067 230813850150479843807748101)
  ·
    refine ⟨43277596903214970713952769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230813850150479843807748101 43277596903214970713952769)
    ·
      refine ⟨32458197677411228035464577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43277596903214970713952769 32458197677411228035464577)
      ·
        refine ⟨24343648258058421026598433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32458197677411228035464577 24343648258058421026598433)
        ·
          refine ⟨18257736193543815769948825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24343648258058421026598433 18257736193543815769948825)
          ·
            refine ⟨13693302145157861827461619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18257736193543815769948825 13693302145157861827461619)
            ·
              refine ⟨20539953217736792741192429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13693302145157861827461619 20539953217736792741192429)
              ·
                refine ⟨7702482456651297277947161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20539953217736792741192429 7702482456651297277947161)
                ·
                  refine ⟨5776861842488472958460371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7702482456651297277947161 5776861842488472958460371)
                  ·
                    refine ⟨8665292763732709437690557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5776861842488472958460371 8665292763732709437690557)
                    ·
                      refine ⟨3249484786399766039133959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8665292763732709437690557 3249484786399766039133959)
                      ·
                        rfl

theorem cell23_6328349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_6328349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6328349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6328349 prefixEnd_6328349 := by exact prefixLift 6328349
  have htrace : WordTrace (prefixWord ++ tailWord_6328349) baseStart_6328349 baseEnd_6328349 := by
    simpa [prefixWord, tailWord_6328349, baseEnd_6328349] using wordTrace_append hprefix tailTrace_6328349
  have hstable : (prefixWord ++ tailWord_6328349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6328349).length < 2 ^ (prefixWord ++ tailWord_6328349).sum := by decide
  have hdescent : baseEnd_6328349 < baseStart_6328349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6328349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6328376 : List Nat := [2, 1, 2, 1, 6, 1, 3, 1, 1, 3, 2]
def baseStart_6328376 : Nat := 118140960795 + 6328376 * 2 ^ 59
def prefixEnd_6328376 : Nat := 4983230072969 + 3 ^ 40 * 6328376 * 2
def baseEnd_6328376 : Nat := 3249498650377437433496335

theorem tailTrace_6328376 : CollatzResearch.WordTrace tailWord_6328376 prefixEnd_6328376 3249498650377437433496335 := by
  unfold tailWord_6328376
  simp only [CollatzResearch.WordTrace]
  refine ⟨115407417460691013709490491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153876556614254684945987321 115407417460691013709490491)
  ·
    refine ⟨173111126191036520564235737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115407417460691013709490491 173111126191036520564235737)
    ·
      refine ⟨129833344643277390423176803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173111126191036520564235737 129833344643277390423176803)
      ·
        refine ⟨194750016964916085634765205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129833344643277390423176803 194750016964916085634765205)
        ·
          refine ⟨9128907045230441514129619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 194750016964916085634765205 9128907045230441514129619)
          ·
            refine ⟨13693360567845662271194429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9128907045230441514129619 13693360567845662271194429)
            ·
              refine ⟨5135010212942123351697911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13693360567845662271194429 5135010212942123351697911)
              ·
                refine ⟨7702515319413185027546867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5135010212942123351697911 7702515319413185027546867)
                ·
                  refine ⟨11553772979119777541320301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7702515319413185027546867 11553772979119777541320301)
                  ·
                    refine ⟨4332664867169916577995113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11553772979119777541320301 4332664867169916577995113)
                    ·
                      refine ⟨3249498650377437433496335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4332664867169916577995113 3249498650377437433496335)
                      ·
                        rfl

theorem cell23_6328376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 1, 1, 3, 2].length) (baseStart_6328376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6328376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6328376 prefixEnd_6328376 := by exact prefixLift 6328376
  have htrace : WordTrace (prefixWord ++ tailWord_6328376) baseStart_6328376 baseEnd_6328376 := by
    simpa [prefixWord, tailWord_6328376, baseEnd_6328376] using wordTrace_append hprefix tailTrace_6328376
  have hstable : (prefixWord ++ tailWord_6328376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6328376).length < 2 ^ (prefixWord ++ tailWord_6328376).sum := by decide
  have hdescent : baseEnd_6328376 < baseStart_6328376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6328376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6328395 : List Nat := [1, 1, 1, 1, 3, 1, 2, 8, 5]
def baseStart_6328395 : Nat := 118140960795 + 6328395 * 2 ^ 59
def prefixEnd_6328395 : Nat := 4983230072969 + 3 ^ 40 * 6328395 * 2
def baseEnd_6328395 : Nat := 361056489612208095462083

theorem tailTrace_6328395 : CollatzResearch.WordTrace tailWord_6328395 prefixEnd_6328395 361056489612208095462083 := by
  unfold tailWord_6328395
  simp only [CollatzResearch.WordTrace]
  refine ⟨230815527908313193663922639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153877018605542129109281759 230815527908313193663922639)
  ·
    refine ⟨346223291862469790495883959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230815527908313193663922639 346223291862469790495883959)
    ·
      refine ⟨519334937793704685743825939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346223291862469790495883959 519334937793704685743825939)
      ·
        refine ⟨779002406690557028615738909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 519334937793704685743825939 779002406690557028615738909)
        ·
          refine ⟨292125902508958885730902091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 779002406690557028615738909 292125902508958885730902091)
          ·
            refine ⟨438188853763438328596353137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292125902508958885730902091 438188853763438328596353137)
            ·
              refine ⟨328641640322578746447264853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 438188853763438328596353137 328641640322578746447264853)
              ·
                refine ⟨3851269222530219684928885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 328641640322578746447264853 3851269222530219684928885)
                ·
                  refine ⟨361056489612208095462083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3851269222530219684928885 361056489612208095462083)
                  ·
                    rfl

theorem cell23_6328395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 8, 5].length) (baseStart_6328395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6328395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6328395 prefixEnd_6328395 := by exact prefixLift 6328395
  have htrace : WordTrace (prefixWord ++ tailWord_6328395) baseStart_6328395 baseEnd_6328395 := by
    simpa [prefixWord, tailWord_6328395, baseEnd_6328395] using wordTrace_append hprefix tailTrace_6328395
  have hstable : (prefixWord ++ tailWord_6328395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6328395).length < 2 ^ (prefixWord ++ tailWord_6328395).sum := by decide
  have hdescent : baseEnd_6328395 < baseStart_6328395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6328395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6328402 : List Nat := [3, 2, 2, 1, 4, 1, 1, 1, 2, 2, 4]
def baseStart_6328402 : Nat := 118140960795 + 6328402 * 2 ^ 59
def prefixEnd_6328402 : Nat := 4983230072969 + 3 ^ 40 * 6328402 * 2
def baseEnd_6328402 : Nat := 3249512000874454331771215

theorem tailTrace_6328402 : CollatzResearch.WordTrace tailWord_6328402 prefixEnd_6328402 3249512000874454331771215 := by
  unfold tailWord_6328402
  simp only [CollatzResearch.WordTrace]
  refine ⟨57703945804821958464856865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153877188812858555906284973 57703945804821958464856865)
  ·
    refine ⟨43277959353616468848642649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57703945804821958464856865 43277959353616468848642649)
    ·
      refine ⟨32458469515212351636481987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43277959353616468848642649 32458469515212351636481987)
      ·
        refine ⟨48687704272818527454722981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32458469515212351636481987 48687704272818527454722981)
        ·
          refine ⟨9128944551153473897760559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48687704272818527454722981 9128944551153473897760559)
          ·
            refine ⟨13693416826730210846640839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9128944551153473897760559 13693416826730210846640839)
            ·
              refine ⟨20540125240095316269961259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13693416826730210846640839 20540125240095316269961259)
              ·
                refine ⟨30810187860142974404941889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20540125240095316269961259 30810187860142974404941889)
                ·
                  refine ⟨23107640895107230803706417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30810187860142974404941889 23107640895107230803706417)
                  ·
                    refine ⟨17330730671330423102779813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23107640895107230803706417 17330730671330423102779813)
                    ·
                      refine ⟨3249512000874454331771215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17330730671330423102779813 3249512000874454331771215)
                      ·
                        rfl

theorem cell23_6328402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_6328402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6328402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6328402 prefixEnd_6328402 := by exact prefixLift 6328402
  have htrace : WordTrace (prefixWord ++ tailWord_6328402) baseStart_6328402 baseEnd_6328402 := by
    simpa [prefixWord, tailWord_6328402, baseEnd_6328402] using wordTrace_append hprefix tailTrace_6328402
  have hstable : (prefixWord ++ tailWord_6328402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6328402).length < 2 ^ (prefixWord ++ tailWord_6328402).sum := by decide
  have hdescent : baseEnd_6328402 < baseStart_6328402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6328402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6328405 : List Nat := [1, 3, 2, 2, 1, 3, 1, 1, 1, 5, 3]
def baseStart_6328405 : Nat := 118140960795 + 6328405 * 2 ^ 59
def prefixEnd_6328405 : Nat := 4983230072969 + 3 ^ 40 * 6328405 * 2
def baseEnd_6328405 : Nat := 3249513541316417820033701

theorem tailTrace_6328405 : CollatzResearch.WordTrace tailWord_6328405 prefixEnd_6328405 3249513541316417820033701 := by
  unfold tailWord_6328405
  simp only [CollatzResearch.WordTrace]
  refine ⟨230815892638276965371786669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153877261758851310247857779 230815892638276965371786669)
  ·
    refine ⟨86555959739353862014420001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230815892638276965371786669 86555959739353862014420001)
    ·
      refine ⟨64916969804515396510815001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86555959739353862014420001 64916969804515396510815001)
      ·
        refine ⟨48687727353386547383111251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64916969804515396510815001 48687727353386547383111251)
        ·
          refine ⟨73031591030079821074666877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48687727353386547383111251 73031591030079821074666877)
          ·
            refine ⟨27386846636279932903000079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73031591030079821074666877 27386846636279932903000079)
            ·
              refine ⟨41080269954419899354500119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27386846636279932903000079 41080269954419899354500119)
              ·
                refine ⟨61620404931629849031750179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41080269954419899354500119 61620404931629849031750179)
                ·
                  refine ⟨92430607397444773547625269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61620404931629849031750179 92430607397444773547625269)
                  ·
                    refine ⟨8665369443510447520089869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 92430607397444773547625269 8665369443510447520089869)
                    ·
                      refine ⟨3249513541316417820033701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8665369443510447520089869 3249513541316417820033701)
                      ·
                        rfl

theorem cell23_6328405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_6328405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6328405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6328405 prefixEnd_6328405 := by exact prefixLift 6328405
  have htrace : WordTrace (prefixWord ++ tailWord_6328405) baseStart_6328405 baseEnd_6328405 := by
    simpa [prefixWord, tailWord_6328405, baseEnd_6328405] using wordTrace_append hprefix tailTrace_6328405
  have hstable : (prefixWord ++ tailWord_6328405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6328405).length < 2 ^ (prefixWord ++ tailWord_6328405).sum := by decide
  have hdescent : baseEnd_6328405 < baseStart_6328405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6328405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6328406 : List Nat := [5, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2]
def baseStart_6328406 : Nat := 118140960795 + 6328406 * 2 ^ 59
def prefixEnd_6328406 : Nat := 4983230072969 + 3 ^ 40 * 6328406 * 2
def baseEnd_6328406 : Nat := 3249514054797072316121197

theorem tailTrace_6328406 : CollatzResearch.WordTrace tailWord_6328406 prefixEnd_6328406 3249514054797072316121197 := by
  unfold tailWord_6328406
  simp only [CollatzResearch.WordTrace]
  refine ⟨14425995569454583908910817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153877286074182228361715381 14425995569454583908910817)
  ·
    refine ⟨10819496677090937931683113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14425995569454583908910817 10819496677090937931683113)
    ·
      refine ⟨8114622507818203448762335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10819496677090937931683113 8114622507818203448762335)
      ·
        refine ⟨12171933761727305173143503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8114622507818203448762335 12171933761727305173143503)
        ·
          refine ⟨18257900642590957759715255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12171933761727305173143503 18257900642590957759715255)
          ·
            refine ⟨27386850963886436639572883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18257900642590957759715255 27386850963886436639572883)
            ·
              refine ⟨41080276445829654959359325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27386850963886436639572883 41080276445829654959359325)
              ·
                refine ⟨15405103667186120609759747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41080276445829654959359325 15405103667186120609759747)
                ·
                  refine ⟨23107655500779180914639621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15405103667186120609759747 23107655500779180914639621)
                  ·
                    refine ⟨4332685406396096421494929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23107655500779180914639621 4332685406396096421494929)
                    ·
                      refine ⟨3249514054797072316121197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4332685406396096421494929 3249514054797072316121197)
                      ·
                        rfl

theorem cell23_6328406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_6328406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6328406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6328406 prefixEnd_6328406 := by exact prefixLift 6328406
  have htrace : WordTrace (prefixWord ++ tailWord_6328406) baseStart_6328406 baseEnd_6328406 := by
    simpa [prefixWord, tailWord_6328406, baseEnd_6328406] using wordTrace_append hprefix tailTrace_6328406
  have hstable : (prefixWord ++ tailWord_6328406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6328406).length < 2 ^ (prefixWord ++ tailWord_6328406).sum := by decide
  have hdescent : baseEnd_6328406 < baseStart_6328406 := by decide
  rcases family_descends (prefixWord ++ tailWord_6328406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6328613 : List Nat := [1, 3, 1, 2, 6, 1, 1, 2, 2, 4]
def baseStart_6328613 : Nat := 118140960795 + 6328613 * 2 ^ 59
def prefixEnd_6328613 : Nat := 4983230072969 + 3 ^ 40 * 6328613 * 2
def baseEnd_6328613 : Nat := 1083206781764184335410915

theorem tailTrace_6328613 : CollatzResearch.WordTrace tailWord_6328613 prefixEnd_6328613 1083206781764184335410915 := by
  unfold tailWord_6328613
  simp only [CollatzResearch.WordTrace]
  refine ⟨230823479021523416895358493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153882319347682277930238995 230823479021523416895358493)
  ·
    refine ⟨86558804633071281335759435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230823479021523416895358493 86558804633071281335759435)
    ·
      refine ⟨129838206949606922003639153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86558804633071281335759435 129838206949606922003639153)
      ·
        refine ⟨97378655212205191502729365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129838206949606922003639153 97378655212205191502729365)
        ·
          refine ⟨4564624463072118351690439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 97378655212205191502729365 4564624463072118351690439)
          ·
            refine ⟨6846936694608177527535659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4564624463072118351690439 6846936694608177527535659)
            ·
              refine ⟨10270405041912266291303489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6846936694608177527535659 10270405041912266291303489)
              ·
                refine ⟨7702803781434199718477617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10270405041912266291303489 7702803781434199718477617)
                ·
                  refine ⟨5777102836075649788858213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7702803781434199718477617 5777102836075649788858213)
                  ·
                    refine ⟨1083206781764184335410915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5777102836075649788858213 1083206781764184335410915)
                    ·
                      rfl

theorem cell23_6328613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 2, 2, 4].length) (baseStart_6328613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6328613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6328613 prefixEnd_6328613 := by exact prefixLift 6328613
  have htrace : WordTrace (prefixWord ++ tailWord_6328613) baseStart_6328613 baseEnd_6328613 := by
    simpa [prefixWord, tailWord_6328613, baseEnd_6328613] using wordTrace_append hprefix tailTrace_6328613
  have hstable : (prefixWord ++ tailWord_6328613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6328613).length < 2 ^ (prefixWord ++ tailWord_6328613).sum := by decide
  have hdescent : baseEnd_6328613 < baseStart_6328613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6328613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6328676 : List Nat := [2, 3, 1, 1, 3, 1, 1, 3, 4, 2, 2]
def baseStart_6328676 : Nat := 118140960795 + 6328676 * 2 ^ 59
def prefixEnd_6328676 : Nat := 4983230072969 + 3 ^ 40 * 6328676 * 2
def baseEnd_6328676 : Nat := 3249652694573786259744955

theorem tailTrace_6328676 : CollatzResearch.WordTrace tailWord_6328676 prefixEnd_6328676 3249652694573786259744955 := by
  unfold tailWord_6328676
  simp only [CollatzResearch.WordTrace]
  refine ⟨115412888410147589327450941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153883851213530119103267921 115412888410147589327450941)
  ·
    refine ⟨43279833153805345997794103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115412888410147589327450941 43279833153805345997794103)
    ·
      refine ⟨64919749730708018996691155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43279833153805345997794103 64919749730708018996691155)
      ·
        refine ⟨97379624596062028495036733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64919749730708018996691155 97379624596062028495036733)
        ·
          refine ⟨36517359223523260685638775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97379624596062028495036733 36517359223523260685638775)
          ·
            refine ⟨54776038835284891028458163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36517359223523260685638775 54776038835284891028458163)
            ·
              refine ⟨82164058252927336542687245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54776038835284891028458163 82164058252927336542687245)
              ·
                refine ⟨30811521844847751203507717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82164058252927336542687245 30811521844847751203507717)
                ·
                  refine ⟨5777160345908953350657697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30811521844847751203507717 5777160345908953350657697)
                  ·
                    refine ⟨4332870259431715012993273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5777160345908953350657697 4332870259431715012993273)
                    ·
                      refine ⟨3249652694573786259744955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4332870259431715012993273 3249652694573786259744955)
                      ·
                        rfl

theorem cell23_6328676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 4, 2, 2].length) (baseStart_6328676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6328676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6328676 prefixEnd_6328676 := by exact prefixLift 6328676
  have htrace : WordTrace (prefixWord ++ tailWord_6328676) baseStart_6328676 baseEnd_6328676 := by
    simpa [prefixWord, tailWord_6328676, baseEnd_6328676] using wordTrace_append hprefix tailTrace_6328676
  have hstable : (prefixWord ++ tailWord_6328676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6328676).length < 2 ^ (prefixWord ++ tailWord_6328676).sum := by decide
  have hdescent : baseEnd_6328676 < baseStart_6328676 := by decide
  rcases family_descends (prefixWord ++ tailWord_6328676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6328759 : List Nat := [1, 1, 3, 1, 3, 3, 1, 1, 5, 4]
def baseStart_6328759 : Nat := 118140960795 + 6328759 * 2 ^ 59
def prefixEnd_6328759 : Nat := 4983230072969 + 3 ^ 40 * 6328759 * 2
def baseEnd_6328759 : Nat := 1083231771156036478335691

theorem tailTrace_6328759 : CollatzResearch.WordTrace tailWord_6328759 prefixEnd_6328759 1083231771156036478335691 := by
  unfold tailWord_6328759
  simp only [CollatzResearch.WordTrace]
  refine ⟨230828804078994483830173331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153885869385996322553448887 230828804078994483830173331)
  ·
    refine ⟨346243206118491725745259997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230828804078994483830173331 346243206118491725745259997)
    ·
      refine ⟨129841202294434397154472499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 346243206118491725745259997 129841202294434397154472499)
      ·
        refine ⟨194761803441651595731708749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129841202294434397154472499 194761803441651595731708749)
        ·
          refine ⟨73035676290619348399390781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194761803441651595731708749 73035676290619348399390781)
          ·
            refine ⟨27388378608982255649771543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73035676290619348399390781 27388378608982255649771543)
            ·
              refine ⟨41082567913473383474657315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27388378608982255649771543 41082567913473383474657315)
              ·
                refine ⟨61623851870210075211985973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41082567913473383474657315 61623851870210075211985973)
                ·
                  refine ⟨5777236112832194551123685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61623851870210075211985973 5777236112832194551123685)
                  ·
                    refine ⟨1083231771156036478335691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5777236112832194551123685 1083231771156036478335691)
                    ·
                      rfl

theorem cell23_6328759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 5, 4].length) (baseStart_6328759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6328759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6328759 prefixEnd_6328759 := by exact prefixLift 6328759
  have htrace : WordTrace (prefixWord ++ tailWord_6328759) baseStart_6328759 baseEnd_6328759 := by
    simpa [prefixWord, tailWord_6328759, baseEnd_6328759] using wordTrace_append hprefix tailTrace_6328759
  have hstable : (prefixWord ++ tailWord_6328759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6328759).length < 2 ^ (prefixWord ++ tailWord_6328759).sum := by decide
  have hdescent : baseEnd_6328759 < baseStart_6328759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6328759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6328762 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 4, 1, 6]
def baseStart_6328762 : Nat := 118140960795 + 6328762 * 2 ^ 59
def prefixEnd_6328762 : Nat := 4983230072969 + 3 ^ 40 * 6328762 * 2
def baseEnd_6328762 : Nat := 3249696853910072923269559

theorem tailTrace_6328762 : CollatzResearch.WordTrace tailWord_6328762 prefixEnd_6328762 3249696853910072923269559 := by
  unfold tailWord_6328762
  simp only [CollatzResearch.WordTrace]
  refine ⟨57707228374495903835633135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153885942331989076895021693 57707228374495903835633135)
  ·
    refine ⟨86560842561743855753449703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57707228374495903835633135 86560842561743855753449703)
    ·
      refine ⟨129841263842615783630174555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86560842561743855753449703 129841263842615783630174555)
      ·
        refine ⟨194761895763923675445261833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129841263842615783630174555 194761895763923675445261833)
        ·
          refine ⟨146071421822942756583946375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194761895763923675445261833 146071421822942756583946375)
          ·
            refine ⟨219107132734414134875919563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146071421822942756583946375 219107132734414134875919563)
            ·
              refine ⟨328660699101621202313879345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219107132734414134875919563 328660699101621202313879345)
              ·
                refine ⟨246495524326215901735409509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 328660699101621202313879345 246495524326215901735409509)
                ·
                  refine ⟨46217910811165481575389283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 246495524326215901735409509 46217910811165481575389283)
                  ·
                    refine ⟨69326866216748222363083925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46217910811165481575389283 69326866216748222363083925)
                    ·
                      refine ⟨3249696853910072923269559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69326866216748222363083925 3249696853910072923269559)
                      ·
                        rfl

theorem cell23_6328762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_6328762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6328762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6328762 prefixEnd_6328762 := by exact prefixLift 6328762
  have htrace : WordTrace (prefixWord ++ tailWord_6328762) baseStart_6328762 baseEnd_6328762 := by
    simpa [prefixWord, tailWord_6328762, baseEnd_6328762] using wordTrace_append hprefix tailTrace_6328762
  have hstable : (prefixWord ++ tailWord_6328762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6328762).length < 2 ^ (prefixWord ++ tailWord_6328762).sum := by decide
  have hdescent : baseEnd_6328762 < baseStart_6328762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6328762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6328766 : List Nat := [4, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4]
def baseStart_6328766 : Nat := 118140960795 + 6328766 * 2 ^ 59
def prefixEnd_6328766 : Nat := 4983230072969 + 3 ^ 40 * 6328766 * 2
def baseEnd_6328766 : Nat := 3249698907832690907619541

theorem tailTrace_6328766 : CollatzResearch.WordTrace tailWord_6328766 prefixEnd_6328766 3249698907832690907619541 := by
  unfold tailWord_6328766
  simp only [CollatzResearch.WordTrace]
  refine ⟨28853632423746140503209769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153886039593312749350452101 28853632423746140503209769)
  ·
    refine ⟨21640224317809605377407327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28853632423746140503209769 21640224317809605377407327)
    ·
      refine ⟨32460336476714408066110991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21640224317809605377407327 32460336476714408066110991)
      ·
        refine ⟨48690504715071612099166487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32460336476714408066110991 48690504715071612099166487)
        ·
          refine ⟨73035757072607418148749731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48690504715071612099166487 73035757072607418148749731)
          ·
            refine ⟨109553635608911127223124597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73035757072607418148749731 109553635608911127223124597)
            ·
              refine ⟨10270653338335418177167931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109553635608911127223124597 10270653338335418177167931)
              ·
                refine ⟨15405980007503127265751897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10270653338335418177167931 15405980007503127265751897)
                ·
                  refine ⟨11554485005627345449313923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15405980007503127265751897 11554485005627345449313923)
                  ·
                    refine ⟨17331727508441018173970885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11554485005627345449313923 17331727508441018173970885)
                    ·
                      refine ⟨3249698907832690907619541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17331727508441018173970885 3249698907832690907619541)
                      ·
                        rfl

theorem cell23_6328766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_6328766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6328766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6328766 prefixEnd_6328766 := by exact prefixLift 6328766
  have htrace : WordTrace (prefixWord ++ tailWord_6328766) baseStart_6328766 baseEnd_6328766 := by
    simpa [prefixWord, tailWord_6328766, baseEnd_6328766] using wordTrace_append hprefix tailTrace_6328766
  have hstable : (prefixWord ++ tailWord_6328766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6328766).length < 2 ^ (prefixWord ++ tailWord_6328766).sum := by decide
  have hdescent : baseEnd_6328766 < baseStart_6328766 := by decide
  rcases family_descends (prefixWord ++ tailWord_6328766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6328789 : List Nat := [1, 3, 2, 3, 1, 3, 1, 1, 8]
def baseStart_6328789 : Nat := 118140960795 + 6328789 * 2 ^ 59
def prefixEnd_6328789 : Nat := 4983230072969 + 3 ^ 40 * 6328789 * 2
def baseEnd_6328789 : Nat := 361078968654193813070215

theorem tailTrace_6328789 : CollatzResearch.WordTrace tailWord_6328789 prefixEnd_6328789 361078968654193813070215 := by
  unfold tailWord_6328789
  simp only [CollatzResearch.WordTrace]
  refine ⟨230829898268885798953765421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153886598845923865969176947 230829898268885798953765421)
  ·
    refine ⟨86561211850832174607662033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230829898268885798953765421 86561211850832174607662033)
    ·
      refine ⟨64920908888124130955746525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86561211850832174607662033 64920908888124130955746525)
      ·
        refine ⟨24345340833046549108404947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64920908888124130955746525 24345340833046549108404947)
        ·
          refine ⟨36518011249569823662607421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24345340833046549108404947 36518011249569823662607421)
          ·
            refine ⟨13694254218588683873477783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36518011249569823662607421 13694254218588683873477783)
            ·
              refine ⟨20541381327883025810216675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13694254218588683873477783 20541381327883025810216675)
              ·
                refine ⟨30812071991824538715325013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20541381327883025810216675 30812071991824538715325013)
                ·
                  refine ⟨361078968654193813070215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30812071991824538715325013 361078968654193813070215)
                  ·
                    rfl

theorem cell23_6328789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 8].length) (baseStart_6328789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6328789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6328789 prefixEnd_6328789 := by exact prefixLift 6328789
  have htrace : WordTrace (prefixWord ++ tailWord_6328789) baseStart_6328789 baseEnd_6328789 := by
    simpa [prefixWord, tailWord_6328789, baseEnd_6328789] using wordTrace_append hprefix tailTrace_6328789
  have hstable : (prefixWord ++ tailWord_6328789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6328789).length < 2 ^ (prefixWord ++ tailWord_6328789).sum := by decide
  have hdescent : baseEnd_6328789 < baseStart_6328789 := by decide
  rcases family_descends (prefixWord ++ tailWord_6328789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6328816 : List Nat := [2, 1, 1, 1, 3, 3, 1, 4, 3, 1, 3]
def baseStart_6328816 : Nat := 118140960795 + 6328816 * 2 ^ 59
def prefixEnd_6328816 : Nat := 4983230072969 + 3 ^ 40 * 6328816 * 2
def baseEnd_6328816 : Nat := 3249724581865415711994311

theorem tailTrace_6328816 : CollatzResearch.WordTrace tailWord_6328816 prefixEnd_6328816 3249724581865415711994311 := by
  unfold tailWord_6328816
  simp only [CollatzResearch.WordTrace]
  refine ⟨115415441519893991282499151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153887255359858655043332201 115415441519893991282499151)
  ·
    refine ⟨173123162279840986923748727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115415441519893991282499151 173123162279840986923748727)
    ·
      refine ⟨259684743419761480385623091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173123162279840986923748727 259684743419761480385623091)
      ·
        refine ⟨389527115129642220578434637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259684743419761480385623091 389527115129642220578434637)
        ·
          refine ⟨146072668173615832716912989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 389527115129642220578434637 146072668173615832716912989)
          ·
            refine ⟨54777250565105937268842371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146072668173615832716912989 54777250565105937268842371)
            ·
              refine ⟨82165875847658905903263557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54777250565105937268842371 82165875847658905903263557)
              ·
                refine ⟨15406101721436044856861917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82165875847658905903263557 15406101721436044856861917)
                ·
                  refine ⟨5777288145538516821323219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15406101721436044856861917 5777288145538516821323219)
                  ·
                    refine ⟨8665932218307775231984829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5777288145538516821323219 8665932218307775231984829)
                    ·
                      refine ⟨3249724581865415711994311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8665932218307775231984829 3249724581865415711994311)
                      ·
                        rfl

theorem cell23_6328816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 3, 1, 3].length) (baseStart_6328816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6328816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6328816 prefixEnd_6328816 := by exact prefixLift 6328816
  have htrace : WordTrace (prefixWord ++ tailWord_6328816) baseStart_6328816 baseEnd_6328816 := by
    simpa [prefixWord, tailWord_6328816, baseEnd_6328816] using wordTrace_append hprefix tailTrace_6328816
  have hstable : (prefixWord ++ tailWord_6328816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6328816).length < 2 ^ (prefixWord ++ tailWord_6328816).sum := by decide
  have hdescent : baseEnd_6328816 < baseStart_6328816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6328816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6328843 : List Nat := [1, 1, 1, 1, 7, 2, 1, 2, 2, 3, 2]
def baseStart_6328843 : Nat := 118140960795 + 6328843 * 2 ^ 59
def prefixEnd_6328843 : Nat := 4983230072969 + 3 ^ 40 * 6328843 * 2
def baseEnd_6328843 : Nat := 3249738445843087106356687

theorem tailTrace_6328843 : CollatzResearch.WordTrace tailWord_6328843 prefixEnd_6328843 3249738445843087106356687 := by
  unfold tailWord_6328843
  simp only [CollatzResearch.WordTrace]
  refine ⟨230831867810690166176231183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153887911873793444117487455 230831867810690166176231183)
  ·
    refine ⟨346247801716035249264346775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230831867810690166176231183 346247801716035249264346775)
    ·
      refine ⟨519371702574052873896520163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346247801716035249264346775 519371702574052873896520163)
      ·
        refine ⟨779057553861079310844780245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 519371702574052873896520163 779057553861079310844780245)
        ·
          refine ⟨18259161418619046347924537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 779057553861079310844780245 18259161418619046347924537)
          ·
            refine ⟨13694371063964284760943403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18259161418619046347924537 13694371063964284760943403)
            ·
              refine ⟨20541556595946427141415105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13694371063964284760943403 20541556595946427141415105)
              ·
                refine ⟨15406167446959820356061329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20541556595946427141415105 15406167446959820356061329)
                ·
                  refine ⟨11554625585219865267045997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15406167446959820356061329 11554625585219865267045997)
                  ·
                    refine ⟨4332984594457449475142249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11554625585219865267045997 4332984594457449475142249)
                    ·
                      refine ⟨3249738445843087106356687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4332984594457449475142249 3249738445843087106356687)
                      ·
                        rfl

theorem cell23_6328843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 2, 3, 2].length) (baseStart_6328843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6328843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6328843 prefixEnd_6328843 := by exact prefixLift 6328843
  have htrace : WordTrace (prefixWord ++ tailWord_6328843) baseStart_6328843 baseEnd_6328843 := by
    simpa [prefixWord, tailWord_6328843, baseEnd_6328843] using wordTrace_append hprefix tailTrace_6328843
  have hstable : (prefixWord ++ tailWord_6328843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6328843).length < 2 ^ (prefixWord ++ tailWord_6328843).sum := by decide
  have hdescent : baseEnd_6328843 < baseStart_6328843 := by decide
  rcases family_descends (prefixWord ++ tailWord_6328843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6328869 : List Nat := [1, 3, 1, 2, 2, 1, 4, 1, 1, 1, 6]
def baseStart_6328869 : Nat := 118140960795 + 6328869 * 2 ^ 59
def prefixEnd_6328869 : Nat := 4983230072969 + 3 ^ 40 * 6328869 * 2
def baseEnd_6328869 : Nat := 3249751796340104004631567

theorem tailTrace_6328869 : CollatzResearch.WordTrace tailWord_6328869 prefixEnd_6328869 3249751796340104004631567 := by
  unfold tailWord_6328869
  simp only [CollatzResearch.WordTrace]
  refine ⟨230832816108595972616677661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153888544072397315077785107 230832816108595972616677661)
  ·
    refine ⟨86562306040723489731254123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230832816108595972616677661 86562306040723489731254123)
    ·
      refine ⟨129843459061085234596881185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86562306040723489731254123 129843459061085234596881185)
      ·
        refine ⟨97382594295813925947660889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129843459061085234596881185 97382594295813925947660889)
        ·
          refine ⟨73036945721860444460745667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97382594295813925947660889 73036945721860444460745667)
          ·
            refine ⟨109555418582790666691118501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73036945721860444460745667 109555418582790666691118501)
            ·
              refine ⟨20541640984273250004584719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109555418582790666691118501 20541640984273250004584719)
              ·
                refine ⟨30812461476409875006877079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20541640984273250004584719 30812461476409875006877079)
                ·
                  refine ⟨46218692214614812510315619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30812461476409875006877079 46218692214614812510315619)
                  ·
                    refine ⟨69328038321922218765473429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46218692214614812510315619 69328038321922218765473429)
                    ·
                      refine ⟨3249751796340104004631567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69328038321922218765473429 3249751796340104004631567)
                      ·
                        rfl

theorem cell23_6328869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_6328869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6328869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6328869 prefixEnd_6328869 := by exact prefixLift 6328869
  have htrace : WordTrace (prefixWord ++ tailWord_6328869) baseStart_6328869 baseEnd_6328869 := by
    simpa [prefixWord, tailWord_6328869, baseEnd_6328869] using wordTrace_append hprefix tailTrace_6328869
  have hstable : (prefixWord ++ tailWord_6328869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6328869).length < 2 ^ (prefixWord ++ tailWord_6328869).sum := by decide
  have hdescent : baseEnd_6328869 < baseStart_6328869 := by decide
  rcases family_descends (prefixWord ++ tailWord_6328869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6328893 : List Nat := [1, 4, 1, 3, 2, 3, 1, 1, 1, 1, 5]
def baseStart_6328893 : Nat := 118140960795 + 6328893 * 2 ^ 59
def prefixEnd_6328893 : Nat := 4983230072969 + 3 ^ 40 * 6328893 * 2
def baseEnd_6328893 : Nat := 3249764119875811910731457

theorem tailTrace_6328893 : CollatzResearch.WordTrace tailWord_6328893 prefixEnd_6328893 3249764119875811910731457 := by
  unfold tailWord_6328893
  simp only [CollatzResearch.WordTrace]
  refine ⟨230833691460509024715551333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153889127640339349810367555 230833691460509024715551333)
  ·
    refine ⟨43281317148845442134165875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230833691460509024715551333 43281317148845442134165875)
    ·
      refine ⟨64921975723268163201248813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43281317148845442134165875 64921975723268163201248813)
      ·
        refine ⟨24345740896225561200468305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64921975723268163201248813 24345740896225561200468305)
        ·
          refine ⟨18259305672169170900351229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24345740896225561200468305 18259305672169170900351229)
          ·
            refine ⟨6847239627063439087631711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18259305672169170900351229 6847239627063439087631711)
            ·
              refine ⟨10270859440595158631447567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6847239627063439087631711 10270859440595158631447567)
              ·
                refine ⟨15406289160892737947171351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10270859440595158631447567 15406289160892737947171351)
                ·
                  refine ⟨23109433741339106920757027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15406289160892737947171351 23109433741339106920757027)
                  ·
                    refine ⟨34664150612008660381135541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23109433741339106920757027 34664150612008660381135541)
                    ·
                      refine ⟨3249764119875811910731457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34664150612008660381135541 3249764119875811910731457)
                      ·
                        rfl

theorem cell23_6328893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_6328893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6328893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6328893 prefixEnd_6328893 := by exact prefixLift 6328893
  have htrace : WordTrace (prefixWord ++ tailWord_6328893) baseStart_6328893 baseEnd_6328893 := by
    simpa [prefixWord, tailWord_6328893, baseEnd_6328893] using wordTrace_append hprefix tailTrace_6328893
  have hstable : (prefixWord ++ tailWord_6328893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6328893).length < 2 ^ (prefixWord ++ tailWord_6328893).sum := by decide
  have hdescent : baseEnd_6328893 < baseStart_6328893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6328893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6328907 : List Nat := [1, 1, 1, 1, 3, 1, 8, 2, 1, 2, 2]
def baseStart_6328907 : Nat := 118140960795 + 6328907 * 2 ^ 59
def prefixEnd_6328907 : Nat := 4983230072969 + 3 ^ 40 * 6328907 * 2
def baseEnd_6328907 : Nat := 3249771308604974855956393

theorem tailTrace_6328907 : CollatzResearch.WordTrace tailWord_6328907 prefixEnd_6328907 3249771308604974855956393 := by
  unfold tailWord_6328907
  simp only [CollatzResearch.WordTrace]
  refine ⟨230834202082458305106560975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153889468054972203404373983 230834202082458305106560975)
  ·
    refine ⟨346251303123687457659841463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230834202082458305106560975 346251303123687457659841463)
    ·
      refine ⟨519376954685531186489762195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346251303123687457659841463 519376954685531186489762195)
      ·
        refine ⟨779065432028296779734643293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 519376954685531186489762195 779065432028296779734643293)
        ·
          refine ⟨292149537010611292400491235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 779065432028296779734643293 292149537010611292400491235)
          ·
            refine ⟨438224305515916938600736853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292149537010611292400491235 438224305515916938600736853)
            ·
              refine ⟨5135441080264651624227385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 438224305515916938600736853 5135441080264651624227385)
              ·
                refine ⟨3851580810198488718170539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5135441080264651624227385 3851580810198488718170539)
                ·
                  refine ⟨5777371215297733077255809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3851580810198488718170539 5777371215297733077255809)
                  ·
                    refine ⟨4333028411473299807941857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5777371215297733077255809 4333028411473299807941857)
                    ·
                      refine ⟨3249771308604974855956393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4333028411473299807941857 3249771308604974855956393)
                      ·
                        rfl

theorem cell23_6328907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 2, 1, 2, 2].length) (baseStart_6328907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6328907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6328907 prefixEnd_6328907 := by exact prefixLift 6328907
  have htrace : WordTrace (prefixWord ++ tailWord_6328907) baseStart_6328907 baseEnd_6328907 := by
    simpa [prefixWord, tailWord_6328907, baseEnd_6328907] using wordTrace_append hprefix tailTrace_6328907
  have hstable : (prefixWord ++ tailWord_6328907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6328907).length < 2 ^ (prefixWord ++ tailWord_6328907).sum := by decide
  have hdescent : baseEnd_6328907 < baseStart_6328907 := by decide
  rcases family_descends (prefixWord ++ tailWord_6328907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6328930 : List Nat := [3, 3, 2, 3, 1, 1, 3, 7]
def baseStart_6328930 : Nat := 118140960795 + 6328930 * 2 ^ 59
def prefixEnd_6328930 : Nat := 4983230072969 + 3 ^ 40 * 6328930 * 2
def baseEnd_6328930 : Nat := 120362337728149195035881

theorem tailTrace_6328930 : CollatzResearch.WordTrace tailWord_6328930 prefixEnd_6328930 120362337728149195035881 := by
  unfold tailWord_6328930
  simp only [CollatzResearch.WordTrace]
  refine ⟨57708760240343745008662061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153890027307583320023098829 57708760240343745008662061)
  ·
    refine ⟨21640785090128904378248273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57708760240343745008662061 21640785090128904378248273)
    ·
      refine ⟨16230588817596678283686205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21640785090128904378248273 16230588817596678283686205)
      ·
        refine ⟨6086470806598754356382327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16230588817596678283686205 6086470806598754356382327)
        ·
          refine ⟨9129706209898131534573491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6086470806598754356382327 9129706209898131534573491)
          ·
            refine ⟨13694559314847197301860237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9129706209898131534573491 13694559314847197301860237)
            ·
              refine ⟨5135459743067698988197589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13694559314847197301860237 5135459743067698988197589)
              ·
                refine ⟨120362337728149195035881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5135459743067698988197589 120362337728149195035881)
                ·
                  rfl

theorem cell23_6328930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 7].length) (baseStart_6328930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6328930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6328930 prefixEnd_6328930 := by exact prefixLift 6328930
  have htrace : WordTrace (prefixWord ++ tailWord_6328930) baseStart_6328930 baseEnd_6328930 := by
    simpa [prefixWord, tailWord_6328930, baseEnd_6328930] using wordTrace_append hprefix tailTrace_6328930
  have hstable : (prefixWord ++ tailWord_6328930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6328930).length < 2 ^ (prefixWord ++ tailWord_6328930).sum := by decide
  have hdescent : baseEnd_6328930 < baseStart_6328930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6328930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6328957 : List Nat := [1, 4, 1, 1, 5, 2, 1, 2, 2, 1, 3]
def baseStart_6328957 : Nat := 118140960795 + 6328957 * 2 ^ 59
def prefixEnd_6328957 : Nat := 4983230072969 + 3 ^ 40 * 6328957 * 2
def baseEnd_6328957 : Nat := 3249796982637699660331163

theorem tailTrace_6328957 : CollatzResearch.WordTrace tailWord_6328957 prefixEnd_6328957 3249796982637699660331163 := by
  unfold tailWord_6328957
  simp only [CollatzResearch.WordTrace]
  refine ⟨230836025732277163645881125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153890683821518109097254083 230836025732277163645881125)
  ·
    refine ⟨43281754824801968183602711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230836025732277163645881125 43281754824801968183602711)
    ·
      refine ⟨64922632237202952275404067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43281754824801968183602711 64922632237202952275404067)
      ·
        refine ⟨97383948355804428413106101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64922632237202952275404067 97383948355804428413106101)
        ·
          refine ⟨9129745158356665163728697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97383948355804428413106101 9129745158356665163728697)
          ·
            refine ⟨6847308868767498872796523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9129745158356665163728697 6847308868767498872796523)
            ·
              refine ⟨10270963303151248309194785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6847308868767498872796523 10270963303151248309194785)
              ·
                refine ⟨7703222477363436231896089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10270963303151248309194785 7703222477363436231896089)
                ·
                  refine ⟨5777416858022577173922067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7703222477363436231896089 5777416858022577173922067)
                  ·
                    refine ⟨8666125287033865760883101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5777416858022577173922067 8666125287033865760883101)
                    ·
                      refine ⟨3249796982637699660331163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8666125287033865760883101 3249796982637699660331163)
                      ·
                        rfl

theorem cell23_6328957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 2, 2, 1, 3].length) (baseStart_6328957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6328957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6328957 prefixEnd_6328957 := by exact prefixLift 6328957
  have htrace : WordTrace (prefixWord ++ tailWord_6328957) baseStart_6328957 baseEnd_6328957 := by
    simpa [prefixWord, tailWord_6328957, baseEnd_6328957] using wordTrace_append hprefix tailTrace_6328957
  have hstable : (prefixWord ++ tailWord_6328957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6328957).length < 2 ^ (prefixWord ++ tailWord_6328957).sum := by decide
  have hdescent : baseEnd_6328957 < baseStart_6328957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6328957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329019 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 8]
def baseStart_6329019 : Nat := 118140960795 + 6329019 * 2 ^ 59
def prefixEnd_6329019 : Nat := 4983230072969 + 3 ^ 40 * 6329019 * 2
def baseEnd_6329019 : Nat := 3249828818438278417755877

theorem tailTrace_6329019 : CollatzResearch.WordTrace tailWord_6329019 prefixEnd_6329019 3249828818438278417755877 := by
  unfold tailWord_6329019
  simp only [CollatzResearch.WordTrace]
  refine ⟨230838287058052548234638111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153892191372035032156425407 230838287058052548234638111)
  ·
    refine ⟨346257430587078822351957167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230838287058052548234638111 346257430587078822351957167)
    ·
      refine ⟨519386145880618233527935751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346257430587078822351957167 519386145880618233527935751)
      ·
        refine ⟨779079218820927350291903627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 519386145880618233527935751 779079218820927350291903627)
        ·
          refine ⟨1168618828231391025437855441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 779079218820927350291903627 1168618828231391025437855441)
          ·
            refine ⟨876464121173543269078391581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1168618828231391025437855441 876464121173543269078391581)
            ·
              refine ⟨328674045440078725904396843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 876464121173543269078391581 328674045440078725904396843)
              ·
                refine ⟨493011068160118088856595265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 328674045440078725904396843 493011068160118088856595265)
                ·
                  refine ⟨369758301120088566642446449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 493011068160118088856595265 369758301120088566642446449)
                  ·
                    refine ⟨277318725840066424981834837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 369758301120088566642446449 277318725840066424981834837)
                    ·
                      refine ⟨3249828818438278417755877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 277318725840066424981834837 3249828818438278417755877)
                      ·
                        rfl

theorem cell23_6329019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 8].length) (baseStart_6329019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329019 prefixEnd_6329019 := by exact prefixLift 6329019
  have htrace : WordTrace (prefixWord ++ tailWord_6329019) baseStart_6329019 baseEnd_6329019 := by
    simpa [prefixWord, tailWord_6329019, baseEnd_6329019] using wordTrace_append hprefix tailTrace_6329019
  have hstable : (prefixWord ++ tailWord_6329019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329019).length < 2 ^ (prefixWord ++ tailWord_6329019).sum := by decide
  have hdescent : baseEnd_6329019 < baseStart_6329019 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329020 : List Nat := [2, 2, 2, 3, 1, 1, 5, 2, 5]
def baseStart_6329020 : Nat := 118140960795 + 6329020 * 2 ^ 59
def prefixEnd_6329020 : Nat := 4983230072969 + 3 ^ 40 * 6329020 * 2
def baseEnd_6329020 : Nat := 361092147990992545982597

theorem tailTrace_6329020 : CollatzResearch.WordTrace tailWord_6329020 prefixEnd_6329020 361092147990992545982597 := by
  unfold tailWord_6329020
  simp only [CollatzResearch.WordTrace]
  refine ⟨115419161765524462702712257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153892215687365950270283009 115419161765524462702712257)
  ·
    refine ⟨86564371324143347027034193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115419161765524462702712257 86564371324143347027034193)
    ·
      refine ⟨64923278493107510270275645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86564371324143347027034193 64923278493107510270275645)
      ·
        refine ⟨24346229434915316351353367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64923278493107510270275645 24346229434915316351353367)
        ·
          refine ⟨36519344152372974527030051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24346229434915316351353367 36519344152372974527030051)
          ·
            refine ⟨54779016228559461790545077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36519344152372974527030051 54779016228559461790545077)
            ·
              refine ⟨5135532771427449542863601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54779016228559461790545077 5135532771427449542863601)
              ·
                refine ⟨3851649578570587157147701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5135532771427449542863601 3851649578570587157147701)
                ·
                  refine ⟨361092147990992545982597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3851649578570587157147701 361092147990992545982597)
                  ·
                    rfl

theorem cell23_6329020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 2, 5].length) (baseStart_6329020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329020 prefixEnd_6329020 := by exact prefixLift 6329020
  have htrace : WordTrace (prefixWord ++ tailWord_6329020) baseStart_6329020 baseEnd_6329020 := by
    simpa [prefixWord, tailWord_6329020, baseEnd_6329020] using wordTrace_append hprefix tailTrace_6329020
  have hstable : (prefixWord ++ tailWord_6329020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329020).length < 2 ^ (prefixWord ++ tailWord_6329020).sum := by decide
  have hdescent : baseEnd_6329020 < baseStart_6329020 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329066 : List Nat := [3, 1, 3, 1, 1, 1, 1, 3, 2, 1, 6]
def baseStart_6329066 : Nat := 118140960795 + 6329066 * 2 ^ 59
def prefixEnd_6329066 : Nat := 4983230072969 + 3 ^ 40 * 6329066 * 2
def baseEnd_6329066 : Nat := 3249852952029039733868161

theorem tailTrace_6329066 : CollatzResearch.WordTrace tailWord_6329066 prefixEnd_6329066 3249852952029039733868161 := by
  unfold tailWord_6329066
  simp only [CollatzResearch.WordTrace]
  refine ⟨57710000322220568815399763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153893334192588183507732701 57710000322220568815399763)
  ·
    refine ⟨86565000483330853223099645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57710000322220568815399763 86565000483330853223099645)
    ·
      refine ⟨32461875181249069958662367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86565000483330853223099645 32461875181249069958662367)
      ·
        refine ⟨48692812771873604937993551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32461875181249069958662367 48692812771873604937993551)
        ·
          refine ⟨73039219157810407406990327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48692812771873604937993551 73039219157810407406990327)
          ·
            refine ⟨109558828736715611110485491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73039219157810407406990327 109558828736715611110485491)
            ·
              refine ⟨164338243105073416665728237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109558828736715611110485491 164338243105073416665728237)
              ·
                refine ⟨61626841164402531249648089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164338243105073416665728237 61626841164402531249648089)
                ·
                  refine ⟨46220130873301898437236067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61626841164402531249648089 46220130873301898437236067)
                  ·
                    refine ⟨69330196309952847655854101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46220130873301898437236067 69330196309952847655854101)
                    ·
                      refine ⟨3249852952029039733868161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69330196309952847655854101 3249852952029039733868161)
                      ·
                        rfl

theorem cell23_6329066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_6329066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329066 prefixEnd_6329066 := by exact prefixLift 6329066
  have htrace : WordTrace (prefixWord ++ tailWord_6329066) baseStart_6329066 baseEnd_6329066 := by
    simpa [prefixWord, tailWord_6329066, baseEnd_6329066] using wordTrace_append hprefix tailTrace_6329066
  have hstable : (prefixWord ++ tailWord_6329066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329066).length < 2 ^ (prefixWord ++ tailWord_6329066).sum := by decide
  have hdescent : baseEnd_6329066 < baseStart_6329066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329073 : List Nat := [1, 2, 2, 2, 2, 2, 1, 4, 2, 2, 3]
def baseStart_6329073 : Nat := 118140960795 + 6329073 * 2 ^ 59
def prefixEnd_6329073 : Nat := 4983230072969 + 3 ^ 40 * 6329073 * 2
def baseEnd_6329073 : Nat := 3249856546393621206480629

theorem tailTrace_6329073 : CollatzResearch.WordTrace tailWord_6329073 prefixEnd_6329073 3249856546393621206480629 := by
  unfold tailWord_6329073
  simp only [CollatzResearch.WordTrace]
  refine ⟨230840256599856915457103873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153893504399904610304735915 230840256599856915457103873)
  ·
    refine ⟨173130192449892686592827905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230840256599856915457103873 173130192449892686592827905)
    ·
      refine ⟨129847644337419514944620929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173130192449892686592827905 129847644337419514944620929)
      ·
        refine ⟨97385733253064636208465697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129847644337419514944620929 97385733253064636208465697)
        ·
          refine ⟨73039299939798477156349273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97385733253064636208465697 73039299939798477156349273)
          ·
            refine ⟨54779474954848857867261955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73039299939798477156349273 54779474954848857867261955)
            ·
              refine ⟨82169212432273286800892933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54779474954848857867261955 82169212432273286800892933)
              ·
                refine ⟨15406727331051241275167425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82169212432273286800892933 15406727331051241275167425)
                ·
                  refine ⟨11555045498288430956375569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15406727331051241275167425 11555045498288430956375569)
                  ·
                    refine ⟨8666284123716323217281677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11555045498288430956375569 8666284123716323217281677)
                    ·
                      refine ⟨3249856546393621206480629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8666284123716323217281677 3249856546393621206480629)
                      ·
                        rfl

theorem cell23_6329073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 2, 2, 3].length) (baseStart_6329073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329073 prefixEnd_6329073 := by exact prefixLift 6329073
  have htrace : WordTrace (prefixWord ++ tailWord_6329073) baseStart_6329073 baseEnd_6329073 := by
    simpa [prefixWord, tailWord_6329073, baseEnd_6329073] using wordTrace_append hprefix tailTrace_6329073
  have hstable : (prefixWord ++ tailWord_6329073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329073).length < 2 ^ (prefixWord ++ tailWord_6329073).sum := by decide
  have hdescent : baseEnd_6329073 < baseStart_6329073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329080 : List Nat := [2, 1, 2, 1, 1, 2, 5, 4, 1, 4]
def baseStart_6329080 : Nat := 118140960795 + 6329080 * 2 ^ 59
def prefixEnd_6329080 : Nat := 4983230072969 + 3 ^ 40 * 6329080 * 2
def baseEnd_6329080 : Nat := 1083286713586067559697699

theorem tailTrace_6329080 : CollatzResearch.WordTrace tailWord_6329080 prefixEnd_6329080 1083286713586067559697699 := by
  unfold tailWord_6329080
  simp only [CollatzResearch.WordTrace]
  refine ⟨115420255955415777826304347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153893674607221037101739129 115420255955415777826304347)
  ·
    refine ⟨173130383933123666739456521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115420255955415777826304347 173130383933123666739456521)
    ·
      refine ⟨129847787949842750054592391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173130383933123666739456521 129847787949842750054592391)
      ·
        refine ⟨194771681924764125081888587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129847787949842750054592391 194771681924764125081888587)
        ·
          refine ⟨292157522887146187622832881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194771681924764125081888587 292157522887146187622832881)
          ·
            refine ⟨219118142165359640717124661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292157522887146187622832881 219118142165359640717124661)
            ·
              refine ⟨20542325828002466317230437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 219118142165359640717124661 20542325828002466317230437)
              ·
                refine ⟨3851686092750462434480707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20542325828002466317230437 3851686092750462434480707)
                ·
                  refine ⟨5777529139125693651721061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3851686092750462434480707 5777529139125693651721061)
                  ·
                    refine ⟨1083286713586067559697699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5777529139125693651721061 1083286713586067559697699)
                    ·
                      rfl

theorem cell23_6329080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 4, 1, 4].length) (baseStart_6329080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329080 prefixEnd_6329080 := by exact prefixLift 6329080
  have htrace : WordTrace (prefixWord ++ tailWord_6329080) baseStart_6329080 baseEnd_6329080 := by
    simpa [prefixWord, tailWord_6329080, baseEnd_6329080] using wordTrace_append hprefix tailTrace_6329080
  have hstable : (prefixWord ++ tailWord_6329080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329080).length < 2 ^ (prefixWord ++ tailWord_6329080).sum := by decide
  have hdescent : baseEnd_6329080 < baseStart_6329080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329136 : List Nat := [2, 1, 1, 1, 2, 2, 1, 4, 3, 6]
def baseStart_6329136 : Nat := 118140960795 + 6329136 * 2 ^ 59
def prefixEnd_6329136 : Nat := 4983230072969 + 3 ^ 40 * 6329136 * 2
def baseEnd_6329136 : Nat := 1083296298558284819997613

theorem tailTrace_6329136 : CollatzResearch.WordTrace tailWord_6329136 prefixEnd_6329136 1083296298558284819997613 := by
  unfold tailWord_6329136
  simp only [CollatzResearch.WordTrace]
  refine ⟨115421277199314338608323631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153895036265752451477764841 115421277199314338608323631)
  ·
    refine ⟨173131915798971507912485447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115421277199314338608323631 173131915798971507912485447)
    ·
      refine ⟨259697873698457261868728171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173131915798971507912485447 259697873698457261868728171)
      ·
        refine ⟨389546810547685892803092257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259697873698457261868728171 389546810547685892803092257)
        ·
          refine ⟨292160107910764419602319193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 389546810547685892803092257 292160107910764419602319193)
          ·
            refine ⟨219120080933073314701739395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292160107910764419602319193 219120080933073314701739395)
            ·
              refine ⟨328680121399609972052609093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219120080933073314701739395 328680121399609972052609093)
              ·
                refine ⟨61627522762426869759864205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 328680121399609972052609093 61627522762426869759864205)
                ·
                  refine ⟨23110321035910076159949077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61627522762426869759864205 23110321035910076159949077)
                  ·
                    refine ⟨1083296298558284819997613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23110321035910076159949077 1083296298558284819997613)
                    ·
                      rfl

theorem cell23_6329136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 3, 6].length) (baseStart_6329136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329136 prefixEnd_6329136 := by exact prefixLift 6329136
  have htrace : WordTrace (prefixWord ++ tailWord_6329136) baseStart_6329136 baseEnd_6329136 := by
    simpa [prefixWord, tailWord_6329136, baseEnd_6329136] using wordTrace_append hprefix tailTrace_6329136
  have hstable : (prefixWord ++ tailWord_6329136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329136).length < 2 ^ (prefixWord ++ tailWord_6329136).sum := by decide
  have hdescent : baseEnd_6329136 < baseStart_6329136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329137 : List Nat := [1, 2, 2, 3, 2, 1, 1, 6, 1, 1, 3]
def baseStart_6329137 : Nat := 118140960795 + 6329137 * 2 ^ 59
def prefixEnd_6329137 : Nat := 4983230072969 + 3 ^ 40 * 6329137 * 2
def baseEnd_6329137 : Nat := 3249889409155508956080335

theorem tailTrace_6329137 : CollatzResearch.WordTrace tailWord_6329137 prefixEnd_6329137 3249889409155508956080335 := by
  unfold tailWord_6329137
  simp only [CollatzResearch.WordTrace]
  refine ⟨230842590871625054387433665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153895060581083369591622443 230842590871625054387433665)
  ·
    refine ⟨173131943153718790790575249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230842590871625054387433665 173131943153718790790575249)
    ·
      refine ⟨129848957365289093092931437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173131943153718790790575249 129848957365289093092931437)
      ·
        refine ⟨48693359011983409909849289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129848957365289093092931437 48693359011983409909849289)
        ·
          refine ⟨36520019258987557432386967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48693359011983409909849289 36520019258987557432386967)
          ·
            refine ⟨54780028888481336148580451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36520019258987557432386967 54780028888481336148580451)
            ·
              refine ⟨82170043332722004222870677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54780028888481336148580451 82170043332722004222870677)
              ·
                refine ⟨3851720781221343947947063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82170043332722004222870677 3851720781221343947947063)
                ·
                  refine ⟨5777581171832015921920595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3851720781221343947947063 5777581171832015921920595)
                  ·
                    refine ⟨8666371757748023882880893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5777581171832015921920595 8666371757748023882880893)
                    ·
                      refine ⟨3249889409155508956080335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8666371757748023882880893 3249889409155508956080335)
                      ·
                        rfl

theorem cell23_6329137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 6, 1, 1, 3].length) (baseStart_6329137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329137 prefixEnd_6329137 := by exact prefixLift 6329137
  have htrace : WordTrace (prefixWord ++ tailWord_6329137) baseStart_6329137 baseEnd_6329137 := by
    simpa [prefixWord, tailWord_6329137, baseEnd_6329137] using wordTrace_append hprefix tailTrace_6329137
  have hstable : (prefixWord ++ tailWord_6329137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329137).length < 2 ^ (prefixWord ++ tailWord_6329137).sum := by decide
  have hdescent : baseEnd_6329137 < baseStart_6329137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329160 : List Nat := [2, 1, 3, 1, 1, 3, 4, 2, 1, 1, 4]
def baseStart_6329160 : Nat := 118140960795 + 6329160 * 2 ^ 59
def prefixEnd_6329160 : Nat := 4983230072969 + 3 ^ 40 * 6329160 * 2
def baseEnd_6329160 : Nat := 3249901219210562366092729

theorem tailTrace_6329160 : CollatzResearch.WordTrace tailWord_6329160 prefixEnd_6329160 3249901219210562366092729 := by
  unfold tailWord_6329160
  simp only [CollatzResearch.WordTrace]
  refine ⟨115421714875270864657760467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153895619833694486210347289 115421714875270864657760467)
  ·
    refine ⟨173132572312906296986640701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115421714875270864657760467 173132572312906296986640701)
    ·
      refine ⟨64924714617339861369990263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173132572312906296986640701 64924714617339861369990263)
      ·
        refine ⟨97387071926009792054985395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64924714617339861369990263 97387071926009792054985395)
        ·
          refine ⟨146080607889014688082478093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97387071926009792054985395 146080607889014688082478093)
          ·
            refine ⟨54780227958380508030929285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146080607889014688082478093 54780227958380508030929285)
            ·
              refine ⟨10271292742196345255799241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54780227958380508030929285 10271292742196345255799241)
              ·
                refine ⟨7703469556647258941849431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10271292742196345255799241 7703469556647258941849431)
                ·
                  refine ⟨11555204334970888412774147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7703469556647258941849431 11555204334970888412774147)
                  ·
                    refine ⟨17332806502456332619161221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11555204334970888412774147 17332806502456332619161221)
                    ·
                      refine ⟨3249901219210562366092729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17332806502456332619161221 3249901219210562366092729)
                      ·
                        rfl

theorem cell23_6329160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 2, 1, 1, 4].length) (baseStart_6329160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329160 prefixEnd_6329160 := by exact prefixLift 6329160
  have htrace : WordTrace (prefixWord ++ tailWord_6329160) baseStart_6329160 baseEnd_6329160 := by
    simpa [prefixWord, tailWord_6329160, baseEnd_6329160] using wordTrace_append hprefix tailTrace_6329160
  have hstable : (prefixWord ++ tailWord_6329160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329160).length < 2 ^ (prefixWord ++ tailWord_6329160).sum := by decide
  have hdescent : baseEnd_6329160 < baseStart_6329160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329173 : List Nat := [1, 3, 2, 2, 2, 1, 2, 1, 3, 2, 4]
def baseStart_6329173 : Nat := 118140960795 + 6329173 * 2 ^ 59
def prefixEnd_6329173 : Nat := 4983230072969 + 3 ^ 40 * 6329173 * 2
def baseEnd_6329173 : Nat := 3249907894459070815230169

theorem tailTrace_6329173 : CollatzResearch.WordTrace tailWord_6329173 prefixEnd_6329173 3249907894459070815230169 := by
  unfold tailWord_6329173
  simp only [CollatzResearch.WordTrace]
  refine ⟨230843903899494632535744173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153895935932996421690496115 230843903899494632535744173)
  ·
    refine ⟨86566463962310487200904065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230843903899494632535744173 86566463962310487200904065)
    ·
      refine ⟨64924847971732865400678049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86566463962310487200904065 64924847971732865400678049)
      ·
        refine ⟨48693635978799649050508537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64924847971732865400678049 48693635978799649050508537)
        ·
          refine ⟨36520226984099736787881403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48693635978799649050508537 36520226984099736787881403)
          ·
            refine ⟨54780340476149605181822105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36520226984099736787881403 54780340476149605181822105)
            ·
              refine ⟨41085255357112203886366579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54780340476149605181822105 41085255357112203886366579)
              ·
                refine ⟨61627883035668305829549869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41085255357112203886366579 61627883035668305829549869)
                ·
                  refine ⟨23110456138375614686081201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61627883035668305829549869 23110456138375614686081201)
                  ·
                    refine ⟨17332842103781711014560901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23110456138375614686081201 17332842103781711014560901)
                    ·
                      refine ⟨3249907894459070815230169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17332842103781711014560901 3249907894459070815230169)
                      ·
                        rfl

theorem cell23_6329173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_6329173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329173 prefixEnd_6329173 := by exact prefixLift 6329173
  have htrace : WordTrace (prefixWord ++ tailWord_6329173) baseStart_6329173 baseEnd_6329173 := by
    simpa [prefixWord, tailWord_6329173, baseEnd_6329173] using wordTrace_append hprefix tailTrace_6329173
  have hstable : (prefixWord ++ tailWord_6329173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329173).length < 2 ^ (prefixWord ++ tailWord_6329173).sum := by decide
  have hdescent : baseEnd_6329173 < baseStart_6329173 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329180 : List Nat := [2, 2, 4, 2, 1, 1, 1, 3, 1, 1, 5]
def baseStart_6329180 : Nat := 118140960795 + 6329180 * 2 ^ 59
def prefixEnd_6329180 : Nat := 4983230072969 + 3 ^ 40 * 6329180 * 2
def baseEnd_6329180 : Nat := 3249911488823652287842637

theorem tailTrace_6329180 : CollatzResearch.WordTrace tailWord_6329180 prefixEnd_6329180 3249911488823652287842637 := by
  unfold tailWord_6329180
  simp only [CollatzResearch.WordTrace]
  refine ⟨115422079605234636365624497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153896106140312848487499329 115422079605234636365624497)
  ·
    refine ⟨86566559703925977274218373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115422079605234636365624497 86566559703925977274218373)
    ·
      refine ⟨16231229944486120738915945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86566559703925977274218373 16231229944486120738915945)
      ·
        refine ⟨12173422458364590554186959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16231229944486120738915945 12173422458364590554186959)
        ·
          refine ⟨18260133687546885831280439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12173422458364590554186959 18260133687546885831280439)
          ·
            refine ⟨27390200531320328746920659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18260133687546885831280439 27390200531320328746920659)
            ·
              refine ⟨41085300796980493120380989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27390200531320328746920659 41085300796980493120380989)
              ·
                refine ⟨15406987798867684920142871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41085300796980493120380989 15406987798867684920142871)
                ·
                  refine ⟨23110481698301527380214307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15406987798867684920142871 23110481698301527380214307)
                  ·
                    refine ⟨34665722547452291070321461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23110481698301527380214307 34665722547452291070321461)
                    ·
                      refine ⟨3249911488823652287842637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34665722547452291070321461 3249911488823652287842637)
                      ·
                        rfl

theorem cell23_6329180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_6329180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329180 prefixEnd_6329180 := by exact prefixLift 6329180
  have htrace : WordTrace (prefixWord ++ tailWord_6329180) baseStart_6329180 baseEnd_6329180 := by
    simpa [prefixWord, tailWord_6329180, baseEnd_6329180] using wordTrace_append hprefix tailTrace_6329180
  have hstable : (prefixWord ++ tailWord_6329180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329180).length < 2 ^ (prefixWord ++ tailWord_6329180).sum := by decide
  have hdescent : baseEnd_6329180 < baseStart_6329180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329214 : List Nat := [4, 2, 3, 1, 2, 1, 1, 1, 3, 2, 3]
def baseStart_6329214 : Nat := 118140960795 + 6329214 * 2 ^ 59
def prefixEnd_6329214 : Nat := 4983230072969 + 3 ^ 40 * 6329214 * 2
def baseEnd_6329214 : Nat := 3249928947165905154817481

theorem tailTrace_6329214 : CollatzResearch.WordTrace tailWord_6329214 prefixEnd_6329214 3249928947165905154817481 := by
  unfold tailWord_6329214
  simp only [CollatzResearch.WordTrace]
  refine ⟨28855674911543262067248337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153896932861564064358657797 28855674911543262067248337)
  ·
    refine ⟨21641756183657446550436253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28855674911543262067248337 21641756183657446550436253)
    ·
      refine ⟨8115658568871542456413595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21641756183657446550436253 8115658568871542456413595)
      ·
        refine ⟨12173487853307313684620393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8115658568871542456413595 12173487853307313684620393)
        ·
          refine ⟨9130115889980485263465295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12173487853307313684620393 9130115889980485263465295)
          ·
            refine ⟨13695173834970727895197943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9130115889980485263465295 13695173834970727895197943)
            ·
              refine ⟨20542760752456091842796915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13695173834970727895197943 20542760752456091842796915)
              ·
                refine ⟨30814141128684137764195373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20542760752456091842796915 30814141128684137764195373)
                ·
                  refine ⟨11555302923256551661573265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30814141128684137764195373 11555302923256551661573265)
                  ·
                    refine ⟨8666477192442413746179949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11555302923256551661573265 8666477192442413746179949)
                    ·
                      refine ⟨3249928947165905154817481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8666477192442413746179949 3249928947165905154817481)
                      ·
                        rfl

theorem cell23_6329214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_6329214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329214 prefixEnd_6329214 := by exact prefixLift 6329214
  have htrace : WordTrace (prefixWord ++ tailWord_6329214) baseStart_6329214 baseEnd_6329214 := by
    simpa [prefixWord, tailWord_6329214, baseEnd_6329214] using wordTrace_append hprefix tailTrace_6329214
  have hstable : (prefixWord ++ tailWord_6329214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329214).length < 2 ^ (prefixWord ++ tailWord_6329214).sum := by decide
  have hdescent : baseEnd_6329214 < baseStart_6329214 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329250 : List Nat := [3, 3, 1, 2, 2, 1, 1, 1, 2, 3, 4]
def baseStart_6329250 : Nat := 118140960795 + 6329250 * 2 ^ 59
def prefixEnd_6329250 : Nat := 4983230072969 + 3 ^ 40 * 6329250 * 2
def baseEnd_6329250 : Nat := 3249947432469467013967315

theorem tailTrace_6329250 : CollatzResearch.WordTrace tailWord_6329250 prefixEnd_6329250 3249947432469467013967315 := by
  unfold tailWord_6329250
  simp only [CollatzResearch.WordTrace]
  refine ⟨57711678080053918671574301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153897808213477116457531469 57711678080053918671574301)
  ·
    refine ⟨21641879280020219501840363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57711678080053918671574301 21641879280020219501840363)
    ·
      refine ⟨32462818920030329252760545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21641879280020219501840363 32462818920030329252760545)
      ·
        refine ⟨24347114190022746939570409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32462818920030329252760545 24347114190022746939570409)
        ·
          refine ⟨18260335642517060204677807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24347114190022746939570409 18260335642517060204677807)
          ·
            refine ⟨27390503463775590307016711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18260335642517060204677807 27390503463775590307016711)
            ·
              refine ⟨41085755195663385460525067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27390503463775590307016711 41085755195663385460525067)
              ·
                refine ⟨61628632793495078190787601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41085755195663385460525067 61628632793495078190787601)
                ·
                  refine ⟨46221474595121308643090701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61628632793495078190787601 46221474595121308643090701)
                  ·
                    refine ⟨17333052973170490741159013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46221474595121308643090701 17333052973170490741159013)
                    ·
                      refine ⟨3249947432469467013967315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17333052973170490741159013 3249947432469467013967315)
                      ·
                        rfl

theorem cell23_6329250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_6329250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329250 prefixEnd_6329250 := by exact prefixLift 6329250
  have htrace : WordTrace (prefixWord ++ tailWord_6329250) baseStart_6329250 baseEnd_6329250 := by
    simpa [prefixWord, tailWord_6329250, baseEnd_6329250] using wordTrace_append hprefix tailTrace_6329250
  have hstable : (prefixWord ++ tailWord_6329250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329250).length < 2 ^ (prefixWord ++ tailWord_6329250).sum := by decide
  have hdescent : baseEnd_6329250 < baseStart_6329250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329273 : List Nat := [1, 2, 1, 4, 2, 2, 1, 1, 9]
def baseStart_6329273 : Nat := 118140960795 + 6329273 * 2 ^ 59
def prefixEnd_6329273 : Nat := 4983230072969 + 3 ^ 40 * 6329273 * 2
def baseEnd_6329273 : Nat := 361106582502724491553301

theorem tailTrace_6329273 : CollatzResearch.WordTrace tailWord_6329273 prefixEnd_6329273 361106582502724491553301 := by
  unfold tailWord_6329273
  simp only [CollatzResearch.WordTrace]
  refine ⟨230847551199132349614384473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153898367466088233076256315 230847551199132349614384473)
  ·
    refine ⟨173135663399349262210788355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230847551199132349614384473 173135663399349262210788355)
    ·
      refine ⟨259703495099023893316182533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173135663399349262210788355 259703495099023893316182533)
      ·
        refine ⟨48694405331066979996784225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 259703495099023893316182533 48694405331066979996784225)
        ·
          refine ⟨36520803998300234997588169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48694405331066979996784225 36520803998300234997588169)
          ·
            refine ⟨27390602998725176248191127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36520803998300234997588169 27390602998725176248191127)
            ·
              refine ⟨41085904498087764372286691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27390602998725176248191127 41085904498087764372286691)
              ·
                refine ⟨61628856747131646558430037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41085904498087764372286691 61628856747131646558430037)
                ·
                  refine ⟨361106582502724491553301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 61628856747131646558430037 361106582502724491553301)
                  ·
                    rfl

theorem cell23_6329273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 9].length) (baseStart_6329273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329273 prefixEnd_6329273 := by exact prefixLift 6329273
  have htrace : WordTrace (prefixWord ++ tailWord_6329273) baseStart_6329273 baseEnd_6329273 := by
    simpa [prefixWord, tailWord_6329273, baseEnd_6329273] using wordTrace_append hprefix tailTrace_6329273
  have hstable : (prefixWord ++ tailWord_6329273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329273).length < 2 ^ (prefixWord ++ tailWord_6329273).sum := by decide
  have hdescent : baseEnd_6329273 < baseStart_6329273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329288 : List Nat := [2, 1, 3, 1, 6, 1, 2, 1, 1, 3, 2]
def baseStart_6329288 : Nat := 118140960795 + 6329288 * 2 ^ 59
def prefixEnd_6329288 : Nat := 4983230072969 + 3 ^ 40 * 6329288 * 2
def baseEnd_6329288 : Nat := 3249966944734337865292141

theorem tailTrace_6329288 : CollatzResearch.WordTrace tailWord_6329288 prefixEnd_6329288 3249966944734337865292141 := by
  unfold tailWord_6329288
  simp only [CollatzResearch.WordTrace]
  refine ⟨115424049147039003588090259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153898732196052004784120345 115424049147039003588090259)
  ·
    refine ⟨173136073720558505382135389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115424049147039003588090259 173136073720558505382135389)
    ·
      refine ⟨64926027645209439518300771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173136073720558505382135389 64926027645209439518300771)
      ·
        refine ⟨97389041467814159277451157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64926027645209439518300771 97389041467814159277451157)
        ·
          refine ⟨4565111318803788716130523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 97389041467814159277451157 4565111318803788716130523)
          ·
            refine ⟨6847666978205683074195785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4565111318803788716130523 6847666978205683074195785)
            ·
              refine ⟨5135750233654262305646839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6847666978205683074195785 5135750233654262305646839)
              ·
                refine ⟨7703625350481393458470259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5135750233654262305646839 7703625350481393458470259)
                ·
                  refine ⟨11555438025722090187705389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7703625350481393458470259 11555438025722090187705389)
                  ·
                    refine ⟨4333289259645783820389521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11555438025722090187705389 4333289259645783820389521)
                    ·
                      refine ⟨3249966944734337865292141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4333289259645783820389521 3249966944734337865292141)
                      ·
                        rfl

theorem cell23_6329288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 1, 1, 3, 2].length) (baseStart_6329288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329288 prefixEnd_6329288 := by exact prefixLift 6329288
  have htrace : WordTrace (prefixWord ++ tailWord_6329288) baseStart_6329288 baseEnd_6329288 := by
    simpa [prefixWord, tailWord_6329288, baseEnd_6329288] using wordTrace_append hprefix tailTrace_6329288
  have hstable : (prefixWord ++ tailWord_6329288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329288).length < 2 ^ (prefixWord ++ tailWord_6329288).sum := by decide
  have hdescent : baseEnd_6329288 < baseStart_6329288 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329313 : List Nat := [1, 2, 3, 1, 2, 1, 1, 3, 1, 1, 7]
def baseStart_6329313 : Nat := 118140960795 + 6329313 * 2 ^ 59
def prefixEnd_6329313 : Nat := 4983230072969 + 3 ^ 40 * 6329313 * 2
def baseEnd_6329313 : Nat := 3249979781750700267479525

theorem tailTrace_6329313 : CollatzResearch.WordTrace tailWord_6329313 prefixEnd_6329313 3249979781750700267479525 := by
  unfold tailWord_6329313
  simp only [CollatzResearch.WordTrace]
  refine ⟨230849010118987436445840593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153899340079324957630560395 230849010118987436445840593)
  ·
    refine ⟨173136757589240577334380445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230849010118987436445840593 173136757589240577334380445)
    ·
      refine ⟨64926284095965216500392667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173136757589240577334380445 64926284095965216500392667)
      ·
        refine ⟨97389426143947824750589001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64926284095965216500392667 97389426143947824750589001)
        ·
          refine ⟨73042069607960868562941751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97389426143947824750589001 73042069607960868562941751)
          ·
            refine ⟨109563104411941302844412627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73042069607960868562941751 109563104411941302844412627)
            ·
              refine ⟨164344656617911954266618941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109563104411941302844412627 164344656617911954266618941)
              ·
                refine ⟨61629246231716982849982103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164344656617911954266618941 61629246231716982849982103)
                ·
                  refine ⟨92443869347575474274973155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61629246231716982849982103 92443869347575474274973155)
                  ·
                    refine ⟨138665804021363211412459733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 92443869347575474274973155 138665804021363211412459733)
                    ·
                      refine ⟨3249979781750700267479525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 138665804021363211412459733 3249979781750700267479525)
                      ·
                        rfl

theorem cell23_6329313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_6329313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329313 prefixEnd_6329313 := by exact prefixLift 6329313
  have htrace : WordTrace (prefixWord ++ tailWord_6329313) baseStart_6329313 baseEnd_6329313 := by
    simpa [prefixWord, tailWord_6329313, baseEnd_6329313] using wordTrace_append hprefix tailTrace_6329313
  have hstable : (prefixWord ++ tailWord_6329313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329313).length < 2 ^ (prefixWord ++ tailWord_6329313).sum := by decide
  have hdescent : baseEnd_6329313 < baseStart_6329313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329340 : List Nat := [2, 2, 2, 1, 2, 3, 2, 1, 1, 3, 4]
def baseStart_6329340 : Nat := 118140960795 + 6329340 * 2 ^ 59
def prefixEnd_6329340 : Nat := 4983230072969 + 3 ^ 40 * 6329340 * 2
def baseEnd_6329340 : Nat := 3249993645728371661841901

theorem tailTrace_6329340 : CollatzResearch.WordTrace tailWord_6329340 prefixEnd_6329340 3249993645728371661841901 := by
  unfold tailWord_6329340
  simp only [CollatzResearch.WordTrace]
  refine ⟨115424997444944810028536737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153899996593259746704715649 115424997444944810028536737)
  ·
    refine ⟨86568748083708607521402553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115424997444944810028536737 86568748083708607521402553)
    ·
      refine ⟨64926561062781455641051915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86568748083708607521402553 64926561062781455641051915)
      ·
        refine ⟨97389841594172183461577873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64926561062781455641051915 97389841594172183461577873)
        ·
          refine ⟨73042381195629137596183405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97389841594172183461577873 73042381195629137596183405)
          ·
            refine ⟨27390892948360926598568777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73042381195629137596183405 27390892948360926598568777)
            ·
              refine ⟨20543169711270694948926583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27390892948360926598568777 20543169711270694948926583)
              ·
                refine ⟨30814754566906042423389875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20543169711270694948926583 30814754566906042423389875)
                ·
                  refine ⟨46222131850359063635084813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30814754566906042423389875 46222131850359063635084813)
                  ·
                    refine ⟨17333299443884648863156805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46222131850359063635084813 17333299443884648863156805)
                    ·
                      refine ⟨3249993645728371661841901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17333299443884648863156805 3249993645728371661841901)
                      ·
                        rfl

theorem cell23_6329340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_6329340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329340 prefixEnd_6329340 := by exact prefixLift 6329340
  have htrace : WordTrace (prefixWord ++ tailWord_6329340) baseStart_6329340 baseEnd_6329340 := by
    simpa [prefixWord, tailWord_6329340, baseEnd_6329340] using wordTrace_append hprefix tailTrace_6329340
  have hstable : (prefixWord ++ tailWord_6329340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329340).length < 2 ^ (prefixWord ++ tailWord_6329340).sum := by decide
  have hdescent : baseEnd_6329340 < baseStart_6329340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329343 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 5]
def baseStart_6329343 : Nat := 118140960795 + 6329343 * 2 ^ 59
def prefixEnd_6329343 : Nat := 4983230072969 + 3 ^ 40 * 6329343 * 2
def baseEnd_6329343 : Nat := 3249995186170335150104387

theorem tailTrace_6329343 : CollatzResearch.WordTrace tailWord_6329343 prefixEnd_6329343 3249995186170335150104387 := by
  unfold tailWord_6329343
  simp only [CollatzResearch.WordTrace]
  refine ⟨230850104308878751569432683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153900069539252501046288455 230850104308878751569432683)
  ·
    refine ⟨346275156463318127354149025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230850104308878751569432683 346275156463318127354149025)
    ·
      refine ⟨259706367347488595515611769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346275156463318127354149025 259706367347488595515611769)
      ·
        refine ⟨194779775510616446636708827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259706367347488595515611769 194779775510616446636708827)
        ·
          refine ⟨292169663265924669955063241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194779775510616446636708827 292169663265924669955063241)
          ·
            refine ⟨219127247449443502466297431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292169663265924669955063241 219127247449443502466297431)
            ·
              refine ⟨328690871174165253699446147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219127247449443502466297431 328690871174165253699446147)
              ·
                refine ⟨493036306761247880549169221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 328690871174165253699446147 493036306761247880549169221)
                ·
                  refine ⟨92444307517733977602969229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 493036306761247880549169221 92444307517733977602969229)
                  ·
                    refine ⟨34666615319150241601113461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92444307517733977602969229 34666615319150241601113461)
                    ·
                      refine ⟨3249995186170335150104387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34666615319150241601113461 3249995186170335150104387)
                      ·
                        rfl

theorem cell23_6329343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_6329343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329343 prefixEnd_6329343 := by exact prefixLift 6329343
  have htrace : WordTrace (prefixWord ++ tailWord_6329343) baseStart_6329343 baseEnd_6329343 := by
    simpa [prefixWord, tailWord_6329343, baseEnd_6329343] using wordTrace_append hprefix tailTrace_6329343
  have hstable : (prefixWord ++ tailWord_6329343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329343).length < 2 ^ (prefixWord ++ tailWord_6329343).sum := by decide
  have hdescent : baseEnd_6329343 < baseStart_6329343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329353 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 1, 3, 6]
def baseStart_6329353 : Nat := 118140960795 + 6329353 * 2 ^ 59
def prefixEnd_6329353 : Nat := 4983230072969 + 3 ^ 40 * 6329353 * 2
def baseEnd_6329353 : Nat := 3250000320976880110979341

theorem tailTrace_6329353 : CollatzResearch.WordTrace tailWord_6329353 prefixEnd_6329353 3250000320976880110979341 := by
  unfold tailWord_6329353
  simp only [CollatzResearch.WordTrace]
  refine ⟨230850469038842523277296713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153900312692561682184864475 230850469038842523277296713)
  ·
    refine ⟨173137851779131892457972535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230850469038842523277296713 173137851779131892457972535)
    ·
      refine ⟨259706777668697838686958803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173137851779131892457972535 259706777668697838686958803)
      ·
        refine ⟨389560166503046758030438205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259706777668697838686958803 389560166503046758030438205)
        ·
          refine ⟨146085062438642534261414327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 389560166503046758030438205 146085062438642534261414327)
          ·
            refine ⟨219127593657963801392121491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146085062438642534261414327 219127593657963801392121491)
            ·
              refine ⟨328691390486945702088182237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219127593657963801392121491 328691390486945702088182237)
              ·
                refine ⟨123259271432604638283068339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 328691390486945702088182237 123259271432604638283068339)
                ·
                  refine ⟨184888907148906957424602509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123259271432604638283068339 184888907148906957424602509)
                  ·
                    refine ⟨69333340180840109034225941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 184888907148906957424602509 69333340180840109034225941)
                    ·
                      refine ⟨3250000320976880110979341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69333340180840109034225941 3250000320976880110979341)
                      ·
                        rfl

theorem cell23_6329353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 3, 6].length) (baseStart_6329353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329353 prefixEnd_6329353 := by exact prefixLift 6329353
  have htrace : WordTrace (prefixWord ++ tailWord_6329353) baseStart_6329353 baseEnd_6329353 := by
    simpa [prefixWord, tailWord_6329353, baseEnd_6329353] using wordTrace_append hprefix tailTrace_6329353
  have hstable : (prefixWord ++ tailWord_6329353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329353).length < 2 ^ (prefixWord ++ tailWord_6329353).sum := by decide
  have hdescent : baseEnd_6329353 < baseStart_6329353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329414 : List Nat := [6, 1, 1, 1, 1, 2, 1, 4, 6]
def baseStart_6329414 : Nat := 118140960795 + 6329414 * 2 ^ 59
def prefixEnd_6329414 : Nat := 4983230072969 + 3 ^ 40 * 6329414 * 2
def baseEnd_6329414 : Nat := 361114627032978263590729

theorem tailTrace_6329414 : CollatzResearch.WordTrace tailWord_6329414 prefixEnd_6329414 361114627032978263590729 := by
  unfold tailWord_6329414
  simp only [CollatzResearch.WordTrace]
  refine ⟨7214146684113172834227103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 153901795927747687130178197 7214146684113172834227103)
  ·
    refine ⟨10821220026169759251340655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7214146684113172834227103 10821220026169759251340655)
    ·
      refine ⟨16231830039254638877010983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10821220026169759251340655 16231830039254638877010983)
      ·
        refine ⟨24347745058881958315516475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16231830039254638877010983 24347745058881958315516475)
        ·
          refine ⟨36521617588322937473274713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24347745058881958315516475 36521617588322937473274713)
          ·
            refine ⟨27391213191242203104956035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36521617588322937473274713 27391213191242203104956035)
            ·
              refine ⟨41086819786863304657434053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27391213191242203104956035 41086819786863304657434053)
              ·
                refine ⟨7703778710036869623268885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41086819786863304657434053 7703778710036869623268885)
                ·
                  refine ⟨361114627032978263590729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7703778710036869623268885 361114627032978263590729)
                  ·
                    rfl

theorem cell23_6329414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_6329414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329414 prefixEnd_6329414 := by exact prefixLift 6329414
  have htrace : WordTrace (prefixWord ++ tailWord_6329414) baseStart_6329414 baseEnd_6329414 := by
    simpa [prefixWord, tailWord_6329414, baseEnd_6329414] using wordTrace_append hprefix tailTrace_6329414
  have hstable : (prefixWord ++ tailWord_6329414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329414).length < 2 ^ (prefixWord ++ tailWord_6329414).sum := by decide
  have hdescent : baseEnd_6329414 < baseStart_6329414 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329417 : List Nat := [1, 2, 1, 1, 2, 2, 2, 3, 4, 3, 2]
def baseStart_6329417 : Nat := 118140960795 + 6329417 * 2 ^ 59
def prefixEnd_6329417 : Nat := 4983230072969 + 3 ^ 40 * 6329417 * 2
def baseEnd_6329417 : Nat := 3250033183738767860579047

theorem tailTrace_6329417 : CollatzResearch.WordTrace tailWord_6329417 prefixEnd_6329417 3250033183738767860579047 := by
  unfold tailWord_6329417
  simp only [CollatzResearch.WordTrace]
  refine ⟨230852803310610662207626505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153901868873740441471751003 230852803310610662207626505)
  ·
    refine ⟨173139602482957996655719879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230852803310610662207626505 173139602482957996655719879)
    ·
      refine ⟨259709403724436994983579819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173139602482957996655719879 259709403724436994983579819)
      ·
        refine ⟨389564105586655492475369729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259709403724436994983579819 389564105586655492475369729)
        ·
          refine ⟨292173079189991619356527297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 389564105586655492475369729 292173079189991619356527297)
          ·
            refine ⟨219129809392493714517395473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292173079189991619356527297 219129809392493714517395473)
            ·
              refine ⟨164347357044370285888046605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219129809392493714517395473 164347357044370285888046605)
              ·
                refine ⟨61630258891638857208017477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164347357044370285888046605 61630258891638857208017477)
                ·
                  refine ⟨11555673542182285726503277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61630258891638857208017477 11555673542182285726503277)
                  ·
                    refine ⟨4333377578318357147438729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11555673542182285726503277 4333377578318357147438729)
                    ·
                      refine ⟨3250033183738767860579047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4333377578318357147438729 3250033183738767860579047)
                      ·
                        rfl

theorem cell23_6329417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 4, 3, 2].length) (baseStart_6329417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329417 prefixEnd_6329417 := by exact prefixLift 6329417
  have htrace : WordTrace (prefixWord ++ tailWord_6329417) baseStart_6329417 baseEnd_6329417 := by
    simpa [prefixWord, tailWord_6329417, baseEnd_6329417] using wordTrace_append hprefix tailTrace_6329417
  have hstable : (prefixWord ++ tailWord_6329417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329417).length < 2 ^ (prefixWord ++ tailWord_6329417).sum := by decide
  have hdescent : baseEnd_6329417 < baseStart_6329417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329447 : List Nat := [1, 1, 5, 1, 1, 3, 2, 1, 3, 1, 4]
def baseStart_6329447 : Nat := 118140960795 + 6329447 * 2 ^ 59
def prefixEnd_6329447 : Nat := 4983230072969 + 3 ^ 40 * 6329447 * 2
def baseEnd_6329447 : Nat := 3250048588158402743203909

theorem tailTrace_6329447 : CollatzResearch.WordTrace tailWord_6329447 prefixEnd_6329447 3250048588158402743203909 := by
  unfold tailWord_6329447
  simp only [CollatzResearch.WordTrace]
  refine ⟨230853897500501977331218595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153902598333667984887479063 230853897500501977331218595)
  ·
    refine ⟨346280846250752965996827893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230853897500501977331218595 346280846250752965996827893)
    ·
      refine ⟨32463829336008090562202615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 346280846250752965996827893 32463829336008090562202615)
      ·
        refine ⟨48695744004012135843303923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32463829336008090562202615 48695744004012135843303923)
        ·
          refine ⟨73043616006018203764955885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48695744004012135843303923 73043616006018203764955885)
          ·
            refine ⟨27391356002256826411858457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73043616006018203764955885 27391356002256826411858457)
            ·
              refine ⟨20543517001692619808893843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27391356002256826411858457 20543517001692619808893843)
              ·
                refine ⟨30815275502538929713340765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20543517001692619808893843 30815275502538929713340765)
                ·
                  refine ⟨11555728313452098642502787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30815275502538929713340765 11555728313452098642502787)
                  ·
                    refine ⟨17333592470178147963754181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11555728313452098642502787 17333592470178147963754181)
                    ·
                      refine ⟨3250048588158402743203909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17333592470178147963754181 3250048588158402743203909)
                      ·
                        rfl

theorem cell23_6329447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_6329447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329447 prefixEnd_6329447 := by exact prefixLift 6329447
  have htrace : WordTrace (prefixWord ++ tailWord_6329447) baseStart_6329447 baseEnd_6329447 := by
    simpa [prefixWord, tailWord_6329447, baseEnd_6329447] using wordTrace_append hprefix tailTrace_6329447
  have hstable : (prefixWord ++ tailWord_6329447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329447).length < 2 ^ (prefixWord ++ tailWord_6329447).sum := by decide
  have hdescent : baseEnd_6329447 < baseStart_6329447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329461 : List Nat := [1, 3, 4, 3, 1, 1, 1, 3, 1, 5]
def baseStart_6329461 : Nat := 118140960795 + 6329461 * 2 ^ 59
def prefixEnd_6329461 : Nat := 4983230072969 + 3 ^ 40 * 6329461 * 2
def baseEnd_6329461 : Nat := 1083351925629188562809615

theorem tailTrace_6329461 : CollatzResearch.WordTrace tailWord_6329461 prefixEnd_6329461 1083351925629188562809615 := by
  unfold tailWord_6329461
  simp only [CollatzResearch.WordTrace]
  refine ⟨230854408122451257722228237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153902938748300838481485491 230854408122451257722228237)
  ·
    refine ⟨86570403045919221645835589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230854408122451257722228237 86570403045919221645835589)
    ·
      refine ⟨16231950571109854058594173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86570403045919221645835589 16231950571109854058594173)
      ·
        refine ⟨6086981464166195271972815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16231950571109854058594173 6086981464166195271972815)
        ·
          refine ⟨9130472196249292907959223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6086981464166195271972815 9130472196249292907959223)
          ·
            refine ⟨13695708294373939361938835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9130472196249292907959223 13695708294373939361938835)
            ·
              refine ⟨20543562441560909042908253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13695708294373939361938835 20543562441560909042908253)
              ·
                refine ⟨7703835915585340891090595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20543562441560909042908253 7703835915585340891090595)
                ·
                  refine ⟨11555753873378011336635893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7703835915585340891090595 11555753873378011336635893)
                  ·
                    refine ⟨1083351925629188562809615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11555753873378011336635893 1083351925629188562809615)
                    ·
                      rfl

theorem cell23_6329461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_6329461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329461 prefixEnd_6329461 := by exact prefixLift 6329461
  have htrace : WordTrace (prefixWord ++ tailWord_6329461) baseStart_6329461 baseEnd_6329461 := by
    simpa [prefixWord, tailWord_6329461, baseEnd_6329461] using wordTrace_append hprefix tailTrace_6329461
  have hstable : (prefixWord ++ tailWord_6329461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329461).length < 2 ^ (prefixWord ++ tailWord_6329461).sum := by decide
  have hdescent : baseEnd_6329461 < baseStart_6329461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329464 : List Nat := [2, 1, 2, 1, 1, 1, 8, 1, 1, 1, 4]
def baseStart_6329464 : Nat := 118140960795 + 6329464 * 2 ^ 59
def prefixEnd_6329464 : Nat := 4983230072969 + 3 ^ 40 * 6329464 * 2
def baseEnd_6329464 : Nat := 3250057317329529176691331

theorem tailTrace_6329464 : CollatzResearch.WordTrace tailWord_6329464 prefixEnd_6329464 3250057317329529176691331 := by
  unfold tailWord_6329464
  simp only [CollatzResearch.WordTrace]
  refine ⟨115427258770720194617293723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153903011694293592823058297 115427258770720194617293723)
  ·
    refine ⟨173140888156080291925940585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115427258770720194617293723 173140888156080291925940585)
    ·
      refine ⟨129855666117060218944455439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173140888156080291925940585 129855666117060218944455439)
      ·
        refine ⟨194783499175590328416683159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129855666117060218944455439 194783499175590328416683159)
        ·
          refine ⟨292175248763385492625024739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194783499175590328416683159 292175248763385492625024739)
          ·
            refine ⟨438262873145078238937537109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292175248763385492625024739 438262873145078238937537109)
            ·
              refine ⟨5135893044668885612549263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 438262873145078238937537109 5135893044668885612549263)
              ·
                refine ⟨7703839567003328418823895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5135893044668885612549263 7703839567003328418823895)
                ·
                  refine ⟨11555759350504992628235843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7703839567003328418823895 11555759350504992628235843)
                  ·
                    refine ⟨17333639025757488942353765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11555759350504992628235843 17333639025757488942353765)
                    ·
                      refine ⟨3250057317329529176691331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17333639025757488942353765 3250057317329529176691331)
                      ·
                        rfl

theorem cell23_6329464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 1, 1, 1, 4].length) (baseStart_6329464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329464 prefixEnd_6329464 := by exact prefixLift 6329464
  have htrace : WordTrace (prefixWord ++ tailWord_6329464) baseStart_6329464 baseEnd_6329464 := by
    simpa [prefixWord, tailWord_6329464, baseEnd_6329464] using wordTrace_append hprefix tailTrace_6329464
  have hstable : (prefixWord ++ tailWord_6329464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329464).length < 2 ^ (prefixWord ++ tailWord_6329464).sum := by decide
  have hdescent : baseEnd_6329464 < baseStart_6329464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329481 : List Nat := [1, 2, 1, 1, 4, 4, 2, 1, 3, 2, 2]
def baseStart_6329481 : Nat := 118140960795 + 6329481 * 2 ^ 59
def prefixEnd_6329481 : Nat := 4983230072969 + 3 ^ 40 * 6329481 * 2
def baseEnd_6329481 : Nat := 3250066046500655610178753

theorem tailTrace_6329481 : CollatzResearch.WordTrace tailWord_6329481 prefixEnd_6329481 3250066046500655610178753 := by
  unfold tailWord_6329481
  simp only [CollatzResearch.WordTrace]
  refine ⟨230855137582378801137956297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153903425054919200758637531 230855137582378801137956297)
  ·
    refine ⟨173141353186784100853467223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230855137582378801137956297 173141353186784100853467223)
    ·
      refine ⟨259712029780176151280200835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173141353186784100853467223 259712029780176151280200835)
      ·
        refine ⟨389568044670264226920301253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259712029780176151280200835 389568044670264226920301253)
        ·
          refine ⟨73044008375674542547556485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 389568044670264226920301253 73044008375674542547556485)
          ·
            refine ⟨13695751570438976727666841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73044008375674542547556485 13695751570438976727666841)
            ·
              refine ⟨10271813677829232545750131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13695751570438976727666841 10271813677829232545750131)
              ·
                refine ⟨15407720516743848818625197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10271813677829232545750131 15407720516743848818625197)
                ·
                  refine ⟨5777895193778943306984449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15407720516743848818625197 5777895193778943306984449)
                  ·
                    refine ⟨4333421395334207480238337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5777895193778943306984449 4333421395334207480238337)
                    ·
                      refine ⟨3250066046500655610178753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4333421395334207480238337 3250066046500655610178753)
                      ·
                        rfl

theorem cell23_6329481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 3, 2, 2].length) (baseStart_6329481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329481 prefixEnd_6329481 := by exact prefixLift 6329481
  have htrace : WordTrace (prefixWord ++ tailWord_6329481) baseStart_6329481 baseEnd_6329481 := by
    simpa [prefixWord, tailWord_6329481, baseEnd_6329481] using wordTrace_append hprefix tailTrace_6329481
  have hstable : (prefixWord ++ tailWord_6329481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329481).length < 2 ^ (prefixWord ++ tailWord_6329481).sum := by decide
  have hdescent : baseEnd_6329481 < baseStart_6329481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329507 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 2, 7, 2]
def baseStart_6329507 : Nat := 118140960795 + 6329507 * 2 ^ 59
def prefixEnd_6329507 : Nat := 4983230072969 + 3 ^ 40 * 6329507 * 2
def baseEnd_6329507 : Nat := 3250079396997672508453633

theorem tailTrace_6329507 : CollatzResearch.WordTrace tailWord_6329507 prefixEnd_6329507 3250079396997672508453633 := by
  unfold tailWord_6329507
  simp only [CollatzResearch.WordTrace]
  refine ⟨230856085880284607578402775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153904057253523071718935183 230856085880284607578402775)
  ·
    refine ⟨346284128820426911367604163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230856085880284607578402775 346284128820426911367604163)
    ·
      refine ⟨519426193230640367051406245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346284128820426911367604163 519426193230640367051406245)
      ·
        refine ⟨97392411230745068822138671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 519426193230640367051406245 97392411230745068822138671)
        ·
          refine ⟨146088616846117603233208007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97392411230745068822138671 146088616846117603233208007)
          ·
            refine ⟨219132925269176404849812011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146088616846117603233208007 219132925269176404849812011)
            ·
              refine ⟨328699387903764607274718017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219132925269176404849812011 328699387903764607274718017)
              ·
                refine ⟨246524540927823455456038513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 328699387903764607274718017 246524540927823455456038513)
                ·
                  refine ⟨184893405695867591592028885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 246524540927823455456038513 184893405695867591592028885)
                  ·
                    refine ⟨4333439195996896677938177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 184893405695867591592028885 4333439195996896677938177)
                    ·
                      refine ⟨3250079396997672508453633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4333439195996896677938177 3250079396997672508453633)
                      ·
                        rfl

theorem cell23_6329507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 7, 2].length) (baseStart_6329507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329507 prefixEnd_6329507 := by exact prefixLift 6329507
  have htrace : WordTrace (prefixWord ++ tailWord_6329507) baseStart_6329507 baseEnd_6329507 := by
    simpa [prefixWord, tailWord_6329507, baseEnd_6329507] using wordTrace_append hprefix tailTrace_6329507
  have hstable : (prefixWord ++ tailWord_6329507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329507).length < 2 ^ (prefixWord ++ tailWord_6329507).sum := by decide
  have hdescent : baseEnd_6329507 < baseStart_6329507 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329575 : List Nat := [1, 1, 5, 3, 2, 1, 3, 1, 1, 3, 2]
def baseStart_6329575 : Nat := 118140960795 + 6329575 * 2 ^ 59
def prefixEnd_6329575 : Nat := 4983230072969 + 3 ^ 40 * 6329575 * 2
def baseEnd_6329575 : Nat := 3250114313682178242403321

theorem tailTrace_6329575 : CollatzResearch.WordTrace tailWord_6329575 prefixEnd_6329575 3250114313682178242403321 := by
  unfold tailWord_6329575
  simp only [CollatzResearch.WordTrace]
  refine ⟨230858566044038255191878179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153905710696025503461252119 230858566044038255191878179)
  ·
    refine ⟨346287849066057382787817269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230858566044038255191878179 346287849066057382787817269)
    ·
      refine ⟨32464485849942879636357869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 346287849066057382787817269 32464485849942879636357869)
      ·
        refine ⟨12174182193728579863634201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32464485849942879636357869 12174182193728579863634201)
        ·
          refine ⟨9130636645296434897725651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12174182193728579863634201 9130636645296434897725651)
          ·
            refine ⟨13695954967944652346588477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9130636645296434897725651 13695954967944652346588477)
            ·
              refine ⟨5135983112979244629970679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13695954967944652346588477 5135983112979244629970679)
              ·
                refine ⟨7703974669468866944956019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5135983112979244629970679 7703974669468866944956019)
                ·
                  refine ⟨11555962004203300417434029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7703974669468866944956019 11555962004203300417434029)
                  ·
                    refine ⟨4333485751576237656537761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11555962004203300417434029 4333485751576237656537761)
                    ·
                      refine ⟨3250114313682178242403321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4333485751576237656537761 3250114313682178242403321)
                      ·
                        rfl

theorem cell23_6329575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_6329575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329575 prefixEnd_6329575 := by exact prefixLift 6329575
  have htrace : WordTrace (prefixWord ++ tailWord_6329575) baseStart_6329575 baseEnd_6329575 := by
    simpa [prefixWord, tailWord_6329575, baseEnd_6329575] using wordTrace_append hprefix tailTrace_6329575
  have hstable : (prefixWord ++ tailWord_6329575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329575).length < 2 ^ (prefixWord ++ tailWord_6329575).sum := by decide
  have hdescent : baseEnd_6329575 < baseStart_6329575 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329594 : List Nat := [3, 1, 1, 1, 1, 4, 3, 4, 5]
def baseStart_6329594 : Nat := 118140960795 + 6329594 * 2 ^ 59
def prefixEnd_6329594 : Nat := 4983230072969 + 3 ^ 40 * 6329594 * 2
def baseEnd_6329594 : Nat := 361124896646068185340637

theorem tailTrace_6329594 : CollatzResearch.WordTrace tailWord_6329594 prefixEnd_6329594 361124896646068185340637 := by
  unfold tailWord_6329594
  simp only [CollatzResearch.WordTrace]
  refine ⟨57714814757742355359204959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153906172687312947624546557 57714814757742355359204959)
  ·
    refine ⟨86572222136613533038807439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57714814757742355359204959 86572222136613533038807439)
    ·
      refine ⟨129858333204920299558211159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86572222136613533038807439 129858333204920299558211159)
      ·
        refine ⟨194787499807380449337316739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129858333204920299558211159 194787499807380449337316739)
        ·
          refine ⟨292181249711070674005975109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194787499807380449337316739 292181249711070674005975109)
          ·
            refine ⟨54783984320825751376120333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 292181249711070674005975109 54783984320825751376120333)
            ·
              refine ⟨20543994120309656766045125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54783984320825751376120333 20543994120309656766045125)
              ·
                refine ⟨3851998897558060643633461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20543994120309656766045125 3851998897558060643633461)
                ·
                  refine ⟨361124896646068185340637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3851998897558060643633461 361124896646068185340637)
                  ·
                    rfl

theorem cell23_6329594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 4, 5].length) (baseStart_6329594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329594 prefixEnd_6329594 := by exact prefixLift 6329594
  have htrace : WordTrace (prefixWord ++ tailWord_6329594) baseStart_6329594 baseEnd_6329594 := by
    simpa [prefixWord, tailWord_6329594, baseEnd_6329594] using wordTrace_append hprefix tailTrace_6329594
  have hstable : (prefixWord ++ tailWord_6329594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329594).length < 2 ^ (prefixWord ++ tailWord_6329594).sum := by decide
  have hdescent : baseEnd_6329594 < baseStart_6329594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329604 : List Nat := [2, 3, 2, 2, 2, 1, 1, 1, 1, 5, 3]
def baseStart_6329604 : Nat := 118140960795 + 6329604 * 2 ^ 59
def prefixEnd_6329604 : Nat := 4983230072969 + 3 ^ 40 * 6329604 * 2
def baseEnd_6329604 : Nat := 3250129204621158628940687

theorem tailTrace_6329604 : CollatzResearch.WordTrace tailWord_6329604 prefixEnd_6329604 3250129204621158628940687 := by
  unfold tailWord_6329604
  simp only [CollatzResearch.WordTrace]
  refine ⟨115429811880466596572341933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153906415840622128763122577 115429811880466596572341933)
  ·
    refine ⟨43286179455174973714628225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115429811880466596572341933 43286179455174973714628225)
    ·
      refine ⟨32464634591381230285971169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43286179455174973714628225 32464634591381230285971169)
      ·
        refine ⟨24348475943535922714478377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32464634591381230285971169 24348475943535922714478377)
        ·
          refine ⟨18261356957651942035858783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24348475943535922714478377 18261356957651942035858783)
          ·
            refine ⟨27392035436477913053788175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18261356957651942035858783 27392035436477913053788175)
            ·
              refine ⟨41088053154716869580682263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27392035436477913053788175 41088053154716869580682263)
              ·
                refine ⟨61632079732075304371023395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41088053154716869580682263 61632079732075304371023395)
                ·
                  refine ⟨92448119598112956556535093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61632079732075304371023395 92448119598112956556535093)
                  ·
                    refine ⟨8667011212323089677175165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 92448119598112956556535093 8667011212323089677175165)
                    ·
                      refine ⟨3250129204621158628940687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8667011212323089677175165 3250129204621158628940687)
                      ·
                        rfl

theorem cell23_6329604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_6329604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329604 prefixEnd_6329604 := by exact prefixLift 6329604
  have htrace : WordTrace (prefixWord ++ tailWord_6329604) baseStart_6329604 baseEnd_6329604 := by
    simpa [prefixWord, tailWord_6329604, baseEnd_6329604] using wordTrace_append hprefix tailTrace_6329604
  have hstable : (prefixWord ++ tailWord_6329604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329604).length < 2 ^ (prefixWord ++ tailWord_6329604).sum := by decide
  have hdescent : baseEnd_6329604 < baseStart_6329604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329624 : List Nat := [2, 1, 2, 3, 1, 3, 3, 1, 2, 5]
def baseStart_6329624 : Nat := 118140960795 + 6329624 * 2 ^ 59
def prefixEnd_6329624 : Nat := 4983230072969 + 3 ^ 40 * 6329624 * 2
def baseEnd_6329624 : Nat := 1083379824744749516896865

theorem tailTrace_6329624 : CollatzResearch.WordTrace tailWord_6329624 prefixEnd_6329624 1083379824744749516896865 := by
  unfold tailWord_6329624
  simp only [CollatzResearch.WordTrace]
  refine ⟨115430176610430368280205963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153906902147240491040274617 115430176610430368280205963)
  ·
    refine ⟨173145264915645552420308945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115430176610430368280205963 173145264915645552420308945)
    ·
      refine ⟨129858948686734164315231709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173145264915645552420308945 129858948686734164315231709)
      ·
        refine ⟨48697105757525311618211891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129858948686734164315231709 48697105757525311618211891)
        ·
          refine ⟨73045658636287967427317837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48697105757525311618211891 73045658636287967427317837)
          ·
            refine ⟨27392121988607987785244189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73045658636287967427317837 27392121988607987785244189)
            ·
              refine ⟨10272045745727995419466571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27392121988607987785244189 10272045745727995419466571)
              ·
                refine ⟨15408068618591993129199857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10272045745727995419466571 15408068618591993129199857)
                ·
                  refine ⟨11556051463943994846899893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15408068618591993129199857 11556051463943994846899893)
                  ·
                    refine ⟨1083379824744749516896865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11556051463943994846899893 1083379824744749516896865)
                    ·
                      rfl

theorem cell23_6329624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 2, 5].length) (baseStart_6329624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329624 prefixEnd_6329624 := by exact prefixLift 6329624
  have htrace : WordTrace (prefixWord ++ tailWord_6329624) baseStart_6329624 baseEnd_6329624 := by
    simpa [prefixWord, tailWord_6329624, baseEnd_6329624] using wordTrace_append hprefix tailTrace_6329624
  have hstable : (prefixWord ++ tailWord_6329624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329624).length < 2 ^ (prefixWord ++ tailWord_6329624).sum := by decide
  have hdescent : baseEnd_6329624 < baseStart_6329624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329714 : List Nat := [3, 2, 1, 2, 1, 2, 2, 2, 3, 5]
def baseStart_6329714 : Nat := 118140960795 + 6329714 * 2 ^ 59
def prefixEnd_6329714 : Nat := 4983230072969 + 3 ^ 40 * 6329714 * 2
def baseEnd_6329714 : Nat := 1083395229164384399521727

theorem tailTrace_6329714 : CollatzResearch.WordTrace tailWord_6329714 prefixEnd_6329714 1083395229164384399521727 := by
  unfold tailWord_6329714
  simp only [CollatzResearch.WordTrace]
  refine ⟨57715908947633670482797049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153909090527023121287458797 57715908947633670482797049)
  ·
    refine ⟨43286931710725252862097787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57715908947633670482797049 43286931710725252862097787)
    ·
      refine ⟨64930397566087879293146681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43286931710725252862097787 64930397566087879293146681)
      ·
        refine ⟨48697798174565909469860011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64930397566087879293146681 48697798174565909469860011)
        ·
          refine ⟨73046697261848864204790017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48697798174565909469860011 73046697261848864204790017)
          ·
            refine ⟨54785022946386648153592513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73046697261848864204790017 54785022946386648153592513)
            ·
              refine ⟨41088767209789986115194385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54785022946386648153592513 41088767209789986115194385)
              ·
                refine ⟨30816575407342489586395789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41088767209789986115194385 30816575407342489586395789)
                ·
                  refine ⟨11556215777753433594898421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30816575407342489586395789 11556215777753433594898421)
                  ·
                    refine ⟨1083395229164384399521727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11556215777753433594898421 1083395229164384399521727)
                    ·
                      rfl

theorem cell23_6329714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_6329714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329714 prefixEnd_6329714 := by exact prefixLift 6329714
  have htrace : WordTrace (prefixWord ++ tailWord_6329714) baseStart_6329714 baseEnd_6329714 := by
    simpa [prefixWord, tailWord_6329714, baseEnd_6329714] using wordTrace_append hprefix tailTrace_6329714
  have hstable : (prefixWord ++ tailWord_6329714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329714).length < 2 ^ (prefixWord ++ tailWord_6329714).sum := by decide
  have hdescent : baseEnd_6329714 < baseStart_6329714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329731 : List Nat := [1, 1, 1, 3, 5, 1, 3, 2, 1, 5]
def baseStart_6329731 : Nat := 118140960795 + 6329731 * 2 ^ 59
def prefixEnd_6329731 : Nat := 4983230072969 + 3 ^ 40 * 6329731 * 2
def baseEnd_6329731 : Nat := 1083398138888093210684201

theorem tailTrace_6329731 : CollatzResearch.WordTrace tailWord_6329731 prefixEnd_6329731 1083398138888093210684201 := by
  unfold tailWord_6329731
  simp only [CollatzResearch.WordTrace]
  refine ⟨230864255831473093834557047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153909503887648729223038031 230864255831473093834557047)
  ·
    refine ⟨346296383747209640751835571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230864255831473093834557047 346296383747209640751835571)
    ·
      refine ⟨519444575620814461127753357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346296383747209640751835571 519444575620814461127753357)
      ·
        refine ⟨194791715857805422922907509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 519444575620814461127753357 194791715857805422922907509)
        ·
          refine ⟨18261723361669258399022579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 194791715857805422922907509 18261723361669258399022579)
          ·
            refine ⟨27392585042503887598533869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18261723361669258399022579 27392585042503887598533869)
            ·
              refine ⟨10272219390938957849450201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27392585042503887598533869 10272219390938957849450201)
              ·
                refine ⟨7704164543204218387087651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10272219390938957849450201 7704164543204218387087651)
                ·
                  refine ⟨11556246814806327580631477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7704164543204218387087651 11556246814806327580631477)
                  ·
                    refine ⟨1083398138888093210684201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11556246814806327580631477 1083398138888093210684201)
                    ·
                      rfl

theorem cell23_6329731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 2, 1, 5].length) (baseStart_6329731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329731 prefixEnd_6329731 := by exact prefixLift 6329731
  have htrace : WordTrace (prefixWord ++ tailWord_6329731) baseStart_6329731 baseEnd_6329731 := by
    simpa [prefixWord, tailWord_6329731, baseEnd_6329731] using wordTrace_append hprefix tailTrace_6329731
  have hstable : (prefixWord ++ tailWord_6329731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329731).length < 2 ^ (prefixWord ++ tailWord_6329731).sum := by decide
  have hdescent : baseEnd_6329731 < baseStart_6329731 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329747 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 6]
def baseStart_6329747 : Nat := 118140960795 + 6329747 * 2 ^ 59
def prefixEnd_6329747 : Nat := 4983230072969 + 3 ^ 40 * 6329747 * 2
def baseEnd_6329747 : Nat := 3250202632354751569452529

theorem tailTrace_6329747 : CollatzResearch.WordTrace tailWord_6329747 prefixEnd_6329747 3250202632354751569452529 := by
  unfold tailWord_6329747
  simp only [CollatzResearch.WordTrace]
  refine ⟨230864839399415128567139495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153909892932943419044759663 230864839399415128567139495)
  ·
    refine ⟨346297259099122692850709243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230864839399415128567139495 346297259099122692850709243)
    ·
      refine ⟨519445888648684039276063865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346297259099122692850709243 519445888648684039276063865)
      ·
        refine ⟨389584416486513029457047899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 519445888648684039276063865 389584416486513029457047899)
        ·
          refine ⟨584376624729769544185571849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389584416486513029457047899 584376624729769544185571849)
          ·
            refine ⟨438282468547327158139178887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 584376624729769544185571849 438282468547327158139178887)
            ·
              refine ⟨657423702820990737208768331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 438282468547327158139178887 657423702820990737208768331)
              ·
                refine ⟨986135554231486105813152497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 657423702820990737208768331 986135554231486105813152497)
                ·
                  refine ⟨739601665673614579359864373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 986135554231486105813152497 739601665673614579359864373)
                  ·
                    refine ⟨69337656156901366814987285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 739601665673614579359864373 69337656156901366814987285)
                    ·
                      refine ⟨3250202632354751569452529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69337656156901366814987285 3250202632354751569452529)
                      ·
                        rfl

theorem cell23_6329747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 6].length) (baseStart_6329747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329747 prefixEnd_6329747 := by exact prefixLift 6329747
  have htrace : WordTrace (prefixWord ++ tailWord_6329747) baseStart_6329747 baseEnd_6329747 := by
    simpa [prefixWord, tailWord_6329747, baseEnd_6329747] using wordTrace_append hprefix tailTrace_6329747
  have hstable : (prefixWord ++ tailWord_6329747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329747).length < 2 ^ (prefixWord ++ tailWord_6329747).sum := by decide
  have hdescent : baseEnd_6329747 < baseStart_6329747 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329762 : List Nat := [3, 3, 1, 2, 1, 2, 4, 2, 1, 1, 3]
def baseStart_6329762 : Nat := 118140960795 + 6329762 * 2 ^ 59
def prefixEnd_6329762 : Nat := 4983230072969 + 3 ^ 40 * 6329762 * 2
def baseEnd_6329762 : Nat := 3250210334564569010764961

theorem tailTrace_6329762 : CollatzResearch.WordTrace tailWord_6329762 prefixEnd_6329762 3250210334564569010764961 := by
  unfold tailWord_6329762
  simp only [CollatzResearch.WordTrace]
  refine ⟨57716346623590196532233885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153910257662907190752623693 57716346623590196532233885)
  ·
    refine ⟨21643629983846323699587707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57716346623590196532233885 21643629983846323699587707)
    ·
      refine ⟨32465444975769485549381561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21643629983846323699587707 32465444975769485549381561)
      ·
        refine ⟨24349083731827114162036171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32465444975769485549381561 24349083731827114162036171)
        ·
          refine ⟨36523625597740671243054257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24349083731827114162036171 36523625597740671243054257)
          ·
            refine ⟨27392719198305503432290693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36523625597740671243054257 27392719198305503432290693)
            ·
              refine ⟨5136134849682281893554505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27392719198305503432290693 5136134849682281893554505)
              ·
                refine ⟨3852101137261711420165879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5136134849682281893554505 3852101137261711420165879)
                ·
                  refine ⟨5778151705892567130248819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3852101137261711420165879 5778151705892567130248819)
                  ·
                    refine ⟨8667227558838850695373229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5778151705892567130248819 8667227558838850695373229)
                    ·
                      refine ⟨3250210334564569010764961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8667227558838850695373229 3250210334564569010764961)
                      ·
                        rfl

theorem cell23_6329762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_6329762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329762 prefixEnd_6329762 := by exact prefixLift 6329762
  have htrace : WordTrace (prefixWord ++ tailWord_6329762) baseStart_6329762 baseEnd_6329762 := by
    simpa [prefixWord, tailWord_6329762, baseEnd_6329762] using wordTrace_append hprefix tailTrace_6329762
  have hstable : (prefixWord ++ tailWord_6329762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329762).length < 2 ^ (prefixWord ++ tailWord_6329762).sum := by decide
  have hdescent : baseEnd_6329762 < baseStart_6329762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329764 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 5, 2, 4]
def baseStart_6329764 : Nat := 118140960795 + 6329764 * 2 ^ 59
def prefixEnd_6329764 : Nat := 4983230072969 + 3 ^ 40 * 6329764 * 2
def baseEnd_6329764 : Nat := 3250211361525878002939951

theorem tailTrace_6329764 : CollatzResearch.WordTrace tailWord_6329764 prefixEnd_6329764 3250211361525878002939951 := by
  unfold tailWord_6329764
  simp only [CollatzResearch.WordTrace]
  refine ⟨115432729720176770235254173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153910306293569026980338897 115432729720176770235254173)
  ·
    refine ⟨43287273645066288838220315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115432729720176770235254173 43287273645066288838220315)
    ·
      refine ⟨64930910467599433257330473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43287273645066288838220315 64930910467599433257330473)
      ·
        refine ⟨48698182850699574942997855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64930910467599433257330473 48698182850699574942997855)
        ·
          refine ⟨73047274276049362414496783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48698182850699574942997855 73047274276049362414496783)
          ·
            refine ⟨109570911414074043621745175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73047274276049362414496783 109570911414074043621745175)
            ·
              refine ⟨164356367121111065432617763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109570911414074043621745175 164356367121111065432617763)
              ·
                refine ⟨246534550681666598148926645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164356367121111065432617763 246534550681666598148926645)
                ·
                  refine ⟨23112614126406243576461873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 246534550681666598148926645 23112614126406243576461873)
                  ·
                    refine ⟨17334460594804682682346405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23112614126406243576461873 17334460594804682682346405)
                    ·
                      refine ⟨3250211361525878002939951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17334460594804682682346405 3250211361525878002939951)
                      ·
                        rfl

theorem cell23_6329764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_6329764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329764 prefixEnd_6329764 := by exact prefixLift 6329764
  have htrace : WordTrace (prefixWord ++ tailWord_6329764) baseStart_6329764 baseEnd_6329764 := by
    simpa [prefixWord, tailWord_6329764, baseEnd_6329764] using wordTrace_append hprefix tailTrace_6329764
  have hstable : (prefixWord ++ tailWord_6329764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329764).length < 2 ^ (prefixWord ++ tailWord_6329764).sum := by decide
  have hdescent : baseEnd_6329764 < baseStart_6329764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329781 : List Nat := [1, 3, 3, 2, 2, 1, 1, 3, 1, 2, 4]
def baseStart_6329781 : Nat := 118140960795 + 6329781 * 2 ^ 59
def prefixEnd_6329781 : Nat := 4983230072969 + 3 ^ 40 * 6329781 * 2
def baseEnd_6329781 : Nat := 3250220090697004436427373

theorem tailTrace_6329781 : CollatzResearch.WordTrace tailWord_6329781 prefixEnd_6329781 3250220090697004436427373 := by
  unfold tailWord_6329781
  simp only [CollatzResearch.WordTrace]
  refine ⟨230866079481291952373877197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153910719654194634915918131 230866079481291952373877197)
  ·
    refine ⟨86574779805484482140203949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230866079481291952373877197 86574779805484482140203949)
    ·
      refine ⟨32465542427056680802576481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86574779805484482140203949 32465542427056680802576481)
      ·
        refine ⟨24349156820292510601932361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32465542427056680802576481 24349156820292510601932361)
        ·
          refine ⟨18261867615219382951449271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24349156820292510601932361 18261867615219382951449271)
          ·
            refine ⟨27392801422829074427173907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18261867615219382951449271 27392801422829074427173907)
            ·
              refine ⟨41089202134243611640760861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27392801422829074427173907 41089202134243611640760861)
              ·
                refine ⟨15408450800341354365285323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41089202134243611640760861 15408450800341354365285323)
                ·
                  refine ⟨23112676200512031547927985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15408450800341354365285323 23112676200512031547927985)
                  ·
                    refine ⟨17334507150384023660945989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23112676200512031547927985 17334507150384023660945989)
                    ·
                      refine ⟨3250220090697004436427373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17334507150384023660945989 3250220090697004436427373)
                      ·
                        rfl

theorem cell23_6329781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_6329781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329781 prefixEnd_6329781 := by exact prefixLift 6329781
  have htrace : WordTrace (prefixWord ++ tailWord_6329781) baseStart_6329781 baseEnd_6329781 := by
    simpa [prefixWord, tailWord_6329781, baseEnd_6329781] using wordTrace_append hprefix tailTrace_6329781
  have hstable : (prefixWord ++ tailWord_6329781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329781).length < 2 ^ (prefixWord ++ tailWord_6329781).sum := by decide
  have hdescent : baseEnd_6329781 < baseStart_6329781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329785 : List Nat := [1, 2, 1, 4, 4, 1, 1, 2, 3, 2, 2]
def baseStart_6329785 : Nat := 118140960795 + 6329785 * 2 ^ 59
def prefixEnd_6329785 : Nat := 4983230072969 + 3 ^ 40 * 6329785 * 2
def baseEnd_6329785 : Nat := 3250222144619622420777355

theorem tailTrace_6329785 : CollatzResearch.WordTrace tailWord_6329785 prefixEnd_6329785 3250222144619622420777355 := by
  unfold tailWord_6329785
  simp only [CollatzResearch.WordTrace]
  refine ⟨230866225373277461057022809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153910816915518307371348539 230866225373277461057022809)
  ·
    refine ⟨173149669029958095792767107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230866225373277461057022809 173149669029958095792767107)
    ·
      refine ⟨259724503544937143689150661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173149669029958095792767107 259724503544937143689150661)
      ·
        refine ⟨48698344414675714441715749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 259724503544937143689150661 48698344414675714441715749)
        ·
          refine ⟨9130939577751696457821703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48698344414675714441715749 9130939577751696457821703)
          ·
            refine ⟨13696409366627544686732555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9130939577751696457821703 13696409366627544686732555)
            ·
              refine ⟨20544614049941317030098833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13696409366627544686732555 20544614049941317030098833)
              ·
                refine ⟨15408460537455987772574125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20544614049941317030098833 15408460537455987772574125)
                ·
                  refine ⟨5778172701545995414715297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15408460537455987772574125 5778172701545995414715297)
                  ·
                    refine ⟨4333629526159496561036473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5778172701545995414715297 4333629526159496561036473)
                    ·
                      refine ⟨3250222144619622420777355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4333629526159496561036473 3250222144619622420777355)
                      ·
                        rfl

theorem cell23_6329785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 3, 2, 2].length) (baseStart_6329785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329785 prefixEnd_6329785 := by exact prefixLift 6329785
  have htrace : WordTrace (prefixWord ++ tailWord_6329785) baseStart_6329785 baseEnd_6329785 := by
    simpa [prefixWord, tailWord_6329785, baseEnd_6329785] using wordTrace_append hprefix tailTrace_6329785
  have hstable : (prefixWord ++ tailWord_6329785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329785).length < 2 ^ (prefixWord ++ tailWord_6329785).sum := by decide
  have hdescent : baseEnd_6329785 < baseStart_6329785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329801 : List Nat := [1, 2, 1, 1, 2, 1, 3, 4, 4, 1, 3]
def baseStart_6329801 : Nat := 118140960795 + 6329801 * 2 ^ 59
def prefixEnd_6329801 : Nat := 4983230072969 + 3 ^ 40 * 6329801 * 2
def baseEnd_6329801 : Nat := 3250230360310094358177281

theorem tailTrace_6329801 : CollatzResearch.WordTrace tailWord_6329801 prefixEnd_6329801 3250230360310094358177281 := by
  unfold tailWord_6329801
  simp only [CollatzResearch.WordTrace]
  refine ⟨230866808941219495789605257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153911205960812997193070171 230866808941219495789605257)
  ·
    refine ⟨173150106705914621842203943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230866808941219495789605257 173150106705914621842203943)
    ·
      refine ⟨259725160058871932763305915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173150106705914621842203943 259725160058871932763305915)
      ·
        refine ⟨389587740088307899144958873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259725160058871932763305915 389587740088307899144958873)
        ·
          refine ⟨292190805066230924358719155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 389587740088307899144958873 292190805066230924358719155)
          ·
            refine ⟨438286207599346386538078733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292190805066230924358719155 438286207599346386538078733)
            ·
              refine ⟨164357327849754894951779525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 438286207599346386538078733 164357327849754894951779525)
              ·
                refine ⟨30816998971829042803458661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 164357327849754894951779525 30816998971829042803458661)
                ·
                  refine ⟨5778187307217945525648499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30816998971829042803458661 5778187307217945525648499)
                  ·
                    refine ⟨8667280960826918288472749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5778187307217945525648499 8667280960826918288472749)
                    ·
                      refine ⟨3250230360310094358177281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8667280960826918288472749 3250230360310094358177281)
                      ·
                        rfl

theorem cell23_6329801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 4, 1, 3].length) (baseStart_6329801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329801 prefixEnd_6329801 := by exact prefixLift 6329801
  have htrace : WordTrace (prefixWord ++ tailWord_6329801) baseStart_6329801 baseEnd_6329801 := by
    simpa [prefixWord, tailWord_6329801, baseEnd_6329801] using wordTrace_append hprefix tailTrace_6329801
  have hstable : (prefixWord ++ tailWord_6329801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329801).length < 2 ^ (prefixWord ++ tailWord_6329801).sum := by decide
  have hdescent : baseEnd_6329801 < baseStart_6329801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329802 : List Nat := [3, 1, 2, 1, 2, 4, 2, 3, 1, 2, 2]
def baseStart_6329802 : Nat := 118140960795 + 6329802 * 2 ^ 59
def prefixEnd_6329802 : Nat := 4983230072969 + 3 ^ 40 * 6329802 * 2
def baseEnd_6329802 : Nat := 3250230873790748854264777

theorem tailTrace_6329802 : CollatzResearch.WordTrace tailWord_6329802 prefixEnd_6329802 3250230873790748854264777 := by
  unfold tailWord_6329802
  simp only [CollatzResearch.WordTrace]
  refine ⟨57716711353553968240097915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153911230276143915306927773 57716711353553968240097915)
  ·
    refine ⟨86575067030330952360146873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57716711353553968240097915 86575067030330952360146873)
    ·
      refine ⟨64931300272748214270110155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86575067030330952360146873 64931300272748214270110155)
      ·
        refine ⟨97396950409122321405165233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64931300272748214270110155 97396950409122321405165233)
        ·
          refine ⟨73047712806841741053873925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97396950409122321405165233 73047712806841741053873925)
          ·
            refine ⟨13696446151282826447601361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73047712806841741053873925 13696446151282826447601361)
            ·
              refine ⟨10272334613462119835701021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13696446151282826447601361 10272334613462119835701021)
              ·
                refine ⟨3852125480048294938387883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10272334613462119835701021 3852125480048294938387883)
                ·
                  refine ⟨5778188220072442407581825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3852125480048294938387883 5778188220072442407581825)
                  ·
                    refine ⟨4333641165054331805686369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5778188220072442407581825 4333641165054331805686369)
                    ·
                      refine ⟨3250230873790748854264777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4333641165054331805686369 3250230873790748854264777)
                      ·
                        rfl

theorem cell23_6329802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 3, 1, 2, 2].length) (baseStart_6329802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329802 prefixEnd_6329802 := by exact prefixLift 6329802
  have htrace : WordTrace (prefixWord ++ tailWord_6329802) baseStart_6329802 baseEnd_6329802 := by
    simpa [prefixWord, tailWord_6329802, baseEnd_6329802] using wordTrace_append hprefix tailTrace_6329802
  have hstable : (prefixWord ++ tailWord_6329802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329802).length < 2 ^ (prefixWord ++ tailWord_6329802).sum := by decide
  have hdescent : baseEnd_6329802 < baseStart_6329802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329812 : List Nat := [2, 4, 1, 2, 4, 1, 1, 2, 2, 4]
def baseStart_6329812 : Nat := 118140960795 + 6329812 * 2 ^ 59
def prefixEnd_6329812 : Nat := 4983230072969 + 3 ^ 40 * 6329812 * 2
def baseEnd_6329812 : Nat := 1083412002865764605046577

theorem tailTrace_6329812 : CollatzResearch.WordTrace tailWord_6329812 prefixEnd_6329812 1083412002865764605046577 := by
  unfold tailWord_6329812
  simp only [CollatzResearch.WordTrace]
  refine ⟨115433605072089822334127845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153911473429453096445503793 115433605072089822334127845)
  ·
    refine ⟨21643800951016841687648971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115433605072089822334127845 21643800951016841687648971)
    ·
      refine ⟨32465701426525262531473457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21643800951016841687648971 32465701426525262531473457)
      ·
        refine ⟨24349276069893946898605093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32465701426525262531473457 24349276069893946898605093)
        ·
          refine ⟨4565489263105115043488455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24349276069893946898605093 4565489263105115043488455)
          ·
            refine ⟨6848233894657672565232683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4565489263105115043488455 6848233894657672565232683)
            ·
              refine ⟨10272350841986508847849025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6848233894657672565232683 10272350841986508847849025)
              ·
                refine ⟨7704263131489881635886769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10272350841986508847849025 7704263131489881635886769)
                ·
                  refine ⟨5778197348617411226915077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7704263131489881635886769 5778197348617411226915077)
                  ·
                    refine ⟨1083412002865764605046577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5778197348617411226915077 1083412002865764605046577)
                    ·
                      rfl

theorem cell23_6329812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_6329812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329812 prefixEnd_6329812 := by exact prefixLift 6329812
  have htrace : WordTrace (prefixWord ++ tailWord_6329812) baseStart_6329812 baseEnd_6329812 := by
    simpa [prefixWord, tailWord_6329812, baseEnd_6329812] using wordTrace_append hprefix tailTrace_6329812
  have hstable : (prefixWord ++ tailWord_6329812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329812).length < 2 ^ (prefixWord ++ tailWord_6329812).sum := by decide
  have hdescent : baseEnd_6329812 < baseStart_6329812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329818 : List Nat := [3, 1, 1, 2, 3, 3, 1, 1, 4, 1, 3]
def baseStart_6329818 : Nat := 118140960795 + 6329818 * 2 ^ 59
def prefixEnd_6329818 : Nat := 4983230072969 + 3 ^ 40 * 6329818 * 2
def baseEnd_6329818 : Nat := 3250239089481220791664703

theorem tailTrace_6329818 : CollatzResearch.WordTrace tailWord_6329818 prefixEnd_6329818 3250239089481220791664703 := by
  unfold tailWord_6329818
  simp only [CollatzResearch.WordTrace]
  refine ⟨57716857245539476923243527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153911619321438605128649405 57716857245539476923243527)
  ·
    refine ⟨86575285868309215384865291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57716857245539476923243527 86575285868309215384865291)
    ·
      refine ⟨129862928802463823077297937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86575285868309215384865291 129862928802463823077297937)
      ·
        refine ⟨97397196601847867307973453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129862928802463823077297937 97397196601847867307973453)
        ·
          refine ⟨36523948725692950240490045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97397196601847867307973453 36523948725692950240490045)
          ·
            refine ⟨13696480772134856340183767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36523948725692950240490045 13696480772134856340183767)
            ·
              refine ⟨20544721158202284510275651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13696480772134856340183767 20544721158202284510275651)
              ·
                refine ⟨30817081737303426765413477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20544721158202284510275651 30817081737303426765413477)
                ·
                  refine ⟨5778202825744392518515027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30817081737303426765413477 5778202825744392518515027)
                  ·
                    refine ⟨8667304238616588777772541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5778202825744392518515027 8667304238616588777772541)
                    ·
                      refine ⟨3250239089481220791664703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8667304238616588777772541 3250239089481220791664703)
                      ·
                        rfl

theorem cell23_6329818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 4, 1, 3].length) (baseStart_6329818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329818 prefixEnd_6329818 := by exact prefixLift 6329818
  have htrace : WordTrace (prefixWord ++ tailWord_6329818) baseStart_6329818 baseEnd_6329818 := by
    simpa [prefixWord, tailWord_6329818, baseEnd_6329818] using wordTrace_append hprefix tailTrace_6329818
  have hstable : (prefixWord ++ tailWord_6329818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329818).length < 2 ^ (prefixWord ++ tailWord_6329818).sum := by decide
  have hdescent : baseEnd_6329818 < baseStart_6329818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329824 : List Nat := [2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 4]
def baseStart_6329824 : Nat := 118140960795 + 6329824 * 2 ^ 59
def prefixEnd_6329824 : Nat := 4983230072969 + 3 ^ 40 * 6329824 * 2
def baseEnd_6329824 : Nat := 3250242170365147768189675

theorem tailTrace_6329824 : CollatzResearch.WordTrace tailWord_6329824 prefixEnd_6329824 3250242170365147768189675 := by
  unfold tailWord_6329824
  simp only [CollatzResearch.WordTrace]
  refine ⟨115433823910068085358846263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153911765213424113811795017 115433823910068085358846263)
  ·
    refine ⟨173150735865102128038269395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115433823910068085358846263 173150735865102128038269395)
    ·
      refine ⟨259726103797653192057404093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173150735865102128038269395 259726103797653192057404093)
      ·
        refine ⟨97397288924119947021526535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259726103797653192057404093 97397288924119947021526535)
        ·
          refine ⟨146095933386179920532289803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97397288924119947021526535 146095933386179920532289803)
          ·
            refine ⟨219143900079269880798434705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146095933386179920532289803 219143900079269880798434705)
            ·
              refine ⟨164357925059452410598826029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219143900079269880798434705 164357925059452410598826029)
              ·
                refine ⟨61634221897294653974559761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164357925059452410598826029 61634221897294653974559761)
                ·
                  refine ⟨46225666422970990480919821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61634221897294653974559761 46225666422970990480919821)
                  ·
                    refine ⟨17334624908614121430344933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46225666422970990480919821 17334624908614121430344933)
                    ·
                      refine ⟨3250242170365147768189675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17334624908614121430344933 3250242170365147768189675)
                      ·
                        rfl

theorem cell23_6329824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_6329824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329824 prefixEnd_6329824 := by exact prefixLift 6329824
  have htrace : WordTrace (prefixWord ++ tailWord_6329824) baseStart_6329824 baseEnd_6329824 := by
    simpa [prefixWord, tailWord_6329824, baseEnd_6329824] using wordTrace_append hprefix tailTrace_6329824
  have hstable : (prefixWord ++ tailWord_6329824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329824).length < 2 ^ (prefixWord ++ tailWord_6329824).sum := by decide
  have hdescent : baseEnd_6329824 < baseStart_6329824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329864 : List Nat := [2, 1, 3, 2, 1, 1, 2, 2, 9]
def baseStart_6329864 : Nat := 118140960795 + 6329864 * 2 ^ 59
def prefixEnd_6329864 : Nat := 4983230072969 + 3 ^ 40 * 6329864 * 2
def baseEnd_6329864 : Nat := 361140301065703067965499

theorem tailTrace_6329864 : CollatzResearch.WordTrace tailWord_6329864 prefixEnd_6329864 361140301065703067965499 := by
  unfold tailWord_6329864
  simp only [CollatzResearch.WordTrace]
  refine ⟨115434553369995628774574323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153912737826660838366099097 115434553369995628774574323)
  ·
    refine ⟨173151830054993443161861485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115434553369995628774574323 173151830054993443161861485)
    ·
      refine ⟨64931936270622541185698057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173151830054993443161861485 64931936270622541185698057)
      ·
        refine ⟨48698952202966905889273543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64931936270622541185698057 48698952202966905889273543)
        ·
          refine ⟨73048428304450358833910315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48698952202966905889273543 73048428304450358833910315)
          ·
            refine ⟨109572642456675538250865473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73048428304450358833910315 109572642456675538250865473)
            ·
              refine ⟨82179481842506653688149105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109572642456675538250865473 82179481842506653688149105)
              ·
                refine ⟨61634611381879990266111829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82179481842506653688149105 61634611381879990266111829)
                ·
                  refine ⟨361140301065703067965499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 61634611381879990266111829 361140301065703067965499)
                  ·
                    rfl

theorem cell23_6329864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 9].length) (baseStart_6329864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329864 prefixEnd_6329864 := by exact prefixLift 6329864
  have htrace : WordTrace (prefixWord ++ tailWord_6329864) baseStart_6329864 baseEnd_6329864 := by
    simpa [prefixWord, tailWord_6329864, baseEnd_6329864] using wordTrace_append hprefix tailTrace_6329864
  have hstable : (prefixWord ++ tailWord_6329864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329864).length < 2 ^ (prefixWord ++ tailWord_6329864).sum := by decide
  have hdescent : baseEnd_6329864 < baseStart_6329864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329886 : List Nat := [4, 3, 3, 1, 1, 1, 1, 3, 2, 1, 3]
def baseStart_6329886 : Nat := 118140960795 + 6329886 * 2 ^ 59
def prefixEnd_6329886 : Nat := 4983230072969 + 3 ^ 40 * 6329886 * 2
def baseEnd_6329886 : Nat := 3250274006165726525614391

theorem tailTrace_6329886 : CollatzResearch.WordTrace tailWord_6329886 prefixEnd_6329886 3250274006165726525614391 := by
  unfold tailWord_6329886
  simp only [CollatzResearch.WordTrace]
  refine ⟨28858738643238944413306189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153913272763941036870966341 28858738643238944413306189)
  ·
    refine ⟨10822026991214604154989821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28858738643238944413306189 10822026991214604154989821)
    ·
      refine ⟨4058260121705476558121183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10822026991214604154989821 4058260121705476558121183)
      ·
        refine ⟨6087390182558214837181775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4058260121705476558121183 6087390182558214837181775)
        ·
          refine ⟨9131085273837322255772663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6087390182558214837181775 9131085273837322255772663)
          ·
            refine ⟨13696627910755983383658995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9131085273837322255772663 13696627910755983383658995)
            ·
              refine ⟨20544941866133975075488493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13696627910755983383658995 20544941866133975075488493)
              ·
                refine ⟨7704353199800240653308185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20544941866133975075488493 7704353199800240653308185)
                ·
                  refine ⟨5778264899850180489981139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7704353199800240653308185 5778264899850180489981139)
                  ·
                    refine ⟨8667397349775270734971709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5778264899850180489981139 8667397349775270734971709)
                    ·
                      refine ⟨3250274006165726525614391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8667397349775270734971709 3250274006165726525614391)
                      ·
                        rfl

theorem cell23_6329886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_6329886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329886 prefixEnd_6329886 := by exact prefixLift 6329886
  have htrace : WordTrace (prefixWord ++ tailWord_6329886) baseStart_6329886 baseEnd_6329886 := by
    simpa [prefixWord, tailWord_6329886, baseEnd_6329886] using wordTrace_append hprefix tailTrace_6329886
  have hstable : (prefixWord ++ tailWord_6329886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329886).length < 2 ^ (prefixWord ++ tailWord_6329886).sum := by decide
  have hdescent : baseEnd_6329886 < baseStart_6329886 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329904 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 7]
def baseStart_6329904 : Nat := 118140960795 + 6329904 * 2 ^ 59
def prefixEnd_6329904 : Nat := 4983230072969 + 3 ^ 40 * 6329904 * 2
def baseEnd_6329904 : Nat := 3250283248817507455189307

theorem tailTrace_6329904 : CollatzResearch.WordTrace tailWord_6329904 prefixEnd_6329904 3250283248817507455189307 := by
  unfold tailWord_6329904
  simp only [CollatzResearch.WordTrace]
  refine ⟨115435282829923172190302383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153913710439897562920403177 115435282829923172190302383)
  ·
    refine ⟨173152924244884758285453575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115435282829923172190302383 173152924244884758285453575)
    ·
      refine ⟨259729386367327137428180363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173152924244884758285453575 259729386367327137428180363)
      ·
        refine ⟨389594079550990706142270545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259729386367327137428180363 389594079550990706142270545)
        ·
          refine ⟨292195559663243029606702909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 389594079550990706142270545 292195559663243029606702909)
          ·
            refine ⟨109573334873716136102513591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 292195559663243029606702909 109573334873716136102513591)
            ·
              refine ⟨164360002310574204153770387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109573334873716136102513591 164360002310574204153770387)
              ·
                refine ⟨246540003465861306230655581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164360002310574204153770387 246540003465861306230655581)
                ·
                  refine ⟨92452501299697989836495843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 246540003465861306230655581 92452501299697989836495843)
                  ·
                    refine ⟨138678751949546984754743765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 92452501299697989836495843 138678751949546984754743765)
                    ·
                      refine ⟨3250283248817507455189307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 138678751949546984754743765 3250283248817507455189307)
                      ·
                        rfl

theorem cell23_6329904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 7].length) (baseStart_6329904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329904 prefixEnd_6329904 := by exact prefixLift 6329904
  have htrace : WordTrace (prefixWord ++ tailWord_6329904) baseStart_6329904 baseEnd_6329904 := by
    simpa [prefixWord, tailWord_6329904, baseEnd_6329904] using wordTrace_append hprefix tailTrace_6329904
  have hstable : (prefixWord ++ tailWord_6329904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329904).length < 2 ^ (prefixWord ++ tailWord_6329904).sum := by decide
  have hdescent : baseEnd_6329904 < baseStart_6329904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329911 : List Nat := [1, 1, 3, 1, 2, 4, 1, 3, 2, 5]
def baseStart_6329911 : Nat := 118140960795 + 6329911 * 2 ^ 59
def prefixEnd_6329911 : Nat := 4983230072969 + 3 ^ 40 * 6329911 * 2
def baseEnd_6329911 : Nat := 1083428947727362975933925

theorem tailTrace_6329911 : CollatzResearch.WordTrace tailWord_6329911 prefixEnd_6329911 1083428947727362975933925 := by
  unfold tailWord_6329911
  simp only [CollatzResearch.WordTrace]
  refine ⟨230870820970820984576109587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153913880647213989717406391 230870820970820984576109587)
  ·
    refine ⟨346306231456231476864164381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230870820970820984576109587 346306231456231476864164381)
    ·
      refine ⟨129864836796086803824061643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 346306231456231476864164381 129864836796086803824061643)
      ·
        refine ⟨194797255194130205736092465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129864836796086803824061643 194797255194130205736092465)
        ·
          refine ⟨146097941395597654302069349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194797255194130205736092465 146097941395597654302069349)
          ·
            refine ⟨27393364011674560181638003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146097941395597654302069349 27393364011674560181638003)
            ·
              refine ⟨41090046017511840272457005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27393364011674560181638003 41090046017511840272457005)
              ·
                refine ⟨15408767256566940102171377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41090046017511840272457005 15408767256566940102171377)
                ·
                  refine ⟨11556575442425205076628533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15408767256566940102171377 11556575442425205076628533)
                  ·
                    refine ⟨1083428947727362975933925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11556575442425205076628533 1083428947727362975933925)
                    ·
                      rfl

theorem cell23_6329911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 2, 5].length) (baseStart_6329911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329911 prefixEnd_6329911 := by exact prefixLift 6329911
  have htrace : WordTrace (prefixWord ++ tailWord_6329911) baseStart_6329911 baseEnd_6329911 := by
    simpa [prefixWord, tailWord_6329911, baseEnd_6329911] using wordTrace_append hprefix tailTrace_6329911
  have hstable : (prefixWord ++ tailWord_6329911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329911).length < 2 ^ (prefixWord ++ tailWord_6329911).sum := by decide
  have hdescent : baseEnd_6329911 < baseStart_6329911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329921 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 3, 2, 5]
def baseStart_6329921 : Nat := 118140960795 + 6329921 * 2 ^ 59
def prefixEnd_6329921 : Nat := 4983230072969 + 3 ^ 40 * 6329921 * 2
def baseEnd_6329921 : Nat := 3250291977988633888676729

theorem tailTrace_6329921 : CollatzResearch.WordTrace tailWord_6329921 prefixEnd_6329921 3250291977988633888676729 := by
  unfold tailWord_6329921
  simp only [CollatzResearch.WordTrace]
  refine ⟨230871185700784756283973617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153914123800523170855982411 230871185700784756283973617)
  ·
    refine ⟨173153389275588567212980213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230871185700784756283973617 173153389275588567212980213)
    ·
      refine ⟨16233130244586428176216895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 173153389275588567212980213 16233130244586428176216895)
      ·
        refine ⟨24349695366879642264325343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16233130244586428176216895 24349695366879642264325343)
        ·
          refine ⟨36524543050319463396488015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24349695366879642264325343 36524543050319463396488015)
          ·
            refine ⟨54786814575479195094732023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36524543050319463396488015 54786814575479195094732023)
            ·
              refine ⟨82180221863218792642098035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54786814575479195094732023 82180221863218792642098035)
              ·
                refine ⟨123270332794828188963147053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82180221863218792642098035 123270332794828188963147053)
                ·
                  refine ⟨46226374798060570861180145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123270332794828188963147053 46226374798060570861180145)
                  ·
                    refine ⟨34669781098545428145885109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46226374798060570861180145 34669781098545428145885109)
                    ·
                      refine ⟨3250291977988633888676729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34669781098545428145885109 3250291977988633888676729)
                      ·
                        rfl

theorem cell23_6329921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_6329921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329921 prefixEnd_6329921 := by exact prefixLift 6329921
  have htrace : WordTrace (prefixWord ++ tailWord_6329921) baseStart_6329921 baseEnd_6329921 := by
    simpa [prefixWord, tailWord_6329921, baseEnd_6329921] using wordTrace_append hprefix tailTrace_6329921
  have hstable : (prefixWord ++ tailWord_6329921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329921).length < 2 ^ (prefixWord ++ tailWord_6329921).sum := by decide
  have hdescent : baseEnd_6329921 < baseStart_6329921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329926 : List Nat := [6, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2]
def baseStart_6329926 : Nat := 118140960795 + 6329926 * 2 ^ 59
def prefixEnd_6329926 : Nat := 4983230072969 + 3 ^ 40 * 6329926 * 2
def baseEnd_6329926 : Nat := 3250294545391906369114207

theorem tailTrace_6329926 : CollatzResearch.WordTrace tailWord_6329926 prefixEnd_6329926 3250294545391906369114207 := by
  unfold tailWord_6329926
  simp only [CollatzResearch.WordTrace]
  refine ⟨7214730252055207566809551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 153914245377177761425270421 7214730252055207566809551)
  ·
    refine ⟨10822095378082811350214327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7214730252055207566809551 10822095378082811350214327)
    ·
      refine ⟨16233143067124217025321491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10822095378082811350214327 16233143067124217025321491)
      ·
        refine ⟨24349714600686325537982237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16233143067124217025321491 24349714600686325537982237)
        ·
          refine ⟨9131142975257372076743339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24349714600686325537982237 9131142975257372076743339)
          ·
            refine ⟨13696714462886058115115009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9131142975257372076743339 13696714462886058115115009)
            ·
              refine ⟨10272535847164543586336257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13696714462886058115115009 10272535847164543586336257)
              ·
                refine ⟨7704401885373407689752193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10272535847164543586336257 7704401885373407689752193)
                ·
                  refine ⟨5778301414030055767314145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7704401885373407689752193 5778301414030055767314145)
                  ·
                    refine ⟨4333726060522541825485609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5778301414030055767314145 4333726060522541825485609)
                    ·
                      refine ⟨3250294545391906369114207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4333726060522541825485609 3250294545391906369114207)
                      ·
                        rfl

theorem cell23_6329926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_6329926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329926 prefixEnd_6329926 := by exact prefixLift 6329926
  have htrace : WordTrace (prefixWord ++ tailWord_6329926) baseStart_6329926 baseEnd_6329926 := by
    simpa [prefixWord, tailWord_6329926, baseEnd_6329926] using wordTrace_append hprefix tailTrace_6329926
  have hstable : (prefixWord ++ tailWord_6329926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329926).length < 2 ^ (prefixWord ++ tailWord_6329926).sum := by decide
  have hdescent : baseEnd_6329926 < baseStart_6329926 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329968 : List Nat := [2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 3]
def baseStart_6329968 : Nat := 118140960795 + 6329968 * 2 ^ 59
def prefixEnd_6329968 : Nat := 4983230072969 + 3 ^ 40 * 6329968 * 2
def baseEnd_6329968 : Nat := 3250316111579395204789013

theorem tailTrace_6329968 : CollatzResearch.WordTrace tailWord_6329968 prefixEnd_6329968 3250316111579395204789013 := by
  unfold tailWord_6329968
  simp only [CollatzResearch.WordTrace]
  refine ⟨115436449965807241655467279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153915266621076322207289705 115436449965807241655467279)
  ·
    refine ⟨173154674948710862483200919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115436449965807241655467279 173154674948710862483200919)
    ·
      refine ⟨259732012423066293724801379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173154674948710862483200919 259732012423066293724801379)
      ·
        refine ⟨389598018634599440587202069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259732012423066293724801379 389598018634599440587202069)
        ·
          refine ⟨18262407123496848777525097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 389598018634599440587202069 18262407123496848777525097)
          ·
            refine ⟨13696805342622636583143823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18262407123496848777525097 13696805342622636583143823)
            ·
              refine ⟨20545208013933954874715735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13696805342622636583143823 20545208013933954874715735)
              ·
                refine ⟨30817812020900932312073603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20545208013933954874715735 30817812020900932312073603)
                ·
                  refine ⟨46226718031351398468110405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30817812020900932312073603 46226718031351398468110405)
                  ·
                    refine ⟨8667509630878387212770701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46226718031351398468110405 8667509630878387212770701)
                    ·
                      refine ⟨3250316111579395204789013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8667509630878387212770701 3250316111579395204789013)
                      ·
                        rfl

theorem cell23_6329968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 3].length) (baseStart_6329968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329968 prefixEnd_6329968 := by exact prefixLift 6329968
  have htrace : WordTrace (prefixWord ++ tailWord_6329968) baseStart_6329968 baseEnd_6329968 := by
    simpa [prefixWord, tailWord_6329968, baseEnd_6329968] using wordTrace_append hprefix tailTrace_6329968
  have hstable : (prefixWord ++ tailWord_6329968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329968).length < 2 ^ (prefixWord ++ tailWord_6329968).sum := by decide
  have hdescent : baseEnd_6329968 < baseStart_6329968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329988 : List Nat := [2, 3, 2, 1, 4, 1, 1, 1, 8]
def baseStart_6329988 : Nat := 118140960795 + 6329988 * 2 ^ 59
def prefixEnd_6329988 : Nat := 4983230072969 + 3 ^ 40 * 6329988 * 2
def baseEnd_6329988 : Nat := 361147375688053902948769

theorem tailTrace_6329988 : CollatzResearch.WordTrace tailWord_6329988 prefixEnd_6329988 361147375688053902948769 := by
  unfold tailWord_6329988
  simp only [CollatzResearch.WordTrace]
  refine ⟨115436814695771013363331309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153915752927694684484441745 115436814695771013363331309)
  ·
    refine ⟨43288805510914130011249241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115436814695771013363331309 43288805510914130011249241)
    ·
      refine ⟨32466604133185597508436931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43288805510914130011249241 32466604133185597508436931)
      ·
        refine ⟨48699906199778396262655397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32466604133185597508436931 48699906199778396262655397)
        ·
          refine ⟨9131232412458449299247887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48699906199778396262655397 9131232412458449299247887)
          ·
            refine ⟨13696848618687673948871831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9131232412458449299247887 13696848618687673948871831)
            ·
              refine ⟨20545272928031510923307747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13696848618687673948871831 20545272928031510923307747)
              ·
                refine ⟨30817909392047266384961621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20545272928031510923307747 30817909392047266384961621)
                ·
                  refine ⟨361147375688053902948769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30817909392047266384961621 361147375688053902948769)
                  ·
                    rfl

theorem cell23_6329988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 8].length) (baseStart_6329988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329988 prefixEnd_6329988 := by exact prefixLift 6329988
  have htrace : WordTrace (prefixWord ++ tailWord_6329988) baseStart_6329988 baseEnd_6329988 := by
    simpa [prefixWord, tailWord_6329988, baseEnd_6329988] using wordTrace_append hprefix tailTrace_6329988
  have hstable : (prefixWord ++ tailWord_6329988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329988).length < 2 ^ (prefixWord ++ tailWord_6329988).sum := by decide
  have hdescent : baseEnd_6329988 < baseStart_6329988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329991 : List Nat := [1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 6]
def baseStart_6329991 : Nat := 118140960795 + 6329991 * 2 ^ 59
def prefixEnd_6329991 : Nat := 4983230072969 + 3 ^ 40 * 6329991 * 2
def baseEnd_6329991 : Nat := 3250327921634448614801407

theorem tailTrace_6329991 : CollatzResearch.WordTrace tailWord_6329991 prefixEnd_6329991 3250327921634448614801407 := by
  unfold tailWord_6329991
  simp only [CollatzResearch.WordTrace]
  refine ⟨230873738810531158239021827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153915825873687438826014551 230873738810531158239021827)
  ·
    refine ⟨346310608215796737358532741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230873738810531158239021827 346310608215796737358532741)
    ·
      refine ⟨64933239040461888254724889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 346310608215796737358532741 64933239040461888254724889)
      ·
        refine ⟨48699929280346416191043667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64933239040461888254724889 48699929280346416191043667)
        ·
          refine ⟨73049893920519624286565501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48699929280346416191043667 73049893920519624286565501)
          ·
            refine ⟨27393710220194859107462063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73049893920519624286565501 27393710220194859107462063)
            ·
              refine ⟨41090565330292288661193095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27393710220194859107462063 41090565330292288661193095)
              ·
                refine ⟨61635847995438432991789643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41090565330292288661193095 61635847995438432991789643)
                ·
                  refine ⟨92453771993157649487684465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61635847995438432991789643 92453771993157649487684465)
                  ·
                    refine ⟨69340328994868237115763349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 92453771993157649487684465 69340328994868237115763349)
                    ·
                      refine ⟨3250327921634448614801407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69340328994868237115763349 3250327921634448614801407)
                      ·
                        rfl

theorem cell23_6329991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_6329991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329991 prefixEnd_6329991 := by exact prefixLift 6329991
  have htrace : WordTrace (prefixWord ++ tailWord_6329991) baseStart_6329991 baseEnd_6329991 := by
    simpa [prefixWord, tailWord_6329991, baseEnd_6329991] using wordTrace_append hprefix tailTrace_6329991
  have hstable : (prefixWord ++ tailWord_6329991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329991).length < 2 ^ (prefixWord ++ tailWord_6329991).sum := by decide
  have hdescent : baseEnd_6329991 < baseStart_6329991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6329992 : List Nat := [2, 1, 3, 5, 1, 1, 2, 1, 3, 4]
def baseStart_6329992 : Nat := 118140960795 + 6329992 * 2 ^ 59
def prefixEnd_6329992 : Nat := 4983230072969 + 3 ^ 40 * 6329992 * 2
def baseEnd_6329992 : Nat := 1083442811705034370296301

theorem tailTrace_6329992 : CollatzResearch.WordTrace tailWord_6329992 prefixEnd_6329992 1083442811705034370296301 := by
  unfold tailWord_6329992
  simp only [CollatzResearch.WordTrace]
  refine ⟨115436887641763767704904115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153915850189018356939872153 115436887641763767704904115)
  ·
    refine ⟨173155331462645651557356173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115436887641763767704904115 173155331462645651557356173)
    ·
      refine ⟨64933249298492119334008565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173155331462645651557356173 64933249298492119334008565)
      ·
        refine ⟨6087492121733636187563303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64933249298492119334008565 6087492121733636187563303)
        ·
          refine ⟨9131238182600454281344955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6087492121733636187563303 9131238182600454281344955)
          ·
            refine ⟨13696857273900681422017433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9131238182600454281344955 13696857273900681422017433)
            ·
              refine ⟨10272642955425511066513075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13696857273900681422017433 10272642955425511066513075)
              ·
                refine ⟨15408964433138266599769613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10272642955425511066513075 15408964433138266599769613)
                ·
                  refine ⟨5778361662426849974913605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15408964433138266599769613 5778361662426849974913605)
                  ·
                    refine ⟨1083442811705034370296301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5778361662426849974913605 1083442811705034370296301)
                    ·
                      rfl

theorem cell23_6329992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 3, 4].length) (baseStart_6329992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6329992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6329992 prefixEnd_6329992 := by exact prefixLift 6329992
  have htrace : WordTrace (prefixWord ++ tailWord_6329992) baseStart_6329992 baseEnd_6329992 := by
    simpa [prefixWord, tailWord_6329992, baseEnd_6329992] using wordTrace_append hprefix tailTrace_6329992
  have hstable : (prefixWord ++ tailWord_6329992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6329992).length < 2 ^ (prefixWord ++ tailWord_6329992).sum := by decide
  have hdescent : baseEnd_6329992 < baseStart_6329992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6329992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6330001 : List Nat := [1, 2, 2, 1, 1, 1, 1, 6, 3, 5]
def baseStart_6330001 : Nat := 118140960795 + 6330001 * 2 ^ 59
def prefixEnd_6330001 : Nat := 4983230072969 + 3 ^ 40 * 6330001 * 2
def baseEnd_6330001 : Nat := 1083444352146997858558787

theorem tailTrace_6330001 : CollatzResearch.WordTrace tailWord_6330001 prefixEnd_6330001 1083444352146997858558787 := by
  unfold tailWord_6330001
  simp only [CollatzResearch.WordTrace]
  refine ⟨230874103540494929946885857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153916069026996619964590571 230874103540494929946885857)
  ·
    refine ⟨173155577655371197460164393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230874103540494929946885857 173155577655371197460164393)
    ·
      refine ⟨129866683241528398095123295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173155577655371197460164393 129866683241528398095123295)
      ·
        refine ⟨194800024862292597142684943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129866683241528398095123295 194800024862292597142684943)
        ·
          refine ⟨292200037293438895714027415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194800024862292597142684943 292200037293438895714027415)
          ·
            refine ⟨438300055940158343571041123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292200037293438895714027415 438300055940158343571041123)
            ·
              refine ⟨657450083910237515356561685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 438300055940158343571041123 657450083910237515356561685)
              ·
                refine ⟨30817972683292383532338829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 657450083910237515356561685 30817972683292383532338829)
                ·
                  refine ⟨11556739756234643824627061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30817972683292383532338829 11556739756234643824627061)
                  ·
                    refine ⟨1083444352146997858558787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11556739756234643824627061 1083444352146997858558787)
                    ·
                      rfl

theorem cell23_6330001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 5].length) (baseStart_6330001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6330001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6330001 prefixEnd_6330001 := by exact prefixLift 6330001
  have htrace : WordTrace (prefixWord ++ tailWord_6330001) baseStart_6330001 baseEnd_6330001 := by
    simpa [prefixWord, tailWord_6330001, baseEnd_6330001] using wordTrace_append hprefix tailTrace_6330001
  have hstable : (prefixWord ++ tailWord_6330001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6330001).length < 2 ^ (prefixWord ++ tailWord_6330001).sum := by decide
  have hdescent : baseEnd_6330001 < baseStart_6330001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6330001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6330031 : List Nat := [1, 1, 2, 1, 2, 4, 2, 1, 3, 6]
def baseStart_6330031 : Nat := 118140960795 + 6330031 * 2 ^ 59
def prefixEnd_6330031 : Nat := 4983230072969 + 3 ^ 40 * 6330031 * 2
def baseEnd_6330031 : Nat := 1083449486953542819433741

theorem tailTrace_6330031 : CollatzResearch.WordTrace tailWord_6330031 prefixEnd_6330031 1083449486953542819433741 := by
  unfold tailWord_6330031
  simp only [CollatzResearch.WordTrace]
  refine ⟨230875197730386245070477947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153916798486924163380318631 230875197730386245070477947)
  ·
    refine ⟨346312796595579367605716921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230875197730386245070477947 346312796595579367605716921)
    ·
      refine ⟨259734597446684525704287691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346312796595579367605716921 259734597446684525704287691)
      ·
        refine ⟨389601896170026788556431537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259734597446684525704287691 389601896170026788556431537)
        ·
          refine ⟨292201422127520091417323653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 389601896170026788556431537 292201422127520091417323653)
          ·
            refine ⟨54787766648910017140748185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 292201422127520091417323653 54787766648910017140748185)
            ·
              refine ⟨41090824986682512855561139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54787766648910017140748185 41090824986682512855561139)
              ·
                refine ⟨61636237480023769283341709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41090824986682512855561139 61636237480023769283341709)
                ·
                  refine ⟨23113589055008913481253141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61636237480023769283341709 23113589055008913481253141)
                  ·
                    refine ⟨1083449486953542819433741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23113589055008913481253141 1083449486953542819433741)
                    ·
                      rfl

theorem cell23_6330031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 6].length) (baseStart_6330031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6330031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6330031 prefixEnd_6330031 := by exact prefixLift 6330031
  have htrace : WordTrace (prefixWord ++ tailWord_6330031) baseStart_6330031 baseEnd_6330031 := by
    simpa [prefixWord, tailWord_6330031, baseEnd_6330031] using wordTrace_append hprefix tailTrace_6330031
  have hstable : (prefixWord ++ tailWord_6330031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6330031).length < 2 ^ (prefixWord ++ tailWord_6330031).sum := by decide
  have hdescent : baseEnd_6330031 < baseStart_6330031 := by decide
  rcases family_descends (prefixWord ++ tailWord_6330031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6330032 : List Nat := [2, 1, 1, 1, 2, 1, 7, 3, 1, 1, 3]
def baseStart_6330032 : Nat := 118140960795 + 6330032 * 2 ^ 59
def prefixEnd_6330032 : Nat := 4983230072969 + 3 ^ 40 * 6330032 * 2
def baseEnd_6330032 : Nat := 3250348974341282954388719

theorem tailTrace_6330032 : CollatzResearch.WordTrace tailWord_6330032 prefixEnd_6330032 3250348974341282954388719 := by
  unfold tailWord_6330032
  simp only [CollatzResearch.WordTrace]
  refine ⟨115437617101691311120632175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153916822802255081494176233 115437617101691311120632175)
  ·
    refine ⟨173156425652536966680948263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115437617101691311120632175 173156425652536966680948263)
    ·
      refine ⟨259734638478805450021422395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173156425652536966680948263 259734638478805450021422395)
      ·
        refine ⟨389601957718208175032133593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259734638478805450021422395 389601957718208175032133593)
        ·
          refine ⟨292201468288656131274100195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 389601957718208175032133593 292201468288656131274100195)
          ·
            refine ⟨438302202432984196911150293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292201468288656131274100195 438302202432984196911150293)
            ·
              refine ⟨10272707869523067115105085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 438302202432984196911150293 10272707869523067115105085)
              ·
                refine ⟨3852265451071150168164407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10272707869523067115105085 3852265451071150168164407)
                ·
                  refine ⟨5778398176606725252246611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3852265451071150168164407 5778398176606725252246611)
                  ·
                    refine ⟨8667597264910087878369917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5778398176606725252246611 8667597264910087878369917)
                    ·
                      refine ⟨3250348974341282954388719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8667597264910087878369917 3250348974341282954388719)
                      ·
                        rfl

theorem cell23_6330032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 3, 1, 1, 3].length) (baseStart_6330032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6330032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6330032 prefixEnd_6330032 := by exact prefixLift 6330032
  have htrace : WordTrace (prefixWord ++ tailWord_6330032) baseStart_6330032 baseEnd_6330032 := by
    simpa [prefixWord, tailWord_6330032, baseEnd_6330032] using wordTrace_append hprefix tailTrace_6330032
  have hstable : (prefixWord ++ tailWord_6330032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6330032).length < 2 ^ (prefixWord ++ tailWord_6330032).sum := by decide
  have hdescent : baseEnd_6330032 < baseStart_6330032 := by decide
  rcases family_descends (prefixWord ++ tailWord_6330032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6330048 : List Nat := [2, 1, 1, 2, 4, 1, 1, 3, 4, 4]
def baseStart_6330048 : Nat := 118140960795 + 6330048 * 2 ^ 59
def prefixEnd_6330048 : Nat := 4983230072969 + 3 ^ 40 * 6330048 * 2
def baseEnd_6330048 : Nat := 1083452396677251630596215

theorem tailTrace_6330048 : CollatzResearch.WordTrace tailWord_6330048 prefixEnd_6330048 1083452396677251630596215 := by
  unfold tailWord_6330048
  simp only [CollatzResearch.WordTrace]
  refine ⟨115437908885662328486923399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153917211847549771315897865 115437908885662328486923399)
  ·
    refine ⟨173156863328493492730385099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115437908885662328486923399 173156863328493492730385099)
    ·
      refine ⟨259735294992740239095577649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173156863328493492730385099 259735294992740239095577649)
      ·
        refine ⟨194801471244555179321683237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259735294992740239095577649 194801471244555179321683237)
        ·
          refine ⟨36525275858354096122815607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194801471244555179321683237 36525275858354096122815607)
          ·
            refine ⟨54787913787531144184223411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36525275858354096122815607 54787913787531144184223411)
            ·
              refine ⟨82181870681296716276335117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54787913787531144184223411 82181870681296716276335117)
              ·
                refine ⟨30818201505486268603625669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82181870681296716276335117 30818201505486268603625669)
                ·
                  refine ⟨5778412782278675363179813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30818201505486268603625669 5778412782278675363179813)
                  ·
                    refine ⟨1083452396677251630596215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5778412782278675363179813 1083452396677251630596215)
                    ·
                      rfl

theorem cell23_6330048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 4, 4].length) (baseStart_6330048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6330048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6330048 prefixEnd_6330048 := by exact prefixLift 6330048
  have htrace : WordTrace (prefixWord ++ tailWord_6330048) baseStart_6330048 baseEnd_6330048 := by
    simpa [prefixWord, tailWord_6330048, baseEnd_6330048] using wordTrace_append hprefix tailTrace_6330048
  have hstable : (prefixWord ++ tailWord_6330048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6330048).length < 2 ^ (prefixWord ++ tailWord_6330048).sum := by decide
  have hdescent : baseEnd_6330048 < baseStart_6330048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6330048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6330065 : List Nat := [1, 2, 2, 1, 2, 5, 1, 3, 2, 4]
def baseStart_6330065 : Nat := 118140960795 + 6330065 * 2 ^ 59
def prefixEnd_6330065 : Nat := 4983230072969 + 3 ^ 40 * 6330065 * 2
def baseEnd_6330065 : Nat := 1083455306400960441758689

theorem tailTrace_6330065 : CollatzResearch.WordTrace tailWord_6330065 prefixEnd_6330065 1083455306400960441758689 := by
  unfold tailWord_6330065
  simp only [CollatzResearch.WordTrace]
  refine ⟨230876437812263068877215649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153917625208175379251477099 230876437812263068877215649)
  ·
    refine ⟨173157328359197301657911737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230876437812263068877215649 173157328359197301657911737)
    ·
      refine ⟨129867996269397976243433803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173157328359197301657911737 129867996269397976243433803)
      ·
        refine ⟨194801994404096964365150705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129867996269397976243433803 194801994404096964365150705)
        ·
          refine ⟨146101495803072723273863029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194801994404096964365150705 146101495803072723273863029)
          ·
            refine ⟨13697015231538067806924659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 146101495803072723273863029 13697015231538067806924659)
            ·
              refine ⟨20545522847307101710386989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13697015231538067806924659 20545522847307101710386989)
              ·
                refine ⟨7704571067740163141395121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20545522847307101710386989 7704571067740163141395121)
                ·
                  refine ⟨5778428300805122356046341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7704571067740163141395121 5778428300805122356046341)
                  ·
                    refine ⟨1083455306400960441758689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5778428300805122356046341 1083455306400960441758689)
                    ·
                      rfl

theorem cell23_6330065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 3, 2, 4].length) (baseStart_6330065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6330065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6330065 prefixEnd_6330065 := by exact prefixLift 6330065
  have htrace : WordTrace (prefixWord ++ tailWord_6330065) baseStart_6330065 baseEnd_6330065 := by
    simpa [prefixWord, tailWord_6330065, baseEnd_6330065] using wordTrace_append hprefix tailTrace_6330065
  have hstable : (prefixWord ++ tailWord_6330065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6330065).length < 2 ^ (prefixWord ++ tailWord_6330065).sum := by decide
  have hdescent : baseEnd_6330065 < baseStart_6330065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6330065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6330100 : List Nat := [2, 6, 1, 1, 1, 3, 2, 2, 1, 1, 3]
def baseStart_6330100 : Nat := 118140960795 + 6330100 * 2 ^ 59
def prefixEnd_6330100 : Nat := 4983230072969 + 3 ^ 40 * 6330100 * 2
def baseEnd_6330100 : Nat := 3250383891025788688338407

theorem tailTrace_6330100 : CollatzResearch.WordTrace tailWord_6330100 prefixEnd_6330100 3250383891025788688338407 := by
  unfold tailWord_6330100
  simp only [CollatzResearch.WordTrace]
  refine ⟨115438857183568134927369877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153918476244757513236493169 115438857183568134927369877)
  ·
    refine ⟨5411196430479756324720463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 115438857183568134927369877 5411196430479756324720463)
    ·
      refine ⟨8116794645719634487080695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5411196430479756324720463 8116794645719634487080695)
      ·
        refine ⟨12175191968579451730621043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8116794645719634487080695 12175191968579451730621043)
        ·
          refine ⟨18262787952869177595931565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12175191968579451730621043 18262787952869177595931565)
          ·
            refine ⟨6848545482325941598474337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18262787952869177595931565 6848545482325941598474337)
            ·
              refine ⟨5136409111744456198855753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6848545482325941598474337 5136409111744456198855753)
              ·
                refine ⟨3852306833808342149141815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5136409111744456198855753 3852306833808342149141815)
                ·
                  refine ⟨5778460250712513223712723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3852306833808342149141815 5778460250712513223712723)
                  ·
                    refine ⟨8667690376068769835569085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5778460250712513223712723 8667690376068769835569085)
                    ·
                      refine ⟨3250383891025788688338407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8667690376068769835569085 3250383891025788688338407)
                      ·
                        rfl

theorem cell23_6330100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_6330100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6330100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6330100 prefixEnd_6330100 := by exact prefixLift 6330100
  have htrace : WordTrace (prefixWord ++ tailWord_6330100) baseStart_6330100 baseEnd_6330100 := by
    simpa [prefixWord, tailWord_6330100, baseEnd_6330100] using wordTrace_append hprefix tailTrace_6330100
  have hstable : (prefixWord ++ tailWord_6330100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6330100).length < 2 ^ (prefixWord ++ tailWord_6330100).sum := by decide
  have hdescent : baseEnd_6330100 < baseStart_6330100 := by decide
  rcases family_descends (prefixWord ++ tailWord_6330100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6330115 : List Nat := [1, 1, 1, 3, 2, 2, 3, 2, 3, 3, 2]
def baseStart_6330115 : Nat := 118140960795 + 6330115 * 2 ^ 59
def prefixEnd_6330115 : Nat := 4983230072969 + 3 ^ 40 * 6330115 * 2
def baseEnd_6330115 : Nat := 3250391593235606129650837

theorem tailTrace_6330115 : CollatzResearch.WordTrace tailWord_6330115 prefixEnd_6330115 3250391593235606129650837 := by
  unfold tailWord_6330115
  simp only [CollatzResearch.WordTrace]
  refine ⟨230878261462081927416535799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153918840974721284944357199 230878261462081927416535799)
  ·
    refine ⟨346317392193122891124803699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230878261462081927416535799 346317392193122891124803699)
    ·
      refine ⟨519476088289684336687205549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346317392193122891124803699 519476088289684336687205549)
      ·
        refine ⟨194803533108631626257702081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 519476088289684336687205549 194803533108631626257702081)
        ·
          refine ⟨146102649831473719693276561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194803533108631626257702081 146102649831473719693276561)
          ·
            refine ⟨109576987373605289769957421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146102649831473719693276561 109576987373605289769957421)
            ·
              refine ⟨41091370265101983663734033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109576987373605289769957421 41091370265101983663734033)
              ·
                refine ⟨30818527698826487747800525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41091370265101983663734033 30818527698826487747800525)
                ·
                  refine ⟨11556947887059932905425197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30818527698826487747800525 11556947887059932905425197)
                  ·
                    refine ⟨4333855457647474839534449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11556947887059932905425197 4333855457647474839534449)
                    ·
                      refine ⟨3250391593235606129650837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4333855457647474839534449 3250391593235606129650837)
                      ·
                        rfl

theorem cell23_6330115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 3, 3, 2].length) (baseStart_6330115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6330115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6330115 prefixEnd_6330115 := by exact prefixLift 6330115
  have htrace : WordTrace (prefixWord ++ tailWord_6330115) baseStart_6330115 baseEnd_6330115 := by
    simpa [prefixWord, tailWord_6330115, baseEnd_6330115] using wordTrace_append hprefix tailTrace_6330115
  have hstable : (prefixWord ++ tailWord_6330115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6330115).length < 2 ^ (prefixWord ++ tailWord_6330115).sum := by decide
  have hdescent : baseEnd_6330115 < baseStart_6330115 := by decide
  rcases family_descends (prefixWord ++ tailWord_6330115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6330122 : List Nat := [3, 1, 2, 2, 1, 3, 2, 3, 2, 1, 3]
def baseStart_6330122 : Nat := 118140960795 + 6330122 * 2 ^ 59
def prefixEnd_6330122 : Nat := 4983230072969 + 3 ^ 40 * 6330122 * 2
def baseEnd_6330122 : Nat := 3250395187600187602263305

theorem tailTrace_6330122 : CollatzResearch.WordTrace tailWord_6330122 prefixEnd_6330122 3250395187600187602263305 := by
  unfold tailWord_6330122
  simp only [CollatzResearch.WordTrace]
  refine ⟨57719629193264141903010155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153919011182037711741360413 57719629193264141903010155)
  ·
    refine ⟨86579443789896212854515233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57719629193264141903010155 86579443789896212854515233)
    ·
      refine ⟨64934582842422159640886425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86579443789896212854515233 64934582842422159640886425)
      ·
        refine ⟨48700937131816619730664819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64934582842422159640886425 48700937131816619730664819)
        ·
          refine ⟨73051405697724929595997229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48700937131816619730664819 73051405697724929595997229)
          ·
            refine ⟨27394277136646848598498961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73051405697724929595997229 27394277136646848598498961)
            ·
              refine ⟨20545707852485136448874221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27394277136646848598498961 20545707852485136448874221)
              ·
                refine ⟨7704640444681926168327833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20545707852485136448874221 7704640444681926168327833)
                ·
                  refine ⟨5778480333511444626245875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7704640444681926168327833 5778480333511444626245875)
                  ·
                    refine ⟨8667720500267166939368813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5778480333511444626245875 8667720500267166939368813)
                    ·
                      refine ⟨3250395187600187602263305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8667720500267166939368813 3250395187600187602263305)
                      ·
                        rfl

theorem cell23_6330122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_6330122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6330122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6330122 prefixEnd_6330122 := by exact prefixLift 6330122
  have htrace : WordTrace (prefixWord ++ tailWord_6330122) baseStart_6330122 baseEnd_6330122 := by
    simpa [prefixWord, tailWord_6330122, baseEnd_6330122] using wordTrace_append hprefix tailTrace_6330122
  have hstable : (prefixWord ++ tailWord_6330122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6330122).length < 2 ^ (prefixWord ++ tailWord_6330122).sum := by decide
  have hdescent : baseEnd_6330122 < baseStart_6330122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6330122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6330149 : List Nat := [1, 3, 1, 2, 3, 2, 4, 1, 1, 3, 2]
def baseStart_6330149 : Nat := 118140960795 + 6330149 * 2 ^ 59
def prefixEnd_6330149 : Nat := 4983230072969 + 3 ^ 40 * 6330149 * 2
def baseEnd_6330149 : Nat := 3250409051577858996625681

theorem tailTrace_6330149 : CollatzResearch.WordTrace tailWord_6330149 prefixEnd_6330149 3250409051577858996625681 := by
  unfold tailWord_6330149
  simp only [CollatzResearch.WordTrace]
  refine ⟨230879501543958751223273501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153919667695972500815515667 230879501543958751223273501)
  ·
    refine ⟨86579813078984531708727563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230879501543958751223273501 86579813078984531708727563)
    ·
      refine ⟨129869719618476797563091345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86579813078984531708727563 129869719618476797563091345)
      ·
        refine ⟨97402289713857598172318509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129869719618476797563091345 97402289713857598172318509)
        ·
          refine ⟨36525858642696599314619441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97402289713857598172318509 36525858642696599314619441)
          ·
            refine ⟨27394393982022449485964581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36525858642696599314619441 27394393982022449485964581)
            ·
              refine ⟨5136448871629209278618359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27394393982022449485964581 5136448871629209278618359)
              ·
                refine ⟨7704673307443813917927539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5136448871629209278618359 7704673307443813917927539)
                ·
                  refine ⟨11557009961165720876891309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7704673307443813917927539 11557009961165720876891309)
                  ·
                    refine ⟨4333878735437145328834241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11557009961165720876891309 4333878735437145328834241)
                    ·
                      refine ⟨3250409051577858996625681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4333878735437145328834241 3250409051577858996625681)
                      ·
                        rfl

theorem cell23_6330149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 1, 1, 3, 2].length) (baseStart_6330149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6330149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6330149 prefixEnd_6330149 := by exact prefixLift 6330149
  have htrace : WordTrace (prefixWord ++ tailWord_6330149) baseStart_6330149 baseEnd_6330149 := by
    simpa [prefixWord, tailWord_6330149, baseEnd_6330149] using wordTrace_append hprefix tailTrace_6330149
  have hstable : (prefixWord ++ tailWord_6330149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6330149).length < 2 ^ (prefixWord ++ tailWord_6330149).sum := by decide
  have hdescent : baseEnd_6330149 < baseStart_6330149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6330149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6330168 : List Nat := [2, 1, 2, 1, 3, 3, 1, 3, 7]
def baseStart_6330168 : Nat := 118140960795 + 6330168 * 2 ^ 59
def prefixEnd_6330168 : Nat := 4983230072969 + 3 ^ 40 * 6330168 * 2
def baseEnd_6330168 : Nat := 361157645301143824698677

theorem tailTrace_6330168 : CollatzResearch.WordTrace tailWord_6330168 prefixEnd_6330168 361157645301143824698677 := by
  unfold tailWord_6330168
  simp only [CollatzResearch.WordTrace]
  refine ⟨115440097265444958734107579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153920129687259944978810105 115440097265444958734107579)
  ·
    refine ⟨173160145898167438101161369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115440097265444958734107579 173160145898167438101161369)
    ·
      refine ⟨129870109423625578575871027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173160145898167438101161369 129870109423625578575871027)
      ·
        refine ⟨194805164135438367863806541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129870109423625578575871027 194805164135438367863806541)
        ·
          refine ⟨73051936550789387948927453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194805164135438367863806541 73051936550789387948927453)
          ·
            refine ⟨27394476206546020480847795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73051936550789387948927453 27394476206546020480847795)
            ·
              refine ⟨41091714309819030721271693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27394476206546020480847795 41091714309819030721271693)
              ·
                refine ⟨15409392866182136520476885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41091714309819030721271693 15409392866182136520476885)
                ·
                  refine ⟨361157645301143824698677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15409392866182136520476885 361157645301143824698677)
                  ·
                    rfl

theorem cell23_6330168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 7].length) (baseStart_6330168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6330168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6330168 prefixEnd_6330168 := by exact prefixLift 6330168
  have htrace : WordTrace (prefixWord ++ tailWord_6330168) baseStart_6330168 baseEnd_6330168 := by
    simpa [prefixWord, tailWord_6330168, baseEnd_6330168] using wordTrace_append hprefix tailTrace_6330168
  have hstable : (prefixWord ++ tailWord_6330168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6330168).length < 2 ^ (prefixWord ++ tailWord_6330168).sum := by decide
  have hdescent : baseEnd_6330168 < baseStart_6330168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6330168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6330215 : List Nat := [1, 1, 5, 1, 2, 1, 3, 2, 2, 5]
def baseStart_6330215 : Nat := 118140960795 + 6330215 * 2 ^ 59
def prefixEnd_6330215 : Nat := 4983230072969 + 3 ^ 40 * 6330215 * 2
def baseEnd_6330215 : Nat := 1083480980433685246133459

theorem tailTrace_6330215 : CollatzResearch.WordTrace tailWord_6330215 prefixEnd_6330215 1083480980433685246133459 := by
  unfold tailWord_6330215
  simp only [CollatzResearch.WordTrace]
  refine ⟨230881908761719644495176099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153921272507813096330117399 230881908761719644495176099)
  ·
    refine ⟨346322863142579466742764149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230881908761719644495176099 346322863142579466742764149)
    ·
      refine ⟨32467768419616825007134139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 346322863142579466742764149 32467768419616825007134139)
      ·
        refine ⟨48701652629425237510701209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32467768419616825007134139 48701652629425237510701209)
        ·
          refine ⟨36526239472068928133025907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48701652629425237510701209 36526239472068928133025907)
          ·
            refine ⟨54789359208103392199538861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36526239472068928133025907 54789359208103392199538861)
            ·
              refine ⟨20546009703038772074827073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54789359208103392199538861 20546009703038772074827073)
              ·
                refine ⟨15409507277279079056120305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20546009703038772074827073 15409507277279079056120305)
                ·
                  refine ⟨11557130457959309292090229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15409507277279079056120305 11557130457959309292090229)
                  ·
                    refine ⟨1083480980433685246133459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11557130457959309292090229 1083480980433685246133459)
                    ·
                      rfl

theorem cell23_6330215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_6330215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6330215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6330215 prefixEnd_6330215 := by exact prefixLift 6330215
  have htrace : WordTrace (prefixWord ++ tailWord_6330215) baseStart_6330215 baseEnd_6330215 := by
    simpa [prefixWord, tailWord_6330215, baseEnd_6330215] using wordTrace_append hprefix tailTrace_6330215
  have hstable : (prefixWord ++ tailWord_6330215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6330215).length < 2 ^ (prefixWord ++ tailWord_6330215).sum := by decide
  have hdescent : baseEnd_6330215 < baseStart_6330215 := by decide
  rcases family_descends (prefixWord ++ tailWord_6330215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6330230 : List Nat := [5, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2]
def baseStart_6330230 : Nat := 118140960795 + 6330230 * 2 ^ 59
def prefixEnd_6330230 : Nat := 4983230072969 + 3 ^ 40 * 6330230 * 2
def baseEnd_6330230 : Nat := 3250450643510873179712809

theorem tailTrace_6330230 : CollatzResearch.WordTrace tailWord_6330230 prefixEnd_6330230 3250450643510873179712809 := by
  unfold tailWord_6330230
  simp only [CollatzResearch.WordTrace]
  refine ⟨14430153491041581378560759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153921637237776868037981429 14430153491041581378560759)
  ·
    refine ⟨21645230236562372067841139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14430153491041581378560759 21645230236562372067841139)
    ·
      refine ⟨32467845354843558101761709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21645230236562372067841139 32467845354843558101761709)
      ·
        refine ⟨12175442008066334288160641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32467845354843558101761709 12175442008066334288160641)
        ·
          refine ⟨9131581506049750716120481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12175442008066334288160641 9131581506049750716120481)
          ·
            refine ⟨6848686129537313037090361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9131581506049750716120481 6848686129537313037090361)
            ·
              refine ⟨5136514597152984777817771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6848686129537313037090361 5136514597152984777817771)
              ·
                refine ⟨7704771895729477166726657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5136514597152984777817771 7704771895729477166726657)
                ·
                  refine ⟨5778578921797107875044993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7704771895729477166726657 5778578921797107875044993)
                  ·
                    refine ⟨4333934191347830906283745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5778578921797107875044993 4333934191347830906283745)
                    ·
                      refine ⟨3250450643510873179712809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4333934191347830906283745 3250450643510873179712809)
                      ·
                        rfl

theorem cell23_6330230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_6330230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6330230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6330230 prefixEnd_6330230 := by exact prefixLift 6330230
  have htrace : WordTrace (prefixWord ++ tailWord_6330230) baseStart_6330230 baseEnd_6330230 := by
    simpa [prefixWord, tailWord_6330230, baseEnd_6330230] using wordTrace_append hprefix tailTrace_6330230
  have hstable : (prefixWord ++ tailWord_6330230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6330230).length < 2 ^ (prefixWord ++ tailWord_6330230).sum := by decide
  have hdescent : baseEnd_6330230 < baseStart_6330230 := by decide
  rcases family_descends (prefixWord ++ tailWord_6330230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6330235 : List Nat := [1, 1, 1, 1, 1, 5, 1, 3, 1, 6, 2]
def baseStart_6330235 : Nat := 118140960795 + 6330235 * 2 ^ 59
def prefixEnd_6330235 : Nat := 4983230072969 + 3 ^ 40 * 6330235 * 2
def baseEnd_6330235 : Nat := 3250453210914145660150285

theorem tailTrace_6330235 : CollatzResearch.WordTrace tailWord_6330235 prefixEnd_6330235 3250453210914145660150285 := by
  unfold tailWord_6330235
  simp only [CollatzResearch.WordTrace]
  refine ⟨230882638221647187910904159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153921758814431458607269439 230882638221647187910904159)
  ·
    refine ⟨346323957332470781866356239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230882638221647187910904159 346323957332470781866356239)
    ·
      refine ⟨519485935998706172799534359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346323957332470781866356239 519485935998706172799534359)
      ·
        refine ⟨779228903998059259199301539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 519485935998706172799534359 779228903998059259199301539)
        ·
          refine ⟨1168843355997088888798952309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 779228903998059259199301539 1168843355997088888798952309)
          ·
            refine ⟨109579064624727083324901779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1168843355997088888798952309 109579064624727083324901779)
            ·
              refine ⟨164368596937090624987352669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109579064624727083324901779 164368596937090624987352669)
              ·
                refine ⟨61638223851408984370257251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164368596937090624987352669 61638223851408984370257251)
                ·
                  refine ⟨92457335777113476555385877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61638223851408984370257251 92457335777113476555385877)
                  ·
                    refine ⟨4333937614552194213533713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 92457335777113476555385877 4333937614552194213533713)
                    ·
                      refine ⟨3250453210914145660150285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4333937614552194213533713 3250453210914145660150285)
                      ·
                        rfl

theorem cell23_6330235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 6, 2].length) (baseStart_6330235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6330235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6330235 prefixEnd_6330235 := by exact prefixLift 6330235
  have htrace : WordTrace (prefixWord ++ tailWord_6330235) baseStart_6330235 baseEnd_6330235 := by
    simpa [prefixWord, tailWord_6330235, baseEnd_6330235] using wordTrace_append hprefix tailTrace_6330235
  have hstable : (prefixWord ++ tailWord_6330235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6330235).length < 2 ^ (prefixWord ++ tailWord_6330235).sum := by decide
  have hdescent : baseEnd_6330235 < baseStart_6330235 := by decide
  rcases family_descends (prefixWord ++ tailWord_6330235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6330245 : List Nat := [1, 3, 1, 1, 3, 2, 2, 1, 5, 4]
def baseStart_6330245 : Nat := 118140960795 + 6330245 * 2 ^ 59
def prefixEnd_6330245 : Nat := 4983230072969 + 3 ^ 40 * 6330245 * 2
def baseEnd_6330245 : Nat := 1083486115240230207008413

theorem tailTrace_6330245 : CollatzResearch.WordTrace tailWord_6330245 prefixEnd_6330245 1083486115240230207008413 := by
  unfold tailWord_6330245
  simp only [CollatzResearch.WordTrace]
  refine ⟨230883002951610959618768189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153922001967740639745845459 230883002951610959618768189)
  ·
    refine ⟨86581126106854109857038071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230883002951610959618768189 86581126106854109857038071)
    ·
      refine ⟨129871689160281164785557107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86581126106854109857038071 129871689160281164785557107)
      ·
        refine ⟨194807533740421747178335661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129871689160281164785557107 194807533740421747178335661)
        ·
          refine ⟨73052825152658155191875873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194807533740421747178335661 73052825152658155191875873)
          ·
            refine ⟨54789618864493616393906905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73052825152658155191875873 54789618864493616393906905)
            ·
              refine ⟨41092214148370212295430179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54789618864493616393906905 41092214148370212295430179)
              ·
                refine ⟨61638321222555318443145269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41092214148370212295430179 61638321222555318443145269)
                ·
                  refine ⟨5778592614614561104044869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61638321222555318443145269 5778592614614561104044869)
                  ·
                    refine ⟨1083486115240230207008413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5778592614614561104044869 1083486115240230207008413)
                    ·
                      rfl

theorem cell23_6330245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 5, 4].length) (baseStart_6330245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6330245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6330245 prefixEnd_6330245 := by exact prefixLift 6330245
  have htrace : WordTrace (prefixWord ++ tailWord_6330245) baseStart_6330245 baseEnd_6330245 := by
    simpa [prefixWord, tailWord_6330245, baseEnd_6330245] using wordTrace_append hprefix tailTrace_6330245
  have hstable : (prefixWord ++ tailWord_6330245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6330245).length < 2 ^ (prefixWord ++ tailWord_6330245).sum := by decide
  have hdescent : baseEnd_6330245 < baseStart_6330245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6330245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6330270 : List Nat := [4, 3, 1, 3, 2, 1, 2, 2, 5]
def baseStart_6330270 : Nat := 118140960795 + 6330270 * 2 ^ 59
def prefixEnd_6330270 : Nat := 4983230072969 + 3 ^ 40 * 6330270 * 2
def baseEnd_6330270 : Nat := 361163464748561447023625

theorem tailTrace_6330270 : CollatzResearch.WordTrace tailWord_6330270 prefixEnd_6330270 361163464748561447023625 := by
  unfold tailWord_6330270
  simp only [CollatzResearch.WordTrace]
  refine ⟨28860489347065048611053533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153922609851013592592285509 28860489347065048611053533)
  ·
    refine ⟨10822683505149393229145075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28860489347065048611053533 10822683505149393229145075)
    ·
      refine ⟨16234025257724089843717613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10822683505149393229145075 16234025257724089843717613)
      ·
        refine ⟨6087759471646533691394105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16234025257724089843717613 6087759471646533691394105)
        ·
          refine ⟨4565819603734900268545579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6087759471646533691394105 4565819603734900268545579)
          ·
            refine ⟨6848729405602350402818369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4565819603734900268545579 6848729405602350402818369)
            ·
              refine ⟨5136547054201762802113777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6848729405602350402818369 5136547054201762802113777)
              ·
                refine ⟨3852410290651322101585333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5136547054201762802113777 3852410290651322101585333)
                ·
                  refine ⟨361163464748561447023625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3852410290651322101585333 361163464748561447023625)
                  ·
                    rfl

theorem cell23_6330270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_6330270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6330270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6330270 prefixEnd_6330270 := by exact prefixLift 6330270
  have htrace : WordTrace (prefixWord ++ tailWord_6330270) baseStart_6330270 baseEnd_6330270 := by
    simpa [prefixWord, tailWord_6330270, baseEnd_6330270] using wordTrace_append hprefix tailTrace_6330270
  have hstable : (prefixWord ++ tailWord_6330270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6330270).length < 2 ^ (prefixWord ++ tailWord_6330270).sum := by decide
  have hdescent : baseEnd_6330270 < baseStart_6330270 := by decide
  rcases family_descends (prefixWord ++ tailWord_6330270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6330326 : List Nat := [5, 2, 1, 1, 3, 2, 1, 2, 6]
def baseStart_6330326 : Nat := 118140960795 + 6330326 * 2 ^ 59
def prefixEnd_6330326 : Nat := 4983230072969 + 3 ^ 40 * 6330326 * 2
def baseEnd_6330326 : Nat := 361166659739300533790263

theorem tailTrace_6330326 : CollatzResearch.WordTrace tailWord_6330326 prefixEnd_6330326 361166659739300533790263 := by
  unfold tailWord_6330326
  simp only [CollatzResearch.WordTrace]
  refine ⟨14430372329019844403279177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153923971509545006968311221 14430372329019844403279177)
  ·
    refine ⟨10822779246764883302459383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14430372329019844403279177 10822779246764883302459383)
    ·
      refine ⟨16234168870147324953689075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10822779246764883302459383 16234168870147324953689075)
      ·
        refine ⟨24351253305220987430533613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16234168870147324953689075 24351253305220987430533613)
        ·
          refine ⟨9131719989457870286450105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24351253305220987430533613 9131719989457870286450105)
          ·
            refine ⟨6848789992093402714837579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9131719989457870286450105 6848789992093402714837579)
            ·
              refine ⟨10273184988140104072256369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6848789992093402714837579 10273184988140104072256369)
              ·
                refine ⟨7704888741105078054192277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10273184988140104072256369 7704888741105078054192277)
                ·
                  refine ⟨361166659739300533790263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7704888741105078054192277 361166659739300533790263)
                  ·
                    rfl

theorem cell23_6330326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_6330326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6330326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6330326 prefixEnd_6330326 := by exact prefixLift 6330326
  have htrace : WordTrace (prefixWord ++ tailWord_6330326) baseStart_6330326 baseEnd_6330326 := by
    simpa [prefixWord, tailWord_6330326, baseEnd_6330326] using wordTrace_append hprefix tailTrace_6330326
  have hstable : (prefixWord ++ tailWord_6330326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6330326).length < 2 ^ (prefixWord ++ tailWord_6330326).sum := by decide
  have hdescent : baseEnd_6330326 < baseStart_6330326 := by decide
  rcases family_descends (prefixWord ++ tailWord_6330326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6330352 : List Nat := [2, 1, 1, 1, 3, 2, 2, 5, 2, 4]
def baseStart_6330352 : Nat := 118140960795 + 6330352 * 2 ^ 59
def prefixEnd_6330352 : Nat := 4983230072969 + 3 ^ 40 * 6330352 * 2
def baseEnd_6330352 : Nat := 1083504429383573900795749

theorem tailTrace_6330352 : CollatzResearch.WordTrace tailWord_6330352 prefixEnd_6330352 1083504429383573900795749 := by
  unfold tailWord_6330352
  simp only [CollatzResearch.WordTrace]
  refine ⟨115443452781111658446456655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153924603708148877928608873 115443452781111658446456655)
  ·
    refine ⟨173165179171667487669684983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115443452781111658446456655 173165179171667487669684983)
    ·
      refine ⟨259747768757501231504527475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173165179171667487669684983 259747768757501231504527475)
      ·
        refine ⟨389621653136251847256791213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259747768757501231504527475 389621653136251847256791213)
        ·
          refine ⟨146108119926094442721296705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 389621653136251847256791213 146108119926094442721296705)
          ·
            refine ⟨109581089944570832040972529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146108119926094442721296705 109581089944570832040972529)
            ·
              refine ⟨82185817458428124030729397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109581089944570832040972529 82185817458428124030729397)
              ·
                refine ⟨7704920386727636627880881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82185817458428124030729397 7704920386727636627880881)
                ·
                  refine ⟨5778690290045727470910661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7704920386727636627880881 5778690290045727470910661)
                  ·
                    refine ⟨1083504429383573900795749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5778690290045727470910661 1083504429383573900795749)
                    ·
                      rfl

theorem cell23_6330352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 5, 2, 4].length) (baseStart_6330352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6330352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6330352 prefixEnd_6330352 := by exact prefixLift 6330352
  have htrace : WordTrace (prefixWord ++ tailWord_6330352) baseStart_6330352 baseEnd_6330352 := by
    simpa [prefixWord, tailWord_6330352, baseEnd_6330352] using wordTrace_append hprefix tailTrace_6330352
  have hstable : (prefixWord ++ tailWord_6330352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6330352).length < 2 ^ (prefixWord ++ tailWord_6330352).sum := by decide
  have hdescent : baseEnd_6330352 < baseStart_6330352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6330352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6330415 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 4, 3, 4]
def baseStart_6330415 : Nat := 118140960795 + 6330415 * 2 ^ 59
def prefixEnd_6330415 : Nat := 4983230072969 + 3 ^ 40 * 6330415 * 2
def baseEnd_6330415 : Nat := 3250545637431954955899457

theorem tailTrace_6330415 : CollatzResearch.WordTrace tailWord_6330415 prefixEnd_6330415 3250545637431954955899457 := by
  unfold tailWord_6330415
  simp only [CollatzResearch.WordTrace]
  refine ⟨230889203360995078652456699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153926135573996719101637799 230889203360995078652456699)
  ·
    refine ⟨346333805041492617978685049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230889203360995078652456699 346333805041492617978685049)
    ·
      refine ⟨259750353781119463484013787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346333805041492617978685049 259750353781119463484013787)
      ·
        refine ⟨389625530671679195226020681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259750353781119463484013787 389625530671679195226020681)
        ·
          refine ⟨292219148003759396419515511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 389625530671679195226020681 292219148003759396419515511)
          ·
            refine ⟨438328722005639094629273267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292219148003759396419515511 438328722005639094629273267)
            ·
              refine ⟨657493083008458641943909901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 438328722005639094629273267 657493083008458641943909901)
              ·
                refine ⟨246559906128171990728966213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 657493083008458641943909901 246559906128171990728966213)
                ·
                  refine ⟨46229982399032248261681165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 246559906128171990728966213 46229982399032248261681165)
                  ·
                    refine ⟨17336243399637093098130437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46229982399032248261681165 17336243399637093098130437)
                    ·
                      refine ⟨3250545637431954955899457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17336243399637093098130437 3250545637431954955899457)
                      ·
                        rfl

theorem cell23_6330415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 3, 4].length) (baseStart_6330415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6330415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6330415 prefixEnd_6330415 := by exact prefixLift 6330415
  have htrace : WordTrace (prefixWord ++ tailWord_6330415) baseStart_6330415 baseEnd_6330415 := by
    simpa [prefixWord, tailWord_6330415, baseEnd_6330415] using wordTrace_append hprefix tailTrace_6330415
  have hstable : (prefixWord ++ tailWord_6330415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6330415).length < 2 ^ (prefixWord ++ tailWord_6330415).sum := by decide
  have hdescent : baseEnd_6330415 < baseStart_6330415 := by decide
  rcases family_descends (prefixWord ++ tailWord_6330415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6330435 : List Nat := [1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 5]
def baseStart_6330435 : Nat := 118140960795 + 6330435 * 2 ^ 59
def prefixEnd_6330435 : Nat := 4983230072969 + 3 ^ 40 * 6330435 * 2
def baseEnd_6330435 : Nat := 3250555907045044877649365

theorem tailTrace_6330435 : CollatzResearch.WordTrace tailWord_6330435 prefixEnd_6330435 3250555907045044877649365 := by
  unfold tailWord_6330435
  simp only [CollatzResearch.WordTrace]
  refine ⟨230889932820922622068184759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153926621880615081378789839 230889932820922622068184759)
  ·
    refine ⟨346334899231383933102277139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230889932820922622068184759 346334899231383933102277139)
    ·
      refine ⟨519502348847075899653415709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346334899231383933102277139 519502348847075899653415709)
      ·
        refine ⟨194813380817653462370030891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 519502348847075899653415709 194813380817653462370030891)
        ·
          refine ⟨292220071226480193555046337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194813380817653462370030891 292220071226480193555046337)
          ·
            refine ⟨219165053419860145166284753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292220071226480193555046337 219165053419860145166284753)
            ·
              refine ⟨164373790064895108874713565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219165053419860145166284753 164373790064895108874713565)
              ·
                refine ⟨61640171274335665828017587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164373790064895108874713565 61640171274335665828017587)
                ·
                  refine ⟨92460256911503498742026381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61640171274335665828017587 92460256911503498742026381)
                  ·
                    refine ⟨34672596341813812028259893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92460256911503498742026381 34672596341813812028259893)
                    ·
                      refine ⟨3250555907045044877649365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34672596341813812028259893 3250555907045044877649365)
                      ·
                        rfl

theorem cell23_6330435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_6330435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6330435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6330435 prefixEnd_6330435 := by exact prefixLift 6330435
  have htrace : WordTrace (prefixWord ++ tailWord_6330435) baseStart_6330435 baseEnd_6330435 := by
    simpa [prefixWord, tailWord_6330435, baseEnd_6330435] using wordTrace_append hprefix tailTrace_6330435
  have hstable : (prefixWord ++ tailWord_6330435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6330435).length < 2 ^ (prefixWord ++ tailWord_6330435).sum := by decide
  have hdescent : baseEnd_6330435 < baseStart_6330435 := by decide
  rcases family_descends (prefixWord ++ tailWord_6330435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6330489 : List Nat := [1, 2, 1, 3, 4, 1, 1, 5, 5]
def baseStart_6330489 : Nat := 118140960795 + 6330489 * 2 ^ 59
def prefixEnd_6330489 : Nat := 4983230072969 + 3 ^ 40 * 6330489 * 2
def baseEnd_6330489 : Nat := 361175959444487518486013

theorem tailTrace_6330489 : CollatzResearch.WordTrace tailWord_6330489 prefixEnd_6330489 361175959444487518486013 := by
  unfold tailWord_6330489
  simp only [CollatzResearch.WordTrace]
  refine ⟨230891902362726989290650521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153927934908484659527100347 230891902362726989290650521)
  ·
    refine ⟨173168926772045241967987891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230891902362726989290650521 173168926772045241967987891)
    ·
      refine ⟨259753390158067862951981837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173168926772045241967987891 259753390158067862951981837)
      ·
        refine ⟨97407521309275448606993189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259753390158067862951981837 97407521309275448606993189)
        ·
          refine ⟨18263910245489146613811223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97407521309275448606993189 18263910245489146613811223)
          ·
            refine ⟨27395865368233719920716835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18263910245489146613811223 27395865368233719920716835)
            ·
              refine ⟨41093798052350579881075253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27395865368233719920716835 41093798052350579881075253)
              ·
                refine ⟨3852543567407866863850805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41093798052350579881075253 3852543567407866863850805)
                ·
                  refine ⟨361175959444487518486013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3852543567407866863850805 361175959444487518486013)
                  ·
                    rfl

theorem cell23_6330489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 5, 5].length) (baseStart_6330489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6330489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6330489 prefixEnd_6330489 := by exact prefixLift 6330489
  have htrace : WordTrace (prefixWord ++ tailWord_6330489) baseStart_6330489 baseEnd_6330489 := by
    simpa [prefixWord, tailWord_6330489, baseEnd_6330489] using wordTrace_append hprefix tailTrace_6330489
  have hstable : (prefixWord ++ tailWord_6330489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6330489).length < 2 ^ (prefixWord ++ tailWord_6330489).sum := by decide
  have hdescent : baseEnd_6330489 < baseStart_6330489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6330489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6330556 : List Nat := [2, 2, 2, 3, 3, 1, 1, 2, 2, 1, 4]
def baseStart_6330556 : Nat := 118140960795 + 6330556 * 2 ^ 59
def prefixEnd_6330556 : Nat := 4983230072969 + 3 ^ 40 * 6330556 * 2
def baseEnd_6330556 : Nat := 3250618038204238904236309

theorem tailTrace_6330556 : CollatzResearch.WordTrace tailWord_6330556 prefixEnd_6330556 3250618038204238904236309 := by
  unfold tailWord_6330556
  simp only [CollatzResearch.WordTrace]
  refine ⟨115447173026742129866669761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153929564035656173155559681 115447173026742129866669761)
  ·
    refine ⟨86585379770056597400002321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115447173026742129866669761 86585379770056597400002321)
    ·
      refine ⟨64939034827542448050001741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86585379770056597400002321 64939034827542448050001741)
      ·
        refine ⟨24352138060328418018750653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64939034827542448050001741 24352138060328418018750653)
        ·
          refine ⟨9132051772623156757031495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24352138060328418018750653 9132051772623156757031495)
          ·
            refine ⟨13698077658934735135547243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9132051772623156757031495 13698077658934735135547243)
            ·
              refine ⟨20547116488402102703320865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13698077658934735135547243 20547116488402102703320865)
              ·
                refine ⟨15410337366301577027490649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20547116488402102703320865 15410337366301577027490649)
                ·
                  refine ⟨11557753024726182770617987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15410337366301577027490649 11557753024726182770617987)
                  ·
                    refine ⟨17336629537089274155926981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11557753024726182770617987 17336629537089274155926981)
                    ·
                      refine ⟨3250618038204238904236309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17336629537089274155926981 3250618038204238904236309)
                      ·
                        rfl

theorem cell23_6330556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_6330556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6330556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6330556 prefixEnd_6330556 := by exact prefixLift 6330556
  have htrace : WordTrace (prefixWord ++ tailWord_6330556) baseStart_6330556 baseEnd_6330556 := by
    simpa [prefixWord, tailWord_6330556, baseEnd_6330556] using wordTrace_append hprefix tailTrace_6330556
  have hstable : (prefixWord ++ tailWord_6330556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6330556).length < 2 ^ (prefixWord ++ tailWord_6330556).sum := by decide
  have hdescent : baseEnd_6330556 < baseStart_6330556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6330556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6330609 : List Nat := [1, 2, 2, 2, 2, 1, 2, 5, 1, 5]
def baseStart_6330609 : Nat := 118140960795 + 6330609 * 2 ^ 59
def prefixEnd_6330609 : Nat := 4983230072969 + 3 ^ 40 * 6330609 * 2
def baseEnd_6330609 : Nat := 1083548417559642398957855

theorem tailTrace_6330609 : CollatzResearch.WordTrace tailWord_6330609 prefixEnd_6330609 1083548417559642398957855 := by
  unfold tailWord_6330609
  simp only [CollatzResearch.WordTrace]
  refine ⟨230896279122292249785018881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153930852748194833190012587 230896279122292249785018881)
  ·
    refine ⟨173172209341719187338764161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230896279122292249785018881 173172209341719187338764161)
    ·
      refine ⟨129879157006289390504073121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173172209341719187338764161 129879157006289390504073121)
      ·
        refine ⟨97409367754717042878054841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129879157006289390504073121 97409367754717042878054841)
        ·
          refine ⟨73057025816037782158541131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97409367754717042878054841 73057025816037782158541131)
          ·
            refine ⟨109585538724056673237811697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73057025816037782158541131 109585538724056673237811697)
            ·
              refine ⟨82189154043042504928358773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109585538724056673237811697 82189154043042504928358773)
              ·
                refine ⟨7705233191535234837033635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82189154043042504928358773 7705233191535234837033635)
                ·
                  refine ⟨11557849787302852255550453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7705233191535234837033635 11557849787302852255550453)
                  ·
                    refine ⟨1083548417559642398957855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11557849787302852255550453 1083548417559642398957855)
                    ·
                      rfl

theorem cell23_6330609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 5, 1, 5].length) (baseStart_6330609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6330609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6330609 prefixEnd_6330609 := by exact prefixLift 6330609
  have htrace : WordTrace (prefixWord ++ tailWord_6330609) baseStart_6330609 baseEnd_6330609 := by
    simpa [prefixWord, tailWord_6330609, baseEnd_6330609] using wordTrace_append hprefix tailTrace_6330609
  have hstable : (prefixWord ++ tailWord_6330609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6330609).length < 2 ^ (prefixWord ++ tailWord_6330609).sum := by decide
  have hdescent : baseEnd_6330609 < baseStart_6330609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6330609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6330623 : List Nat := [1, 1, 2, 2, 1, 4, 3, 4, 1, 1, 3]
def baseStart_6330623 : Nat := 118140960795 + 6330623 * 2 ^ 59
def prefixEnd_6330623 : Nat := 4983230072969 + 3 ^ 40 * 6330623 * 2
def baseEnd_6330623 : Nat := 3250652441408090142098501

theorem tailTrace_6330623 : CollatzResearch.WordTrace tailWord_6330623 prefixEnd_6330623 3250652441408090142098501 := by
  unfold tailWord_6330623
  simp only [CollatzResearch.WordTrace]
  refine ⟨230896789744241530176028523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153931193162827686784019015 230896789744241530176028523)
  ·
    refine ⟨346345184616362295264042785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230896789744241530176028523 346345184616362295264042785)
    ·
      refine ⟨259758888462271721448032089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346345184616362295264042785 259758888462271721448032089)
      ·
        refine ⟨194819166346703791086024067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259758888462271721448032089 194819166346703791086024067)
        ·
          refine ⟨292228749520055686629036101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194819166346703791086024067 292228749520055686629036101)
          ·
            refine ⟨54792890535010441242944269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 292228749520055686629036101 54792890535010441242944269)
            ·
              refine ⟨20547333950628915466104101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54792890535010441242944269 20547333950628915466104101)
              ·
                refine ⟨3852625115742921649894519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20547333950628915466104101 3852625115742921649894519)
                ·
                  refine ⟨5778937673614382474841779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3852625115742921649894519 5778937673614382474841779)
                  ·
                    refine ⟨8668406510421573712262669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5778937673614382474841779 8668406510421573712262669)
                    ·
                      refine ⟨3250652441408090142098501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8668406510421573712262669 3250652441408090142098501)
                      ·
                        rfl

theorem cell23_6330623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 4, 1, 1, 3].length) (baseStart_6330623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6330623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6330623 prefixEnd_6330623 := by exact prefixLift 6330623
  have htrace : WordTrace (prefixWord ++ tailWord_6330623) baseStart_6330623 baseEnd_6330623 := by
    simpa [prefixWord, tailWord_6330623, baseEnd_6330623] using wordTrace_append hprefix tailTrace_6330623
  have hstable : (prefixWord ++ tailWord_6330623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6330623).length < 2 ^ (prefixWord ++ tailWord_6330623).sum := by decide
  have hdescent : baseEnd_6330623 < baseStart_6330623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6330623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6330626 : List Nat := [3, 4, 1, 1, 2, 1, 1, 2, 3, 5]
def baseStart_6330626 : Nat := 118140960795 + 6330626 * 2 ^ 59
def prefixEnd_6330626 : Nat := 4983230072969 + 3 ^ 40 * 6330626 * 2
def baseEnd_6330626 : Nat := 1083551327283351210120329

theorem tailTrace_6330626 : CollatzResearch.WordTrace tailWord_6330626 prefixEnd_6330626 1083551327283351210120329 := by
  unfold tailWord_6330626
  simp only [CollatzResearch.WordTrace]
  refine ⟨57724224790807665422096933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153931266108820441125591821 57724224790807665422096933)
  ·
    refine ⟨10823292148276437266643175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57724224790807665422096933 10823292148276437266643175)
    ·
      refine ⟨16234938222414655899964763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10823292148276437266643175 16234938222414655899964763)
      ·
        refine ⟨24352407333621983849947145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16234938222414655899964763 24352407333621983849947145)
        ·
          refine ⟨18264305500216487887460359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24352407333621983849947145 18264305500216487887460359)
          ·
            refine ⟨27396458250324731831190539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18264305500216487887460359 27396458250324731831190539)
            ·
              refine ⟨41094687375487097746785809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27396458250324731831190539 41094687375487097746785809)
              ·
                refine ⟨30821015531615323310089357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41094687375487097746785809 30821015531615323310089357)
                ·
                  refine ⟨11557880824355746241283509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30821015531615323310089357 11557880824355746241283509)
                  ·
                    refine ⟨1083551327283351210120329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11557880824355746241283509 1083551327283351210120329)
                    ·
                      rfl

theorem cell23_6330626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_6330626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6330626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6330626 prefixEnd_6330626 := by exact prefixLift 6330626
  have htrace : WordTrace (prefixWord ++ tailWord_6330626) baseStart_6330626 baseEnd_6330626 := by
    simpa [prefixWord, tailWord_6330626, baseEnd_6330626] using wordTrace_append hprefix tailTrace_6330626
  have hstable : (prefixWord ++ tailWord_6330626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6330626).length < 2 ^ (prefixWord ++ tailWord_6330626).sum := by decide
  have hdescent : baseEnd_6330626 < baseStart_6330626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6330626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6330650 : List Nat := [3, 1, 1, 3, 4, 2, 1, 1, 2, 3, 2]
def baseStart_6330650 : Nat := 118140960795 + 6330650 * 2 ^ 59
def prefixEnd_6330650 : Nat := 4983230072969 + 3 ^ 40 * 6330650 * 2
def baseEnd_6330650 : Nat := 3250666305385761536460877

theorem tailTrace_6330650 : CollatzResearch.WordTrace tailWord_6330650 prefixEnd_6330650 3250666305385761536460877 := by
  unfold tailWord_6330650
  simp only [CollatzResearch.WordTrace]
  refine ⟨57724443628785928446815351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153931849676762475858174269 57724443628785928446815351)
  ·
    refine ⟨86586665443178892670223027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57724443628785928446815351 86586665443178892670223027)
    ·
      refine ⟨129879998164768339005334541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86586665443178892670223027 129879998164768339005334541)
      ·
        refine ⟨48704999311788127127000453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129879998164768339005334541 48704999311788127127000453)
        ·
          refine ⟨9132187370960273836312585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48704999311788127127000453 9132187370960273836312585)
          ·
            refine ⟨6849140528220205377234439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9132187370960273836312585 6849140528220205377234439)
            ·
              refine ⟨10273710792330308065851659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6849140528220205377234439 10273710792330308065851659)
              ·
                refine ⟨15410566188495462098777489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10273710792330308065851659 15410566188495462098777489)
                ·
                  refine ⟨11557924641371596574083117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15410566188495462098777489 11557924641371596574083117)
                  ·
                    refine ⟨4334221740514348715281169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11557924641371596574083117 4334221740514348715281169)
                    ·
                      refine ⟨3250666305385761536460877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4334221740514348715281169 3250666305385761536460877)
                      ·
                        rfl

theorem cell23_6330650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 2, 3, 2].length) (baseStart_6330650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6330650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6330650 prefixEnd_6330650 := by exact prefixLift 6330650
  have htrace : WordTrace (prefixWord ++ tailWord_6330650) baseStart_6330650 baseEnd_6330650 := by
    simpa [prefixWord, tailWord_6330650, baseEnd_6330650] using wordTrace_append hprefix tailTrace_6330650
  have hstable : (prefixWord ++ tailWord_6330650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6330650).length < 2 ^ (prefixWord ++ tailWord_6330650).sum := by decide
  have hdescent : baseEnd_6330650 < baseStart_6330650 := by decide
  rcases family_descends (prefixWord ++ tailWord_6330650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6330659 : List Nat := [1, 1, 1, 4, 2, 2, 1, 4, 1, 2, 4]
def baseStart_6330659 : Nat := 118140960795 + 6330659 * 2 ^ 59
def prefixEnd_6330659 : Nat := 4983230072969 + 3 ^ 40 * 6330659 * 2
def baseEnd_6330659 : Nat := 3250670926711652001248335

theorem tailTrace_6330659 : CollatzResearch.WordTrace tailWord_6330659 prefixEnd_6330659 3250670926711652001248335 := by
  unfold tailWord_6330659
  simp only [CollatzResearch.WordTrace]
  refine ⟨230898102772111108324339031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153932068514740738882892687 230898102772111108324339031)
  ·
    refine ⟨346347154158166662486508547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230898102772111108324339031 346347154158166662486508547)
    ·
      refine ⟨519520731237249993729762821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346347154158166662486508547 519520731237249993729762821)
      ·
        refine ⟨97410137106984373824330529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 519520731237249993729762821 97410137106984373824330529)
        ·
          refine ⟨73057602830238280368247897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97410137106984373824330529 73057602830238280368247897)
          ·
            refine ⟨54793202122678710276185923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73057602830238280368247897 54793202122678710276185923)
            ·
              refine ⟨82189803184018065414278885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54793202122678710276185923 82189803184018065414278885)
              ·
                refine ⟨15410588097003387265177291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82189803184018065414278885 15410588097003387265177291)
                ·
                  refine ⟨23115882145505080897765937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15410588097003387265177291 23115882145505080897765937)
                  ·
                    refine ⟨17336911609128810673324453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23115882145505080897765937 17336911609128810673324453)
                    ·
                      refine ⟨3250670926711652001248335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17336911609128810673324453 3250670926711652001248335)
                      ·
                        rfl

theorem cell23_6330659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_6330659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6330659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6330659 prefixEnd_6330659 := by exact prefixLift 6330659
  have htrace : WordTrace (prefixWord ++ tailWord_6330659) baseStart_6330659 baseEnd_6330659 := by
    simpa [prefixWord, tailWord_6330659, baseEnd_6330659] using wordTrace_append hprefix tailTrace_6330659
  have hstable : (prefixWord ++ tailWord_6330659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6330659).length < 2 ^ (prefixWord ++ tailWord_6330659).sum := by decide
  have hdescent : baseEnd_6330659 < baseStart_6330659 := by decide
  rcases family_descends (prefixWord ++ tailWord_6330659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6330679 : List Nat := [1, 1, 3, 1, 2, 1, 1, 4, 3, 3, 3]
def baseStart_6330679 : Nat := 118140960795 + 6330679 * 2 ^ 59
def prefixEnd_6330679 : Nat := 4983230072969 + 3 ^ 40 * 6330679 * 2
def baseEnd_6330679 : Nat := 3250681196324741922998243

theorem tailTrace_6330679 : CollatzResearch.WordTrace tailWord_6330679 prefixEnd_6330679 3250681196324741922998243 := by
  unfold tailWord_6330679
  simp only [CollatzResearch.WordTrace]
  refine ⟨230898832232038651740067091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153932554821359101160044727 230898832232038651740067091)
  ·
    refine ⟨346348248348057977610100637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230898832232038651740067091 346348248348057977610100637)
    ·
      refine ⟨129880593130521741603787739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 346348248348057977610100637 129880593130521741603787739)
      ·
        refine ⟨194820889695782612405681609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129880593130521741603787739 194820889695782612405681609)
        ·
          refine ⟨146115667271836959304261207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194820889695782612405681609 146115667271836959304261207)
          ·
            refine ⟨219173500907755438956391811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146115667271836959304261207 219173500907755438956391811)
            ·
              refine ⟨328760251361633158434587717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219173500907755438956391811 328760251361633158434587717)
              ·
                refine ⟨61642547130306217206485197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 328760251361633158434587717 61642547130306217206485197)
                ·
                  refine ⟨23115955173864831452431949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61642547130306217206485197 23115955173864831452431949)
                  ·
                    refine ⟨8668483190199311794661981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23115955173864831452431949 8668483190199311794661981)
                    ·
                      refine ⟨3250681196324741922998243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8668483190199311794661981 3250681196324741922998243)
                      ·
                        rfl

theorem cell23_6330679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 3, 3].length) (baseStart_6330679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6330679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6330679 prefixEnd_6330679 := by exact prefixLift 6330679
  have htrace : WordTrace (prefixWord ++ tailWord_6330679) baseStart_6330679 baseEnd_6330679 := by
    simpa [prefixWord, tailWord_6330679, baseEnd_6330679] using wordTrace_append hprefix tailTrace_6330679
  have hstable : (prefixWord ++ tailWord_6330679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6330679).length < 2 ^ (prefixWord ++ tailWord_6330679).sum := by decide
  have hdescent : baseEnd_6330679 < baseStart_6330679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6330679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6330680 : List Nat := [2, 1, 2, 1, 3, 1, 4, 4, 1, 2, 2]
def baseStart_6330680 : Nat := 118140960795 + 6330680 * 2 ^ 59
def prefixEnd_6330680 : Nat := 4983230072969 + 3 ^ 40 * 6330680 * 2
def baseEnd_6330680 : Nat := 3250681709805396419085739

theorem tailTrace_6330680 : CollatzResearch.WordTrace tailWord_6330680 prefixEnd_6330680 3250681709805396419085739 := by
  unfold tailWord_6330680
  simp only [CollatzResearch.WordTrace]
  refine ⟨115449434352517514455426747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153932579136690019273902329 115449434352517514455426747)
  ·
    refine ⟨173174151528776271683140121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115449434352517514455426747 173174151528776271683140121)
    ·
      refine ⟨129880613646582203762355091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173174151528776271683140121 129880613646582203762355091)
      ·
        refine ⟨194820920469873305643532637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129880613646582203762355091 194820920469873305643532637)
        ·
          refine ⟨73057845176202489616324739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194820920469873305643532637 73057845176202489616324739)
          ·
            refine ⟨109586767764303734424487109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73057845176202489616324739 109586767764303734424487109)
            ·
              refine ⟨20547518955806950204591333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109586767764303734424487109 20547518955806950204591333)
              ·
                refine ⟨3852659804213803163360875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20547518955806950204591333 3852659804213803163360875)
                ·
                  refine ⟨5778989706320704745041313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3852659804213803163360875 5778989706320704745041313)
                  ·
                    refine ⟨4334242279740528558780985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5778989706320704745041313 4334242279740528558780985)
                    ·
                      refine ⟨3250681709805396419085739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4334242279740528558780985 3250681709805396419085739)
                      ·
                        rfl

theorem cell23_6330680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 4, 1, 2, 2].length) (baseStart_6330680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6330680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6330680 prefixEnd_6330680 := by exact prefixLift 6330680
  have htrace : WordTrace (prefixWord ++ tailWord_6330680) baseStart_6330680 baseEnd_6330680 := by
    simpa [prefixWord, tailWord_6330680, baseEnd_6330680] using wordTrace_append hprefix tailTrace_6330680
  have hstable : (prefixWord ++ tailWord_6330680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6330680).length < 2 ^ (prefixWord ++ tailWord_6330680).sum := by decide
  have hdescent : baseEnd_6330680 < baseStart_6330680 := by decide
  rcases family_descends (prefixWord ++ tailWord_6330680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6330696 : List Nat := [2, 1, 3, 1, 1, 2, 5, 1, 1, 3, 3]
def baseStart_6330696 : Nat := 118140960795 + 6330696 * 2 ^ 59
def prefixEnd_6330696 : Nat := 4983230072969 + 3 ^ 40 * 6330696 * 2
def baseEnd_6330696 : Nat := 3250689925495868356485665

theorem tailTrace_6330696 : CollatzResearch.WordTrace tailWord_6330696 prefixEnd_6330696 3250689925495868356485665 := by
  unfold tailWord_6330696
  simp only [CollatzResearch.WordTrace]
  refine ⟨115449726136488531821717971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153932968181984709095623961 115449726136488531821717971)
  ·
    refine ⟨173174589204732797732576957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115449726136488531821717971 173174589204732797732576957)
    ·
      refine ⟨64940470951774799149716359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173174589204732797732576957 64940470951774799149716359)
      ·
        refine ⟨97410706427662198724574539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64940470951774799149716359 97410706427662198724574539)
        ·
          refine ⟨146116059641493298086861809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97410706427662198724574539 146116059641493298086861809)
          ·
            refine ⟨109587044731119973565146357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146116059641493298086861809 109587044731119973565146357)
            ·
              refine ⟨10273785443542497521732471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109587044731119973565146357 10273785443542497521732471)
              ·
                refine ⟨15410678165313746282598707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10273785443542497521732471 15410678165313746282598707)
                ·
                  refine ⟨23116017247970619423898061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15410678165313746282598707 23116017247970619423898061)
                  ·
                    refine ⟨8668506467988982283961773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23116017247970619423898061 8668506467988982283961773)
                    ·
                      refine ⟨3250689925495868356485665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8668506467988982283961773 3250689925495868356485665)
                      ·
                        rfl

theorem cell23_6330696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 1, 3, 3].length) (baseStart_6330696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6330696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6330696 prefixEnd_6330696 := by exact prefixLift 6330696
  have htrace : WordTrace (prefixWord ++ tailWord_6330696) baseStart_6330696 baseEnd_6330696 := by
    simpa [prefixWord, tailWord_6330696, baseEnd_6330696] using wordTrace_append hprefix tailTrace_6330696
  have hstable : (prefixWord ++ tailWord_6330696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6330696).length < 2 ^ (prefixWord ++ tailWord_6330696).sum := by decide
  have hdescent : baseEnd_6330696 < baseStart_6330696 := by decide
  rcases family_descends (prefixWord ++ tailWord_6330696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6330723 : List Nat := [1, 1, 1, 5, 2, 1, 1, 5, 1, 3, 2]
def baseStart_6330723 : Nat := 118140960795 + 6330723 * 2 ^ 59
def prefixEnd_6330723 : Nat := 4983230072969 + 3 ^ 40 * 6330723 * 2
def baseEnd_6330723 : Nat := 3250703789473539750848041

theorem tailTrace_6330723 : CollatzResearch.WordTrace tailWord_6330723 prefixEnd_6330723 3250703789473539750848041 := by
  unfold tailWord_6330723
  simp only [CollatzResearch.WordTrace]
  refine ⟨230900437043879247254668823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153933624695919498169779215 230900437043879247254668823)
  ·
    refine ⟨346350655565818870882003235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230900437043879247254668823 346350655565818870882003235)
    ·
      refine ⟨519525983348728306323004853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346350655565818870882003235 519525983348728306323004853)
      ·
        refine ⟨48705560938943278717781705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 519525983348728306323004853 48705560938943278717781705)
        ·
          refine ⟨36529170704207459038336279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48705560938943278717781705 36529170704207459038336279)
          ·
            refine ⟨54793756056311188557504419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36529170704207459038336279 54793756056311188557504419)
            ·
              refine ⟨82190634084466782836256629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54793756056311188557504419 82190634084466782836256629)
              ·
                refine ⟨7705371945418760890899059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82190634084466782836256629 7705371945418760890899059)
                ·
                  refine ⟨11558057918128141336348589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7705371945418760890899059 11558057918128141336348589)
                  ·
                    refine ⟨4334271719298053001130721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11558057918128141336348589 4334271719298053001130721)
                    ·
                      refine ⟨3250703789473539750848041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4334271719298053001130721 3250703789473539750848041)
                      ·
                        rfl

theorem cell23_6330723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 5, 1, 3, 2].length) (baseStart_6330723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6330723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6330723 prefixEnd_6330723 := by exact prefixLift 6330723
  have htrace : WordTrace (prefixWord ++ tailWord_6330723) baseStart_6330723 baseEnd_6330723 := by
    simpa [prefixWord, tailWord_6330723, baseEnd_6330723] using wordTrace_append hprefix tailTrace_6330723
  have hstable : (prefixWord ++ tailWord_6330723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6330723).length < 2 ^ (prefixWord ++ tailWord_6330723).sum := by decide
  have hdescent : baseEnd_6330723 < baseStart_6330723 := by decide
  rcases family_descends (prefixWord ++ tailWord_6330723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6330739 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 1, 6, 3]
def baseStart_6330739 : Nat := 118140960795 + 6330739 * 2 ^ 59
def prefixEnd_6330739 : Nat := 4983230072969 + 3 ^ 40 * 6330739 * 2
def baseEnd_6330739 : Nat := 3250712005164011688247967

theorem tailTrace_6330739 : CollatzResearch.WordTrace tailWord_6330739 prefixEnd_6330739 3250712005164011688247967 := by
  unfold tailWord_6330739
  simp only [CollatzResearch.WordTrace]
  refine ⟨230901020611821281987251271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153934013741214187991500847 230901020611821281987251271)
  ·
    refine ⟨346351530917731922980876907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230901020611821281987251271 346351530917731922980876907)
    ·
      refine ⟨519527296376597884471315361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346351530917731922980876907 519527296376597884471315361)
      ·
        refine ⟨389645472282448413353486521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 519527296376597884471315361 389645472282448413353486521)
        ·
          refine ⟨292234104211836310015114891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 389645472282448413353486521 292234104211836310015114891)
          ·
            refine ⟨438351156317754465022672337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292234104211836310015114891 438351156317754465022672337)
            ·
              refine ⟨328763367238315848767004253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 438351156317754465022672337 328763367238315848767004253)
              ·
                refine ⟨123286262714368443287626595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 328763367238315848767004253 123286262714368443287626595)
                ·
                  refine ⟨184929394071552664931439893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123286262714368443287626595 184929394071552664931439893)
                  ·
                    refine ⟨8668565347104031168661245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 184929394071552664931439893 8668565347104031168661245)
                    ·
                      refine ⟨3250712005164011688247967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8668565347104031168661245 3250712005164011688247967)
                      ·
                        rfl

theorem cell23_6330739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 6, 3].length) (baseStart_6330739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6330739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6330739 prefixEnd_6330739 := by exact prefixLift 6330739
  have htrace : WordTrace (prefixWord ++ tailWord_6330739) baseStart_6330739 baseEnd_6330739 := by
    simpa [prefixWord, tailWord_6330739, baseEnd_6330739] using wordTrace_append hprefix tailTrace_6330739
  have hstable : (prefixWord ++ tailWord_6330739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6330739).length < 2 ^ (prefixWord ++ tailWord_6330739).sum := by decide
  have hdescent : baseEnd_6330739 < baseStart_6330739 := by decide
  rcases family_descends (prefixWord ++ tailWord_6330739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6330759 : List Nat := [1, 1, 4, 2, 2, 1, 2, 1, 9]
def baseStart_6330759 : Nat := 118140960795 + 6330759 * 2 ^ 59
def prefixEnd_6330759 : Nat := 4983230072969 + 3 ^ 40 * 6330759 * 2
def baseEnd_6330759 : Nat := 361191363864122401110875

theorem tailTrace_6330759 : CollatzResearch.WordTrace tailWord_6330759 prefixEnd_6330759 361191363864122401110875 := by
  unfold tailWord_6330759
  simp only [CollatzResearch.WordTrace]
  refine ⟨230901750071748825402979331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153934500047832550268652887 230901750071748825402979331)
  ·
    refine ⟨346352625107623238104468997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230901750071748825402979331 346352625107623238104468997)
    ·
      refine ⟨64941117207679357144587937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 346352625107623238104468997 64941117207679357144587937)
      ·
        refine ⟨48705837905759517858440953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64941117207679357144587937 48705837905759517858440953)
        ·
          refine ⟨36529378429319638393830715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48705837905759517858440953 36529378429319638393830715)
          ·
            refine ⟨54794067643979457590746073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36529378429319638393830715 54794067643979457590746073)
            ·
              refine ⟨41095550732984593193059555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54794067643979457590746073 41095550732984593193059555)
              ·
                refine ⟨61643326099476889789589333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41095550732984593193059555 61643326099476889789589333)
                ·
                  refine ⟨361191363864122401110875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 61643326099476889789589333 361191363864122401110875)
                  ·
                    rfl

theorem cell23_6330759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 9].length) (baseStart_6330759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6330759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6330759 prefixEnd_6330759 := by exact prefixLift 6330759
  have htrace : WordTrace (prefixWord ++ tailWord_6330759) baseStart_6330759 baseEnd_6330759 := by
    simpa [prefixWord, tailWord_6330759, baseEnd_6330759] using wordTrace_append hprefix tailTrace_6330759
  have hstable : (prefixWord ++ tailWord_6330759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6330759).length < 2 ^ (prefixWord ++ tailWord_6330759).sum := by decide
  have hdescent : baseEnd_6330759 < baseStart_6330759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6330759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6330804 : List Nat := [2, 5, 2, 2, 1, 1, 2, 1, 1, 4, 2]
def baseStart_6330804 : Nat := 118140960795 + 6330804 * 2 ^ 59
def prefixEnd_6330804 : Nat := 4983230072969 + 3 ^ 40 * 6330804 * 2
def baseEnd_6330804 : Nat := 3250745381406553933935169

theorem tailTrace_6330804 : CollatzResearch.WordTrace tailWord_6330804 prefixEnd_6330804 3250745381406553933935169 := by
  unfold tailWord_6330804
  simp only [CollatzResearch.WordTrace]
  refine ⟨115451695678292899044183733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153935594237723865392244977 115451695678292899044183733)
  ·
    refine ⟨10823596469839959285392225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115451695678292899044183733 10823596469839959285392225)
    ·
      refine ⟨8117697352379969464044169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10823596469839959285392225 8117697352379969464044169)
      ·
        refine ⟨6088273014284977098033127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8117697352379969464044169 6088273014284977098033127)
        ·
          refine ⟨9132409521427465647049691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6088273014284977098033127 9132409521427465647049691)
          ·
            refine ⟨13698614282141198470574537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9132409521427465647049691 13698614282141198470574537)
            ·
              refine ⟨10273960711605898852930903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13698614282141198470574537 10273960711605898852930903)
              ·
                refine ⟨15410941067408848279396355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10273960711605898852930903 15410941067408848279396355)
                ·
                  refine ⟨23116411601113272419094533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15410941067408848279396355 23116411601113272419094533)
                  ·
                    refine ⟨4334327175208738578580225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23116411601113272419094533 4334327175208738578580225)
                    ·
                      refine ⟨3250745381406553933935169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4334327175208738578580225 3250745381406553933935169)
                      ·
                        rfl

theorem cell23_6330804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_6330804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6330804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6330804 prefixEnd_6330804 := by exact prefixLift 6330804
  have htrace : WordTrace (prefixWord ++ tailWord_6330804) baseStart_6330804 baseEnd_6330804 := by
    simpa [prefixWord, tailWord_6330804, baseEnd_6330804] using wordTrace_append hprefix tailTrace_6330804
  have hstable : (prefixWord ++ tailWord_6330804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6330804).length < 2 ^ (prefixWord ++ tailWord_6330804).sum := by decide
  have hdescent : baseEnd_6330804 < baseStart_6330804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6330804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6330823 : List Nat := [1, 1, 4, 1, 1, 6, 1, 1, 2, 5]
def baseStart_6330823 : Nat := 118140960795 + 6330823 * 2 ^ 59
def prefixEnd_6330823 : Nat := 4983230072969 + 3 ^ 40 * 6330823 * 2
def baseEnd_6330823 : Nat := 1083585045846329786532527

theorem tailTrace_6330823 : CollatzResearch.WordTrace tailWord_6330823 prefixEnd_6330823 1083585045846329786532527 := by
  unfold tailWord_6330823
  simp only [CollatzResearch.WordTrace]
  refine ⟨230904084343516964333309123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153936056229011309555539415 230904084343516964333309123)
  ·
    refine ⟨346356126515275446499963685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230904084343516964333309123 346356126515275446499963685)
    ·
      refine ⟨64941773721614146218743191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 346356126515275446499963685 64941773721614146218743191)
      ·
        refine ⟨97412660582421219328114787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64941773721614146218743191 97412660582421219328114787)
        ·
          refine ⟨146118990873631828992172181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97412660582421219328114787 146118990873631828992172181)
          ·
            refine ⟨6849327697201491984008071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 146118990873631828992172181 6849327697201491984008071)
            ·
              refine ⟨10273991545802237976012107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6849327697201491984008071 10273991545802237976012107)
              ·
                refine ⟨15410987318703356964018161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10273991545802237976012107 15410987318703356964018161)
                ·
                  refine ⟨11558240489027517723013621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15410987318703356964018161 11558240489027517723013621)
                  ·
                    refine ⟨1083585045846329786532527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11558240489027517723013621 1083585045846329786532527)
                    ·
                      rfl

theorem cell23_6330823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 2, 5].length) (baseStart_6330823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6330823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6330823 prefixEnd_6330823 := by exact prefixLift 6330823
  have htrace : WordTrace (prefixWord ++ tailWord_6330823) baseStart_6330823 baseEnd_6330823 := by
    simpa [prefixWord, tailWord_6330823, baseEnd_6330823] using wordTrace_append hprefix tailTrace_6330823
  have hstable : (prefixWord ++ tailWord_6330823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6330823).length < 2 ^ (prefixWord ++ tailWord_6330823).sum := by decide
  have hdescent : baseEnd_6330823 < baseStart_6330823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6330823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6330826 : List Nat := [3, 1, 2, 1, 2, 2, 3, 1, 1, 3, 4]
def baseStart_6330826 : Nat := 118140960795 + 6330826 * 2 ^ 59
def prefixEnd_6330826 : Nat := 4983230072969 + 3 ^ 40 * 6330826 * 2
def baseEnd_6330826 : Nat := 3250756677980952847860067

theorem tailTrace_6330826 : CollatzResearch.WordTrace tailWord_6330826 prefixEnd_6330826 3250756677980952847860067 := by
  unfold tailWord_6330826
  simp only [CollatzResearch.WordTrace]
  refine ⟨57726048440626523961417083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153936129175004063897112221 57726048440626523961417083)
  ·
    refine ⟨86589072660939785942125625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57726048440626523961417083 86589072660939785942125625)
    ·
      refine ⟨64941804495704839456594219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86589072660939785942125625 64941804495704839456594219)
      ·
        refine ⟨97412706743557259184891329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64941804495704839456594219 97412706743557259184891329)
        ·
          refine ⟨73059530057667944388668497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97412706743557259184891329 73059530057667944388668497)
          ·
            refine ⟨54794647543250958291501373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73059530057667944388668497 54794647543250958291501373)
            ·
              refine ⟨20547992828719109359313015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54794647543250958291501373 20547992828719109359313015)
              ·
                refine ⟨30821989243078664038969523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20547992828719109359313015 30821989243078664038969523)
                ·
                  refine ⟨46232983864617996058454285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30821989243078664038969523 46232983864617996058454285)
                  ·
                    refine ⟨17337368949231748521920357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46232983864617996058454285 17337368949231748521920357)
                    ·
                      refine ⟨3250756677980952847860067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17337368949231748521920357 3250756677980952847860067)
                      ·
                        rfl

theorem cell23_6330826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_6330826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6330826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6330826 prefixEnd_6330826 := by exact prefixLift 6330826
  have htrace : WordTrace (prefixWord ++ tailWord_6330826) baseStart_6330826 baseEnd_6330826 := by
    simpa [prefixWord, tailWord_6330826, baseEnd_6330826] using wordTrace_append hprefix tailTrace_6330826
  have hstable : (prefixWord ++ tailWord_6330826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6330826).length < 2 ^ (prefixWord ++ tailWord_6330826).sum := by decide
  have hdescent : baseEnd_6330826 < baseStart_6330826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6330826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6330876 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 1, 7, 3]
def baseStart_6330876 : Nat := 118140960795 + 6330876 * 2 ^ 59
def prefixEnd_6330876 : Nat := 4983230072969 + 3 ^ 40 * 6330876 * 2
def baseEnd_6330876 : Nat := 3250782352013677652234837

theorem tailTrace_6330876 : CollatzResearch.WordTrace tailWord_6330876 prefixEnd_6330876 3250782352013677652234837 := by
  unfold tailWord_6330876
  simp only [CollatzResearch.WordTrace]
  refine ⟨115453008706162477192494241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153937344941549969589992321 115453008706162477192494241)
  ·
    refine ⟨86589756529621857894370681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115453008706162477192494241 86589756529621857894370681)
    ·
      refine ⟨64942317397216393420778011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86589756529621857894370681 64942317397216393420778011)
      ·
        refine ⟨97413476095824590131167017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64942317397216393420778011 97413476095824590131167017)
        ·
          refine ⟨73060107071868442598375263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97413476095824590131167017 73060107071868442598375263)
          ·
            refine ⟨109590160607802663897562895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73060107071868442598375263 109590160607802663897562895)
            ·
              refine ⟨164385240911703995846344343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109590160607802663897562895 164385240911703995846344343)
              ·
                refine ⟨246577861367555993769516515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164385240911703995846344343 246577861367555993769516515)
                ·
                  refine ⟨369866792051333990654274773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 246577861367555993769516515 369866792051333990654274773)
                  ·
                    refine ⟨8668752938703140405959565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 369866792051333990654274773 8668752938703140405959565)
                    ·
                      refine ⟨3250782352013677652234837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8668752938703140405959565 3250782352013677652234837)
                      ·
                        rfl

theorem cell23_6330876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 1, 7, 3].length) (baseStart_6330876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6330876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6330876 prefixEnd_6330876 := by exact prefixLift 6330876
  have htrace : WordTrace (prefixWord ++ tailWord_6330876) baseStart_6330876 baseEnd_6330876 := by
    simpa [prefixWord, tailWord_6330876, baseEnd_6330876] using wordTrace_append hprefix tailTrace_6330876
  have hstable : (prefixWord ++ tailWord_6330876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6330876).length < 2 ^ (prefixWord ++ tailWord_6330876).sum := by decide
  have hdescent : baseEnd_6330876 < baseStart_6330876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6330876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6330933 : List Nat := [1, 3, 3, 1, 1, 2, 3, 1, 3, 1, 4]
def baseStart_6330933 : Nat := 118140960795 + 6330933 * 2 ^ 59
def prefixEnd_6330933 : Nat := 4983230072969 + 3 ^ 40 * 6330933 * 2
def baseEnd_6330933 : Nat := 3250811620410983929222075

theorem tailTrace_6330933 : CollatzResearch.WordTrace tailWord_6330933 prefixEnd_6330933 3250811620410983929222075 := by
  unfold tailWord_6330933
  simp only [CollatzResearch.WordTrace]
  refine ⟨230908096373118453119813453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153938730915412302079875635 230908096373118453119813453)
  ·
    refine ⟨86590536139919419919930045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230908096373118453119813453 86590536139919419919930045)
    ·
      refine ⟨32471451052469782469973767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86590536139919419919930045 32471451052469782469973767)
      ·
        refine ⟨48707176578704673704960651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32471451052469782469973767 48707176578704673704960651)
        ·
          refine ⟨73060764868057010557440977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48707176578704673704960651 73060764868057010557440977)
          ·
            refine ⟨54795573651042757918080733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73060764868057010557440977 54795573651042757918080733)
            ·
              refine ⟨20548340119141034219280275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54795573651042757918080733 20548340119141034219280275)
              ·
                refine ⟨30822510178711551328920413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20548340119141034219280275 30822510178711551328920413)
                ·
                  refine ⟨11558441317016831748345155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30822510178711551328920413 11558441317016831748345155)
                  ·
                    refine ⟨17337661975525247622517733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11558441317016831748345155 17337661975525247622517733)
                    ·
                      refine ⟨3250811620410983929222075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17337661975525247622517733 3250811620410983929222075)
                      ·
                        rfl

theorem cell23_6330933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_6330933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6330933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6330933 prefixEnd_6330933 := by exact prefixLift 6330933
  have htrace : WordTrace (prefixWord ++ tailWord_6330933) baseStart_6330933 baseEnd_6330933 := by
    simpa [prefixWord, tailWord_6330933, baseEnd_6330933] using wordTrace_append hprefix tailTrace_6330933
  have hstable : (prefixWord ++ tailWord_6330933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6330933).length < 2 ^ (prefixWord ++ tailWord_6330933).sum := by decide
  have hdescent : baseEnd_6330933 < baseStart_6330933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6330933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6330976 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 6]
def baseStart_6330976 : Nat := 118140960795 + 6330976 * 2 ^ 59
def prefixEnd_6330976 : Nat := 4983230072969 + 3 ^ 40 * 6330976 * 2
def baseEnd_6330976 : Nat := 3250833700079127260984377

theorem tailTrace_6330976 : CollatzResearch.WordTrace tailWord_6330976 prefixEnd_6330976 3250833700079127260984377 := by
  unfold tailWord_6330976
  simp only [CollatzResearch.WordTrace]
  refine ⟨115454832355981335731814391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153939776474641780975752521 115454832355981335731814391)
  ·
    refine ⟨173182248533972003597721587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115454832355981335731814391 173182248533972003597721587)
    ·
      refine ⟨259773372800958005396582381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173182248533972003597721587 259773372800958005396582381)
      ·
        refine ⟨97415014800359252023718393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259773372800958005396582381 97415014800359252023718393)
        ·
          refine ⟨73061261100269439017788795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97415014800359252023718393 73061261100269439017788795)
          ·
            refine ⟨109591891650404158526683193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73061261100269439017788795 109591891650404158526683193)
            ·
              refine ⟨82193918737803118895012395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109591891650404158526683193 82193918737803118895012395)
              ·
                refine ⟨123290878106704678342518593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82193918737803118895012395 123290878106704678342518593)
                ·
                  refine ⟨92468158580028508756888945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123290878106704678342518593 92468158580028508756888945)
                  ·
                    refine ⟨69351118935021381567666709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 92468158580028508756888945 69351118935021381567666709)
                    ·
                      refine ⟨3250833700079127260984377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69351118935021381567666709 3250833700079127260984377)
                      ·
                        rfl

theorem cell23_6330976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_6330976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6330976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6330976 prefixEnd_6330976 := by exact prefixLift 6330976
  have htrace : WordTrace (prefixWord ++ tailWord_6330976) baseStart_6330976 baseEnd_6330976 := by
    simpa [prefixWord, tailWord_6330976, baseEnd_6330976] using wordTrace_append hprefix tailTrace_6330976
  have hstable : (prefixWord ++ tailWord_6330976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6330976).length < 2 ^ (prefixWord ++ tailWord_6330976).sum := by decide
  have hdescent : baseEnd_6330976 < baseStart_6330976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6330976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6330984 : List Nat := [2, 1, 4, 3, 2, 1, 1, 2, 3, 2, 2]
def baseStart_6330984 : Nat := 118140960795 + 6330984 * 2 ^ 59
def prefixEnd_6330984 : Nat := 4983230072969 + 3 ^ 40 * 6330984 * 2
def baseEnd_6330984 : Nat := 3250837807924363229684341

theorem tailTrace_6330984 : CollatzResearch.WordTrace tailWord_6330984 prefixEnd_6330984 3250837807924363229684341 := by
  unfold tailWord_6330984
  simp only [CollatzResearch.WordTrace]
  refine ⟨115454978247966844414960003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153939970997289125886613337 115454978247966844414960003)
  ·
    refine ⟨173182467371950266622440005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115454978247966844414960003 173182467371950266622440005)
    ·
      refine ⟨32471712632240674991707501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173182467371950266622440005 32471712632240674991707501)
      ·
        refine ⟨12176892237090253121890313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32471712632240674991707501 12176892237090253121890313)
        ·
          refine ⟨9132669177817689841417735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12176892237090253121890313 9132669177817689841417735)
          ·
            refine ⟨13699003766726534762126603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9132669177817689841417735 13699003766726534762126603)
            ·
              refine ⟨20548505650089802143189905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13699003766726534762126603 20548505650089802143189905)
              ·
                refine ⟨15411379237567351607392429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20548505650089802143189905 15411379237567351607392429)
                ·
                  refine ⟨5779267214087756852772161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15411379237567351607392429 5779267214087756852772161)
                  ·
                    refine ⟨4334450410565817639579121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5779267214087756852772161 4334450410565817639579121)
                    ·
                      refine ⟨3250837807924363229684341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4334450410565817639579121 3250837807924363229684341)
                      ·
                        rfl

theorem cell23_6330984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_6330984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6330984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6330984 prefixEnd_6330984 := by exact prefixLift 6330984
  have htrace : WordTrace (prefixWord ++ tailWord_6330984) baseStart_6330984 baseEnd_6330984 := by
    simpa [prefixWord, tailWord_6330984, baseEnd_6330984] using wordTrace_append hprefix tailTrace_6330984
  have hstable : (prefixWord ++ tailWord_6330984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6330984).length < 2 ^ (prefixWord ++ tailWord_6330984).sum := by decide
  have hdescent : baseEnd_6330984 < baseStart_6330984 := by decide
  rcases family_descends (prefixWord ++ tailWord_6330984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6330990 : List Nat := [4, 1, 2, 2, 2, 2, 3, 7]
def baseStart_6330990 : Nat := 118140960795 + 6330990 * 2 ^ 59
def prefixEnd_6330990 : Nat := 4983230072969 + 3 ^ 40 * 6330990 * 2
def baseEnd_6330990 : Nat := 120401514400307044674419

theorem tailTrace_6330990 : CollatzResearch.WordTrace tailWord_6330990 prefixEnd_6330990 120401514400307044674419 := by
  unfold tailWord_6330990
  simp only [CollatzResearch.WordTrace]
  refine ⟨28863771916738993981829803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153940116889274634569758949 28863771916738993981829803)
  ·
    refine ⟨43295657875108490972744705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28863771916738993981829803 43295657875108490972744705)
    ·
      refine ⟨32471743406331368229558529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43295657875108490972744705 32471743406331368229558529)
      ·
        refine ⟨24353807554748526172168897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32471743406331368229558529 24353807554748526172168897)
        ·
          refine ⟨18265355666061394629126673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24353807554748526172168897 18265355666061394629126673)
          ·
            refine ⟨13699016749546045971845005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18265355666061394629126673 13699016749546045971845005)
            ·
              refine ⟨5137131281079767239441877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13699016749546045971845005 5137131281079767239441877)
              ·
                refine ⟨120401514400307044674419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5137131281079767239441877 120401514400307044674419)
                ·
                  rfl

theorem cell23_6330990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 7].length) (baseStart_6330990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6330990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6330990 prefixEnd_6330990 := by exact prefixLift 6330990
  have htrace : WordTrace (prefixWord ++ tailWord_6330990) baseStart_6330990 baseEnd_6330990 := by
    simpa [prefixWord, tailWord_6330990, baseEnd_6330990] using wordTrace_append hprefix tailTrace_6330990
  have hstable : (prefixWord ++ tailWord_6330990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6330990).length < 2 ^ (prefixWord ++ tailWord_6330990).sum := by decide
  have hdescent : baseEnd_6330990 < baseStart_6330990 := by decide
  rcases family_descends (prefixWord ++ tailWord_6330990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331034 : List Nat := [3, 1, 1, 6, 1, 2, 1, 1, 1, 3, 3]
def baseStart_6331034 : Nat := 118140960795 + 6331034 * 2 ^ 59
def prefixEnd_6331034 : Nat := 4983230072969 + 3 ^ 40 * 6331034 * 2
def baseEnd_6331034 : Nat := 3250863481957088034059111

theorem tailTrace_6331034 : CollatzResearch.WordTrace tailWord_6331034 prefixEnd_6331034 3250863481957088034059111 := by
  unfold tailWord_6331034
  simp only [CollatzResearch.WordTrace]
  refine ⟨57727945036438136842310039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153941186763835031579493437 57727945036438136842310039)
  ·
    refine ⟨86591917554657205263465059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57727945036438136842310039 86591917554657205263465059)
    ·
      refine ⟨129887876331985807895197589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86591917554657205263465059 129887876331985807895197589)
      ·
        refine ⟨6088494203061834745087387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 129887876331985807895197589 6088494203061834745087387)
        ·
          refine ⟨9132741304592752117631081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6088494203061834745087387 9132741304592752117631081)
          ·
            refine ⟨6849555978444564088223311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9132741304592752117631081 6849555978444564088223311)
            ·
              refine ⟨10274333967666846132334967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6849555978444564088223311 10274333967666846132334967)
              ·
                refine ⟨15411500951500269198502451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10274333967666846132334967 15411500951500269198502451)
                ·
                  refine ⟨23117251427250403797753677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15411500951500269198502451 23117251427250403797753677)
                  ·
                    refine ⟨8668969285218901424157629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23117251427250403797753677 8668969285218901424157629)
                    ·
                      refine ⟨3250863481957088034059111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8668969285218901424157629 3250863481957088034059111)
                      ·
                        rfl

theorem cell23_6331034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_6331034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331034 prefixEnd_6331034 := by exact prefixLift 6331034
  have htrace : WordTrace (prefixWord ++ tailWord_6331034) baseStart_6331034 baseEnd_6331034 := by
    simpa [prefixWord, tailWord_6331034, baseEnd_6331034] using wordTrace_append hprefix tailTrace_6331034
  have hstable : (prefixWord ++ tailWord_6331034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331034).length < 2 ^ (prefixWord ++ tailWord_6331034).sum := by decide
  have hdescent : baseEnd_6331034 < baseStart_6331034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331080 : List Nat := [2, 1, 3, 1, 2, 5, 1, 1, 7]
def baseStart_6331080 : Nat := 118140960795 + 6331080 * 2 ^ 59
def prefixEnd_6331080 : Nat := 4983230072969 + 3 ^ 40 * 6331080 * 2
def baseEnd_6331080 : Nat := 361209678007466094898211

theorem tailTrace_6331080 : CollatzResearch.WordTrace tailWord_6331080 prefixEnd_6331080 361209678007466094898211 := by
  unfold tailWord_6331080
  simp only [CollatzResearch.WordTrace]
  refine ⟨115456728951792948612707347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153942305269057264816943129 115456728951792948612707347)
  ·
    refine ⟨173185093427689422919061021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115456728951792948612707347 173185093427689422919061021)
    ·
      refine ⟨64944410035383533594647883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173185093427689422919061021 64944410035383533594647883)
      ·
        refine ⟨97416615053075300391971825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64944410035383533594647883 97416615053075300391971825)
        ·
          refine ⟨73062461289806475293978869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97416615053075300391971825 73062461289806475293978869)
          ·
            refine ⟨6849605745919357058810519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73062461289806475293978869 6849605745919357058810519)
            ·
              refine ⟨10274408618879035588215779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6849605745919357058810519 10274408618879035588215779)
              ·
                refine ⟨15411612928318553382323669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10274408618879035588215779 15411612928318553382323669)
                ·
                  refine ⟨361209678007466094898211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15411612928318553382323669 361209678007466094898211)
                  ·
                    rfl

theorem cell23_6331080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 7].length) (baseStart_6331080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331080 prefixEnd_6331080 := by exact prefixLift 6331080
  have htrace : WordTrace (prefixWord ++ tailWord_6331080) baseStart_6331080 baseEnd_6331080 := by
    simpa [prefixWord, tailWord_6331080, baseEnd_6331080] using wordTrace_append hprefix tailTrace_6331080
  have hstable : (prefixWord ++ tailWord_6331080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331080).length < 2 ^ (prefixWord ++ tailWord_6331080).sum := by decide
  have hdescent : baseEnd_6331080 < baseStart_6331080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331085 : List Nat := [1, 6, 2, 1, 3, 1, 2, 1, 2, 1, 3]
def baseStart_6331085 : Nat := 118140960795 + 6331085 * 2 ^ 59
def prefixEnd_6331085 : Nat := 4983230072969 + 3 ^ 40 * 6331085 * 2
def baseEnd_6331085 : Nat := 3250889669470467334521377

theorem tailTrace_6331085 : CollatzResearch.WordTrace tailWord_6331085 prefixEnd_6331085 3250889669470467334521377 := by
  unfold tailWord_6331085
  simp only [CollatzResearch.WordTrace]
  refine ⟨230913640268567783079346709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153942426845711855386231139 230913640268567783079346709)
  ·
    refine ⟨10824076887589114831844377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 230913640268567783079346709 10824076887589114831844377)
    ·
      refine ⟨8118057665691836123883283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10824076887589114831844377 8118057665691836123883283)
      ·
        refine ⟨12177086498537754185824925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8118057665691836123883283 12177086498537754185824925)
        ·
          refine ⟨4566407436951657819684347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12177086498537754185824925 4566407436951657819684347)
          ·
            refine ⟨6849611155427486729526521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4566407436951657819684347 6849611155427486729526521)
            ·
              refine ⟨5137208366570615047144891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6849611155427486729526521 5137208366570615047144891)
              ·
                refine ⟨7705812549855922570717337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5137208366570615047144891 7705812549855922570717337)
                ·
                  refine ⟨5779359412391941928038003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7705812549855922570717337 5779359412391941928038003)
                  ·
                    refine ⟨8669039118587912892057005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5779359412391941928038003 8669039118587912892057005)
                    ·
                      refine ⟨3250889669470467334521377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8669039118587912892057005 3250889669470467334521377)
                      ·
                        rfl

theorem cell23_6331085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_6331085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331085 prefixEnd_6331085 := by exact prefixLift 6331085
  have htrace : WordTrace (prefixWord ++ tailWord_6331085) baseStart_6331085 baseEnd_6331085 := by
    simpa [prefixWord, tailWord_6331085, baseEnd_6331085] using wordTrace_append hprefix tailTrace_6331085
  have hstable : (prefixWord ++ tailWord_6331085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331085).length < 2 ^ (prefixWord ++ tailWord_6331085).sum := by decide
  have hdescent : baseEnd_6331085 < baseStart_6331085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331113 : List Nat := [1, 2, 1, 1, 1, 2, 4, 3, 1, 3, 4]
def baseStart_6331113 : Nat := 118140960795 + 6331113 * 2 ^ 59
def prefixEnd_6331113 : Nat := 4983230072969 + 3 ^ 40 * 6331113 * 2
def baseEnd_6331113 : Nat := 3250904046928793224971247

theorem tailTrace_6331113 : CollatzResearch.WordTrace tailWord_6331113 prefixEnd_6331113 3250904046928793224971247 := by
  unfold tailWord_6331113
  simp only [CollatzResearch.WordTrace]
  refine ⟨230914661512466343861365993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153943107674977562574243995 230914661512466343861365993)
  ·
    refine ⟨173185996134349757896024495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230914661512466343861365993 173185996134349757896024495)
    ·
      refine ⟨259778994201524636844036743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173185996134349757896024495 259778994201524636844036743)
      ·
        refine ⟨389668491302286955266055115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259778994201524636844036743 389668491302286955266055115)
        ·
          refine ⟨584502736953430432899082673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389668491302286955266055115 584502736953430432899082673)
          ·
            refine ⟨438377052715072824674312005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 584502736953430432899082673 438377052715072824674312005)
            ·
              refine ⟨82195697384076154626433501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 438377052715072824674312005 82195697384076154626433501)
              ·
                refine ⟨30823386519028557984912563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82195697384076154626433501 30823386519028557984912563)
                ·
                  refine ⟨46235079778542836977368845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30823386519028557984912563 46235079778542836977368845)
                  ·
                    refine ⟨17338154916953563866513317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46235079778542836977368845 17338154916953563866513317)
                    ·
                      refine ⟨3250904046928793224971247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17338154916953563866513317 3250904046928793224971247)
                      ·
                        rfl

theorem cell23_6331113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 3, 4].length) (baseStart_6331113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331113 prefixEnd_6331113 := by exact prefixLift 6331113
  have htrace : WordTrace (prefixWord ++ tailWord_6331113) baseStart_6331113 baseEnd_6331113 := by
    simpa [prefixWord, tailWord_6331113, baseEnd_6331113] using wordTrace_append hprefix tailTrace_6331113
  have hstable : (prefixWord ++ tailWord_6331113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331113).length < 2 ^ (prefixWord ++ tailWord_6331113).sum := by decide
  have hdescent : baseEnd_6331113 < baseStart_6331113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331125 : List Nat := [1, 3, 6, 1, 1, 1, 2, 2, 2, 2, 2]
def baseStart_6331125 : Nat := 118140960795 + 6331125 * 2 ^ 59
def prefixEnd_6331125 : Nat := 4983230072969 + 3 ^ 40 * 6331125 * 2
def baseEnd_6331125 : Nat := 3250910208696647178021193

theorem tailTrace_6331125 : CollatzResearch.WordTrace tailWord_6331125 prefixEnd_6331125 3250910208696647178021193 := by
  unfold tailWord_6331125
  simp only [CollatzResearch.WordTrace]
  refine ⟨230915099188422869910802829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153943399458948579940535219 230915099188422869910802829)
  ·
    refine ⟨86593162195658576216551061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230915099188422869910802829 86593162195658576216551061)
    ·
      refine ⟨4059054477921495760150831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 86593162195658576216551061 4059054477921495760150831)
      ·
        refine ⟨6088581716882243640226247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4059054477921495760150831 6088581716882243640226247)
        ·
          refine ⟨9132872575323365460339371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6088581716882243640226247 9132872575323365460339371)
          ·
            refine ⟨13699308862985048190509057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9132872575323365460339371 13699308862985048190509057)
            ·
              refine ⟨10274481647238786142881793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13699308862985048190509057 10274481647238786142881793)
              ·
                refine ⟨7705861235429089607161345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10274481647238786142881793 7705861235429089607161345)
                ·
                  refine ⟨5779395926571817205371009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7705861235429089607161345 5779395926571817205371009)
                  ·
                    refine ⟨4334546944928862904028257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5779395926571817205371009 4334546944928862904028257)
                    ·
                      refine ⟨3250910208696647178021193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4334546944928862904028257 3250910208696647178021193)
                      ·
                        rfl

theorem cell23_6331125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_6331125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331125 prefixEnd_6331125 := by exact prefixLift 6331125
  have htrace : WordTrace (prefixWord ++ tailWord_6331125) baseStart_6331125 baseEnd_6331125 := by
    simpa [prefixWord, tailWord_6331125, baseEnd_6331125] using wordTrace_append hprefix tailTrace_6331125
  have hstable : (prefixWord ++ tailWord_6331125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331125).length < 2 ^ (prefixWord ++ tailWord_6331125).sum := by decide
  have hdescent : baseEnd_6331125 < baseStart_6331125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331130 : List Nat := [3, 1, 1, 1, 1, 3, 4, 2, 2, 1, 4]
def baseStart_6331130 : Nat := 118140960795 + 6331130 * 2 ^ 59
def prefixEnd_6331130 : Nat := 4983230072969 + 3 ^ 40 * 6331130 * 2
def baseEnd_6331130 : Nat := 3250912776099919658458669

theorem tailTrace_6331130 : CollatzResearch.WordTrace tailWord_6331130 prefixEnd_6331130 3250912776099919658458669 := by
  unfold tailWord_6331130
  simp only [CollatzResearch.WordTrace]
  refine ⟨57728820388351188941183711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153943521035603170509823229 57728820388351188941183711)
  ·
    refine ⟨86593230582526783411775567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57728820388351188941183711 86593230582526783411775567)
    ·
      refine ⟨129889845873790175117663351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86593230582526783411775567 129889845873790175117663351)
      ·
        refine ⟨194834768810685262676495027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129889845873790175117663351 194834768810685262676495027)
        ·
          refine ⟨292252153216027894014742541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194834768810685262676495027 292252153216027894014742541)
          ·
            refine ⟨109594557456010460255528453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 292252153216027894014742541 109594557456010460255528453)
            ·
              refine ⟨20548979523001961297911585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109594557456010460255528453 20548979523001961297911585)
              ·
                refine ⟨15411734642251470973433689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20548979523001961297911585 15411734642251470973433689)
                ·
                  refine ⟨11558800981688603230075267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15411734642251470973433689 11558800981688603230075267)
                  ·
                    refine ⟨17338201472532904845112901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11558800981688603230075267 17338201472532904845112901)
                    ·
                      refine ⟨3250912776099919658458669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17338201472532904845112901 3250912776099919658458669)
                      ·
                        rfl

theorem cell23_6331130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 2, 1, 4].length) (baseStart_6331130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331130 prefixEnd_6331130 := by exact prefixLift 6331130
  have htrace : WordTrace (prefixWord ++ tailWord_6331130) baseStart_6331130 baseEnd_6331130 := by
    simpa [prefixWord, tailWord_6331130, baseEnd_6331130] using wordTrace_append hprefix tailTrace_6331130
  have hstable : (prefixWord ++ tailWord_6331130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331130).length < 2 ^ (prefixWord ++ tailWord_6331130).sum := by decide
  have hdescent : baseEnd_6331130 < baseStart_6331130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331133 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 2, 3, 5]
def baseStart_6331133 : Nat := 118140960795 + 6331133 * 2 ^ 59
def prefixEnd_6331133 : Nat := 4983230072969 + 3 ^ 40 * 6331133 * 2
def baseEnd_6331133 : Nat := 3250914316541883146721155

theorem tailTrace_6331133 : CollatzResearch.WordTrace tailWord_6331133 prefixEnd_6331133 3250914316541883146721155 := by
  unfold tailWord_6331133
  simp only [CollatzResearch.WordTrace]
  refine ⟨230915390972393887277094053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153943593981595924851396035 230915390972393887277094053)
  ·
    refine ⟨43296635807323853864455135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230915390972393887277094053 43296635807323853864455135)
    ·
      refine ⟨64944953710985780796682703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43296635807323853864455135 64944953710985780796682703)
      ·
        refine ⟨97417430566478671195024055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64944953710985780796682703 97417430566478671195024055)
        ·
          refine ⟨146126145849718006792536083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97417430566478671195024055 146126145849718006792536083)
          ·
            refine ⟨219189218774577010188804125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146126145849718006792536083 219189218774577010188804125)
            ·
              refine ⟨82195957040466378820801547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 219189218774577010188804125 82195957040466378820801547)
              ·
                refine ⟨123293935560699568231202321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82195957040466378820801547 123293935560699568231202321)
                ·
                  refine ⟨92470451670524676173401741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123293935560699568231202321 92470451670524676173401741)
                  ·
                    refine ⟨34676419376446753565025653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92470451670524676173401741 34676419376446753565025653)
                    ·
                      refine ⟨3250914316541883146721155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34676419376446753565025653 3250914316541883146721155)
                      ·
                        rfl

theorem cell23_6331133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_6331133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331133 prefixEnd_6331133 := by exact prefixLift 6331133
  have htrace : WordTrace (prefixWord ++ tailWord_6331133) baseStart_6331133 baseEnd_6331133 := by
    simpa [prefixWord, tailWord_6331133, baseEnd_6331133] using wordTrace_append hprefix tailTrace_6331133
  have hstable : (prefixWord ++ tailWord_6331133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331133).length < 2 ^ (prefixWord ++ tailWord_6331133).sum := by decide
  have hdescent : baseEnd_6331133 < baseStart_6331133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331150 : List Nat := [4, 1, 1, 2, 1, 1, 1, 4, 1, 4, 3]
def baseStart_6331150 : Nat := 118140960795 + 6331150 * 2 ^ 59
def prefixEnd_6331150 : Nat := 4983230072969 + 3 ^ 40 * 6331150 * 2
def baseEnd_6331150 : Nat := 3250923045713009580208577

theorem tailTrace_6331150 : CollatzResearch.WordTrace tailWord_6331150 prefixEnd_6331150 3250923045713009580208577 := by
  unfold tailWord_6331150
  simp only [CollatzResearch.WordTrace]
  refine ⟨28864501376666537397557863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153944007342221532786975269 28864501376666537397557863)
  ·
    refine ⟨43296752064999806096336795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28864501376666537397557863 43296752064999806096336795)
    ·
      refine ⟨64945128097499709144505193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43296752064999806096336795 64945128097499709144505193)
      ·
        refine ⟨48708846073124781858378895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64945128097499709144505193 48708846073124781858378895)
        ·
          refine ⟨73063269109687172787568343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48708846073124781858378895 73063269109687172787568343)
          ·
            refine ⟨109594903664530759181352515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73063269109687172787568343 109594903664530759181352515)
            ·
              refine ⟨164392355496796138772028773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109594903664530759181352515 164392355496796138772028773)
              ·
                refine ⟨30823566655649276019755395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 164392355496796138772028773 30823566655649276019755395)
                ·
                  refine ⟨46235349983473914029633093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30823566655649276019755395 46235349983473914029633093)
                  ·
                    refine ⟨8669128121901358880556205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46235349983473914029633093 8669128121901358880556205)
                    ·
                      refine ⟨3250923045713009580208577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8669128121901358880556205 3250923045713009580208577)
                      ·
                        rfl

theorem cell23_6331150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_6331150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331150 prefixEnd_6331150 := by exact prefixLift 6331150
  have htrace : WordTrace (prefixWord ++ tailWord_6331150) baseStart_6331150 baseEnd_6331150 := by
    simpa [prefixWord, tailWord_6331150, baseEnd_6331150] using wordTrace_append hprefix tailTrace_6331150
  have hstable : (prefixWord ++ tailWord_6331150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331150).length < 2 ^ (prefixWord ++ tailWord_6331150).sum := by decide
  have hdescent : baseEnd_6331150 < baseStart_6331150 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331167 : List Nat := [1, 1, 2, 4, 2, 2, 3, 1, 2, 2, 3]
def baseStart_6331167 : Nat := 118140960795 + 6331167 * 2 ^ 59
def prefixEnd_6331167 : Nat := 4983230072969 + 3 ^ 40 * 6331167 * 2
def baseEnd_6331167 : Nat := 3250931774884136013695999

theorem tailTrace_6331167 : CollatzResearch.WordTrace tailWord_6331167 prefixEnd_6331167 3250931774884136013695999 := by
  unfold tailWord_6331167
  simp only [CollatzResearch.WordTrace]
  refine ⟨230916631054270711083831755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153944420702847140722554503 230916631054270711083831755)
  ·
    refine ⟨346374946581406066625747633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230916631054270711083831755 346374946581406066625747633)
    ·
      refine ⟨259781209936054549969310725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346374946581406066625747633 259781209936054549969310725)
      ·
        refine ⟨48708976863010228119245761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 259781209936054549969310725 48708976863010228119245761)
        ·
          refine ⟨36531732647257671089434321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48708976863010228119245761 36531732647257671089434321)
          ·
            refine ⟨27398799485443253317075741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36531732647257671089434321 27398799485443253317075741)
            ·
              refine ⟨10274549807041219993903403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27398799485443253317075741 10274549807041219993903403)
              ·
                refine ⟨15411824710561829990855105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10274549807041219993903403 15411824710561829990855105)
                ·
                  refine ⟨11558868532921372493141329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15411824710561829990855105 11558868532921372493141329)
                  ·
                    refine ⟨8669151399691029369855997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11558868532921372493141329 8669151399691029369855997)
                    ·
                      refine ⟨3250931774884136013695999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8669151399691029369855997 3250931774884136013695999)
                      ·
                        rfl

theorem cell23_6331167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_6331167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331167 prefixEnd_6331167 := by exact prefixLift 6331167
  have htrace : WordTrace (prefixWord ++ tailWord_6331167) baseStart_6331167 baseEnd_6331167 := by
    simpa [prefixWord, tailWord_6331167, baseEnd_6331167] using wordTrace_append hprefix tailTrace_6331167
  have hstable : (prefixWord ++ tailWord_6331167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331167).length < 2 ^ (prefixWord ++ tailWord_6331167).sum := by decide
  have hdescent : baseEnd_6331167 < baseStart_6331167 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331187 : List Nat := [1, 1, 1, 2, 6, 3, 1, 2, 6]
def baseStart_6331187 : Nat := 118140960795 + 6331187 * 2 ^ 59
def prefixEnd_6331187 : Nat := 4983230072969 + 3 ^ 40 * 6331187 * 2
def baseEnd_6331187 : Nat := 361215782721913992827323

theorem tailTrace_6331187 : CollatzResearch.WordTrace tailWord_6331187 prefixEnd_6331187 361215782721913992827323 := by
  unfold tailWord_6331187
  simp only [CollatzResearch.WordTrace]
  refine ⟨230917360514198254499559815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153944907009465502999706543 230917360514198254499559815)
  ·
    refine ⟨346376040771297381749339723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230917360514198254499559815 346376040771297381749339723)
    ·
      refine ⟨519564061156946072624009585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346376040771297381749339723 519564061156946072624009585)
      ·
        refine ⟨389673045867709554468007189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 519564061156946072624009585 389673045867709554468007189)
        ·
          refine ⟨18265924025048885365687837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 389673045867709554468007189 18265924025048885365687837)
          ·
            refine ⟨6849721509393332012132939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18265924025048885365687837 6849721509393332012132939)
            ·
              refine ⟨10274582264089998018199409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6849721509393332012132939 10274582264089998018199409)
              ·
                refine ⟨7705936698067498513649557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10274582264089998018199409 7705936698067498513649557)
                ·
                  refine ⟨361215782721913992827323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7705936698067498513649557 361215782721913992827323)
                  ·
                    rfl

theorem cell23_6331187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 2, 6].length) (baseStart_6331187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331187 prefixEnd_6331187 := by exact prefixLift 6331187
  have htrace : WordTrace (prefixWord ++ tailWord_6331187) baseStart_6331187 baseEnd_6331187 := by
    simpa [prefixWord, tailWord_6331187, baseEnd_6331187] using wordTrace_append hprefix tailTrace_6331187
  have hstable : (prefixWord ++ tailWord_6331187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331187).length < 2 ^ (prefixWord ++ tailWord_6331187).sum := by decide
  have hdescent : baseEnd_6331187 < baseStart_6331187 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331237 : List Nat := [1, 3, 1, 3, 1, 1, 4, 3, 1, 1, 4]
def baseStart_6331237 : Nat := 118140960795 + 6331237 * 2 ^ 59
def prefixEnd_6331237 : Nat := 4983230072969 + 3 ^ 40 * 6331237 * 2
def baseEnd_6331237 : Nat := 3250967718529950739820677

theorem tailTrace_6331237 : CollatzResearch.WordTrace tailWord_6331237 prefixEnd_6331237 3250967718529950739820677 := by
  unfold tailWord_6331237
  simp only [CollatzResearch.WordTrace]
  refine ⟨230919184164017113038879965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153946122776011408692586643 230919184164017113038879965)
  ·
    refine ⟨86594694061506417389579987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230919184164017113038879965 86594694061506417389579987)
    ·
      refine ⟨129892041092259626084369981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86594694061506417389579987 129892041092259626084369981)
      ·
        refine ⟨48709515409597359781638743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129892041092259626084369981 48709515409597359781638743)
        ·
          refine ⟨73064273114396039672458115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48709515409597359781638743 73064273114396039672458115)
          ·
            refine ⟨109596409671594059508687173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73064273114396039672458115 109596409671594059508687173)
            ·
              refine ⟨20549326813423886157878845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109596409671594059508687173 20549326813423886157878845)
              ·
                refine ⟨7705997555033957309204567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20549326813423886157878845 7705997555033957309204567)
                ·
                  refine ⟨11558996332550935963806851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7705997555033957309204567 11558996332550935963806851)
                  ·
                    refine ⟨17338494498826403945710277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11558996332550935963806851 17338494498826403945710277)
                    ·
                      refine ⟨3250967718529950739820677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17338494498826403945710277 3250967718529950739820677)
                      ·
                        rfl

theorem cell23_6331237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_6331237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331237 prefixEnd_6331237 := by exact prefixLift 6331237
  have htrace : WordTrace (prefixWord ++ tailWord_6331237) baseStart_6331237 baseEnd_6331237 := by
    simpa [prefixWord, tailWord_6331237, baseEnd_6331237] using wordTrace_append hprefix tailTrace_6331237
  have hstable : (prefixWord ++ tailWord_6331237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331237).length < 2 ^ (prefixWord ++ tailWord_6331237).sum := by decide
  have hdescent : baseEnd_6331237 < baseStart_6331237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331243 : List Nat := [1, 1, 1, 1, 2, 2, 15]
def baseStart_6331243 : Nat := 118140960795 + 6331243 * 2 ^ 59
def prefixEnd_6331243 : Nat := 4983230072969 + 3 ^ 40 * 6331243 * 2
def baseEnd_6331243 : Nat := 40135441968072564399329

theorem tailTrace_6331243 : CollatzResearch.WordTrace tailWord_6331243 prefixEnd_6331243 40135441968072564399329 := by
  unfold tailWord_6331243
  simp only [CollatzResearch.WordTrace]
  refine ⟨230919403001995376063598383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153946268667996917375732255 230919403001995376063598383)
  ·
    refine ⟨346379104502993064095397575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230919403001995376063598383 346379104502993064095397575)
    ·
      refine ⟨519568656754489596143096363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346379104502993064095397575 519568656754489596143096363)
      ·
        refine ⟨779352985131734394214644545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 519568656754489596143096363 779352985131734394214644545)
        ·
          refine ⟨584514738848800795660983409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 779352985131734394214644545 584514738848800795660983409)
          ·
            refine ⟨438386054136600596745737557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 584514738848800795660983409 438386054136600596745737557)
            ·
              refine ⟨40135441968072564399329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 15 438386054136600596745737557 40135441968072564399329)
              ·
                rfl

theorem cell23_6331243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 15].length) (baseStart_6331243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331243 prefixEnd_6331243 := by exact prefixLift 6331243
  have htrace : WordTrace (prefixWord ++ tailWord_6331243) baseStart_6331243 baseEnd_6331243 := by
    simpa [prefixWord, tailWord_6331243, baseEnd_6331243] using wordTrace_append hprefix tailTrace_6331243
  have hstable : (prefixWord ++ tailWord_6331243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331243).length < 2 ^ (prefixWord ++ tailWord_6331243).sum := by decide
  have hdescent : baseEnd_6331243 < baseStart_6331243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331250 : List Nat := [3, 2, 1, 2, 1, 1, 3, 2, 1, 1, 6]
def baseStart_6331250 : Nat := 118140960795 + 6331250 * 2 ^ 59
def prefixEnd_6331250 : Nat := 4983230072969 + 3 ^ 40 * 6331250 * 2
def baseEnd_6331250 : Nat := 3250974393778459188958117

theorem tailTrace_6331250 : CollatzResearch.WordTrace tailWord_6331250 prefixEnd_6331250 3250974393778459188958117 := by
  unfold tailWord_6331250
  simp only [CollatzResearch.WordTrace]
  refine ⟨57729914578242504064775801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153946438875313344172735469 57729914578242504064775801)
  ·
    refine ⟨43297435933681878048581851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57729914578242504064775801 43297435933681878048581851)
    ·
      refine ⟨64946153900522817072872777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43297435933681878048581851 64946153900522817072872777)
      ·
        refine ⟨48709615425392112804654583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64946153900522817072872777 48709615425392112804654583)
        ·
          refine ⟨73064423138088169206981875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48709615425392112804654583 73064423138088169206981875)
          ·
            refine ⟨109596634707132253810472813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73064423138088169206981875 109596634707132253810472813)
            ·
              refine ⟨41098738015174595178927305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109596634707132253810472813 41098738015174595178927305)
              ·
                refine ⟨30824053511380946384195479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41098738015174595178927305 30824053511380946384195479)
                ·
                  refine ⟨46236080267071419576293219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30824053511380946384195479 46236080267071419576293219)
                  ·
                    refine ⟨69354120400607129364439829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46236080267071419576293219 69354120400607129364439829)
                    ·
                      refine ⟨3250974393778459188958117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69354120400607129364439829 3250974393778459188958117)
                      ·
                        rfl

theorem cell23_6331250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_6331250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331250 prefixEnd_6331250 := by exact prefixLift 6331250
  have htrace : WordTrace (prefixWord ++ tailWord_6331250) baseStart_6331250 baseEnd_6331250 := by
    simpa [prefixWord, tailWord_6331250, baseEnd_6331250] using wordTrace_append hprefix tailTrace_6331250
  have hstable : (prefixWord ++ tailWord_6331250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331250).length < 2 ^ (prefixWord ++ tailWord_6331250).sum := by decide
  have hdescent : baseEnd_6331250 < baseStart_6331250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331274 : List Nat := [3, 1, 2, 4, 1, 2, 1, 1, 3, 2, 3]
def baseStart_6331274 : Nat := 118140960795 + 6331274 * 2 ^ 59
def prefixEnd_6331274 : Nat := 4983230072969 + 3 ^ 40 * 6331274 * 2
def baseEnd_6331274 : Nat := 3250986717314167095058007

theorem tailTrace_6331274 : CollatzResearch.WordTrace tailWord_6331274 prefixEnd_6331274 3250986717314167095058007 := by
  unfold tailWord_6331274
  simp only [CollatzResearch.WordTrace]
  refine ⟨57730133416220767089494219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153947022443255378905317917 57730133416220767089494219)
  ·
    refine ⟨86595200124331150634241329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57730133416220767089494219 86595200124331150634241329)
    ·
      refine ⟨64946400093248362975680997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86595200124331150634241329 64946400093248362975680997)
      ·
        refine ⟨12177450017484068057940187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64946400093248362975680997 12177450017484068057940187)
        ·
          refine ⟨18266175026226102086910281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12177450017484068057940187 18266175026226102086910281)
          ·
            refine ⟨13699631269669576565182711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18266175026226102086910281 13699631269669576565182711)
            ·
              refine ⟨20549446904504364847774067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13699631269669576565182711 20549446904504364847774067)
              ·
                refine ⟨30824170356756547271661101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20549446904504364847774067 30824170356756547271661101)
                ·
                  refine ⟨11559063883783705226872913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30824170356756547271661101 11559063883783705226872913)
                  ·
                    refine ⟨8669297912837778920154685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11559063883783705226872913 8669297912837778920154685)
                    ·
                      refine ⟨3250986717314167095058007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8669297912837778920154685 3250986717314167095058007)
                      ·
                        rfl

theorem cell23_6331274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_6331274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331274 prefixEnd_6331274 := by exact prefixLift 6331274
  have htrace : WordTrace (prefixWord ++ tailWord_6331274) baseStart_6331274 baseEnd_6331274 := by
    simpa [prefixWord, tailWord_6331274, baseEnd_6331274] using wordTrace_append hprefix tailTrace_6331274
  have hstable : (prefixWord ++ tailWord_6331274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331274).length < 2 ^ (prefixWord ++ tailWord_6331274).sum := by decide
  have hdescent : baseEnd_6331274 < baseStart_6331274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331287 : List Nat := [1, 1, 3, 3, 1, 2, 3, 2, 1, 3, 3]
def baseStart_6331287 : Nat := 118140960795 + 6331287 * 2 ^ 59
def prefixEnd_6331287 : Nat := 4983230072969 + 3 ^ 40 * 6331287 * 2
def baseEnd_6331287 : Nat := 3250993392562675544195447

theorem tailTrace_6331287 : CollatzResearch.WordTrace tailWord_6331287 prefixEnd_6331287 3250993392562675544195447 := by
  unfold tailWord_6331287
  simp only [CollatzResearch.WordTrace]
  refine ⟨230921007813835971578200115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153947338542557314385466743 230921007813835971578200115)
  ·
    refine ⟨346381511720753957367300173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230921007813835971578200115 346381511720753957367300173)
    ·
      refine ⟨129893066895282734012737565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 346381511720753957367300173 129893066895282734012737565)
      ·
        refine ⟨48709900085731025254776587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129893066895282734012737565 48709900085731025254776587)
        ·
          refine ⟨73064850128596537882164881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48709900085731025254776587 73064850128596537882164881)
          ·
            refine ⟨54798637596447403411623661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73064850128596537882164881 54798637596447403411623661)
            ·
              refine ⟨20549489098667776279358873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54798637596447403411623661 20549489098667776279358873)
              ·
                refine ⟨15412116824000832209519155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20549489098667776279358873 15412116824000832209519155)
                ·
                  refine ⟨23118175236001248314278733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15412116824000832209519155 23118175236001248314278733)
                  ·
                    refine ⟨8669315713500468117854525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23118175236001248314278733 8669315713500468117854525)
                    ·
                      refine ⟨3250993392562675544195447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8669315713500468117854525 3250993392562675544195447)
                      ·
                        rfl

theorem cell23_6331287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_6331287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331287 prefixEnd_6331287 := by exact prefixLift 6331287
  have htrace : WordTrace (prefixWord ++ tailWord_6331287) baseStart_6331287 baseEnd_6331287 := by
    simpa [prefixWord, tailWord_6331287, baseEnd_6331287] using wordTrace_append hprefix tailTrace_6331287
  have hstable : (prefixWord ++ tailWord_6331287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331287).length < 2 ^ (prefixWord ++ tailWord_6331287).sum := by decide
  have hdescent : baseEnd_6331287 < baseStart_6331287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331320 : List Nat := [2, 1, 2, 1, 2, 4, 1, 1, 1, 8]
def baseStart_6331320 : Nat := 118140960795 + 6331320 * 2 ^ 59
def prefixEnd_6331320 : Nat := 4983230072969 + 3 ^ 40 * 6331320 * 2
def baseEnd_6331320 : Nat := 1083670112474757971694265

theorem tailTrace_6331320 : CollatzResearch.WordTrace tailWord_6331320 prefixEnd_6331320 1083670112474757971694265 := by
  unfold tailWord_6331320
  simp only [CollatzResearch.WordTrace]
  refine ⟨115461105711358209107075707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153948140948477612142767609 115461105711358209107075707)
  ·
    refine ⟨173191658567037313660613561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115461105711358209107075707 173191658567037313660613561)
    ·
      refine ⟨129893743925277985245460171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173191658567037313660613561 129893743925277985245460171)
      ·
        refine ⟨194840615887916977868190257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129893743925277985245460171 194840615887916977868190257)
        ·
          refine ⟨146130461915937733401142693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194840615887916977868190257 146130461915937733401142693)
          ·
            refine ⟨27399461609238325012714255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146130461915937733401142693 27399461609238325012714255)
            ·
              refine ⟨41099192413857487519071383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27399461609238325012714255 41099192413857487519071383)
              ·
                refine ⟨61648788620786231278607075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41099192413857487519071383 61648788620786231278607075)
                ·
                  refine ⟨92473182931179346917910613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61648788620786231278607075 92473182931179346917910613)
                  ·
                    refine ⟨1083670112474757971694265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 92473182931179346917910613 1083670112474757971694265)
                    ·
                      rfl

theorem cell23_6331320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 1, 8].length) (baseStart_6331320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331320 prefixEnd_6331320 := by exact prefixLift 6331320
  have htrace : WordTrace (prefixWord ++ tailWord_6331320) baseStart_6331320 baseEnd_6331320 := by
    simpa [prefixWord, tailWord_6331320, baseEnd_6331320] using wordTrace_append hprefix tailTrace_6331320
  have hstable : (prefixWord ++ tailWord_6331320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331320).length < 2 ^ (prefixWord ++ tailWord_6331320).sum := by decide
  have hdescent : baseEnd_6331320 < baseStart_6331320 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331344 : List Nat := [2, 1, 1, 1, 1, 2, 3, 4, 4, 2, 2]
def baseStart_6331344 : Nat := 118140960795 + 6331344 * 2 ^ 59
def prefixEnd_6331344 : Nat := 4983230072969 + 3 ^ 40 * 6331344 * 2
def baseEnd_6331344 : Nat := 3251022660959981821182685

theorem tailTrace_6331344 : CollatzResearch.WordTrace tailWord_6331344 prefixEnd_6331344 3251022660959981821182685 := by
  unfold tailWord_6331344
  simp only [CollatzResearch.WordTrace]
  refine ⟨115461543387314735156512543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153948724516419646875350057 115461543387314735156512543)
  ·
    refine ⟨173192315080972102734768815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115461543387314735156512543 173192315080972102734768815)
    ·
      refine ⟨259788472621458154102153223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173192315080972102734768815 259788472621458154102153223)
      ·
        refine ⟨389682708932187231153229835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259788472621458154102153223 389682708932187231153229835)
        ·
          refine ⟨584524063398280846729844753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389682708932187231153229835 584524063398280846729844753)
          ·
            refine ⟨438393047548710635047383565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 584524063398280846729844753 438393047548710635047383565)
            ·
              refine ⟨164397392830766488142768837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 438393047548710635047383565 164397392830766488142768837)
              ·
                refine ⟨30824511155768716526769157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 164397392830766488142768837 30824511155768716526769157)
                ·
                  refine ⟨5779595841706634348769217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30824511155768716526769157 5779595841706634348769217)
                  ·
                    refine ⟨4334696881279975761576913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5779595841706634348769217 4334696881279975761576913)
                    ·
                      refine ⟨3251022660959981821182685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4334696881279975761576913 3251022660959981821182685)
                      ·
                        rfl

theorem cell23_6331344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 4, 2, 2].length) (baseStart_6331344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331344 prefixEnd_6331344 := by exact prefixLift 6331344
  have htrace : WordTrace (prefixWord ++ tailWord_6331344) baseStart_6331344 baseEnd_6331344 := by
    simpa [prefixWord, tailWord_6331344, baseEnd_6331344] using wordTrace_append hprefix tailTrace_6331344
  have hstable : (prefixWord ++ tailWord_6331344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331344).length < 2 ^ (prefixWord ++ tailWord_6331344).sum := by decide
  have hdescent : baseEnd_6331344 < baseStart_6331344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331348 : List Nat := [2, 4, 1, 2, 1, 2, 4, 1, 1, 3, 2]
def baseStart_6331348 : Nat := 118140960795 + 6331348 * 2 ^ 59
def prefixEnd_6331348 : Nat := 4983230072969 + 3 ^ 40 * 6331348 * 2
def baseEnd_6331348 : Nat := 3251024714882599805532667

theorem tailTrace_6331348 : CollatzResearch.WordTrace tailWord_6331348 prefixEnd_6331348 3251024714882599805532667 := by
  unfold tailWord_6331348
  simp only [CollatzResearch.WordTrace]
  refine ⟨115461616333307489498085349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153948821777743319330780465 115461616333307489498085349)
  ·
    refine ⟨21649053062495154280891003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115461616333307489498085349 21649053062495154280891003)
    ·
      refine ⟨32473579593742731421336505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21649053062495154280891003 32473579593742731421336505)
      ·
        refine ⟨24355184695307048566002379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32473579593742731421336505 24355184695307048566002379)
        ·
          refine ⟨36532777042960572849003569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24355184695307048566002379 36532777042960572849003569)
          ·
            refine ⟨27399582782220429636752677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36532777042960572849003569 27399582782220429636752677)
            ·
              refine ⟨5137421771666330556891127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27399582782220429636752677 5137421771666330556891127)
              ·
                refine ⟨7706132657499495835336691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5137421771666330556891127 7706132657499495835336691)
                ·
                  refine ⟨11559198986249243753005037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7706132657499495835336691 11559198986249243753005037)
                  ·
                    refine ⟨4334699619843466407376889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11559198986249243753005037 4334699619843466407376889)
                    ·
                      refine ⟨3251024714882599805532667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4334699619843466407376889 3251024714882599805532667)
                      ·
                        rfl

theorem cell23_6331348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_6331348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331348 prefixEnd_6331348 := by exact prefixLift 6331348
  have htrace : WordTrace (prefixWord ++ tailWord_6331348) baseStart_6331348 baseEnd_6331348 := by
    simpa [prefixWord, tailWord_6331348, baseEnd_6331348] using wordTrace_append hprefix tailTrace_6331348
  have hstable : (prefixWord ++ tailWord_6331348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331348).length < 2 ^ (prefixWord ++ tailWord_6331348).sum := by decide
  have hdescent : baseEnd_6331348 < baseStart_6331348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331367 : List Nat := [1, 1, 5, 2, 2, 1, 1, 3, 7]
def baseStart_6331367 : Nat := 118140960795 + 6331367 * 2 ^ 59
def prefixEnd_6331367 : Nat := 4983230072969 + 3 ^ 40 * 6331367 * 2
def baseEnd_6331367 : Nat := 361226052335003914577231

theorem tailTrace_6331367 : CollatzResearch.WordTrace tailWord_6331367 prefixEnd_6331367 361226052335003914577231 := by
  unfold tailWord_6331367
  simp only [CollatzResearch.WordTrace]
  refine ⟨230923925653546145241112355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153949283769030763494074903 230923925653546145241112355)
  ·
    refine ⟨346385888480319217861668533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230923925653546145241112355 346385888480319217861668533)
    ·
      refine ⟨32473677045029926674531425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 346385888480319217861668533 32473677045029926674531425)
      ·
        refine ⟨24355257783772445005898569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32473677045029926674531425 24355257783772445005898569)
        ·
          refine ⟨18266443337829333754423927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24355257783772445005898569 18266443337829333754423927)
          ·
            refine ⟨27399665006744000631635891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18266443337829333754423927 27399665006744000631635891)
            ·
              refine ⟨41099497510116000947453837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27399665006744000631635891 41099497510116000947453837)
              ·
                refine ⟨15412311566293500355295189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41099497510116000947453837 15412311566293500355295189)
                ·
                  refine ⟨361226052335003914577231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15412311566293500355295189 361226052335003914577231)
                  ·
                    rfl

theorem cell23_6331367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 7].length) (baseStart_6331367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331367 prefixEnd_6331367 := by exact prefixLift 6331367
  have htrace : WordTrace (prefixWord ++ tailWord_6331367) baseStart_6331367 baseEnd_6331367 := by
    simpa [prefixWord, tailWord_6331367, baseEnd_6331367] using wordTrace_append hprefix tailTrace_6331367
  have hstable : (prefixWord ++ tailWord_6331367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331367).length < 2 ^ (prefixWord ++ tailWord_6331367).sum := by decide
  have hdescent : baseEnd_6331367 < baseStart_6331367 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331397 : List Nat := [1, 3, 1, 1, 2, 3, 2, 3, 2, 5]
def baseStart_6331397 : Nat := 118140960795 + 6331397 * 2 ^ 59
def prefixEnd_6331397 : Nat := 4983230072969 + 3 ^ 40 * 6331397 * 2
def baseEnd_6331397 : Nat := 1083683291811556704606647

theorem tailTrace_6331397 : CollatzResearch.WordTrace tailWord_6331397 prefixEnd_6331397 1083683291811556704606647 := by
  unfold tailWord_6331397
  simp only [CollatzResearch.WordTrace]
  refine ⟨230925019843437460364704445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153950013228958306909802963 230925019843437460364704445)
  ·
    refine ⟨86596882441289047636764167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230925019843437460364704445 86596882441289047636764167)
    ·
      refine ⟨129895323661933571455146251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86596882441289047636764167 129895323661933571455146251)
      ·
        refine ⟨194842985492900357182719377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129895323661933571455146251 194842985492900357182719377)
        ·
          refine ⟨146132239119675267887039533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194842985492900357182719377 146132239119675267887039533)
          ·
            refine ⟨54799589669878225457639825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146132239119675267887039533 54799589669878225457639825)
            ·
              refine ⟨41099692252408669093229869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54799589669878225457639825 41099692252408669093229869)
              ·
                refine ⟨15412384594653250909961201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41099692252408669093229869 15412384594653250909961201)
                ·
                  refine ⟨11559288445989938182470901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15412384594653250909961201 11559288445989938182470901)
                  ·
                    refine ⟨1083683291811556704606647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11559288445989938182470901 1083683291811556704606647)
                    ·
                      rfl

theorem cell23_6331397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 2, 5].length) (baseStart_6331397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331397 prefixEnd_6331397 := by exact prefixLift 6331397
  have htrace : WordTrace (prefixWord ++ tailWord_6331397) baseStart_6331397 baseEnd_6331397 := by
    simpa [prefixWord, tailWord_6331397, baseEnd_6331397] using wordTrace_append hprefix tailTrace_6331397
  have hstable : (prefixWord ++ tailWord_6331397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331397).length < 2 ^ (prefixWord ++ tailWord_6331397).sum := by decide
  have hdescent : baseEnd_6331397 < baseStart_6331397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331417 : List Nat := [1, 2, 1, 2, 1, 1, 5, 1, 4, 1, 4]
def baseStart_6331417 : Nat := 118140960795 + 6331417 * 2 ^ 59
def prefixEnd_6331417 : Nat := 4983230072969 + 3 ^ 40 * 6331417 * 2
def baseEnd_6331417 : Nat := 3251060145047760035569849

theorem tailTrace_6331417 : CollatzResearch.WordTrace tailWord_6331417 prefixEnd_6331417 3251060145047760035569849 := by
  unfold tailWord_6331417
  simp only [CollatzResearch.WordTrace]
  refine ⟨230925749303365003780432505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153950499535576669186955003 230925749303365003780432505)
  ·
    refine ⟨173194311977523752835324379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230925749303365003780432505 173194311977523752835324379)
    ·
      refine ⟨259791467966285629252986569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173194311977523752835324379 259791467966285629252986569)
      ·
        refine ⟨194843600974714221939739927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259791467966285629252986569 194843600974714221939739927)
        ·
          refine ⟨292265401462071332909609891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194843600974714221939739927 292265401462071332909609891)
          ·
            refine ⟨438398102193106999364414837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292265401462071332909609891 438398102193106999364414837)
            ·
              refine ⟨41099822080603781190413891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 438398102193106999364414837 41099822080603781190413891)
              ·
                refine ⟨61649733120905671785620837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41099822080603781190413891 61649733120905671785620837)
                ·
                  refine ⟨11559324960169813459803907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61649733120905671785620837 11559324960169813459803907)
                  ·
                    refine ⟨17338987440254720189705861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11559324960169813459803907 17338987440254720189705861)
                    ·
                      refine ⟨3251060145047760035569849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17338987440254720189705861 3251060145047760035569849)
                      ·
                        rfl

theorem cell23_6331417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 4, 1, 4].length) (baseStart_6331417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331417 prefixEnd_6331417 := by exact prefixLift 6331417
  have htrace : WordTrace (prefixWord ++ tailWord_6331417) baseStart_6331417 baseEnd_6331417 := by
    simpa [prefixWord, tailWord_6331417, baseEnd_6331417] using wordTrace_append hprefix tailTrace_6331417
  have hstable : (prefixWord ++ tailWord_6331417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331417).length < 2 ^ (prefixWord ++ tailWord_6331417).sum := by decide
  have hdescent : baseEnd_6331417 < baseStart_6331417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331474 : List Nat := [3, 2, 2, 1, 3, 1, 1, 4, 6]
def baseStart_6331474 : Nat := 118140960795 + 6331474 * 2 ^ 59
def prefixEnd_6331474 : Nat := 4983230072969 + 3 ^ 40 * 6331474 * 2
def baseEnd_6331474 : Nat := 361232157049451812506343

theorem tailTrace_6331474 : CollatzResearch.WordTrace tailWord_6331474 prefixEnd_6331474 361232157049451812506343 := by
  unfold tailWord_6331474
  simp only [CollatzResearch.WordTrace]
  refine ⟨57731957066039625628814369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153951885509439001676838317 57731957066039625628814369)
  ·
    refine ⟨43298967799529719221610777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57731957066039625628814369 43298967799529719221610777)
    ·
      refine ⟨32474225849647289416208083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43298967799529719221610777 32474225849647289416208083)
      ·
        refine ⟨48711338774470934124312125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32474225849647289416208083 48711338774470934124312125)
        ·
          refine ⟨18266752040426600296617047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48711338774470934124312125 18266752040426600296617047)
          ·
            refine ⟨27400128060639900444925571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18266752040426600296617047 27400128060639900444925571)
            ·
              refine ⟨41100192090959850667388357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27400128060639900444925571 41100192090959850667388357)
              ·
                refine ⟨7706286017054972000135317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41100192090959850667388357 7706286017054972000135317)
                ·
                  refine ⟨361232157049451812506343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7706286017054972000135317 361232157049451812506343)
                  ·
                    rfl

theorem cell23_6331474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4, 6].length) (baseStart_6331474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331474 prefixEnd_6331474 := by exact prefixLift 6331474
  have htrace : WordTrace (prefixWord ++ tailWord_6331474) baseStart_6331474 baseEnd_6331474 := by
    simpa [prefixWord, tailWord_6331474, baseEnd_6331474] using wordTrace_append hprefix tailTrace_6331474
  have hstable : (prefixWord ++ tailWord_6331474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331474).length < 2 ^ (prefixWord ++ tailWord_6331474).sum := by decide
  have hdescent : baseEnd_6331474 < baseStart_6331474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331477 : List Nat := [1, 3, 2, 2, 1, 2, 2, 1, 1, 2, 6]
def baseStart_6331477 : Nat := 118140960795 + 6331477 * 2 ^ 59
def prefixEnd_6331477 : Nat := 4983230072969 + 3 ^ 40 * 6331477 * 2
def baseEnd_6331477 : Nat := 3251090953887029800819573

theorem tailTrace_6331477 : CollatzResearch.WordTrace tailWord_6331477 prefixEnd_6331477 3251090953887029800819573 := by
  unfold tailWord_6331477
  simp only [CollatzResearch.WordTrace]
  refine ⟨230927937683147634027616685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153951958455431756018411123 230927937683147634027616685)
  ·
    refine ⟨86597976631180362760356257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230927937683147634027616685 86597976631180362760356257)
    ·
      refine ⟨64948482473385272070267193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86597976631180362760356257 64948482473385272070267193)
      ·
        refine ⟨48711361855038954052700395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64948482473385272070267193 48711361855038954052700395)
        ·
          refine ⟨73067042782558431079050593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48711361855038954052700395 73067042782558431079050593)
          ·
            refine ⟨54800282086918823309287945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73067042782558431079050593 54800282086918823309287945)
            ·
              refine ⟨41100211565189117481965959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54800282086918823309287945 41100211565189117481965959)
              ·
                refine ⟨61650317347783676222948939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41100211565189117481965959 61650317347783676222948939)
                ·
                  refine ⟨92475476021675514334423409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61650317347783676222948939 92475476021675514334423409)
                  ·
                    refine ⟨69356607016256635750817557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 92475476021675514334423409 69356607016256635750817557)
                    ·
                      refine ⟨3251090953887029800819573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69356607016256635750817557 3251090953887029800819573)
                      ·
                        rfl

theorem cell23_6331477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_6331477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331477 prefixEnd_6331477 := by exact prefixLift 6331477
  have htrace : WordTrace (prefixWord ++ tailWord_6331477) baseStart_6331477 baseEnd_6331477 := by
    simpa [prefixWord, tailWord_6331477, baseEnd_6331477] using wordTrace_append hprefix tailTrace_6331477
  have hstable : (prefixWord ++ tailWord_6331477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331477).length < 2 ^ (prefixWord ++ tailWord_6331477).sum := by decide
  have hdescent : baseEnd_6331477 < baseStart_6331477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331487 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 5, 5]
def baseStart_6331487 : Nat := 118140960795 + 6331487 * 2 ^ 59
def prefixEnd_6331487 : Nat := 4983230072969 + 3 ^ 40 * 6331487 * 2
def baseEnd_6331487 : Nat := 1083698696231191587231509

theorem tailTrace_6331487 : CollatzResearch.WordTrace tailWord_6331487 prefixEnd_6331487 1083698696231191587231509 := by
  unfold tailWord_6331487
  simp only [CollatzResearch.WordTrace]
  refine ⟨230928302413111405735480715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153952201608740937156987143 230928302413111405735480715)
  ·
    refine ⟨346392453619667108603221073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230928302413111405735480715 346392453619667108603221073)
    ·
      refine ⟨259794340214750331452415805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346392453619667108603221073 259794340214750331452415805)
      ·
        refine ⟨97422877580531374294655927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259794340214750331452415805 97422877580531374294655927)
        ·
          refine ⟨146134316370797061441983891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97422877580531374294655927 146134316370797061441983891)
          ·
            refine ⟨219201474556195592162975837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146134316370797061441983891 219201474556195592162975837)
            ·
              refine ⟨82200552958573347061115939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 219201474556195592162975837 82200552958573347061115939)
              ·
                refine ⟨123300829437860020591673909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82200552958573347061115939 123300829437860020591673909)
                ·
                  refine ⟨11559452759799376930469429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 123300829437860020591673909 11559452759799376930469429)
                  ·
                    refine ⟨1083698696231191587231509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11559452759799376930469429 1083698696231191587231509)
                    ·
                      rfl

theorem cell23_6331487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 5, 5].length) (baseStart_6331487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331487 prefixEnd_6331487 := by exact prefixLift 6331487
  have htrace : WordTrace (prefixWord ++ tailWord_6331487) baseStart_6331487 baseEnd_6331487 := by
    simpa [prefixWord, tailWord_6331487, baseEnd_6331487] using wordTrace_append hprefix tailTrace_6331487
  have hstable : (prefixWord ++ tailWord_6331487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331487).length < 2 ^ (prefixWord ++ tailWord_6331487).sum := by decide
  have hdescent : baseEnd_6331487 < baseStart_6331487 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331501 : List Nat := [1, 5, 1, 1, 2, 2, 1, 1, 5, 1, 3]
def baseStart_6331501 : Nat := 118140960795 + 6331501 * 2 ^ 59
def prefixEnd_6331501 : Nat := 4983230072969 + 3 ^ 40 * 6331501 * 2
def baseEnd_6331501 : Nat := 3251103277422737706919463

theorem tailTrace_6331501 : CollatzResearch.WordTrace tailWord_6331501 prefixEnd_6331501 3251103277422737706919463 := by
  unfold tailWord_6331501
  simp only [CollatzResearch.WordTrace]
  refine ⟨230928813035060686126490357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153952542023373790750993571 230928813035060686126490357)
  ·
    refine ⟨21649576222036939324358471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 230928813035060686126490357 21649576222036939324358471)
    ·
      refine ⟨32474364333055408986537707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21649576222036939324358471 32474364333055408986537707)
      ·
        refine ⟨48711546499583113479806561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32474364333055408986537707 48711546499583113479806561)
        ·
          refine ⟨36533659874687335109854921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48711546499583113479806561 36533659874687335109854921)
          ·
            refine ⟨27400244906015501332391191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36533659874687335109854921 27400244906015501332391191)
            ·
              refine ⟨41100367359023251998586787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27400244906015501332391191 41100367359023251998586787)
              ·
                refine ⟨61650551038534877997880181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41100367359023251998586787 61650551038534877997880181)
                ·
                  refine ⟨5779739159862644812301267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61650551038534877997880181 5779739159862644812301267)
                  ·
                    refine ⟨8669608739793967218451901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5779739159862644812301267 8669608739793967218451901)
                    ·
                      refine ⟨3251103277422737706919463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8669608739793967218451901 3251103277422737706919463)
                      ·
                        rfl

theorem cell23_6331501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_6331501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331501 prefixEnd_6331501 := by exact prefixLift 6331501
  have htrace : WordTrace (prefixWord ++ tailWord_6331501) baseStart_6331501 baseEnd_6331501 := by
    simpa [prefixWord, tailWord_6331501, baseEnd_6331501] using wordTrace_append hprefix tailTrace_6331501
  have hstable : (prefixWord ++ tailWord_6331501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331501).length < 2 ^ (prefixWord ++ tailWord_6331501).sum := by decide
  have hdescent : baseEnd_6331501 < baseStart_6331501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331504 : List Nat := [2, 1, 1, 1, 5, 1, 2, 4, 1, 5]
def baseStart_6331504 : Nat := 118140960795 + 6331504 * 2 ^ 59
def prefixEnd_6331504 : Nat := 4983230072969 + 3 ^ 40 * 6331504 * 2
def baseEnd_6331504 : Nat := 1083701605954900398393983

theorem tailTrace_6331504 : CollatzResearch.WordTrace tailWord_6331504 prefixEnd_6331504 1083701605954900398393983 := by
  unfold tailWord_6331504
  simp only [CollatzResearch.WordTrace]
  refine ⟨115464461227024908819424783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153952614969366545092566377 115464461227024908819424783)
  ·
    refine ⟨173196691840537363229137175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115464461227024908819424783 173196691840537363229137175)
    ·
      refine ⟨259795037760806044843705763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173196691840537363229137175 259795037760806044843705763)
      ·
        refine ⟨389692556641209067265558645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259795037760806044843705763 389692556641209067265558645)
        ·
          refine ⟨36533677185113350056146123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 389692556641209067265558645 36533677185113350056146123)
          ·
            refine ⟨54800515777670025084219185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36533677185113350056146123 54800515777670025084219185)
            ·
              refine ⟨41100386833252518813164389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54800515777670025084219185 41100386833252518813164389)
              ·
                refine ⟨7706322531234847277468323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41100386833252518813164389 7706322531234847277468323)
                ·
                  refine ⟨11559483796852270916202485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7706322531234847277468323 11559483796852270916202485)
                  ·
                    refine ⟨1083701605954900398393983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11559483796852270916202485 1083701605954900398393983)
                    ·
                      rfl

theorem cell23_6331504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 4, 1, 5].length) (baseStart_6331504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331504 prefixEnd_6331504 := by exact prefixLift 6331504
  have htrace : WordTrace (prefixWord ++ tailWord_6331504) baseStart_6331504 baseEnd_6331504 := by
    simpa [prefixWord, tailWord_6331504, baseEnd_6331504] using wordTrace_append hprefix tailTrace_6331504
  have hstable : (prefixWord ++ tailWord_6331504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331504).length < 2 ^ (prefixWord ++ tailWord_6331504).sum := by decide
  have hdescent : baseEnd_6331504 < baseStart_6331504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331521 : List Nat := [1, 2, 4, 2, 2, 2, 1, 3, 1, 5]
def baseStart_6331521 : Nat := 118140960795 + 6331521 * 2 ^ 59
def prefixEnd_6331521 : Nat := 4983230072969 + 3 ^ 40 * 6331521 * 2
def baseEnd_6331521 : Nat := 1083704515678609209556457

theorem tailTrace_6331521 : CollatzResearch.WordTrace tailWord_6331521 prefixEnd_6331521 1083704515678609209556457 := by
  unfold tailWord_6331521
  simp only [CollatzResearch.WordTrace]
  refine ⟨230929542494988229542218417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153953028329992153028145611 230929542494988229542218417)
  ·
    refine ⟨173197156871241172156663813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230929542494988229542218417 173197156871241172156663813)
    ·
      refine ⟨32474466913357719779374465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173197156871241172156663813 32474466913357719779374465)
      ·
        refine ⟨24355850185018289834530849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32474466913357719779374465 24355850185018289834530849)
        ·
          refine ⟨18266887638763717375898137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24355850185018289834530849 18266887638763717375898137)
          ·
            refine ⟨13700165729072788031923603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18266887638763717375898137 13700165729072788031923603)
            ·
              refine ⟨20550248593609182047885405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13700165729072788031923603 20550248593609182047885405)
              ·
                refine ⟨7706343222603443267957027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20550248593609182047885405 7706343222603443267957027)
                ·
                  refine ⟨11559514833905164901935541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7706343222603443267957027 11559514833905164901935541)
                  ·
                    refine ⟨1083704515678609209556457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11559514833905164901935541 1083704515678609209556457)
                    ·
                      rfl

theorem cell23_6331521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_6331521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331521 prefixEnd_6331521 := by exact prefixLift 6331521
  have htrace : WordTrace (prefixWord ++ tailWord_6331521) baseStart_6331521 baseEnd_6331521 := by
    simpa [prefixWord, tailWord_6331521, baseEnd_6331521] using wordTrace_append hprefix tailTrace_6331521
  have hstable : (prefixWord ++ tailWord_6331521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331521).length < 2 ^ (prefixWord ++ tailWord_6331521).sum := by decide
  have hdescent : baseEnd_6331521 < baseStart_6331521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331537 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 4]
def baseStart_6331537 : Nat := 118140960795 + 6331537 * 2 ^ 59
def prefixEnd_6331537 : Nat := 4983230072969 + 3 ^ 40 * 6331537 * 2
def baseEnd_6331537 : Nat := 3251121762726299566069297

theorem tailTrace_6331537 : CollatzResearch.WordTrace tailWord_6331537 prefixEnd_6331537 3251121762726299566069297 := by
  unfold tailWord_6331537
  simp only [CollatzResearch.WordTrace]
  refine ⟨230930126062930264274800865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153953417375286842849867243 230930126062930264274800865)
  ·
    refine ⟨173197594547197698206100649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230930126062930264274800865 173197594547197698206100649)
    ·
      refine ⟨129898195910398273654575487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173197594547197698206100649 129898195910398273654575487)
      ·
        refine ⟨194847293865597410481863231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129898195910398273654575487 194847293865597410481863231)
        ·
          refine ⟨292270940798396115722794847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194847293865597410481863231 292270940798396115722794847)
          ·
            refine ⟨438406411197594173584192271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292270940798396115722794847 438406411197594173584192271)
            ·
              refine ⟨657609616796391260376288407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 438406411197594173584192271 657609616796391260376288407)
              ·
                refine ⟨986414425194586890564432611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 657609616796391260376288407 986414425194586890564432611)
                ·
                  refine ⟨1479621637791880335846648917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 986414425194586890564432611 1479621637791880335846648917)
                  ·
                    refine ⟨17339316067873597685702917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1479621637791880335846648917 17339316067873597685702917)
                    ·
                      refine ⟨3251121762726299566069297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17339316067873597685702917 3251121762726299566069297)
                      ·
                        rfl

theorem cell23_6331537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 4].length) (baseStart_6331537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331537 prefixEnd_6331537 := by exact prefixLift 6331537
  have htrace : WordTrace (prefixWord ++ tailWord_6331537) baseStart_6331537 baseEnd_6331537 := by
    simpa [prefixWord, tailWord_6331537, baseEnd_6331537] using wordTrace_append hprefix tailTrace_6331537
  have hstable : (prefixWord ++ tailWord_6331537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331537).length < 2 ^ (prefixWord ++ tailWord_6331537).sum := by decide
  have hdescent : baseEnd_6331537 < baseStart_6331537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331544 : List Nat := [2, 1, 2, 4, 2, 1, 1, 1, 3, 1, 5]
def baseStart_6331544 : Nat := 118140960795 + 6331544 * 2 ^ 59
def prefixEnd_6331544 : Nat := 4983230072969 + 3 ^ 40 * 6331544 * 2
def baseEnd_6331544 : Nat := 3251125357090881038681765

theorem tailTrace_6331544 : CollatzResearch.WordTrace tailWord_6331544 prefixEnd_6331544 3251125357090881038681765 := by
  unfold tailWord_6331544
  simp only [CollatzResearch.WordTrace]
  refine ⟨115465190686952452235152843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153953587582603269646870457 115465190686952452235152843)
  ·
    refine ⟨173197786030428678352729265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115465190686952452235152843 173197786030428678352729265)
    ·
      refine ⟨129898339522821508764546949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173197786030428678352729265 129898339522821508764546949)
      ·
        refine ⟨24355938660529032893352553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129898339522821508764546949 24355938660529032893352553)
        ·
          refine ⟨18266953995396774670014415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24355938660529032893352553 18266953995396774670014415)
          ·
            refine ⟨27400430993095162005021623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18266953995396774670014415 27400430993095162005021623)
            ·
              refine ⟨41100646489642743007532435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27400430993095162005021623 41100646489642743007532435)
              ·
                refine ⟨61650969734464114511298653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41100646489642743007532435 61650969734464114511298653)
                ·
                  refine ⟨23119113650424042941736995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61650969734464114511298653 23119113650424042941736995)
                  ·
                    refine ⟨34678670475636064412605493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23119113650424042941736995 34678670475636064412605493)
                    ·
                      refine ⟨3251125357090881038681765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34678670475636064412605493 3251125357090881038681765)
                      ·
                        rfl

theorem cell23_6331544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_6331544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331544 prefixEnd_6331544 := by exact prefixLift 6331544
  have htrace : WordTrace (prefixWord ++ tailWord_6331544) baseStart_6331544 baseEnd_6331544 := by
    simpa [prefixWord, tailWord_6331544, baseEnd_6331544] using wordTrace_append hprefix tailTrace_6331544
  have hstable : (prefixWord ++ tailWord_6331544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331544).length < 2 ^ (prefixWord ++ tailWord_6331544).sum := by decide
  have hdescent : baseEnd_6331544 < baseStart_6331544 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331586 : List Nat := [3, 5, 1, 1, 2, 1, 3, 2, 1, 1, 3]
def baseStart_6331586 : Nat := 118140960795 + 6331586 * 2 ^ 59
def prefixEnd_6331586 : Nat := 4983230072969 + 3 ^ 40 * 6331586 * 2
def baseEnd_6331586 : Nat := 3251146923278369874356573

theorem tailTrace_6331586 : CollatzResearch.WordTrace tailWord_6331586 prefixEnd_6331586 3251146923278369874356573 := by
  unfold tailWord_6331586
  simp only [CollatzResearch.WordTrace]
  refine ⟨57732978309938186410833653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153954608826501830428889741 57732978309938186410833653)
  ·
    refine ⟨5412466716556704976015655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57732978309938186410833653 5412466716556704976015655)
    ·
      refine ⟨8118700074835057464023483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5412466716556704976015655 8118700074835057464023483)
      ·
        refine ⟨12178050112252586196035225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8118700074835057464023483 12178050112252586196035225)
        ·
          refine ⟨9133537584189439647026419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12178050112252586196035225 9133537584189439647026419)
          ·
            refine ⟨13700306376284159470539629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9133537584189439647026419 13700306376284159470539629)
            ·
              refine ⟨5137614891106559801452361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13700306376284159470539629 5137614891106559801452361)
              ·
                refine ⟨3853211168329919851089271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5137614891106559801452361 3853211168329919851089271)
                ·
                  refine ⟨5779816752494879776633907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3853211168329919851089271 5779816752494879776633907)
                  ·
                    refine ⟨8669725128742319664950861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5779816752494879776633907 8669725128742319664950861)
                    ·
                      refine ⟨3251146923278369874356573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8669725128742319664950861 3251146923278369874356573)
                      ·
                        rfl

theorem cell23_6331586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_6331586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331586 prefixEnd_6331586 := by exact prefixLift 6331586
  have htrace : WordTrace (prefixWord ++ tailWord_6331586) baseStart_6331586 baseEnd_6331586 := by
    simpa [prefixWord, tailWord_6331586, baseEnd_6331586] using wordTrace_append hprefix tailTrace_6331586
  have hstable : (prefixWord ++ tailWord_6331586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331586).length < 2 ^ (prefixWord ++ tailWord_6331586).sum := by decide
  have hdescent : baseEnd_6331586 < baseStart_6331586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331601 : List Nat := [1, 2, 2, 1, 2, 2, 1, 4, 3, 3, 2]
def baseStart_6331601 : Nat := 118140960795 + 6331601 * 2 ^ 59
def prefixEnd_6331601 : Nat := 4983230072969 + 3 ^ 40 * 6331601 * 2
def baseEnd_6331601 : Nat := 3251154625488187315669003

theorem tailTrace_6331601 : CollatzResearch.WordTrace tailWord_6331601 prefixEnd_6331601 3251154625488187315669003 := by
  unfold tailWord_6331601
  simp only [CollatzResearch.WordTrace]
  refine ⟨230932460334698403205130657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153954973556465602136753771 230932460334698403205130657)
  ·
    refine ⟨173199345251023802403847993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230932460334698403205130657 173199345251023802403847993)
    ·
      refine ⟨129899508938267851802885995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173199345251023802403847993 129899508938267851802885995)
      ·
        refine ⟨194849263407401777704328993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129899508938267851802885995 194849263407401777704328993)
        ·
          refine ⟨146136947555551333278246745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194849263407401777704328993 146136947555551333278246745)
          ·
            refine ⟨109602710666663499958685059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146136947555551333278246745 109602710666663499958685059)
            ·
              refine ⟨164404065999995249938027589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109602710666663499958685059 164404065999995249938027589)
              ·
                refine ⟨30825762374999109363380173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 164404065999995249938027589 30825762374999109363380173)
                ·
                  refine ⟨11559660890624666011267565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30825762374999109363380173 11559660890624666011267565)
                  ·
                    refine ⟨4334872833984249754225337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11559660890624666011267565 4334872833984249754225337)
                    ·
                      refine ⟨3251154625488187315669003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4334872833984249754225337 3251154625488187315669003)
                      ·
                        rfl

theorem cell23_6331601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 3, 3, 2].length) (baseStart_6331601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331601 prefixEnd_6331601 := by exact prefixLift 6331601
  have htrace : WordTrace (prefixWord ++ tailWord_6331601) baseStart_6331601 baseEnd_6331601 := by
    simpa [prefixWord, tailWord_6331601, baseEnd_6331601] using wordTrace_append hprefix tailTrace_6331601
  have hstable : (prefixWord ++ tailWord_6331601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331601).length < 2 ^ (prefixWord ++ tailWord_6331601).sum := by decide
  have hdescent : baseEnd_6331601 < baseStart_6331601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331635 : List Nat := [1, 1, 1, 2, 2, 6, 3, 1, 1, 3, 2]
def baseStart_6331635 : Nat := 118140960795 + 6331635 * 2 ^ 59
def prefixEnd_6331635 : Nat := 4983230072969 + 3 ^ 40 * 6331635 * 2
def baseEnd_6331635 : Nat := 3251172083830440182643847

theorem tailTrace_6331635 : CollatzResearch.WordTrace tailWord_6331635 prefixEnd_6331635 3251172083830440182643847 := by
  unfold tailWord_6331635
  simp only [CollatzResearch.WordTrace]
  refine ⟨230933700416575227011868359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153955800277716818007912239 230933700416575227011868359)
  ·
    refine ⟨346400550624862840517802539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230933700416575227011868359 346400550624862840517802539)
    ·
      refine ⟨519600825937294260776703809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346400550624862840517802539 519600825937294260776703809)
      ·
        refine ⟨389700619452970695582527857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 519600825937294260776703809 389700619452970695582527857)
        ·
          refine ⟨292275464589728021686895893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 389700619452970695582527857 292275464589728021686895893)
          ·
            refine ⟨13700412402643501016573245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 292275464589728021686895893 13700412402643501016573245)
            ·
              refine ⟨5137654650991312881214967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13700412402643501016573245 5137654650991312881214967)
              ·
                refine ⟨7706481976486969321822451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5137654650991312881214967 7706481976486969321822451)
                ·
                  refine ⟨11559722964730453982733677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7706481976486969321822451 11559722964730453982733677)
                  ·
                    refine ⟨4334896111773920243525129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11559722964730453982733677 4334896111773920243525129)
                    ·
                      refine ⟨3251172083830440182643847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4334896111773920243525129 3251172083830440182643847)
                      ·
                        rfl

theorem cell23_6331635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 1, 1, 3, 2].length) (baseStart_6331635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331635 prefixEnd_6331635 := by exact prefixLift 6331635
  have htrace : WordTrace (prefixWord ++ tailWord_6331635) baseStart_6331635 baseEnd_6331635 := by
    simpa [prefixWord, tailWord_6331635, baseEnd_6331635] using wordTrace_append hprefix tailTrace_6331635
  have hstable : (prefixWord ++ tailWord_6331635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331635).length < 2 ^ (prefixWord ++ tailWord_6331635).sum := by decide
  have hdescent : baseEnd_6331635 < baseStart_6331635 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331688 : List Nat := [2, 1, 5, 1, 2, 1, 1, 5, 5]
def baseStart_6331688 : Nat := 118140960795 + 6331688 * 2 ^ 59
def prefixEnd_6331688 : Nat := 4983230072969 + 3 ^ 40 * 6331688 * 2
def baseEnd_6331688 : Nat := 361244366478347608364567

theorem tailTrace_6331688 : CollatzResearch.WordTrace tailWord_6331688 prefixEnd_6331688 361244366478347608364567 := by
  unfold tailWord_6331688
  simp only [CollatzResearch.WordTrace]
  refine ⟨115467816742691608531773859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153957088990255478042365145 115467816742691608531773859)
  ·
    refine ⟨173201725114037412797660789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115467816742691608531773859 173201725114037412797660789)
    ·
      refine ⟨16237661729441007449780699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 173201725114037412797660789 16237661729441007449780699)
      ·
        refine ⟨24356492594161511174671049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16237661729441007449780699 24356492594161511174671049)
        ·
          refine ⟨18267369445621133381003287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24356492594161511174671049 18267369445621133381003287)
          ·
            refine ⟨27401054168431700071504931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18267369445621133381003287 27401054168431700071504931)
            ·
              refine ⟨41101581252647550107257397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27401054168431700071504931 41101581252647550107257397)
              ·
                refine ⟨3853273242435707822555381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41101581252647550107257397 3853273242435707822555381)
                ·
                  refine ⟨361244366478347608364567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3853273242435707822555381 361244366478347608364567)
                  ·
                    rfl

theorem cell23_6331688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 5, 5].length) (baseStart_6331688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331688 prefixEnd_6331688 := by exact prefixLift 6331688
  have htrace : WordTrace (prefixWord ++ tailWord_6331688) baseStart_6331688 baseEnd_6331688 := by
    simpa [prefixWord, tailWord_6331688, baseEnd_6331688] using wordTrace_append hprefix tailTrace_6331688
  have hstable : (prefixWord ++ tailWord_6331688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331688).length < 2 ^ (prefixWord ++ tailWord_6331688).sum := by decide
  have hdescent : baseEnd_6331688 < baseStart_6331688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331731 : List Nat := [1, 1, 1, 2, 1, 1, 5, 4, 3, 4]
def baseStart_6331731 : Nat := 118140960795 + 6331731 * 2 ^ 59
def prefixEnd_6331731 : Nat := 4983230072969 + 3 ^ 40 * 6331731 * 2
def baseEnd_6331731 : Nat := 1083740459324423935681135

theorem tailTrace_6331731 : CollatzResearch.WordTrace tailWord_6331731 prefixEnd_6331731 1083740459324423935681135 := by
  unfold tailWord_6331731
  simp only [CollatzResearch.WordTrace]
  refine ⟨230937201824227435407363047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153958134549484956938242031 230937201824227435407363047)
  ·
    refine ⟨346405802736341153111044571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230937201824227435407363047 346405802736341153111044571)
    ·
      refine ⟨519608704104511729666566857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346405802736341153111044571 519608704104511729666566857)
      ·
        refine ⟨389706528078383797249925143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 519608704104511729666566857 389706528078383797249925143)
        ·
          refine ⟨584559792117575695874887715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389706528078383797249925143 584559792117575695874887715)
          ·
            refine ⟨876839688176363543812331573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 584559792117575695874887715 876839688176363543812331573)
            ·
              refine ⟨82203720766534082232406085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 876839688176363543812331573 82203720766534082232406085)
              ·
                refine ⟨15413197643725140418576141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82203720766534082232406085 15413197643725140418576141)
                ·
                  refine ⟨5779949116396927656966053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15413197643725140418576141 5779949116396927656966053)
                  ·
                    refine ⟨1083740459324423935681135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5779949116396927656966053 1083740459324423935681135)
                    ·
                      rfl

theorem cell23_6331731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 3, 4].length) (baseStart_6331731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331731 prefixEnd_6331731 := by exact prefixLift 6331731
  have htrace : WordTrace (prefixWord ++ tailWord_6331731) baseStart_6331731 baseEnd_6331731 := by
    simpa [prefixWord, tailWord_6331731, baseEnd_6331731] using wordTrace_append hprefix tailTrace_6331731
  have hstable : (prefixWord ++ tailWord_6331731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331731).length < 2 ^ (prefixWord ++ tailWord_6331731).sum := by decide
  have hdescent : baseEnd_6331731 < baseStart_6331731 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331788 : List Nat := [2, 2, 1, 2, 1, 3, 2, 1, 5, 1, 3]
def baseStart_6331788 : Nat := 118140960795 + 6331788 * 2 ^ 59
def prefixEnd_6331788 : Nat := 4983230072969 + 3 ^ 40 * 6331788 * 2
def baseEnd_6331788 : Nat := 3251250646370578084030643

theorem tailTrace_6331788 : CollatzResearch.WordTrace tailWord_6331788 prefixEnd_6331788 3251250646370578084030643 := by
  unfold tailWord_6331788
  simp only [CollatzResearch.WordTrace]
  refine ⟨115469640392510467071094009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153959520523347289428125345 115469640392510467071094009)
  ·
    refine ⟨86602230294382850303320507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115469640392510467071094009 86602230294382850303320507)
    ·
      refine ⟨129903345441574275454980761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86602230294382850303320507 129903345441574275454980761)
      ·
        refine ⟨97427509081180706591235571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129903345441574275454980761 97427509081180706591235571)
        ·
          refine ⟨146141263621771059886853357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97427509081180706591235571 146141263621771059886853357)
          ·
            refine ⟨54802973858164147457570009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146141263621771059886853357 54802973858164147457570009)
            ·
              refine ⟨41102230393623110593177507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54802973858164147457570009 41102230393623110593177507)
              ·
                refine ⟨61653345590434665889766261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41102230393623110593177507 61653345590434665889766261)
                ·
                  refine ⟨5780001149103249927165587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61653345590434665889766261 5780001149103249927165587)
                  ·
                    refine ⟨8670001723654874890748381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5780001149103249927165587 8670001723654874890748381)
                    ·
                      refine ⟨3251250646370578084030643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8670001723654874890748381 3251250646370578084030643)
                      ·
                        rfl

theorem cell23_6331788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 5, 1, 3].length) (baseStart_6331788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331788 prefixEnd_6331788 := by exact prefixLift 6331788
  have htrace : WordTrace (prefixWord ++ tailWord_6331788) baseStart_6331788 baseEnd_6331788 := by
    simpa [prefixWord, tailWord_6331788, baseEnd_6331788] using wordTrace_append hprefix tailTrace_6331788
  have hstable : (prefixWord ++ tailWord_6331788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331788).length < 2 ^ (prefixWord ++ tailWord_6331788).sum := by decide
  have hdescent : baseEnd_6331788 < baseStart_6331788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331815 : List Nat := [1, 1, 6, 1, 1, 1, 1, 4, 2, 3, 2]
def baseStart_6331815 : Nat := 118140960795 + 6331815 * 2 ^ 59
def prefixEnd_6331815 : Nat := 4983230072969 + 3 ^ 40 * 6331815 * 2
def baseEnd_6331815 : Nat := 3251264510348249478393019

theorem tailTrace_6331815 : CollatzResearch.WordTrace tailWord_6331815 prefixEnd_6331815 3251264510348249478393019 := by
  unfold tailWord_6331815
  simp only [CollatzResearch.WordTrace]
  refine ⟨230940265555923117753420899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153960177037282078502280599 230940265555923117753420899)
  ·
    refine ⟨346410398333884676630131349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230940265555923117753420899 346410398333884676630131349)
    ·
      refine ⟨16237987421900844217037407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 346410398333884676630131349 16237987421900844217037407)
      ·
        refine ⟨24356981132851266325556111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16237987421900844217037407 24356981132851266325556111)
        ·
          refine ⟨36535471699276899488334167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24356981132851266325556111 36535471699276899488334167)
          ·
            refine ⟨54803207548915349232501251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36535471699276899488334167 54803207548915349232501251)
            ·
              refine ⟨82204811323373023848751877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54803207548915349232501251 82204811323373023848751877)
              ·
                refine ⟨15413402123132441971640977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82204811323373023848751877 15413402123132441971640977)
                ·
                  refine ⟨11560051592349331478730733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15413402123132441971640977 11560051592349331478730733)
                  ·
                    refine ⟨4335019347130999304524025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11560051592349331478730733 4335019347130999304524025)
                    ·
                      refine ⟨3251264510348249478393019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4335019347130999304524025 3251264510348249478393019)
                      ·
                        rfl

theorem cell23_6331815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_6331815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331815 prefixEnd_6331815 := by exact prefixLift 6331815
  have htrace : WordTrace (prefixWord ++ tailWord_6331815) baseStart_6331815 baseEnd_6331815 := by
    simpa [prefixWord, tailWord_6331815, baseEnd_6331815] using wordTrace_append hprefix tailTrace_6331815
  have hstable : (prefixWord ++ tailWord_6331815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331815).length < 2 ^ (prefixWord ++ tailWord_6331815).sum := by decide
  have hdescent : baseEnd_6331815 < baseStart_6331815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331816 : List Nat := [2, 1, 6, 1, 2, 2, 2, 2, 1, 4]
def baseStart_6331816 : Nat := 118140960795 + 6331816 * 2 ^ 59
def prefixEnd_6331816 : Nat := 4983230072969 + 3 ^ 40 * 6331816 * 2
def baseEnd_6331816 : Nat := 1083755007942967991493505

theorem tailTrace_6331816 : CollatzResearch.WordTrace tailWord_6331816 prefixEnd_6331816 1083755007942967991493505 := by
  unfold tailWord_6331816
  simp only [CollatzResearch.WordTrace]
  refine ⟨115470151014459747462103651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153960201352612996616138201 115470151014459747462103651)
  ·
    refine ⟨173205226521689621193155477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115470151014459747462103651 173205226521689621193155477)
    ·
      refine ⟨8118994993204200993429163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 173205226521689621193155477 8118994993204200993429163)
      ·
        refine ⟨12178492489806301490143745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8118994993204200993429163 12178492489806301490143745)
        ·
          refine ⟨9133869367354726117607809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12178492489806301490143745 9133869367354726117607809)
          ·
            refine ⟨6850402025516044588205857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9133869367354726117607809 6850402025516044588205857)
            ·
              refine ⟨5137801519137033441154393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6850402025516044588205857 5137801519137033441154393)
              ·
                refine ⟨3853351139352775080865795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5137801519137033441154393 3853351139352775080865795)
                ·
                  refine ⟨5780026709029162621298693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3853351139352775080865795 5780026709029162621298693)
                  ·
                    refine ⟨1083755007942967991493505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5780026709029162621298693 1083755007942967991493505)
                    ·
                      rfl

theorem cell23_6331816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_6331816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331816 prefixEnd_6331816 := by exact prefixLift 6331816
  have htrace : WordTrace (prefixWord ++ tailWord_6331816) baseStart_6331816 baseEnd_6331816 := by
    simpa [prefixWord, tailWord_6331816, baseEnd_6331816] using wordTrace_append hprefix tailTrace_6331816
  have hstable : (prefixWord ++ tailWord_6331816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331816).length < 2 ^ (prefixWord ++ tailWord_6331816).sum := by decide
  have hdescent : baseEnd_6331816 < baseStart_6331816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331831 : List Nat := [1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 5]
def baseStart_6331831 : Nat := 118140960795 + 6331831 * 2 ^ 59
def prefixEnd_6331831 : Nat := 4983230072969 + 3 ^ 40 * 6331831 * 2
def baseEnd_6331831 : Nat := 3251272726038721415792945

theorem tailTrace_6331831 : CollatzResearch.WordTrace tailWord_6331831 prefixEnd_6331831 3251272726038721415792945 := by
  unfold tailWord_6331831
  simp only [CollatzResearch.WordTrace]
  refine ⟨230940849123865152486003347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153960566082576768324002231 230940849123865152486003347)
  ·
    refine ⟨346411273685797728729005021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230940849123865152486003347 346411273685797728729005021)
    ·
      refine ⟨129904227632174148273376883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 346411273685797728729005021 129904227632174148273376883)
      ·
        refine ⟨194856341448261222410065325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129904227632174148273376883 194856341448261222410065325)
        ·
          refine ⟨73071128043097958403774497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194856341448261222410065325 73071128043097958403774497)
          ·
            refine ⟨54803346032323468802830873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73071128043097958403774497 54803346032323468802830873)
            ·
              refine ⟨41102509524242601602123155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54803346032323468802830873 41102509524242601602123155)
              ·
                refine ⟨61653764286363902403184733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41102509524242601602123155 61653764286363902403184733)
                ·
                  refine ⟨23120161607386463401194275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61653764286363902403184733 23120161607386463401194275)
                  ·
                    refine ⟨34680242411079695101791413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23120161607386463401194275 34680242411079695101791413)
                    ·
                      refine ⟨3251272726038721415792945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34680242411079695101791413 3251272726038721415792945)
                      ·
                        rfl

theorem cell23_6331831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 5].length) (baseStart_6331831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331831 prefixEnd_6331831 := by exact prefixLift 6331831
  have htrace : WordTrace (prefixWord ++ tailWord_6331831) baseStart_6331831 baseEnd_6331831 := by
    simpa [prefixWord, tailWord_6331831, baseEnd_6331831] using wordTrace_append hprefix tailTrace_6331831
  have hstable : (prefixWord ++ tailWord_6331831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331831).length < 2 ^ (prefixWord ++ tailWord_6331831).sum := by decide
  have hdescent : baseEnd_6331831 < baseStart_6331831 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331838 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 6, 4]
def baseStart_6331838 : Nat := 118140960795 + 6331838 * 2 ^ 59
def prefixEnd_6331838 : Nat := 4983230072969 + 3 ^ 40 * 6331838 * 2
def baseEnd_6331838 : Nat := 1083758773467767629468471

theorem tailTrace_6331838 : CollatzResearch.WordTrace tailWord_6331838 prefixEnd_6331838 1083758773467767629468471 := by
  unfold tailWord_6331838
  simp only [CollatzResearch.WordTrace]
  refine ⟨28867638054354974085188521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153960736289893195121005445 28867638054354974085188521)
  ·
    refine ⟨21650728540766230563891391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28867638054354974085188521 21650728540766230563891391)
    ·
      refine ⟨32476092811149345845837087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21650728540766230563891391 32476092811149345845837087)
      ·
        refine ⟨48714139216724018768755631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32476092811149345845837087 48714139216724018768755631)
        ·
          refine ⟨73071208825086028153133447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48714139216724018768755631 73071208825086028153133447)
          ·
            refine ⟨109606813237629042229700171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73071208825086028153133447 109606813237629042229700171)
            ·
              refine ⟨164410219856443563344550257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109606813237629042229700171 164410219856443563344550257)
              ·
                refine ⟨123307664892332672508412693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164410219856443563344550257 123307664892332672508412693)
                ·
                  refine ⟨5780046791828094023831845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 123307664892332672508412693 5780046791828094023831845)
                  ·
                    refine ⟨1083758773467767629468471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5780046791828094023831845 1083758773467767629468471)
                    ·
                      rfl

theorem cell23_6331838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_6331838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331838 prefixEnd_6331838 := by exact prefixLift 6331838
  have htrace : WordTrace (prefixWord ++ tailWord_6331838) baseStart_6331838 baseEnd_6331838 := by
    simpa [prefixWord, tailWord_6331838, baseEnd_6331838] using wordTrace_append hprefix tailTrace_6331838
  have hstable : (prefixWord ++ tailWord_6331838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331838).length < 2 ^ (prefixWord ++ tailWord_6331838).sum := by decide
  have hdescent : baseEnd_6331838 < baseStart_6331838 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331848 : List Nat := [2, 1, 3, 1, 3, 1, 1, 3, 3, 2, 3]
def baseStart_6331848 : Nat := 118140960795 + 6331848 * 2 ^ 59
def prefixEnd_6331848 : Nat := 4983230072969 + 3 ^ 40 * 6331848 * 2
def baseEnd_6331848 : Nat := 3251281455209847849280367

theorem tailTrace_6331848 : CollatzResearch.WordTrace tailWord_6331848 prefixEnd_6331848 3251281455209847849280367 := by
  unfold tailWord_6331848
  simp only [CollatzResearch.WordTrace]
  refine ⟨115470734582401782194686099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153960979443202376259581465 115470734582401782194686099)
  ·
    refine ⟨173206101873602673292029149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115470734582401782194686099 173206101873602673292029149)
    ·
      refine ⟨64952288202601002484510931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173206101873602673292029149 64952288202601002484510931)
      ·
        refine ⟨97428432303901503726766397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64952288202601002484510931 97428432303901503726766397)
        ·
          refine ⟨36535662113963063897537399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97428432303901503726766397 36535662113963063897537399)
          ·
            refine ⟨54803493170944595846306099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36535662113963063897537399 54803493170944595846306099)
            ·
              refine ⟨82205239756416893769459149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54803493170944595846306099 82205239756416893769459149)
              ·
                refine ⟨30826964908656335163547181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82205239756416893769459149 30826964908656335163547181)
                ·
                  refine ⟨11560111840746125686330193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30826964908656335163547181 11560111840746125686330193)
                  ·
                    refine ⟨8670083880559594264747645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11560111840746125686330193 8670083880559594264747645)
                    ·
                      refine ⟨3251281455209847849280367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8670083880559594264747645 3251281455209847849280367)
                      ·
                        rfl

theorem cell23_6331848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 3, 2, 3].length) (baseStart_6331848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331848 prefixEnd_6331848 := by exact prefixLift 6331848
  have htrace : WordTrace (prefixWord ++ tailWord_6331848) baseStart_6331848 baseEnd_6331848 := by
    simpa [prefixWord, tailWord_6331848, baseEnd_6331848] using wordTrace_append hprefix tailTrace_6331848
  have hstable : (prefixWord ++ tailWord_6331848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331848).length < 2 ^ (prefixWord ++ tailWord_6331848).sum := by decide
  have hdescent : baseEnd_6331848 < baseStart_6331848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331862 : List Nat := [5, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4]
def baseStart_6331862 : Nat := 118140960795 + 6331862 * 2 ^ 59
def prefixEnd_6331862 : Nat := 4983230072969 + 3 ^ 40 * 6331862 * 2
def baseEnd_6331862 : Nat := 3251288643939010794505303

theorem tailTrace_6331862 : CollatzResearch.WordTrace tailWord_6331862 prefixEnd_6331862 3251288643939010794505303 := by
  unfold tailWord_6331862
  simp only [CollatzResearch.WordTrace]
  refine ⟨14433873736672052798773865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153961319857835229853587893 14433873736672052798773865)
  ·
    refine ⟨10825405302504039599080399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14433873736672052798773865 10825405302504039599080399)
    ·
      refine ⟨16238107953756059398620599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10825405302504039599080399 16238107953756059398620599)
      ·
        refine ⟨24357161930634089097930899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16238107953756059398620599 24357161930634089097930899)
        ·
          refine ⟨36535742895951133646896349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24357161930634089097930899 36535742895951133646896349)
          ·
            refine ⟨13700903585981675117586131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36535742895951133646896349 13700903585981675117586131)
            ·
              refine ⟨20551355378972512676379197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13700903585981675117586131 20551355378972512676379197)
              ·
                refine ⟨7706758267114692253642199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20551355378972512676379197 7706758267114692253642199)
                ·
                  refine ⟨11560137400672038380463299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7706758267114692253642199 11560137400672038380463299)
                  ·
                    refine ⟨17340206101008057570694949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11560137400672038380463299 17340206101008057570694949)
                    ·
                      refine ⟨3251288643939010794505303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17340206101008057570694949 3251288643939010794505303)
                      ·
                        rfl

theorem cell23_6331862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_6331862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331862 prefixEnd_6331862 := by exact prefixLift 6331862
  have htrace : WordTrace (prefixWord ++ tailWord_6331862) baseStart_6331862 baseEnd_6331862 := by
    simpa [prefixWord, tailWord_6331862, baseEnd_6331862] using wordTrace_append hprefix tailTrace_6331862
  have hstable : (prefixWord ++ tailWord_6331862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331862).length < 2 ^ (prefixWord ++ tailWord_6331862).sum := by decide
  have hdescent : baseEnd_6331862 < baseStart_6331862 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331865 : List Nat := [1, 2, 1, 2, 4, 3, 1, 3, 1, 2, 3]
def baseStart_6331865 : Nat := 118140960795 + 6331865 * 2 ^ 59
def prefixEnd_6331865 : Nat := 4983230072969 + 3 ^ 40 * 6331865 * 2
def baseEnd_6331865 : Nat := 3251290184380974282767789

theorem tailTrace_6331865 : CollatzResearch.WordTrace tailWord_6331865 prefixEnd_6331865 3251290184380974282767789 := by
  unfold tailWord_6331865
  simp only [CollatzResearch.WordTrace]
  refine ⟨230942089205741976292741049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153961392803827984195160699 230942089205741976292741049)
  ·
    refine ⟨173206566904306482219555787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230942089205741976292741049 173206566904306482219555787)
    ·
      refine ⟨259809850356459723329333681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173206566904306482219555787 259809850356459723329333681)
      ·
        refine ⟨194857387767344792497000261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259809850356459723329333681 194857387767344792497000261)
        ·
          refine ⟨36535760206377148593187549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194857387767344792497000261 36535760206377148593187549)
          ·
            refine ⟨13700910077391430722445331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36535760206377148593187549 13700910077391430722445331)
            ·
              refine ⟨20551365116087146083667997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13700910077391430722445331 20551365116087146083667997)
              ·
                refine ⟨7706761918532679781375499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20551365116087146083667997 7706761918532679781375499)
                ·
                  refine ⟨11560142877799019672063249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7706761918532679781375499 11560142877799019672063249)
                  ·
                    refine ⟨8670107158349264754047437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11560142877799019672063249 8670107158349264754047437)
                    ·
                      refine ⟨3251290184380974282767789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8670107158349264754047437 3251290184380974282767789)
                      ·
                        rfl

theorem cell23_6331865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 3, 1, 2, 3].length) (baseStart_6331865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331865 prefixEnd_6331865 := by exact prefixLift 6331865
  have htrace : WordTrace (prefixWord ++ tailWord_6331865) baseStart_6331865 baseEnd_6331865 := by
    simpa [prefixWord, tailWord_6331865, baseEnd_6331865] using wordTrace_append hprefix tailTrace_6331865
  have hstable : (prefixWord ++ tailWord_6331865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331865).length < 2 ^ (prefixWord ++ tailWord_6331865).sum := by decide
  have hdescent : baseEnd_6331865 < baseStart_6331865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331879 : List Nat := [1, 1, 5, 2, 1, 2, 2, 4, 1, 2, 2]
def baseStart_6331879 : Nat := 118140960795 + 6331879 * 2 ^ 59
def prefixEnd_6331879 : Nat := 4983230072969 + 3 ^ 40 * 6331879 * 2
def baseEnd_6331879 : Nat := 3251297373110137227992725

theorem tailTrace_6331879 : CollatzResearch.WordTrace tailWord_6331879 prefixEnd_6331879 3251297373110137227992725 := by
  unfold tailWord_6331879
  simp only [CollatzResearch.WordTrace]
  refine ⟨230942599827691256683750691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153961733218460837789167127 230942599827691256683750691)
  ·
    refine ⟨346413899741536885025626037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230942599827691256683750691 346413899741536885025626037)
    ·
      refine ⟨32476303100769082971152441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 346413899741536885025626037 32476303100769082971152441)
      ·
        refine ⟨24357227325576812228364331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32476303100769082971152441 24357227325576812228364331)
        ·
          refine ⟨36535840988365218342546497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24357227325576812228364331 36535840988365218342546497)
          ·
            refine ⟨27401880741273913756909873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36535840988365218342546497 27401880741273913756909873)
            ·
              refine ⟨20551410555955435317682405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27401880741273913756909873 20551410555955435317682405)
              ·
                refine ⟨3853389479241644122065451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20551410555955435317682405 3853389479241644122065451)
                ·
                  refine ⟨5780084218862466183098177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3853389479241644122065451 5780084218862466183098177)
                  ·
                    refine ⟨4335063164146849637323633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5780084218862466183098177 4335063164146849637323633)
                    ·
                      refine ⟨3251297373110137227992725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4335063164146849637323633 3251297373110137227992725)
                      ·
                        rfl

theorem cell23_6331879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_6331879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331879 prefixEnd_6331879 := by exact prefixLift 6331879
  have htrace : WordTrace (prefixWord ++ tailWord_6331879) baseStart_6331879 baseEnd_6331879 := by
    simpa [prefixWord, tailWord_6331879, baseEnd_6331879] using wordTrace_append hprefix tailTrace_6331879
  have hstable : (prefixWord ++ tailWord_6331879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331879).length < 2 ^ (prefixWord ++ tailWord_6331879).sum := by decide
  have hdescent : baseEnd_6331879 < baseStart_6331879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6331968 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 3]
def baseStart_6331968 : Nat := 118140960795 + 6331968 * 2 ^ 59
def prefixEnd_6331968 : Nat := 4983230072969 + 3 ^ 40 * 6331968 * 2
def baseEnd_6331968 : Nat := 3251343072888387379779815

theorem tailTrace_6331968 : CollatzResearch.WordTrace tailWord_6331968 prefixEnd_6331968 3251343072888387379779815 := by
  unfold tailWord_6331968
  simp only [CollatzResearch.WordTrace]
  refine ⟨115472922962184412441870279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153963897282912549922493705 115472922962184412441870279)
  ·
    refine ⟨173209384443276618662805419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115472922962184412441870279 173209384443276618662805419)
    ·
      refine ⟨259814076664914927994208129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173209384443276618662805419 259814076664914927994208129)
      ·
        refine ⟨194860557498686195995656097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259814076664914927994208129 194860557498686195995656097)
        ·
          refine ⟨146145418124014646996742073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194860557498686195995656097 146145418124014646996742073)
          ·
            refine ⟨109609063593010985247556555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146145418124014646996742073 109609063593010985247556555)
            ·
              refine ⟨164413595389516477871334833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109609063593010985247556555 164413595389516477871334833)
              ·
                refine ⟨123310196542137358403501125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164413595389516477871334833 123310196542137358403501125)
                ·
                  refine ⟨23120661851650754700656461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 123310196542137358403501125 23120661851650754700656461)
                  ·
                    refine ⟨8670248194369033012746173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23120661851650754700656461 8670248194369033012746173)
                    ·
                      refine ⟨3251343072888387379779815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8670248194369033012746173 3251343072888387379779815)
                      ·
                        rfl

theorem cell23_6331968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 3].length) (baseStart_6331968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6331968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6331968 prefixEnd_6331968 := by exact prefixLift 6331968
  have htrace : WordTrace (prefixWord ++ tailWord_6331968) baseStart_6331968 baseEnd_6331968 := by
    simpa [prefixWord, tailWord_6331968, baseEnd_6331968] using wordTrace_append hprefix tailTrace_6331968
  have hstable : (prefixWord ++ tailWord_6331968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6331968).length < 2 ^ (prefixWord ++ tailWord_6331968).sum := by decide
  have hdescent : baseEnd_6331968 < baseStart_6331968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6331968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6332022 : List Nat := [5, 1, 1, 2, 2, 1, 3, 1, 2, 5]
def baseStart_6332022 : Nat := 118140960795 + 6332022 * 2 ^ 59
def prefixEnd_6332022 : Nat := 4983230072969 + 3 ^ 40 * 6332022 * 2
def baseEnd_6332022 : Nat := 1083790266947910056168189

theorem tailTrace_6332022 : CollatzResearch.WordTrace tailWord_6332022 prefixEnd_6332022 1083790266947910056168189 := by
  unfold tailWord_6332022
  simp only [CollatzResearch.WordTrace]
  refine ⟨14434238466635824506637895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153965210310782128070804213 14434238466635824506637895)
  ·
    refine ⟨21651357699953736759956843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14434238466635824506637895 21651357699953736759956843)
    ·
      refine ⟨32477036549930605139935265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21651357699953736759956843 32477036549930605139935265)
      ·
        refine ⟨24357777412447953854951449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32477036549930605139935265 24357777412447953854951449)
        ·
          refine ⟨18268333059335965391213587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24357777412447953854951449 18268333059335965391213587)
          ·
            refine ⟨27402499589003948086820381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18268333059335965391213587 27402499589003948086820381)
            ·
              refine ⟨10275937345876480532557643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27402499589003948086820381 10275937345876480532557643)
              ·
                refine ⟨15413906018814720798836465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10275937345876480532557643 15413906018814720798836465)
                ·
                  refine ⟨11560429514111040599127349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15413906018814720798836465 11560429514111040599127349)
                  ·
                    refine ⟨1083790266947910056168189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11560429514111040599127349 1083790266947910056168189)
                    ·
                      rfl

theorem cell23_6332022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_6332022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6332022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6332022 prefixEnd_6332022 := by exact prefixLift 6332022
  have htrace : WordTrace (prefixWord ++ tailWord_6332022) baseStart_6332022 baseEnd_6332022 := by
    simpa [prefixWord, tailWord_6332022, baseEnd_6332022] using wordTrace_append hprefix tailTrace_6332022
  have hstable : (prefixWord ++ tailWord_6332022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6332022).length < 2 ^ (prefixWord ++ tailWord_6332022).sum := by decide
  have hdescent : baseEnd_6332022 < baseStart_6332022 := by decide
  rcases family_descends (prefixWord ++ tailWord_6332022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6332025 : List Nat := [1, 2, 1, 3, 3, 1, 1, 2, 1, 6, 2]
def baseStart_6332025 : Nat := 118140960795 + 6332025 * 2 ^ 59
def prefixEnd_6332025 : Nat := 4983230072969 + 3 ^ 40 * 6332025 * 2
def baseEnd_6332025 : Nat := 3251372341285693656767053

theorem tailTrace_6332025 : CollatzResearch.WordTrace tailWord_6332025 prefixEnd_6332025 3251372341285693656767053 := by
  unfold tailWord_6332025
  simp only [CollatzResearch.WordTrace]
  refine ⟨230947924885162323618565529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153965283256774882412377019 230947924885162323618565529)
  ·
    refine ⟨173210943663871742713924147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230947924885162323618565529 173210943663871742713924147)
    ·
      refine ⟨259816415495807614070886221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173210943663871742713924147 259816415495807614070886221)
      ·
        refine ⟨97431155810927855276582333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259816415495807614070886221 97431155810927855276582333)
        ·
          refine ⟨36536683429097945728718375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97431155810927855276582333 36536683429097945728718375)
          ·
            refine ⟨54805025143646918593077563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36536683429097945728718375 54805025143646918593077563)
            ·
              refine ⟨82207537715470377889616345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54805025143646918593077563 82207537715470377889616345)
              ·
                refine ⟨61655653286602783417212259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82207537715470377889616345 61655653286602783417212259)
                ·
                  refine ⟨92483479929904175125818389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61655653286602783417212259 92483479929904175125818389)
                  ·
                    refine ⟨4335163121714258209022737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 92483479929904175125818389 4335163121714258209022737)
                    ·
                      refine ⟨3251372341285693656767053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4335163121714258209022737 3251372341285693656767053)
                      ·
                        rfl

theorem cell23_6332025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 6, 2].length) (baseStart_6332025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6332025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6332025 prefixEnd_6332025 := by exact prefixLift 6332025
  have htrace : WordTrace (prefixWord ++ tailWord_6332025) baseStart_6332025 baseEnd_6332025 := by
    simpa [prefixWord, tailWord_6332025, baseEnd_6332025] using wordTrace_append hprefix tailTrace_6332025
  have hstable : (prefixWord ++ tailWord_6332025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6332025).length < 2 ^ (prefixWord ++ tailWord_6332025).sum := by decide
  have hdescent : baseEnd_6332025 < baseStart_6332025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6332025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6332042 : List Nat := [3, 1, 2, 3, 2, 1, 1, 2, 2, 4, 2]
def baseStart_6332042 : Nat := 118140960795 + 6332042 * 2 ^ 59
def prefixEnd_6332042 : Nat := 4983230072969 + 3 ^ 40 * 6332042 * 2
def baseEnd_6332042 : Nat := 3251381070456820090254475

theorem tailTrace_6332042 : CollatzResearch.WordTrace tailWord_6332042 prefixEnd_6332042 3251381070456820090254475 := by
  unfold tailWord_6332042
  simp only [CollatzResearch.WordTrace]
  refine ⟨57737136231525183880483595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153965696617400490347956253 57737136231525183880483595)
  ·
    refine ⟨86605704347287775820725393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57737136231525183880483595 86605704347287775820725393)
    ·
      refine ⟨64954278260465831865544045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86605704347287775820725393 64954278260465831865544045)
      ·
        refine ⟨24357854347674686949579017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64954278260465831865544045 24357854347674686949579017)
        ·
          refine ⟨18268390760756015212184263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24357854347674686949579017 18268390760756015212184263)
          ·
            refine ⟨27402586141134022818276395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18268390760756015212184263 27402586141134022818276395)
            ·
              refine ⟨41103879211701034227414593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27402586141134022818276395 41103879211701034227414593)
              ·
                refine ⟨30827909408775775670560945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41103879211701034227414593 30827909408775775670560945)
                ·
                  refine ⟨23120932056581831752920709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30827909408775775670560945 23120932056581831752920709)
                  ·
                    refine ⟨4335174760609093453672633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23120932056581831752920709 4335174760609093453672633)
                    ·
                      refine ⟨3251381070456820090254475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4335174760609093453672633 3251381070456820090254475)
                      ·
                        rfl

theorem cell23_6332042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_6332042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6332042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6332042 prefixEnd_6332042 := by exact prefixLift 6332042
  have htrace : WordTrace (prefixWord ++ tailWord_6332042) baseStart_6332042 baseEnd_6332042 := by
    simpa [prefixWord, tailWord_6332042, baseEnd_6332042] using wordTrace_append hprefix tailTrace_6332042
  have hstable : (prefixWord ++ tailWord_6332042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6332042).length < 2 ^ (prefixWord ++ tailWord_6332042).sum := by decide
  have hdescent : baseEnd_6332042 < baseStart_6332042 := by decide
  rcases family_descends (prefixWord ++ tailWord_6332042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6332062 : List Nat := [4, 3, 1, 1, 1, 2, 1, 2, 1, 4, 3]
def baseStart_6332062 : Nat := 118140960795 + 6332062 * 2 ^ 59
def prefixEnd_6332062 : Nat := 4983230072969 + 3 ^ 40 * 6332062 * 2
def baseEnd_6332062 : Nat := 3251391340069910012004383

theorem tailTrace_6332062 : CollatzResearch.WordTrace tailWord_6332062 prefixEnd_6332062 3251391340069910012004383 := by
  unfold tailWord_6332062
  simp only [CollatzResearch.WordTrace]
  refine ⟨28868659298253534867207805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153966182924018852625108293 28868659298253534867207805)
  ·
    refine ⟨10825747236845075575202927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28868659298253534867207805 10825747236845075575202927)
    ·
      refine ⟨16238620855267613362804391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10825747236845075575202927 16238620855267613362804391)
      ·
        refine ⟨24357931282901420044206587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16238620855267613362804391 24357931282901420044206587)
        ·
          refine ⟨36536896924352130066309881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24357931282901420044206587 36536896924352130066309881)
          ·
            refine ⟨27402672693264097549732411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36536896924352130066309881 27402672693264097549732411)
            ·
              refine ⟨41104009039896146324598617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27402672693264097549732411 41104009039896146324598617)
              ·
                refine ⟨30828006779922109743448963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41104009039896146324598617 30828006779922109743448963)
                ·
                  refine ⟨46242010169883164615173445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30828006779922109743448963 46242010169883164615173445)
                  ·
                    refine ⟨8670376906853093365345021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46242010169883164615173445 8670376906853093365345021)
                    ·
                      refine ⟨3251391340069910012004383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8670376906853093365345021 3251391340069910012004383)
                      ·
                        rfl

theorem cell23_6332062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_6332062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6332062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6332062 prefixEnd_6332062 := by exact prefixLift 6332062
  have htrace : WordTrace (prefixWord ++ tailWord_6332062) baseStart_6332062 baseEnd_6332062 := by
    simpa [prefixWord, tailWord_6332062, baseEnd_6332062] using wordTrace_append hprefix tailTrace_6332062
  have hstable : (prefixWord ++ tailWord_6332062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6332062).length < 2 ^ (prefixWord ++ tailWord_6332062).sum := by decide
  have hdescent : baseEnd_6332062 < baseStart_6332062 := by decide
  rcases family_descends (prefixWord ++ tailWord_6332062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6332095 : List Nat := [1, 1, 2, 2, 2, 3, 1, 5, 1, 5]
def baseStart_6332095 : Nat := 118140960795 + 6332095 * 2 ^ 59
def prefixEnd_6332095 : Nat := 4983230072969 + 3 ^ 40 * 6332095 * 2
def baseEnd_6332095 : Nat := 1083802761643836127630577

theorem tailTrace_6332095 : CollatzResearch.WordTrace tailWord_6332095 prefixEnd_6332095 1083802761643836127630577 := by
  unfold tailWord_6332095
  simp only [CollatzResearch.WordTrace]
  refine ⟨230950477994908725573613739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153966985329939150382409159 230950477994908725573613739)
  ·
    refine ⟨346425716992363088360420609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230950477994908725573613739 346425716992363088360420609)
    ·
      refine ⟨259819287744272316270315457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346425716992363088360420609 259819287744272316270315457)
      ·
        refine ⟨194864465808204237202736593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259819287744272316270315457 194864465808204237202736593)
        ·
          refine ⟨146148349356153177902052445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194864465808204237202736593 146148349356153177902052445)
          ·
            refine ⟨54805631008557441713269667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146148349356153177902052445 54805631008557441713269667)
            ·
              refine ⟨82208446512836162569904501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54805631008557441713269667 82208446512836162569904501)
              ·
                refine ⟨7707041860578390240928547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82208446512836162569904501 7707041860578390240928547)
                ·
                  refine ⟨11560562790867585361392821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7707041860578390240928547 11560562790867585361392821)
                  ·
                    refine ⟨1083802761643836127630577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11560562790867585361392821 1083802761643836127630577)
                    ·
                      rfl

theorem cell23_6332095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 5, 1, 5].length) (baseStart_6332095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6332095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6332095 prefixEnd_6332095 := by exact prefixLift 6332095
  have htrace : WordTrace (prefixWord ++ tailWord_6332095) baseStart_6332095 baseEnd_6332095 := by
    simpa [prefixWord, tailWord_6332095, baseEnd_6332095] using wordTrace_append hprefix tailTrace_6332095
  have hstable : (prefixWord ++ tailWord_6332095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6332095).length < 2 ^ (prefixWord ++ tailWord_6332095).sum := by decide
  have hdescent : baseEnd_6332095 < baseStart_6332095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6332095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6332115 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 3, 8, 2]
def baseStart_6332115 : Nat := 118140960795 + 6332115 * 2 ^ 59
def prefixEnd_6332115 : Nat := 4983230072969 + 3 ^ 40 * 6332115 * 2
def baseEnd_6332115 : Nat := 3251418554544598304641639

theorem tailTrace_6332115 : CollatzResearch.WordTrace tailWord_6332115 prefixEnd_6332115 3251418554544598304641639 := by
  unfold tailWord_6332115
  simp only [CollatzResearch.WordTrace]
  refine ⟨230951207454836268989341799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153967471636557512659561199 230951207454836268989341799)
  ·
    refine ⟨346426811182254403484012699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230951207454836268989341799 346426811182254403484012699)
    ·
      refine ⟨519640216773381605226019049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346426811182254403484012699 519640216773381605226019049)
      ·
        refine ⟨389730162580036203919514287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 519640216773381605226019049 389730162580036203919514287)
        ·
          refine ⟨584595243870054305879271431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389730162580036203919514287 584595243870054305879271431)
          ·
            refine ⟨876892865805081458818907147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 584595243870054305879271431 876892865805081458818907147)
            ·
              refine ⟨1315339298707622188228360721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 876892865805081458818907147 1315339298707622188228360721)
              ·
                refine ⟨986504474030716641171270541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1315339298707622188228360721 986504474030716641171270541)
                ·
                  refine ⟨369939177761518740439226453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 986504474030716641171270541 369939177761518740439226453)
                  ·
                    refine ⟨4335224739392797739522185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 369939177761518740439226453 4335224739392797739522185)
                    ·
                      refine ⟨3251418554544598304641639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4335224739392797739522185 3251418554544598304641639)
                      ·
                        rfl

theorem cell23_6332115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 8, 2].length) (baseStart_6332115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6332115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6332115 prefixEnd_6332115 := by exact prefixLift 6332115
  have htrace : WordTrace (prefixWord ++ tailWord_6332115) baseStart_6332115 baseEnd_6332115 := by
    simpa [prefixWord, tailWord_6332115, baseEnd_6332115] using wordTrace_append hprefix tailTrace_6332115
  have hstable : (prefixWord ++ tailWord_6332115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6332115).length < 2 ^ (prefixWord ++ tailWord_6332115).sum := by decide
  have hdescent : baseEnd_6332115 < baseStart_6332115 := by decide
  rcases family_descends (prefixWord ++ tailWord_6332115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6332129 : List Nat := [1, 2, 3, 1, 5, 2, 1, 2, 1, 5]
def baseStart_6332129 : Nat := 118140960795 + 6332129 * 2 ^ 59
def prefixEnd_6332129 : Nat := 4983230072969 + 3 ^ 40 * 6332129 * 2
def baseEnd_6332129 : Nat := 1083808581091253749955525

theorem tailTrace_6332129 : CollatzResearch.WordTrace tailWord_6332129 prefixEnd_6332129 1083808581091253749955525 := by
  unfold tailWord_6332129
  simp only [CollatzResearch.WordTrace]
  refine ⟨230951718076785549380351441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153967812051190366253567627 230951718076785549380351441)
  ·
    refine ⟨173213788557589162035263581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230951718076785549380351441 173213788557589162035263581)
    ·
      refine ⟨64955170709095935763223843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173213788557589162035263581 64955170709095935763223843)
      ·
        refine ⟨97432756063643903644835765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64955170709095935763223843 97432756063643903644835765)
        ·
          refine ⟨9134320880966615966703353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97432756063643903644835765 9134320880966615966703353)
          ·
            refine ⟨6850740660724961975027515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9134320880966615966703353 6850740660724961975027515)
            ·
              refine ⟨10276110991087442962541273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6850740660724961975027515 10276110991087442962541273)
              ·
                refine ⟨7707083243315582221905955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10276110991087442962541273 7707083243315582221905955)
                ·
                  refine ⟨11560624864973373332858933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7707083243315582221905955 11560624864973373332858933)
                  ·
                    refine ⟨1083808581091253749955525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11560624864973373332858933 1083808581091253749955525)
                    ·
                      rfl

theorem cell23_6332129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 2, 1, 5].length) (baseStart_6332129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6332129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6332129 prefixEnd_6332129 := by exact prefixLift 6332129
  have htrace : WordTrace (prefixWord ++ tailWord_6332129) baseStart_6332129 baseEnd_6332129 := by
    simpa [prefixWord, tailWord_6332129, baseEnd_6332129] using wordTrace_append hprefix tailTrace_6332129
  have hstable : (prefixWord ++ tailWord_6332129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6332129).length < 2 ^ (prefixWord ++ tailWord_6332129).sum := by decide
  have hdescent : baseEnd_6332129 < baseStart_6332129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6332129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6332145 : List Nat := [1, 2, 2, 2, 2, 3, 1, 1, 3, 2, 4]
def baseStart_6332145 : Nat := 118140960795 + 6332145 * 2 ^ 59
def prefixEnd_6332145 : Nat := 4983230072969 + 3 ^ 40 * 6332145 * 2
def baseEnd_6332145 : Nat := 3251433958964233187266501

theorem tailTrace_6332145 : CollatzResearch.WordTrace tailWord_6332145 prefixEnd_6332145 3251433958964233187266501 := by
  unfold tailWord_6332145
  simp only [CollatzResearch.WordTrace]
  refine ⟨230952301644727584112933889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153968201096485056075289259 230952301644727584112933889)
  ·
    refine ⟨173214226233545688084700417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230952301644727584112933889 173214226233545688084700417)
    ·
      refine ⟨129910669675159266063525313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173214226233545688084700417 129910669675159266063525313)
      ·
        refine ⟨97433002256369449547643985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129910669675159266063525313 97433002256369449547643985)
        ·
          refine ⟨73074751692277087160732989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97433002256369449547643985 73074751692277087160732989)
          ·
            refine ⟨27403031884603907685274871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73074751692277087160732989 27403031884603907685274871)
            ·
              refine ⟨41104547826905861527912307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27403031884603907685274871 41104547826905861527912307)
              ·
                refine ⟨61656821740358792291868461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41104547826905861527912307 61656821740358792291868461)
                ·
                  refine ⟨23121308152634547109450673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61656821740358792291868461 23121308152634547109450673)
                  ·
                    refine ⟨17340981114475910332088005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23121308152634547109450673 17340981114475910332088005)
                    ·
                      refine ⟨3251433958964233187266501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17340981114475910332088005 3251433958964233187266501)
                      ·
                        rfl

theorem cell23_6332145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_6332145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6332145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6332145 prefixEnd_6332145 := by exact prefixLift 6332145
  have htrace : WordTrace (prefixWord ++ tailWord_6332145) baseStart_6332145 baseEnd_6332145 := by
    simpa [prefixWord, tailWord_6332145, baseEnd_6332145] using wordTrace_append hprefix tailTrace_6332145
  have hstable : (prefixWord ++ tailWord_6332145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6332145).length < 2 ^ (prefixWord ++ tailWord_6332145).sum := by decide
  have hdescent : baseEnd_6332145 < baseStart_6332145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6332145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6332162 : List Nat := [3, 4, 1, 1, 1, 1, 1, 2, 3, 2, 4]
def baseStart_6332162 : Nat := 118140960795 + 6332162 * 2 ^ 59
def prefixEnd_6332162 : Nat := 4983230072969 + 3 ^ 40 * 6332162 * 2
def baseEnd_6332162 : Nat := 3251442688135359620753923

theorem tailTrace_6332162 : CollatzResearch.WordTrace tailWord_6332162 prefixEnd_6332162 3251442688135359620753923 := by
  unfold tailWord_6332162
  simp only [CollatzResearch.WordTrace]
  refine ⟨57738230421416499004075685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153968614457110664010868493 57738230421416499004075685)
  ·
    refine ⟨10825918204015593563264191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57738230421416499004075685 10825918204015593563264191)
    ·
      refine ⟨16238877306023390344896287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10825918204015593563264191 16238877306023390344896287)
      ·
        refine ⟨24358315959035085517344431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16238877306023390344896287 24358315959035085517344431)
        ·
          refine ⟨36537473938552628276016647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24358315959035085517344431 36537473938552628276016647)
          ·
            refine ⟨54806210907828942414024971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36537473938552628276016647 54806210907828942414024971)
            ·
              refine ⟨82209316361743413621037457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54806210907828942414024971 82209316361743413621037457)
              ·
                refine ⟨61656987271307560215778093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82209316361743413621037457 61656987271307560215778093)
                ·
                  refine ⟨23121370226740335080916785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61656987271307560215778093 23121370226740335080916785)
                  ·
                    refine ⟨17341027670055251310687589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23121370226740335080916785 17341027670055251310687589)
                    ·
                      refine ⟨3251442688135359620753923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17341027670055251310687589 3251442688135359620753923)
                      ·
                        rfl

theorem cell23_6332162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_6332162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6332162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6332162 prefixEnd_6332162 := by exact prefixLift 6332162
  have htrace : WordTrace (prefixWord ++ tailWord_6332162) baseStart_6332162 baseEnd_6332162 := by
    simpa [prefixWord, tailWord_6332162, baseEnd_6332162] using wordTrace_append hprefix tailTrace_6332162
  have hstable : (prefixWord ++ tailWord_6332162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6332162).length < 2 ^ (prefixWord ++ tailWord_6332162).sum := by decide
  have hdescent : baseEnd_6332162 < baseStart_6332162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6332162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6332216 : List Nat := [2, 1, 2, 1, 3, 5, 1, 2, 2, 1, 3]
def baseStart_6332216 : Nat := 118140960795 + 6332216 * 2 ^ 59
def prefixEnd_6332216 : Nat := 4983230072969 + 3 ^ 40 * 6332216 * 2
def baseEnd_6332216 : Nat := 3251470416090702409478675

theorem tailTrace_6332216 : CollatzResearch.WordTrace tailWord_6332216 prefixEnd_6332216 3251470416090702409478675 := by
  unfold tailWord_6332216
  simp only [CollatzResearch.WordTrace]
  refine ⟨115477445613735181619384251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153969927484980242159179001 115477445613735181619384251)
  ·
    refine ⟨173216168420602772429076377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115477445613735181619384251 173216168420602772429076377)
    ·
      refine ⟨129912126315452079321807283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173216168420602772429076377 129912126315452079321807283)
      ·
        refine ⟨194868189473178118982710925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129912126315452079321807283 194868189473178118982710925)
        ·
          refine ⟨73075571052441794618516597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194868189473178118982710925 73075571052441794618516597)
          ·
            refine ⟨6850834786166418245485931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73075571052441794618516597 6850834786166418245485931)
            ·
              refine ⟨10276252179249627368228897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6850834786166418245485931 10276252179249627368228897)
              ·
                refine ⟨7707189134437220526171673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10276252179249627368228897 7707189134437220526171673)
                ·
                  refine ⟨5780391850827915394628755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7707189134437220526171673 5780391850827915394628755)
                  ·
                    refine ⟨8670587776241873091943133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5780391850827915394628755 8670587776241873091943133)
                    ·
                      refine ⟨3251470416090702409478675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8670587776241873091943133 3251470416090702409478675)
                      ·
                        rfl

theorem cell23_6332216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 2, 2, 1, 3].length) (baseStart_6332216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6332216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6332216 prefixEnd_6332216 := by exact prefixLift 6332216
  have htrace : WordTrace (prefixWord ++ tailWord_6332216) baseStart_6332216 baseEnd_6332216 := by
    simpa [prefixWord, tailWord_6332216, baseEnd_6332216] using wordTrace_append hprefix tailTrace_6332216
  have hstable : (prefixWord ++ tailWord_6332216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6332216).length < 2 ^ (prefixWord ++ tailWord_6332216).sum := by decide
  have hdescent : baseEnd_6332216 < baseStart_6332216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6332216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6332305 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 2, 8]
def baseStart_6332305 : Nat := 118140960795 + 6332305 * 2 ^ 59
def prefixEnd_6332305 : Nat := 4983230072969 + 3 ^ 40 * 6332305 * 2
def baseEnd_6332305 : Nat := 1083838705289650853755255

theorem tailTrace_6332305 : CollatzResearch.WordTrace tailWord_6332305 prefixEnd_6332305 1083838705289650853755255 := by
  unfold tailWord_6332305
  simp only [CollatzResearch.WordTrace]
  refine ⟨230958137324147931438758369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153972091549431954292505579 230958137324147931438758369)
  ·
    refine ⟨173218602993110948579068777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230958137324147931438758369 173218602993110948579068777)
    ·
      refine ⟨129913952244833211434301583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173218602993110948579068777 129913952244833211434301583)
      ·
        refine ⟨194870928367249817151452375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129913952244833211434301583 194870928367249817151452375)
        ·
          refine ⟨292306392550874725727178563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194870928367249817151452375 292306392550874725727178563)
          ·
            refine ⟨438459588826312088590767845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292306392550874725727178563 438459588826312088590767845)
            ·
              refine ⟨82211172904933516610768971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 438459588826312088590767845 82211172904933516610768971)
              ·
                refine ⟨123316759357400274916153457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82211172904933516610768971 123316759357400274916153457)
                ·
                  refine ⟨92487569518050206187115093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123316759357400274916153457 92487569518050206187115093)
                  ·
                    refine ⟨1083838705289650853755255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 92487569518050206187115093 1083838705289650853755255)
                    ·
                      rfl

theorem cell23_6332305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 8].length) (baseStart_6332305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6332305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6332305 prefixEnd_6332305 := by exact prefixLift 6332305
  have htrace : WordTrace (prefixWord ++ tailWord_6332305) baseStart_6332305 baseEnd_6332305 := by
    simpa [prefixWord, tailWord_6332305, baseEnd_6332305] using wordTrace_append hprefix tailTrace_6332305
  have hstable : (prefixWord ++ tailWord_6332305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6332305).length < 2 ^ (prefixWord ++ tailWord_6332305).sum := by decide
  have hdescent : baseEnd_6332305 < baseStart_6332305 := by decide
  rcases family_descends (prefixWord ++ tailWord_6332305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6332352 : List Nat := [2, 1, 1, 2, 3, 2, 1, 5, 6]
def baseStart_6332352 : Nat := 118140960795 + 6332352 * 2 ^ 59
def prefixEnd_6332352 : Nat := 4983230072969 + 3 ^ 40 * 6332352 * 2
def baseEnd_6332352 : Nat := 361282249939968208597561

theorem tailTrace_6332352 : CollatzResearch.WordTrace tailWord_6332352 prefixEnd_6332352 361282249939968208597561 := by
  unfold tailWord_6332352
  simp only [CollatzResearch.WordTrace]
  refine ⟨115479925777488829232859655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153973234369985105643812873 115479925777488829232859655)
  ·
    refine ⟨173219888666233243849289483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115479925777488829232859655 173219888666233243849289483)
    ·
      refine ⟨259829832999349865773934225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173219888666233243849289483 259829832999349865773934225)
      ·
        refine ⟨194872374749512399330450669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259829832999349865773934225 194872374749512399330450669)
        ·
          refine ⟨73077140531067149748919001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194872374749512399330450669 73077140531067149748919001)
          ·
            refine ⟨54807855398300362311689251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73077140531067149748919001 54807855398300362311689251)
            ·
              refine ⟨82211783097450543467533877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54807855398300362311689251 82211783097450543467533877)
              ·
                refine ⟨7707354665385988450081301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82211783097450543467533877 7707354665385988450081301)
                ·
                  refine ⟨361282249939968208597561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7707354665385988450081301 361282249939968208597561)
                  ·
                    rfl

theorem cell23_6332352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 5, 6].length) (baseStart_6332352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6332352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6332352 prefixEnd_6332352 := by exact prefixLift 6332352
  have htrace : WordTrace (prefixWord ++ tailWord_6332352) baseStart_6332352 baseEnd_6332352 := by
    simpa [prefixWord, tailWord_6332352, baseEnd_6332352] using wordTrace_append hprefix tailTrace_6332352
  have hstable : (prefixWord ++ tailWord_6332352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6332352).length < 2 ^ (prefixWord ++ tailWord_6332352).sum := by decide
  have hdescent : baseEnd_6332352 < baseStart_6332352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6332352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6332373 : List Nat := [1, 3, 2, 3, 2, 2, 2, 3, 1, 4]
def baseStart_6332373 : Nat := 118140960795 + 6332373 * 2 ^ 59
def prefixEnd_6332373 : Nat := 4983230072969 + 3 ^ 40 * 6332373 * 2
def baseEnd_6332373 : Nat := 1083850344184486098405151

theorem tailTrace_6332373 : CollatzResearch.WordTrace tailWord_6332373 prefixEnd_6332373 1083850344184486098405151 := by
  unfold tailWord_6332373
  simp only [CollatzResearch.WordTrace]
  refine ⟨230960617487901579052233773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153973744991934386034822515 230960617487901579052233773)
  ·
    refine ⟨86610231557963092144587665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230960617487901579052233773 86610231557963092144587665)
    ·
      refine ⟨64957673668472319108440749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86610231557963092144587665 64957673668472319108440749)
      ·
        refine ⟨24359127625677119665665281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64957673668472319108440749 24359127625677119665665281)
        ·
          refine ⟨18269345719257839749248961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24359127625677119665665281 18269345719257839749248961)
          ·
            refine ⟨13702009289443379811936721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18269345719257839749248961 13702009289443379811936721)
            ·
              refine ⟨10276506967082534858952541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13702009289443379811936721 10276506967082534858952541)
              ·
                refine ⟨3853690112655950572107203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10276506967082534858952541 3853690112655950572107203)
                ·
                  refine ⟨5780535168983925858160805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3853690112655950572107203 5780535168983925858160805)
                  ·
                    refine ⟨1083850344184486098405151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5780535168983925858160805 1083850344184486098405151)
                    ·
                      rfl

theorem cell23_6332373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 3, 1, 4].length) (baseStart_6332373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6332373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6332373 prefixEnd_6332373 := by exact prefixLift 6332373
  have htrace : WordTrace (prefixWord ++ tailWord_6332373) baseStart_6332373 baseEnd_6332373 := by
    simpa [prefixWord, tailWord_6332373, baseEnd_6332373] using wordTrace_append hprefix tailTrace_6332373
  have hstable : (prefixWord ++ tailWord_6332373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6332373).length < 2 ^ (prefixWord ++ tailWord_6332373).sum := by decide
  have hdescent : baseEnd_6332373 < baseStart_6332373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6332373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6332386 : List Nat := [3, 3, 3, 1, 2, 1, 1, 1, 8]
def baseStart_6332386 : Nat := 118140960795 + 6332386 * 2 ^ 59
def prefixEnd_6332386 : Nat := 4983230072969 + 3 ^ 40 * 6332386 * 2
def baseEnd_6332386 : Nat := 361284189755774082705877

theorem tailTrace_6332386 : CollatzResearch.WordTrace tailWord_6332386 prefixEnd_6332386 361284189755774082705877 := by
  unfold tailWord_6332386
  simp only [CollatzResearch.WordTrace]
  refine ⟨57740272909213620568114253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153974061091236321514971341 57740272909213620568114253)
  ·
    refine ⟨21652602340955107713042845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57740272909213620568114253 21652602340955107713042845)
    ·
      refine ⟨8119725877858165392391067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21652602340955107713042845 8119725877858165392391067)
      ·
        refine ⟨12179588816787248088586601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8119725877858165392391067 12179588816787248088586601)
        ·
          refine ⟨9134691612590436066439951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12179588816787248088586601 9134691612590436066439951)
          ·
            refine ⟨13702037418885654099659927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9134691612590436066439951 13702037418885654099659927)
            ·
              refine ⟨20553056128328481149489891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13702037418885654099659927 20553056128328481149489891)
              ·
                refine ⟨30829584192492721724234837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20553056128328481149489891 30829584192492721724234837)
                ·
                  refine ⟨361284189755774082705877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30829584192492721724234837 361284189755774082705877)
                  ·
                    rfl

theorem cell23_6332386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_6332386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6332386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6332386 prefixEnd_6332386 := by exact prefixLift 6332386
  have htrace : WordTrace (prefixWord ++ tailWord_6332386) baseStart_6332386 baseEnd_6332386 := by
    simpa [prefixWord, tailWord_6332386, baseEnd_6332386] using wordTrace_append hprefix tailTrace_6332386
  have hstable : (prefixWord ++ tailWord_6332386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6332386).length < 2 ^ (prefixWord ++ tailWord_6332386).sum := by decide
  have hdescent : baseEnd_6332386 < baseStart_6332386 := by decide
  rcases family_descends (prefixWord ++ tailWord_6332386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6332442 : List Nat := [3, 1, 1, 3, 1, 3, 11]
def baseStart_6332442 : Nat := 118140960795 + 6332442 * 2 ^ 59
def prefixEnd_6332442 : Nat := 4983230072969 + 3 ^ 40 * 6332442 * 2
def baseEnd_6332442 : Nat := 40143042749612574385835

theorem tailTrace_6332442 : CollatzResearch.WordTrace tailWord_6332442 prefixEnd_6332442 40143042749612574385835 := by
  unfold tailWord_6332442
  simp only [CollatzResearch.WordTrace]
  refine ⟨57740783531162900959123895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153975422749767735890997053 57740783531162900959123895)
  ·
    refine ⟨86611175296744351438685843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57740783531162900959123895 86611175296744351438685843)
    ·
      refine ⟨129916762945116527158028765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86611175296744351438685843 129916762945116527158028765)
      ·
        refine ⟨48718786104418697684260787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129916762945116527158028765 48718786104418697684260787)
        ·
          refine ⟨73078179156628046526391181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48718786104418697684260787 73078179156628046526391181)
          ·
            refine ⟨27404317183735517447396693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73078179156628046526391181 27404317183735517447396693)
            ·
              refine ⟨40143042749612574385835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 27404317183735517447396693 40143042749612574385835)
              ·
                rfl

theorem cell23_6332442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 11].length) (baseStart_6332442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6332442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6332442 prefixEnd_6332442 := by exact prefixLift 6332442
  have htrace : WordTrace (prefixWord ++ tailWord_6332442) baseStart_6332442 baseEnd_6332442 := by
    simpa [prefixWord, tailWord_6332442, baseEnd_6332442] using wordTrace_append hprefix tailTrace_6332442
  have hstable : (prefixWord ++ tailWord_6332442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6332442).length < 2 ^ (prefixWord ++ tailWord_6332442).sum := by decide
  have hdescent : baseEnd_6332442 < baseStart_6332442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6332442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6332453 : List Nat := [1, 3, 1, 2, 2, 3, 3, 1, 3, 2, 2]
def baseStart_6332453 : Nat := 118140960795 + 6332453 * 2 ^ 59
def prefixEnd_6332453 : Nat := 4983230072969 + 3 ^ 40 * 6332453 * 2
def baseEnd_6332453 : Nat := 3251592111005817982215085

theorem tailTrace_6332453 : CollatzResearch.WordTrace tailWord_6332453 prefixEnd_6332453 3251592111005817982215085 := by
  unfold tailWord_6332453
  simp only [CollatzResearch.WordTrace]
  refine ⟨230963535327611752715146013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153975690218407835143430675 230963535327611752715146013)
  ·
    refine ⟨86611325747854407268179755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230963535327611752715146013 86611325747854407268179755)
    ·
      refine ⟨129916988621781610902269633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86611325747854407268179755 129916988621781610902269633)
      ·
        refine ⟨97437741466336208176702225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129916988621781610902269633 97437741466336208176702225)
        ·
          refine ⟨73078306099752156132526669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97437741466336208176702225 73078306099752156132526669)
          ·
            refine ⟨27404364787407058549697501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73078306099752156132526669 27404364787407058549697501)
            ·
              refine ⟨10276636795277646956136563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27404364787407058549697501 10276636795277646956136563)
              ·
                refine ⟨15414955192916470434204845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10276636795277646956136563 15414955192916470434204845)
                ·
                  refine ⟨5780608197343676412826817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15414955192916470434204845 5780608197343676412826817)
                  ·
                    refine ⟨4335456148007757309620113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5780608197343676412826817 4335456148007757309620113)
                    ·
                      refine ⟨3251592111005817982215085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4335456148007757309620113 3251592111005817982215085)
                      ·
                        rfl

theorem cell23_6332453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 3, 2, 2].length) (baseStart_6332453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6332453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6332453 prefixEnd_6332453 := by exact prefixLift 6332453
  have htrace : WordTrace (prefixWord ++ tailWord_6332453) baseStart_6332453 baseEnd_6332453 := by
    simpa [prefixWord, tailWord_6332453, baseEnd_6332453] using wordTrace_append hprefix tailTrace_6332453
  have hstable : (prefixWord ++ tailWord_6332453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6332453).length < 2 ^ (prefixWord ++ tailWord_6332453).sum := by decide
  have hdescent : baseEnd_6332453 < baseStart_6332453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6332453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6332510 : List Nat := [4, 4, 1, 1, 2, 2, 1, 8]
def baseStart_6332510 : Nat := 118140960795 + 6332510 * 2 ^ 59
def prefixEnd_6332510 : Nat := 4983230072969 + 3 ^ 40 * 6332510 * 2
def baseEnd_6332510 : Nat := 120430421459374972563049

theorem tailTrace_6332510 : CollatzResearch.WordTrace tailWord_6332510 prefixEnd_6332510 120430421459374972563049 := by
  unfold tailWord_6332510
  simp only [CollatzResearch.WordTrace]
  refine ⟨28870701786050656431246373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153977076192270167633313989 28870701786050656431246373)
  ·
    refine ⟨5413256584884498080858695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28870701786050656431246373 5413256584884498080858695)
    ·
      refine ⟨8119884877326747121288043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5413256584884498080858695 8119884877326747121288043)
      ·
        refine ⟨12179827315990120681932065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8119884877326747121288043 12179827315990120681932065)
        ·
          refine ⟨9134870486992590511449049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12179827315990120681932065 9134870486992590511449049)
          ·
            refine ⟨6851152865244442883586787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9134870486992590511449049 6851152865244442883586787)
            ·
              refine ⟨10276729297866664325380181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6851152865244442883586787 10276729297866664325380181)
              ·
                refine ⟨120430421459374972563049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10276729297866664325380181 120430421459374972563049)
                ·
                  rfl

theorem cell23_6332510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 8].length) (baseStart_6332510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6332510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6332510 prefixEnd_6332510 := by exact prefixLift 6332510
  have htrace : WordTrace (prefixWord ++ tailWord_6332510) baseStart_6332510 baseEnd_6332510 := by
    simpa [prefixWord, tailWord_6332510, baseEnd_6332510] using wordTrace_append hprefix tailTrace_6332510
  have hstable : (prefixWord ++ tailWord_6332510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6332510).length < 2 ^ (prefixWord ++ tailWord_6332510).sum := by decide
  have hdescent : baseEnd_6332510 < baseStart_6332510 := by decide
  rcases family_descends (prefixWord ++ tailWord_6332510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6332519 : List Nat := [1, 1, 5, 1, 1, 2, 3, 1, 2, 6]
def baseStart_6332519 : Nat := 118140960795 + 6332519 * 2 ^ 59
def prefixEnd_6332519 : Nat := 4983230072969 + 3 ^ 40 * 6332519 * 2
def baseEnd_6332519 : Nat := 1083875333576338241329927

theorem tailTrace_6332519 : CollatzResearch.WordTrace tailWord_6332519 prefixEnd_6332519 1083875333576338241329927 := by
  unfold tailWord_6332519
  simp only [CollatzResearch.WordTrace]
  refine ⟨230965942545372645987048611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153977295030248430658032407 230965942545372645987048611)
  ·
    refine ⟨346448913818058968980572917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230965942545372645987048611 346448913818058968980572917)
    ·
      refine ⟨32479585670443028341928711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 346448913818058968980572917 32479585670443028341928711)
      ·
        refine ⟨48719378505664542512893067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32479585670443028341928711 48719378505664542512893067)
        ·
          refine ⟨73079067758496813769339601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48719378505664542512893067 73079067758496813769339601)
          ·
            refine ⟨54809300818872610327004701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73079067758496813769339601 54809300818872610327004701)
            ·
              refine ⟨20553487807077228872626763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54809300818872610327004701 20553487807077228872626763)
              ·
                refine ⟨30830231710615843308940145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20553487807077228872626763 30830231710615843308940145)
                ·
                  refine ⟨23122673782961882481705109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30830231710615843308940145 23122673782961882481705109)
                  ·
                    refine ⟨1083875333576338241329927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23122673782961882481705109 1083875333576338241329927)
                    ·
                      rfl

theorem cell23_6332519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_6332519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6332519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6332519 prefixEnd_6332519 := by exact prefixLift 6332519
  have htrace : WordTrace (prefixWord ++ tailWord_6332519) baseStart_6332519 baseEnd_6332519 := by
    simpa [prefixWord, tailWord_6332519, baseEnd_6332519] using wordTrace_append hprefix tailTrace_6332519
  have hstable : (prefixWord ++ tailWord_6332519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6332519).length < 2 ^ (prefixWord ++ tailWord_6332519).sum := by decide
  have hdescent : baseEnd_6332519 < baseStart_6332519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6332519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6332529 : List Nat := [1, 2, 2, 2, 1, 1, 3, 2, 2, 4, 3]
def baseStart_6332529 : Nat := 118140960795 + 6332529 * 2 ^ 59
def prefixEnd_6332529 : Nat := 4983230072969 + 3 ^ 40 * 6332529 * 2
def baseEnd_6332529 : Nat := 3251631135535559684864735

theorem tailTrace_6332529 : CollatzResearch.WordTrace tailWord_6332529 prefixEnd_6332529 3251631135535559684864735 := by
  unfold tailWord_6332529
  simp only [CollatzResearch.WordTrace]
  refine ⟨230966307275336417694912641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153977538183557611796608427 230966307275336417694912641)
  ·
    refine ⟨173224730456502313271184481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230966307275336417694912641 173224730456502313271184481)
    ·
      refine ⟨129918547842376734953388361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173224730456502313271184481 129918547842376734953388361)
      ·
        refine ⟨97438910881782551215041271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129918547842376734953388361 97438910881782551215041271)
        ·
          refine ⟨146158366322673826822561907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97438910881782551215041271 146158366322673826822561907)
          ·
            refine ⟨219237549484010740233842861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146158366322673826822561907 219237549484010740233842861)
            ·
              refine ⟨82214081056504027587691073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 219237549484010740233842861 82214081056504027587691073)
              ·
                refine ⟨61660560792378020690768305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82214081056504027587691073 61660560792378020690768305)
                ·
                  refine ⟨46245420594283515518076229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61660560792378020690768305 46245420594283515518076229)
                  ·
                    refine ⟨8671016361428159159639293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46245420594283515518076229 8671016361428159159639293)
                    ·
                      refine ⟨3251631135535559684864735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8671016361428159159639293 3251631135535559684864735)
                      ·
                        rfl

theorem cell23_6332529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 4, 3].length) (baseStart_6332529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6332529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6332529 prefixEnd_6332529 := by exact prefixLift 6332529
  have htrace : WordTrace (prefixWord ++ tailWord_6332529) baseStart_6332529 baseEnd_6332529 := by
    simpa [prefixWord, tailWord_6332529, baseEnd_6332529] using wordTrace_append hprefix tailTrace_6332529
  have hstable : (prefixWord ++ tailWord_6332529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6332529).length < 2 ^ (prefixWord ++ tailWord_6332529).sum := by decide
  have hdescent : baseEnd_6332529 < baseStart_6332529 := by decide
  rcases family_descends (prefixWord ++ tailWord_6332529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6332576 : List Nat := [2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 3]
def baseStart_6332576 : Nat := 118140960795 + 6332576 * 2 ^ 59
def prefixEnd_6332576 : Nat := 4983230072969 + 3 ^ 40 * 6332576 * 2
def baseEnd_6332576 : Nat := 3251655269126321000977019

theorem tailTrace_6332576 : CollatzResearch.WordTrace tailWord_6332576 prefixEnd_6332576 3251655269126321000977019 := by
  unfold tailWord_6332576
  simp only [CollatzResearch.WordTrace]
  refine ⟨115484010753083072360936791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153978681004110763147915721 115484010753083072360936791)
  ·
    refine ⟨173226016129624608541405187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115484010753083072360936791 173226016129624608541405187)
    ·
      refine ⟨259839024194436912812107781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173226016129624608541405187 259839024194436912812107781)
      ·
        refine ⟨48719817036456921152270209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 259839024194436912812107781 48719817036456921152270209)
        ·
          refine ⟨36539862777342690864202657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48719817036456921152270209 36539862777342690864202657)
          ·
            refine ⟨27404897083007018148151993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36539862777342690864202657 27404897083007018148151993)
            ·
              refine ⟨20553672812255263611113995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27404897083007018148151993 20553672812255263611113995)
              ·
                refine ⟨30830509218382895416670993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20553672812255263611113995 30830509218382895416670993)
                ·
                  refine ⟨23122881913787171562503245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30830509218382895416670993 23122881913787171562503245)
                  ·
                    refine ⟨8671080717670189335938717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23122881913787171562503245 8671080717670189335938717)
                    ·
                      refine ⟨3251655269126321000977019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8671080717670189335938717 3251655269126321000977019)
                      ·
                        rfl

theorem cell23_6332576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_6332576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6332576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6332576 prefixEnd_6332576 := by exact prefixLift 6332576
  have htrace : WordTrace (prefixWord ++ tailWord_6332576) baseStart_6332576 baseEnd_6332576 := by
    simpa [prefixWord, tailWord_6332576, baseEnd_6332576] using wordTrace_append hprefix tailTrace_6332576
  have hstable : (prefixWord ++ tailWord_6332576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6332576).length < 2 ^ (prefixWord ++ tailWord_6332576).sum := by decide
  have hdescent : baseEnd_6332576 < baseStart_6332576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6332576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6332577 : List Nat := [1, 2, 3, 3, 1, 3, 3, 1, 2, 2, 2]
def baseStart_6332577 : Nat := 118140960795 + 6332577 * 2 ^ 59
def prefixEnd_6332577 : Nat := 4983230072969 + 3 ^ 40 * 6332577 * 2
def baseEnd_6332577 : Nat := 3251655782606975497064515

theorem tailTrace_6332577 : CollatzResearch.WordTrace tailWord_6332577 prefixEnd_6332577 3251655782606975497064515 := by
  unfold tailWord_6332577
  simp only [CollatzResearch.WordTrace]
  refine ⟨230968057979162521892659985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153978705319441681261773323 230968057979162521892659985)
  ·
    refine ⟨173226043484371891419494989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230968057979162521892659985 173226043484371891419494989)
    ·
      refine ⟨64959766306639459282310621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173226043484371891419494989 64959766306639459282310621)
      ·
        refine ⟨24359912364989797230866483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64959766306639459282310621 24359912364989797230866483)
        ·
          refine ⟨36539868547484695846299725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24359912364989797230866483 36539868547484695846299725)
          ·
            refine ⟨13702450705306760942362397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36539868547484695846299725 13702450705306760942362397)
            ·
              refine ⟨5138419014490035353385899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13702450705306760942362397 5138419014490035353385899)
              ·
                refine ⟨7707628521735053030078849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5138419014490035353385899 7707628521735053030078849)
                ·
                  refine ⟨5780721391301289772559137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7707628521735053030078849 5780721391301289772559137)
                  ·
                    refine ⟨4335541043475967329419353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5780721391301289772559137 4335541043475967329419353)
                    ·
                      refine ⟨3251655782606975497064515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4335541043475967329419353 3251655782606975497064515)
                      ·
                        rfl

theorem cell23_6332577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_6332577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6332577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6332577 prefixEnd_6332577 := by exact prefixLift 6332577
  have htrace : WordTrace (prefixWord ++ tailWord_6332577) baseStart_6332577 baseEnd_6332577 := by
    simpa [prefixWord, tailWord_6332577, baseEnd_6332577] using wordTrace_append hprefix tailTrace_6332577
  have hstable : (prefixWord ++ tailWord_6332577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6332577).length < 2 ^ (prefixWord ++ tailWord_6332577).sum := by decide
  have hdescent : baseEnd_6332577 < baseStart_6332577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6332577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6332683 : List Nat := [1, 1, 1, 1, 5, 2, 2, 3, 3, 1, 3]
def baseStart_6332683 : Nat := 118140960795 + 6332683 * 2 ^ 59
def prefixEnd_6332683 : Nat := 4983230072969 + 3 ^ 40 * 6332683 * 2
def baseEnd_6332683 : Nat := 3251710211556352082339027

theorem tailTrace_6332683 : CollatzResearch.WordTrace tailWord_6332683 prefixEnd_6332683 3251710211556352082339027 := by
  unfold tailWord_6332683
  simp only [CollatzResearch.WordTrace]
  refine ⟨230971924116778501996018703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153981282744519001330679135 230971924116778501996018703)
  ·
    refine ⟨346457886175167752994028055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230971924116778501996018703 346457886175167752994028055)
    ·
      refine ⟨519686829262751629491042083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346457886175167752994028055 519686829262751629491042083)
      ·
        refine ⟨779530243894127444236563125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 519686829262751629491042083 779530243894127444236563125)
        ·
          refine ⟨73080960365074447897177793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 779530243894127444236563125 73080960365074447897177793)
          ·
            refine ⟨54810720273805835922883345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73080960365074447897177793 54810720273805835922883345)
            ·
              refine ⟨41108040205354376942162509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54810720273805835922883345 41108040205354376942162509)
              ·
                refine ⟨15415515077007891353310941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41108040205354376942162509 15415515077007891353310941)
                ·
                  refine ⟨5780818153877959257491603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15415515077007891353310941 5780818153877959257491603)
                  ·
                    refine ⟨8671227230816938886237405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5780818153877959257491603 8671227230816938886237405)
                    ·
                      refine ⟨3251710211556352082339027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8671227230816938886237405 3251710211556352082339027)
                      ·
                        rfl

theorem cell23_6332683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 3, 1, 3].length) (baseStart_6332683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6332683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6332683 prefixEnd_6332683 := by exact prefixLift 6332683
  have htrace : WordTrace (prefixWord ++ tailWord_6332683) baseStart_6332683 baseEnd_6332683 := by
    simpa [prefixWord, tailWord_6332683, baseEnd_6332683] using wordTrace_append hprefix tailTrace_6332683
  have hstable : (prefixWord ++ tailWord_6332683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6332683).length < 2 ^ (prefixWord ++ tailWord_6332683).sum := by decide
  have hdescent : baseEnd_6332683 < baseStart_6332683 := by decide
  rcases family_descends (prefixWord ++ tailWord_6332683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6332686 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 5, 5]
def baseStart_6332686 : Nat := 118140960795 + 6332686 * 2 ^ 59
def prefixEnd_6332686 : Nat := 4983230072969 + 3 ^ 40 * 6332686 * 2
def baseEnd_6332686 : Nat := 1083903917332771856867171

theorem tailTrace_6332686 : CollatzResearch.WordTrace tailWord_6332686 prefixEnd_6332686 1083903917332771856867171 := by
  unfold tailWord_6332686
  simp only [CollatzResearch.WordTrace]
  refine ⟨28871504191970954188547239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153981355690511755672251941 28871504191970954188547239)
  ·
    refine ⟨43307256287956431282820859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28871504191970954188547239 43307256287956431282820859)
    ·
      refine ⟨64960884431934646924231289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43307256287956431282820859 64960884431934646924231289)
      ·
        refine ⟨48720663323950985193173467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64960884431934646924231289 48720663323950985193173467)
        ·
          refine ⟨73080994985926477789760201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48720663323950985193173467 73080994985926477789760201)
          ·
            refine ⟨54810746239444858342320151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73080994985926477789760201 54810746239444858342320151)
            ·
              refine ⟨82216119359167287513480227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54810746239444858342320151 82216119359167287513480227)
              ·
                refine ⟨123324179038750931270220341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82216119359167287513480227 123324179038750931270220341)
                ·
                  refine ⟨11561641784882899806583157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 123324179038750931270220341 11561641784882899806583157)
                  ·
                    refine ⟨1083903917332771856867171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11561641784882899806583157 1083903917332771856867171)
                    ·
                      rfl

theorem cell23_6332686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_6332686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6332686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6332686 prefixEnd_6332686 := by exact prefixLift 6332686
  have htrace : WordTrace (prefixWord ++ tailWord_6332686) baseStart_6332686 baseEnd_6332686 := by
    simpa [prefixWord, tailWord_6332686, baseEnd_6332686] using wordTrace_append hprefix tailTrace_6332686
  have hstable : (prefixWord ++ tailWord_6332686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6332686).length < 2 ^ (prefixWord ++ tailWord_6332686).sum := by decide
  have hdescent : baseEnd_6332686 < baseStart_6332686 := by decide
  rcases family_descends (prefixWord ++ tailWord_6332686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6332693 : List Nat := [1, 3, 2, 1, 2, 1, 2, 2, 4, 3, 2]
def baseStart_6332693 : Nat := 118140960795 + 6332693 * 2 ^ 59
def prefixEnd_6332693 : Nat := 4983230072969 + 3 ^ 40 * 6332693 * 2
def baseEnd_6332693 : Nat := 3251715346362897043213981

theorem tailTrace_6332693 : CollatzResearch.WordTrace tailWord_6332693 prefixEnd_6332693 3251715346362897043213981 := by
  unfold tailWord_6332693
  simp only [CollatzResearch.WordTrace]
  refine ⟨230972288846742273703882733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153981525897828182469255155 230972288846742273703882733)
  ·
    refine ⟨86614608317528352638956025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230972288846742273703882733 86614608317528352638956025)
    ·
      refine ⟨64960956238146264479217019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86614608317528352638956025 64960956238146264479217019)
      ·
        refine ⟨97441434357219396718825529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64960956238146264479217019 97441434357219396718825529)
        ·
          refine ⟨73081075767914547539119147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97441434357219396718825529 73081075767914547539119147)
          ·
            refine ⟨109621613651871821308678721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73081075767914547539119147 109621613651871821308678721)
            ·
              refine ⟨82216210238903865981509041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109621613651871821308678721 82216210238903865981509041)
              ·
                refine ⟨61662157679177899486131781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82216210238903865981509041 61662157679177899486131781)
                ·
                  refine ⟨11561654564845856153649709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61662157679177899486131781 11561654564845856153649709)
                  ·
                    refine ⟨4335620461817196057618641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11561654564845856153649709 4335620461817196057618641)
                    ·
                      refine ⟨3251715346362897043213981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4335620461817196057618641 3251715346362897043213981)
                      ·
                        rfl

theorem cell23_6332693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 4, 3, 2].length) (baseStart_6332693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6332693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6332693 prefixEnd_6332693 := by exact prefixLift 6332693
  have htrace : WordTrace (prefixWord ++ tailWord_6332693) baseStart_6332693 baseEnd_6332693 := by
    simpa [prefixWord, tailWord_6332693, baseEnd_6332693] using wordTrace_append hprefix tailTrace_6332693
  have hstable : (prefixWord ++ tailWord_6332693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6332693).length < 2 ^ (prefixWord ++ tailWord_6332693).sum := by decide
  have hdescent : baseEnd_6332693 < baseStart_6332693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6332693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6332711 : List Nat := [1, 1, 8, 1, 1, 1, 2, 3, 1, 4]
def baseStart_6332711 : Nat := 118140960795 + 6332711 * 2 ^ 59
def prefixEnd_6332711 : Nat := 4983230072969 + 3 ^ 40 * 6332711 * 2
def baseEnd_6332711 : Nat := 1083908196338225990929633

theorem tailTrace_6332711 : CollatzResearch.WordTrace tailWord_6332711 prefixEnd_6332711 1083908196338225990929633 := by
  unfold tailWord_6332711
  simp only [CollatzResearch.WordTrace]
  refine ⟨230972945360677062778037987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153981963573784708518691991 230972945360677062778037987)
  ·
    refine ⟨346459418041015594167056981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230972945360677062778037987 346459418041015594167056981)
    ·
      refine ⟨4060071305168151494145199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 346459418041015594167056981 4060071305168151494145199)
      ·
        refine ⟨6090106957752227241217799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4060071305168151494145199 6090106957752227241217799)
        ·
          refine ⟨9135160436628340861826699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6090106957752227241217799 9135160436628340861826699)
          ·
            refine ⟨13702740654942511292740049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9135160436628340861826699 13702740654942511292740049)
            ·
              refine ⟨10277055491206883469555037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13702740654942511292740049 10277055491206883469555037)
              ·
                refine ⟨3853895809202581301083139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10277055491206883469555037 3853895809202581301083139)
                ·
                  refine ⟨5780843713803871951624709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3853895809202581301083139 5780843713803871951624709)
                  ·
                    refine ⟨1083908196338225990929633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5780843713803871951624709 1083908196338225990929633)
                    ·
                      rfl

theorem cell23_6332711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_6332711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6332711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6332711 prefixEnd_6332711 := by exact prefixLift 6332711
  have htrace : WordTrace (prefixWord ++ tailWord_6332711) baseStart_6332711 baseEnd_6332711 := by
    simpa [prefixWord, tailWord_6332711, baseEnd_6332711] using wordTrace_append hprefix tailTrace_6332711
  have hstable : (prefixWord ++ tailWord_6332711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6332711).length < 2 ^ (prefixWord ++ tailWord_6332711).sum := by decide
  have hdescent : baseEnd_6332711 < baseStart_6332711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6332711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6332716 : List Nat := [2, 2, 1, 1, 1, 3, 4, 2, 1, 6]
def baseStart_6332716 : Nat := 118140960795 + 6332716 * 2 ^ 59
def prefixEnd_6332716 : Nat := 4983230072969 + 3 ^ 40 * 6332716 * 2
def baseEnd_6332716 : Nat := 1083909052139316817742125

theorem tailTrace_6332716 : CollatzResearch.WordTrace tailWord_6332716 prefixEnd_6332716 1083909052139316817742125 := by
  unfold tailWord_6332716
  simp only [CollatzResearch.WordTrace]
  refine ⟨115486563862829474315985001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153982085150439299087980001 115486563862829474315985001)
  ·
    refine ⟨86614922897122105736988751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115486563862829474315985001 86614922897122105736988751)
    ·
      refine ⟨129922384345683158605483127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86614922897122105736988751 129922384345683158605483127)
      ·
        refine ⟨194883576518524737908224691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129922384345683158605483127 194883576518524737908224691)
        ·
          refine ⟨292325364777787106862337037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194883576518524737908224691 292325364777787106862337037)
          ·
            refine ⟨109622011791670165073376389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 292325364777787106862337037 109622011791670165073376389)
            ·
              refine ⟨20554127210938155951258073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109622011791670165073376389 20554127210938155951258073)
              ·
                refine ⟨15415595408203616963443555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20554127210938155951258073 15415595408203616963443555)
                ·
                  refine ⟨23123393112305425445165333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15415595408203616963443555 23123393112305425445165333)
                  ·
                    refine ⟨1083909052139316817742125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23123393112305425445165333 1083909052139316817742125)
                    ·
                      rfl

theorem cell23_6332716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 6].length) (baseStart_6332716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6332716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6332716 prefixEnd_6332716 := by exact prefixLift 6332716
  have htrace : WordTrace (prefixWord ++ tailWord_6332716) baseStart_6332716 baseEnd_6332716 := by
    simpa [prefixWord, tailWord_6332716, baseEnd_6332716] using wordTrace_append hprefix tailTrace_6332716
  have hstable : (prefixWord ++ tailWord_6332716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6332716).length < 2 ^ (prefixWord ++ tailWord_6332716).sum := by decide
  have hdescent : baseEnd_6332716 < baseStart_6332716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6332716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6332723 : List Nat := [1, 1, 1, 2, 5, 1, 3, 3, 1, 1, 4]
def baseStart_6332723 : Nat := 118140960795 + 6332723 * 2 ^ 59
def prefixEnd_6332723 : Nat := 4983230072969 + 3 ^ 40 * 6332723 * 2
def baseEnd_6332723 : Nat := 3251730750782531925838843

theorem tailTrace_6332723 : CollatzResearch.WordTrace tailWord_6332723 prefixEnd_6332723 3251730750782531925838843 := by
  unfold tailWord_6332723
  simp only [CollatzResearch.WordTrace]
  refine ⟨230973383036633588827474823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153982255357755725884983215 230973383036633588827474823)
  ·
    refine ⟨346460074554950383241212235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230973383036633588827474823 346460074554950383241212235)
    ·
      refine ⟨519690111832425574861818353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346460074554950383241212235 519690111832425574861818353)
      ·
        refine ⟨389767583874319181146363765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 519690111832425574861818353 389767583874319181146363765)
        ·
          refine ⟨36540710988217423232471603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 389767583874319181146363765 36540710988217423232471603)
          ·
            refine ⟨54811066482326134848707405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36540710988217423232471603 54811066482326134848707405)
            ·
              refine ⟨20554149930872300568265277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54811066482326134848707405 20554149930872300568265277)
              ·
                refine ⟨7707806224077112713099479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20554149930872300568265277 7707806224077112713099479)
                ·
                  refine ⟨11561709336115669069649219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7707806224077112713099479 11561709336115669069649219)
                  ·
                    refine ⟨17342564004173503604473829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11561709336115669069649219 17342564004173503604473829)
                    ·
                      refine ⟨3251730750782531925838843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17342564004173503604473829 3251730750782531925838843)
                      ·
                        rfl

theorem cell23_6332723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 3, 1, 1, 4].length) (baseStart_6332723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6332723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6332723 prefixEnd_6332723 := by exact prefixLift 6332723
  have htrace : WordTrace (prefixWord ++ tailWord_6332723) baseStart_6332723 baseEnd_6332723 := by
    simpa [prefixWord, tailWord_6332723, baseEnd_6332723] using wordTrace_append hprefix tailTrace_6332723
  have hstable : (prefixWord ++ tailWord_6332723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6332723).length < 2 ^ (prefixWord ++ tailWord_6332723).sum := by decide
  have hdescent : baseEnd_6332723 < baseStart_6332723 := by decide
  rcases family_descends (prefixWord ++ tailWord_6332723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6332753 : List Nat := [1, 2, 2, 1, 4, 2, 3, 1, 1, 2, 4]
def baseStart_6332753 : Nat := 118140960795 + 6332753 * 2 ^ 59
def prefixEnd_6332753 : Nat := 4983230072969 + 3 ^ 40 * 6332753 * 2
def baseEnd_6332753 : Nat := 3251746155202166808463705

theorem tailTrace_6332753 : CollatzResearch.WordTrace tailWord_6332753 prefixEnd_6332753 3251746155202166808463705 := by
  unfold tailWord_6332753
  simp only [CollatzResearch.WordTrace]
  refine ⟨230974477226524903951066913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153982984817683269300711275 230974477226524903951066913)
  ·
    refine ⟨173230857919893677963300185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230974477226524903951066913 173230857919893677963300185)
    ·
      refine ⟨129923143439920258472475139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173230857919893677963300185 129923143439920258472475139)
      ·
        refine ⟨194884715159880387708712709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129923143439920258472475139 194884715159880387708712709)
        ·
          refine ⟨36540884092477572695383633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194884715159880387708712709 36540884092477572695383633)
          ·
            refine ⟨27405663069358179521537725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36540884092477572695383633 27405663069358179521537725)
            ·
              refine ⟨10277123651009317320576647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27405663069358179521537725 10277123651009317320576647)
              ·
                refine ⟨15415685476513975980864971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10277123651009317320576647 15415685476513975980864971)
                ·
                  refine ⟨23123528214770963971297457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15415685476513975980864971 23123528214770963971297457)
                  ·
                    refine ⟨17342646161078222978473093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23123528214770963971297457 17342646161078222978473093)
                    ·
                      refine ⟨3251746155202166808463705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17342646161078222978473093 3251746155202166808463705)
                      ·
                        rfl

theorem cell23_6332753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 2, 4].length) (baseStart_6332753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6332753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6332753 prefixEnd_6332753 := by exact prefixLift 6332753
  have htrace : WordTrace (prefixWord ++ tailWord_6332753) baseStart_6332753 baseEnd_6332753 := by
    simpa [prefixWord, tailWord_6332753, baseEnd_6332753] using wordTrace_append hprefix tailTrace_6332753
  have hstable : (prefixWord ++ tailWord_6332753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6332753).length < 2 ^ (prefixWord ++ tailWord_6332753).sum := by decide
  have hdescent : baseEnd_6332753 < baseStart_6332753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6332753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6332834 : List Nat := [3, 3, 1, 2, 1, 1, 5, 1, 1, 3, 2]
def baseStart_6332834 : Nat := 118140960795 + 6332834 * 2 ^ 59
def prefixEnd_6332834 : Nat := 4983230072969 + 3 ^ 40 * 6332834 * 2
def baseEnd_6332834 : Nat := 3251787747135180991550833

theorem tailTrace_6332834 : CollatzResearch.WordTrace tailWord_6332834 prefixEnd_6332834 3251787747135180991550833 := by
  unfold tailWord_6332834
  simp only [CollatzResearch.WordTrace]
  refine ⟨57744357884807863696191389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153984954359487636523177037 57744357884807863696191389)
  ·
    refine ⟨21654134206802948886071771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57744357884807863696191389 21654134206802948886071771)
    ·
      refine ⟨32481201310204423329107657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21654134206802948886071771 32481201310204423329107657)
      ·
        refine ⟨24360900982653317496830743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32481201310204423329107657 24360900982653317496830743)
        ·
          refine ⟨36541351473979976245246115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24360900982653317496830743 36541351473979976245246115)
          ·
            refine ⟨54812027210969964367869173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36541351473979976245246115 54812027210969964367869173)
            ·
              refine ⟨5138627551028434159487735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54812027210969964367869173 5138627551028434159487735)
              ·
                refine ⟨7707941326542651239231603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5138627551028434159487735 7707941326542651239231603)
                ·
                  refine ⟨11561911989813976858847405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7707941326542651239231603 11561911989813976858847405)
                  ·
                    refine ⟨4335716996180241322067777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11561911989813976858847405 4335716996180241322067777)
                    ·
                      refine ⟨3251787747135180991550833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4335716996180241322067777 3251787747135180991550833)
                      ·
                        rfl

theorem cell23_6332834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_6332834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6332834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6332834 prefixEnd_6332834 := by exact prefixLift 6332834
  have htrace : WordTrace (prefixWord ++ tailWord_6332834) baseStart_6332834 baseEnd_6332834 := by
    simpa [prefixWord, tailWord_6332834, baseEnd_6332834] using wordTrace_append hprefix tailTrace_6332834
  have hstable : (prefixWord ++ tailWord_6332834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6332834).length < 2 ^ (prefixWord ++ tailWord_6332834).sum := by decide
  have hdescent : baseEnd_6332834 < baseStart_6332834 := by decide
  rcases family_descends (prefixWord ++ tailWord_6332834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6332842 : List Nat := [3, 1, 6, 1, 1, 2, 2, 2, 1, 2, 2]
def baseStart_6332842 : Nat := 118140960795 + 6332842 * 2 ^ 59
def prefixEnd_6332842 : Nat := 4983230072969 + 3 ^ 40 * 6332842 * 2
def baseEnd_6332842 : Nat := 3251791854980416960250797

theorem tailTrace_6332842 : CollatzResearch.WordTrace tailWord_6332842 prefixEnd_6332842 3251791854980416960250797 := by
  unfold tailWord_6332842
  simp only [CollatzResearch.WordTrace]
  refine ⟨57744430830800618037764195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153985148882134981434037853 57744430830800618037764195)
  ·
    refine ⟨86616646246200927056646293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57744430830800618037764195 86616646246200927056646293)
    ·
      refine ⟨4060155292790668455780295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 86616646246200927056646293 4060155292790668455780295)
      ·
        refine ⟨6090232939186002683670443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4060155292790668455780295 6090232939186002683670443)
        ·
          refine ⟨9135349408779004025505665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6090232939186002683670443 9135349408779004025505665)
          ·
            refine ⟨6851512056584253019129249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9135349408779004025505665 6851512056584253019129249)
            ·
              refine ⟨5138634042438189764346937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6851512056584253019129249 5138634042438189764346937)
              ·
                refine ⟨3853975531828642323260203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5138634042438189764346937 3853975531828642323260203)
                ·
                  refine ⟨5780963297742963484890305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3853975531828642323260203 5780963297742963484890305)
                  ·
                    refine ⟨4335722473307222613667729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5780963297742963484890305 4335722473307222613667729)
                    ·
                      refine ⟨3251791854980416960250797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4335722473307222613667729 3251791854980416960250797)
                      ·
                        rfl

theorem cell23_6332842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_6332842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6332842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6332842 prefixEnd_6332842 := by exact prefixLift 6332842
  have htrace : WordTrace (prefixWord ++ tailWord_6332842) baseStart_6332842 baseEnd_6332842 := by
    simpa [prefixWord, tailWord_6332842, baseEnd_6332842] using wordTrace_append hprefix tailTrace_6332842
  have hstable : (prefixWord ++ tailWord_6332842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6332842).length < 2 ^ (prefixWord ++ tailWord_6332842).sum := by decide
  have hdescent : baseEnd_6332842 < baseStart_6332842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6332842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6332856 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 2, 1, 8]
def baseStart_6332856 : Nat := 118140960795 + 6332856 * 2 ^ 59
def prefixEnd_6332856 : Nat := 4983230072969 + 3 ^ 40 * 6332856 * 2
def baseEnd_6332856 : Nat := 3251799043709579905475731

theorem tailTrace_6332856 : CollatzResearch.WordTrace tailWord_6332856 prefixEnd_6332856 3251799043709579905475731 := by
  unfold tailWord_6332856
  simp only [CollatzResearch.WordTrace]
  refine ⟨115489116972575876271033211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153985489296767835028044281 115489116972575876271033211)
  ·
    refine ⟨173233675458863814406549817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115489116972575876271033211 173233675458863814406549817)
    ·
      refine ⟨129925256594147860804912363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173233675458863814406549817 129925256594147860804912363)
      ·
        refine ⟨194887884891221791207368545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129925256594147860804912363 194887884891221791207368545)
        ·
          refine ⟨146165913668416343405526409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194887884891221791207368545 146165913668416343405526409)
          ·
            refine ⟨109624435251312257554144807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146165913668416343405526409 109624435251312257554144807)
            ·
              refine ⟨164436652876968386331217211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109624435251312257554144807 164436652876968386331217211)
              ·
                refine ⟨246654979315452579496825817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164436652876968386331217211 246654979315452579496825817)
                ·
                  refine ⟨184991234486589434622619363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 246654979315452579496825817 184991234486589434622619363)
                  ·
                    refine ⟨277486851729884151933929045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 184991234486589434622619363 277486851729884151933929045)
                    ·
                      refine ⟨3251799043709579905475731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 277486851729884151933929045 3251799043709579905475731)
                      ·
                        rfl

theorem cell23_6332856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_6332856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6332856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6332856 prefixEnd_6332856 := by exact prefixLift 6332856
  have htrace : WordTrace (prefixWord ++ tailWord_6332856) baseStart_6332856 baseEnd_6332856 := by
    simpa [prefixWord, tailWord_6332856, baseEnd_6332856] using wordTrace_append hprefix tailTrace_6332856
  have hstable : (prefixWord ++ tailWord_6332856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6332856).length < 2 ^ (prefixWord ++ tailWord_6332856).sum := by decide
  have hdescent : baseEnd_6332856 < baseStart_6332856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6332856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6332860 : List Nat := [2, 2, 2, 4, 1, 2, 1, 1, 2, 2, 4]
def baseStart_6332860 : Nat := 118140960795 + 6332860 * 2 ^ 59
def prefixEnd_6332860 : Nat := 4983230072969 + 3 ^ 40 * 6332860 * 2
def baseEnd_6332860 : Nat := 3251801097632197889825713

theorem tailTrace_6332860 : CollatzResearch.WordTrace tailWord_6332860 prefixEnd_6332860 3251801097632197889825713 := by
  unfold tailWord_6332860
  simp only [CollatzResearch.WordTrace]
  refine ⟨115489189918568630612606017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153985586558091507483474689 115489189918568630612606017)
  ·
    refine ⟨86616892438926472959454513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115489189918568630612606017 86616892438926472959454513)
    ·
      refine ⟨64962669329194854719590885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86616892438926472959454513 64962669329194854719590885)
      ·
        refine ⟨12180500499224035259923291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64962669329194854719590885 12180500499224035259923291)
        ·
          refine ⟨18270750748836052889884937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12180500499224035259923291 18270750748836052889884937)
          ·
            refine ⟨13703063061627039667413703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18270750748836052889884937 13703063061627039667413703)
            ·
              refine ⟨20554594592440559501120555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13703063061627039667413703 20554594592440559501120555)
              ·
                refine ⟨30831891888660839251680833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20554594592440559501120555 30831891888660839251680833)
                ·
                  refine ⟨23123918916495629438760625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30831891888660839251680833 23123918916495629438760625)
                  ·
                    refine ⟨17342939187371722079070469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23123918916495629438760625 17342939187371722079070469)
                    ·
                      refine ⟨3251801097632197889825713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17342939187371722079070469 3251801097632197889825713)
                      ·
                        rfl

theorem cell23_6332860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_6332860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6332860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6332860 prefixEnd_6332860 := by exact prefixLift 6332860
  have htrace : WordTrace (prefixWord ++ tailWord_6332860) baseStart_6332860 baseEnd_6332860 := by
    simpa [prefixWord, tailWord_6332860, baseEnd_6332860] using wordTrace_append hprefix tailTrace_6332860
  have hstable : (prefixWord ++ tailWord_6332860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6332860).length < 2 ^ (prefixWord ++ tailWord_6332860).sum := by decide
  have hdescent : baseEnd_6332860 < baseStart_6332860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6332860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6332920 : List Nat := [2, 1, 2, 1, 1, 4, 1, 3, 2, 4, 2]
def baseStart_6332920 : Nat := 118140960795 + 6332920 * 2 ^ 59
def prefixEnd_6332920 : Nat := 4983230072969 + 3 ^ 40 * 6332920 * 2
def baseEnd_6332920 : Nat := 3251831906471467655075437

theorem tailTrace_6332920 : CollatzResearch.WordTrace tailWord_6332920 prefixEnd_6332920 3251831906471467655075437 := by
  unfold tailWord_6332920
  simp only [CollatzResearch.WordTrace]
  refine ⟨115490284108459945736198107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153987045477946594314930809 115490284108459945736198107)
  ·
    refine ⟨173235426162689918604297161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115490284108459945736198107 173235426162689918604297161)
    ·
      refine ⟨129926569622017438953222871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173235426162689918604297161 129926569622017438953222871)
      ·
        refine ⟨194889854433026158429834307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129926569622017438953222871 194889854433026158429834307)
        ·
          refine ⟨292334781649539237644751461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194889854433026158429834307 292334781649539237644751461)
          ·
            refine ⟨54812771559288607058390899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 292334781649539237644751461 54812771559288607058390899)
            ·
              refine ⟨82219157338932910587586349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54812771559288607058390899 82219157338932910587586349)
              ·
                refine ⟨30832184002099841470344881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82219157338932910587586349 30832184002099841470344881)
                ·
                  refine ⟨23124138001574881102758661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30832184002099841470344881 23124138001574881102758661)
                  ·
                    refine ⟨4335775875295290206767249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23124138001574881102758661 4335775875295290206767249)
                    ·
                      refine ⟨3251831906471467655075437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4335775875295290206767249 3251831906471467655075437)
                      ·
                        rfl

theorem cell23_6332920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 2, 4, 2].length) (baseStart_6332920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6332920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6332920 prefixEnd_6332920 := by exact prefixLift 6332920
  have htrace : WordTrace (prefixWord ++ tailWord_6332920) baseStart_6332920 baseEnd_6332920 := by
    simpa [prefixWord, tailWord_6332920, baseEnd_6332920] using wordTrace_append hprefix tailTrace_6332920
  have hstable : (prefixWord ++ tailWord_6332920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6332920).length < 2 ^ (prefixWord ++ tailWord_6332920).sum := by decide
  have hdescent : baseEnd_6332920 < baseStart_6332920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6332920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6332934 : List Nat := [6, 2, 1, 1, 1, 1, 2, 1, 1, 7]
def baseStart_6332934 : Nat := 118140960795 + 6332934 * 2 ^ 59
def prefixEnd_6332934 : Nat := 4983230072969 + 3 ^ 40 * 6332934 * 2
def baseEnd_6332934 : Nat := 1083946365066876866766791

theorem tailTrace_6332934 : CollatzResearch.WordTrace tailWord_6332934 prefixEnd_6332934 1083946365066876866766791 := by
  unfold tailWord_6332934
  simp only [CollatzResearch.WordTrace]
  refine ⟨7218158713714661620731433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 153987385892579447908937237 7218158713714661620731433)
  ·
    refine ⟨5413619035285996215548575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7218158713714661620731433 5413619035285996215548575)
    ·
      refine ⟨8120428552928994323322863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5413619035285996215548575 8120428552928994323322863)
      ·
        refine ⟨12180642829393491484984295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8120428552928994323322863 12180642829393491484984295)
        ·
          refine ⟨18270964244090237227476443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12180642829393491484984295 18270964244090237227476443)
          ·
            refine ⟨27406446366135355841214665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18270964244090237227476443 27406446366135355841214665)
            ·
              refine ⟨20554834774601516880910999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27406446366135355841214665 20554834774601516880910999)
              ·
                refine ⟨30832252161902275321366499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20554834774601516880910999 30832252161902275321366499)
                ·
                  refine ⟨46248378242853412982049749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30832252161902275321366499 46248378242853412982049749)
                  ·
                    refine ⟨1083946365066876866766791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46248378242853412982049749 1083946365066876866766791)
                    ·
                      rfl

theorem cell23_6332934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_6332934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6332934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6332934 prefixEnd_6332934 := by exact prefixLift 6332934
  have htrace : WordTrace (prefixWord ++ tailWord_6332934) baseStart_6332934 baseEnd_6332934 := by
    simpa [prefixWord, tailWord_6332934, baseEnd_6332934] using wordTrace_append hprefix tailTrace_6332934
  have hstable : (prefixWord ++ tailWord_6332934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6332934).length < 2 ^ (prefixWord ++ tailWord_6332934).sum := by decide
  have hdescent : baseEnd_6332934 < baseStart_6332934 := by decide
  rcases family_descends (prefixWord ++ tailWord_6332934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6332940 : List Nat := [2, 2, 1, 2, 4, 1, 2, 1, 1, 4, 3]
def baseStart_6332940 : Nat := 118140960795 + 6332940 * 2 ^ 59
def prefixEnd_6332940 : Nat := 4983230072969 + 3 ^ 40 * 6332940 * 2
def baseEnd_6332940 : Nat := 3251842176084557576825345

theorem tailTrace_6332940 : CollatzResearch.WordTrace tailWord_6332940 prefixEnd_6332940 3251842176084557576825345 := by
  unfold tailWord_6332940
  simp only [CollatzResearch.WordTrace]
  refine ⟨115490648838423717444062137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153987531784564956592082849 115490648838423717444062137)
  ·
    refine ⟨86617986628817788083046603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115490648838423717444062137 86617986628817788083046603)
    ·
      refine ⟨129926979943226682124569905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86617986628817788083046603 129926979943226682124569905)
      ·
        refine ⟨97445234957420011593427429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129926979943226682124569905 97445234957420011593427429)
        ·
          refine ⟨18270981554516252173767643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97445234957420011593427429 18270981554516252173767643)
          ·
            refine ⟨27406472331774378260651465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18270981554516252173767643 27406472331774378260651465)
            ·
              refine ⟨20554854248830783695488599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27406472331774378260651465 20554854248830783695488599)
              ·
                refine ⟨30832281373246175543232899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20554854248830783695488599 30832281373246175543232899)
                ·
                  refine ⟨46248422059869263314849349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30832281373246175543232899 46248422059869263314849349)
                  ·
                    refine ⟨8671579136225486871534253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46248422059869263314849349 8671579136225486871534253)
                    ·
                      refine ⟨3251842176084557576825345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8671579136225486871534253 3251842176084557576825345)
                      ·
                        rfl

theorem cell23_6332940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 1, 4, 3].length) (baseStart_6332940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6332940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6332940 prefixEnd_6332940 := by exact prefixLift 6332940
  have htrace : WordTrace (prefixWord ++ tailWord_6332940) baseStart_6332940 baseEnd_6332940 := by
    simpa [prefixWord, tailWord_6332940, baseEnd_6332940] using wordTrace_append hprefix tailTrace_6332940
  have hstable : (prefixWord ++ tailWord_6332940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6332940).length < 2 ^ (prefixWord ++ tailWord_6332940).sum := by decide
  have hdescent : baseEnd_6332940 < baseStart_6332940 := by decide
  rcases family_descends (prefixWord ++ tailWord_6332940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6332953 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 1, 7, 3]
def baseStart_6332953 : Nat := 118140960795 + 6332953 * 2 ^ 59
def prefixEnd_6332953 : Nat := 4983230072969 + 3 ^ 40 * 6332953 * 2
def baseEnd_6332953 : Nat := 3251848851333066025962785

theorem tailTrace_6332953 : CollatzResearch.WordTrace tailWord_6332953 prefixEnd_6332953 3251848851333066025962785 := by
  unfold tailWord_6332953
  simp only [CollatzResearch.WordTrace]
  refine ⟨230981771825800338108347513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153987847883866892072231675 230981771825800338108347513)
  ·
    refine ⟨173236328869350253581260635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230981771825800338108347513 173236328869350253581260635)
    ·
      refine ⟨259854493304025380371890953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173236328869350253581260635 259854493304025380371890953)
      ·
        refine ⟨194890869978019035278918215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259854493304025380371890953 194890869978019035278918215)
        ·
          refine ⟨292336304967028552918377323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194890869978019035278918215 292336304967028552918377323)
          ·
            refine ⟨438504457450542829377565985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292336304967028552918377323 438504457450542829377565985)
            ·
              refine ⟨328878343087907122033174489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 438504457450542829377565985 328878343087907122033174489)
              ·
                refine ⟨246658757315930341524880867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 328878343087907122033174489 246658757315930341524880867)
                ·
                  refine ⟨369988135973895512287321301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 246658757315930341524880867 369988135973895512287321301)
                  ·
                    refine ⟨8671596936888176069234093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 369988135973895512287321301 8671596936888176069234093)
                    ·
                      refine ⟨3251848851333066025962785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8671596936888176069234093 3251848851333066025962785)
                      ·
                        rfl

theorem cell23_6332953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 7, 3].length) (baseStart_6332953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6332953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6332953 prefixEnd_6332953 := by exact prefixLift 6332953
  have htrace : WordTrace (prefixWord ++ tailWord_6332953) baseStart_6332953 baseEnd_6332953 := by
    simpa [prefixWord, tailWord_6332953, baseEnd_6332953] using wordTrace_append hprefix tailTrace_6332953
  have hstable : (prefixWord ++ tailWord_6332953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6332953).length < 2 ^ (prefixWord ++ tailWord_6332953).sum := by decide
  have hdescent : baseEnd_6332953 < baseStart_6332953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6332953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6332957 : List Nat := [1, 4, 2, 2, 1, 3, 1, 2, 2, 2, 3]
def baseStart_6332957 : Nat := 118140960795 + 6332957 * 2 ^ 59
def prefixEnd_6332957 : Nat := 4983230072969 + 3 ^ 40 * 6332957 * 2
def baseEnd_6332957 : Nat := 3251850905255684010312767

theorem tailTrace_6332957 : CollatzResearch.WordTrace tailWord_6332957 prefixEnd_6332957 3251850905255684010312767 := by
  unfold tailWord_6332957
  simp only [CollatzResearch.WordTrace]
  refine ⟨230981917717785846791493125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153987945145190564527662083 230981917717785846791493125)
  ·
    refine ⟨43309109572084846273404961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230981917717785846791493125 43309109572084846273404961)
    ·
      refine ⟨32481832179063634705053721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43309109572084846273404961 32481832179063634705053721)
      ·
        refine ⟨24361374134297726028790291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32481832179063634705053721 24361374134297726028790291)
        ·
          refine ⟨36542061201446589043185437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24361374134297726028790291 36542061201446589043185437)
          ·
            refine ⟨13703272950542470891194539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36542061201446589043185437 13703272950542470891194539)
            ·
              refine ⟨20554909425813706336791809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13703272950542470891194539 20554909425813706336791809)
              ·
                refine ⟨15416182069360279752593857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20554909425813706336791809 15416182069360279752593857)
                ·
                  refine ⟨11562136552020209814445393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15416182069360279752593857 11562136552020209814445393)
                  ·
                    refine ⟨8671602414015157360834045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11562136552020209814445393 8671602414015157360834045)
                    ·
                      refine ⟨3251850905255684010312767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8671602414015157360834045 3251850905255684010312767)
                      ·
                        rfl

theorem cell23_6332957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_6332957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6332957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6332957 prefixEnd_6332957 := by exact prefixLift 6332957
  have htrace : WordTrace (prefixWord ++ tailWord_6332957) baseStart_6332957 baseEnd_6332957 := by
    simpa [prefixWord, tailWord_6332957, baseEnd_6332957] using wordTrace_append hprefix tailTrace_6332957
  have hstable : (prefixWord ++ tailWord_6332957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6332957).length < 2 ^ (prefixWord ++ tailWord_6332957).sum := by decide
  have hdescent : baseEnd_6332957 < baseStart_6332957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6332957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6332997 : List Nat := [1, 3, 1, 1, 1, 5, 1, 3, 2, 3, 2]
def baseStart_6332997 : Nat := 118140960795 + 6332997 * 2 ^ 59
def prefixEnd_6332997 : Nat := 4983230072969 + 3 ^ 40 * 6332997 * 2
def baseEnd_6332997 : Nat := 3251871444481863853812583

theorem tailTrace_6332997 : CollatzResearch.WordTrace tailWord_6332997 prefixEnd_6332997 3251871444481863853812583 := by
  unfold tailWord_6332997
  simp only [CollatzResearch.WordTrace]
  refine ⟨230983376637640933622949245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153988917758427289081966163 230983376637640933622949245)
  ·
    refine ⟨86618766239115350108605967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230983376637640933622949245 86618766239115350108605967)
    ·
      refine ⟨129928149358673025162908951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86618766239115350108605967 129928149358673025162908951)
      ·
        refine ⟨194892224038009537744363427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129928149358673025162908951 194892224038009537744363427)
        ·
          refine ⟨292338336057014306616545141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194892224038009537744363427 292338336057014306616545141)
          ·
            refine ⟨27406719005345091245301107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 292338336057014306616545141 27406719005345091245301107)
            ·
              refine ⟨41110078508017636867951661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27406719005345091245301107 41110078508017636867951661)
              ·
                refine ⟨15416279440506613825481873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41110078508017636867951661 15416279440506613825481873)
                ·
                  refine ⟨11562209580379960369111405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15416279440506613825481873 11562209580379960369111405)
                  ·
                    refine ⟨4335828592642485138416777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11562209580379960369111405 4335828592642485138416777)
                    ·
                      refine ⟨3251871444481863853812583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4335828592642485138416777 3251871444481863853812583)
                      ·
                        rfl

theorem cell23_6332997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 2, 3, 2].length) (baseStart_6332997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6332997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6332997 prefixEnd_6332997 := by exact prefixLift 6332997
  have htrace : WordTrace (prefixWord ++ tailWord_6332997) baseStart_6332997 baseEnd_6332997 := by
    simpa [prefixWord, tailWord_6332997, baseEnd_6332997] using wordTrace_append hprefix tailTrace_6332997
  have hstable : (prefixWord ++ tailWord_6332997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6332997).length < 2 ^ (prefixWord ++ tailWord_6332997).sum := by decide
  have hdescent : baseEnd_6332997 < baseStart_6332997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6332997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333003 : List Nat := [1, 1, 1, 1, 3, 1, 5, 1, 3, 6]
def baseStart_6333003 : Nat := 118140960795 + 6333003 * 2 ^ 59
def prefixEnd_6333003 : Nat := 4983230072969 + 3 ^ 40 * 6333003 * 2
def baseEnd_6333003 : Nat := 1083958175121930276779185

theorem tailTrace_6333003 : CollatzResearch.WordTrace tailWord_6333003 prefixEnd_6333003 1083958175121930276779185 := by
  unfold tailWord_6333003
  simp only [CollatzResearch.WordTrace]
  refine ⟨230983595475619196647667663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153989063650412797765111775 230983595475619196647667663)
  ·
    refine ⟨346475393213428794971501495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230983595475619196647667663 346475393213428794971501495)
    ·
      refine ⟨519713089820143192457252243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346475393213428794971501495 519713089820143192457252243)
      ·
        refine ⟨779569634730214788685878365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 519713089820143192457252243 779569634730214788685878365)
        ·
          refine ⟨292338613023830545757204387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 779569634730214788685878365 292338613023830545757204387)
          ·
            refine ⟨438507919535745818635806581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292338613023830545757204387 438507919535745818635806581)
            ·
              refine ⟨41110117456476170497106867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 438507919535745818635806581 41110117456476170497106867)
              ·
                refine ⟨61665176184714255745660301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41110117456476170497106867 61665176184714255745660301)
                ·
                  refine ⟨23124441069267845904622613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61665176184714255745660301 23124441069267845904622613)
                  ·
                    refine ⟨1083958175121930276779185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23124441069267845904622613 1083958175121930276779185)
                    ·
                      rfl

theorem cell23_6333003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 6].length) (baseStart_6333003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333003 prefixEnd_6333003 := by exact prefixLift 6333003
  have htrace : WordTrace (prefixWord ++ tailWord_6333003) baseStart_6333003 baseEnd_6333003 := by
    simpa [prefixWord, tailWord_6333003, baseEnd_6333003] using wordTrace_append hprefix tailTrace_6333003
  have hstable : (prefixWord ++ tailWord_6333003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333003).length < 2 ^ (prefixWord ++ tailWord_6333003).sum := by decide
  have hdescent : baseEnd_6333003 < baseStart_6333003 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333004 : List Nat := [2, 2, 1, 3, 1, 2, 2, 5, 1, 1, 3]
def baseStart_6333004 : Nat := 118140960795 + 6333004 * 2 ^ 59
def prefixEnd_6333004 : Nat := 4983230072969 + 3 ^ 40 * 6333004 * 2
def baseEnd_6333004 : Nat := 3251875038846445326425051

theorem tailTrace_6333004 : CollatzResearch.WordTrace tailWord_6333004 prefixEnd_6333004 3251875038846445326425051 := by
  unfold tailWord_6333004
  simp only [CollatzResearch.WordTrace]
  refine ⟨115491815974307786909227033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153989087965743715878969377 115491815974307786909227033)
  ·
    refine ⟨86618861980730840181920275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115491815974307786909227033 86618861980730840181920275)
    ·
      refine ⟨129928292971096260272880413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86618861980730840181920275 129928292971096260272880413)
      ·
        refine ⟨48723109864161097602330155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129928292971096260272880413 48723109864161097602330155)
        ·
          refine ⟨73084664796241646403495233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48723109864161097602330155 73084664796241646403495233)
          ·
            refine ⟨54813498597181234802621425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73084664796241646403495233 54813498597181234802621425)
            ·
              refine ⟨41110123947885926101966069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54813498597181234802621425 41110123947885926101966069)
              ·
                refine ⟨3854074120114305572059319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41110123947885926101966069 3854074120114305572059319)
                ·
                  refine ⟨5781111180171458358088979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3854074120114305572059319 5781111180171458358088979)
                  ·
                    refine ⟨8671666770257187537133469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5781111180171458358088979 8671666770257187537133469)
                    ·
                      refine ⟨3251875038846445326425051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8671666770257187537133469 3251875038846445326425051)
                      ·
                        rfl

theorem cell23_6333004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 5, 1, 1, 3].length) (baseStart_6333004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333004 prefixEnd_6333004 := by exact prefixLift 6333004
  have htrace : WordTrace (prefixWord ++ tailWord_6333004) baseStart_6333004 baseEnd_6333004 := by
    simpa [prefixWord, tailWord_6333004, baseEnd_6333004] using wordTrace_append hprefix tailTrace_6333004
  have hstable : (prefixWord ++ tailWord_6333004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333004).length < 2 ^ (prefixWord ++ tailWord_6333004).sum := by decide
  have hdescent : baseEnd_6333004 < baseStart_6333004 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333023 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 6]
def baseStart_6333023 : Nat := 118140960795 + 6333023 * 2 ^ 59
def prefixEnd_6333023 : Nat := 4983230072969 + 3 ^ 40 * 6333023 * 2
def baseEnd_6333023 : Nat := 3251884794978880752087463

theorem tailTrace_6333023 : CollatzResearch.WordTrace tailWord_6333023 prefixEnd_6333023 3251884794978880752087463 := by
  unfold tailWord_6333023
  simp only [CollatzResearch.WordTrace]
  refine ⟨230984324935546740063395723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153989549957031160042263815 230984324935546740063395723)
  ·
    refine ⟨346476487403320110095093585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230984324935546740063395723 346476487403320110095093585)
    ·
      refine ⟨259857365552490082571320189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346476487403320110095093585 259857365552490082571320189)
      ·
        refine ⟨97446512082183780964245071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259857365552490082571320189 97446512082183780964245071)
        ·
          refine ⟨146169768123275671446367607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97446512082183780964245071 146169768123275671446367607)
          ·
            refine ⟨219254652184913507169551411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146169768123275671446367607 219254652184913507169551411)
            ·
              refine ⟨328881978277370260754327117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219254652184913507169551411 328881978277370260754327117)
              ·
                refine ⟨123330741854013847782872669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 328881978277370260754327117 123330741854013847782872669)
                ·
                  refine ⟨46249028195255192918577251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123330741854013847782872669 46249028195255192918577251)
                  ·
                    refine ⟨69373542292882789377865877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46249028195255192918577251 69373542292882789377865877)
                    ·
                      refine ⟨3251884794978880752087463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69373542292882789377865877 3251884794978880752087463)
                      ·
                        rfl

theorem cell23_6333023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_6333023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333023 prefixEnd_6333023 := by exact prefixLift 6333023
  have htrace : WordTrace (prefixWord ++ tailWord_6333023) baseStart_6333023 baseEnd_6333023 := by
    simpa [prefixWord, tailWord_6333023, baseEnd_6333023] using wordTrace_append hprefix tailTrace_6333023
  have hstable : (prefixWord ++ tailWord_6333023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333023).length < 2 ^ (prefixWord ++ tailWord_6333023).sum := by decide
  have hdescent : baseEnd_6333023 < baseStart_6333023 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333037 : List Nat := [1, 5, 1, 1, 3, 2, 2, 1, 1, 6]
def baseStart_6333037 : Nat := 118140960795 + 6333037 * 2 ^ 59
def prefixEnd_6333037 : Nat := 4983230072969 + 3 ^ 40 * 6333037 * 2
def baseEnd_6333037 : Nat := 1083963994569347899104133

theorem tailTrace_6333037 : CollatzResearch.WordTrace tailWord_6333037 prefixEnd_6333037 1083963994569347899104133 := by
  unfold tailWord_6333037
  simp only [CollatzResearch.WordTrace]
  refine ⟨230984835557496020454405365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153989890371664013636270243 230984835557496020454405365)
  ·
    refine ⟨21654828333515251917600503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 230984835557496020454405365 21654828333515251917600503)
    ·
      refine ⟨32482242500272877876400755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21654828333515251917600503 32482242500272877876400755)
      ·
        refine ⟨48723363750409316814601133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32482242500272877876400755 48723363750409316814601133)
        ·
          refine ⟨18271261406403493805475425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48723363750409316814601133 18271261406403493805475425)
          ·
            refine ⟨13703446054802620354106569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18271261406403493805475425 13703446054802620354106569)
            ·
              refine ⟨10277584541101965265579927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13703446054802620354106569 10277584541101965265579927)
              ·
                refine ⟨15416376811652947898369891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10277584541101965265579927 15416376811652947898369891)
                ·
                  refine ⟨23124565217479421847554837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15416376811652947898369891 23124565217479421847554837)
                  ·
                    refine ⟨1083963994569347899104133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23124565217479421847554837 1083963994569347899104133)
                    ·
                      rfl

theorem cell23_6333037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_6333037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333037 prefixEnd_6333037 := by exact prefixLift 6333037
  have htrace : WordTrace (prefixWord ++ tailWord_6333037) baseStart_6333037 baseEnd_6333037 := by
    simpa [prefixWord, tailWord_6333037, baseEnd_6333037] using wordTrace_append hprefix tailTrace_6333037
  have hstable : (prefixWord ++ tailWord_6333037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333037).length < 2 ^ (prefixWord ++ tailWord_6333037).sum := by decide
  have hdescent : baseEnd_6333037 < baseStart_6333037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333058 : List Nat := [3, 4, 3, 1, 1, 1, 1, 3, 1, 5]
def baseStart_6333058 : Nat := 118140960795 + 6333058 * 2 ^ 59
def prefixEnd_6333058 : Nat := 4983230072969 + 3 ^ 40 * 6333058 * 2
def baseEnd_6333058 : Nat := 1083967588933929371716601

theorem tailTrace_6333058 : CollatzResearch.WordTrace tailWord_6333058 prefixEnd_6333058 1083967588933929371716601 := by
  unfold tailWord_6333058
  simp only [CollatzResearch.WordTrace]
  refine ⟨57746400372604985260229957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153990400993613294027279885 57746400372604985260229957)
  ·
    refine ⟨10827450069863434736293117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57746400372604985260229957 10827450069863434736293117)
    ·
      refine ⟨4060293776198788026109919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10827450069863434736293117 4060293776198788026109919)
      ·
        refine ⟨6090440664298182039164879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4060293776198788026109919 6090440664298182039164879)
        ·
          refine ⟨9135660996447273058747319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6090440664298182039164879 9135660996447273058747319)
          ·
            refine ⟨13703491494670909588120979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9135660996447273058747319 13703491494670909588120979)
            ·
              refine ⟨20555237242006364382181469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13703491494670909588120979 20555237242006364382181469)
              ·
                refine ⟨7708213965752386643318051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20555237242006364382181469 7708213965752386643318051)
                ·
                  refine ⟨11562320948628579964977077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7708213965752386643318051 11562320948628579964977077)
                  ·
                    refine ⟨1083967588933929371716601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11562320948628579964977077 1083967588933929371716601)
                    ·
                      rfl

theorem cell23_6333058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_6333058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333058 prefixEnd_6333058 := by exact prefixLift 6333058
  have htrace : WordTrace (prefixWord ++ tailWord_6333058) baseStart_6333058 baseEnd_6333058 := by
    simpa [prefixWord, tailWord_6333058, baseEnd_6333058] using wordTrace_append hprefix tailTrace_6333058
  have hstable : (prefixWord ++ tailWord_6333058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333058).length < 2 ^ (prefixWord ++ tailWord_6333058).sum := by decide
  have hdescent : baseEnd_6333058 < baseStart_6333058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333061 : List Nat := [1, 3, 1, 1, 4, 2, 1, 5, 1, 2, 2]
def baseStart_6333061 : Nat := 118140960795 + 6333061 * 2 ^ 59
def prefixEnd_6333061 : Nat := 4983230072969 + 3 ^ 40 * 6333061 * 2
def baseEnd_6333061 : Nat := 3251904307243751603412289

theorem tailTrace_6333061 : CollatzResearch.WordTrace tailWord_6333061 prefixEnd_6333061 3251904307243751603412289 := by
  unfold tailWord_6333061
  simp only [CollatzResearch.WordTrace]
  refine ⟨230985710909409072553279037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153990473939606048368852691 230985710909409072553279037)
  ·
    refine ⟨86619641591028402207479639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230985710909409072553279037 86619641591028402207479639)
    ·
      refine ⟨129929462386542603311219459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86619641591028402207479639 129929462386542603311219459)
      ·
        refine ⟨194894193579813904966829189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129929462386542603311219459 194894193579813904966829189)
        ·
          refine ⟨36542661296215107181280473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194894193579813904966829189 36542661296215107181280473)
          ·
            refine ⟨27406995972161330385960355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36542661296215107181280473 27406995972161330385960355)
            ·
              refine ⟨41110493958241995578940533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27406995972161330385960355 41110493958241995578940533)
              ·
                refine ⟨3854108808585187085525675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41110493958241995578940533 3854108808585187085525675)
                ·
                  refine ⟨5781163212877780628288513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3854108808585187085525675 5781163212877780628288513)
                  ·
                    refine ⟨4335872409658335471216385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5781163212877780628288513 4335872409658335471216385)
                    ·
                      refine ⟨3251904307243751603412289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4335872409658335471216385 3251904307243751603412289)
                      ·
                        rfl

theorem cell23_6333061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 5, 1, 2, 2].length) (baseStart_6333061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333061 prefixEnd_6333061 := by exact prefixLift 6333061
  have htrace : WordTrace (prefixWord ++ tailWord_6333061) baseStart_6333061 baseEnd_6333061 := by
    simpa [prefixWord, tailWord_6333061, baseEnd_6333061] using wordTrace_append hprefix tailTrace_6333061
  have hstable : (prefixWord ++ tailWord_6333061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333061).length < 2 ^ (prefixWord ++ tailWord_6333061).sum := by decide
  have hdescent : baseEnd_6333061 < baseStart_6333061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333083 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 8]
def baseStart_6333083 : Nat := 118140960795 + 6333083 * 2 ^ 59
def prefixEnd_6333083 : Nat := 4983230072969 + 3 ^ 40 * 6333083 * 2
def baseEnd_6333083 : Nat := 3251915603818150517337187

theorem tailTrace_6333083 : CollatzResearch.WordTrace tailWord_6333083 prefixEnd_6333083 3251915603818150517337187 := by
  unfold tailWord_6333083
  simp only [CollatzResearch.WordTrace]
  refine ⟨230986513315329370310579903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153991008876886246873719935 230986513315329370310579903)
  ·
    refine ⟨346479769972994055465869855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230986513315329370310579903 346479769972994055465869855)
    ·
      refine ⟨519719654959491083198804783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346479769972994055465869855 519719654959491083198804783)
      ·
        refine ⟨779579482439236624798207175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 519719654959491083198804783 779579482439236624798207175)
        ·
          refine ⟨1169369223658854937197310763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 779579482439236624798207175 1169369223658854937197310763)
          ·
            refine ⟨1754053835488282405795966145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1169369223658854937197310763 1754053835488282405795966145)
            ·
              refine ⟨1315540376616211804346974609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1754053835488282405795966145 1315540376616211804346974609)
              ·
                refine ⟨986655282462158853260230957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1315540376616211804346974609 986655282462158853260230957)
                ·
                  refine ⟨369995730923309569972586609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 986655282462158853260230957 369995730923309569972586609)
                  ·
                    refine ⟨277496798192482177479439957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 369995730923309569972586609 277496798192482177479439957)
                    ·
                      refine ⟨3251915603818150517337187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 277496798192482177479439957 3251915603818150517337187)
                      ·
                        rfl

theorem cell23_6333083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 8].length) (baseStart_6333083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333083 prefixEnd_6333083 := by exact prefixLift 6333083
  have htrace : WordTrace (prefixWord ++ tailWord_6333083) baseStart_6333083 baseEnd_6333083 := by
    simpa [prefixWord, tailWord_6333083, baseEnd_6333083] using wordTrace_append hprefix tailTrace_6333083
  have hstable : (prefixWord ++ tailWord_6333083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333083).length < 2 ^ (prefixWord ++ tailWord_6333083).sum := by decide
  have hdescent : baseEnd_6333083 < baseStart_6333083 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333098 : List Nat := [3, 1, 5, 2, 1, 1, 2, 2, 1, 2, 3]
def baseStart_6333098 : Nat := 118140960795 + 6333098 * 2 ^ 59
def prefixEnd_6333098 : Nat := 4983230072969 + 3 ^ 40 * 6333098 * 2
def baseEnd_6333098 : Nat := 3251923306027967958649619

theorem tailTrace_6333098 : CollatzResearch.WordTrace tailWord_6333098 prefixEnd_6333098 3251923306027967958649619 := by
  unfold tailWord_6333098
  simp only [CollatzResearch.WordTrace]
  refine ⟨57746765102568756968093987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153991373606850018581583965 57746765102568756968093987)
  ·
    refine ⟨86620147653853135452140981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57746765102568756968093987 86620147653853135452140981)
    ·
      refine ⟨8120638842548731448638217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86620147653853135452140981 8120638842548731448638217)
      ·
        refine ⟨6090479131911548586478663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8120638842548731448638217 6090479131911548586478663)
        ·
          refine ⟨9135718697867322879717995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6090479131911548586478663 9135718697867322879717995)
          ·
            refine ⟨13703578046800984319576993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9135718697867322879717995 13703578046800984319576993)
            ·
              refine ⟨10277683535100738239682745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13703578046800984319576993 10277683535100738239682745)
              ·
                refine ⟨7708262651325553679762059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10277683535100738239682745 7708262651325553679762059)
                ·
                  refine ⟨11562393976988330519643089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7708262651325553679762059 11562393976988330519643089)
                  ·
                    refine ⟨8671795482741247889732317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11562393976988330519643089 8671795482741247889732317)
                    ·
                      refine ⟨3251923306027967958649619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8671795482741247889732317 3251923306027967958649619)
                      ·
                        rfl

theorem cell23_6333098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_6333098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333098 prefixEnd_6333098 := by exact prefixLift 6333098
  have htrace : WordTrace (prefixWord ++ tailWord_6333098) baseStart_6333098 baseEnd_6333098 := by
    simpa [prefixWord, tailWord_6333098, baseEnd_6333098] using wordTrace_append hprefix tailTrace_6333098
  have hstable : (prefixWord ++ tailWord_6333098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333098).length < 2 ^ (prefixWord ++ tailWord_6333098).sum := by decide
  have hdescent : baseEnd_6333098 < baseStart_6333098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333120 : List Nat := [2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 5]
def baseStart_6333120 : Nat := 118140960795 + 6333120 * 2 ^ 59
def prefixEnd_6333120 : Nat := 4983230072969 + 3 ^ 40 * 6333120 * 2
def baseEnd_6333120 : Nat := 3251934602602366872574517

theorem tailTrace_6333120 : CollatzResearch.WordTrace tailWord_6333120 prefixEnd_6333120 3251934602602366872574517 := by
  unfold tailWord_6333120
  simp only [CollatzResearch.WordTrace]
  refine ⟨115493931408097662814838407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153991908544130217086451209 115493931408097662814838407)
  ·
    refine ⟨173240897112146494222257611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115493931408097662814838407 173240897112146494222257611)
    ·
      refine ⟨259861345668219741333386417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173240897112146494222257611 259861345668219741333386417)
      ·
        refine ⟨194896009251164806000039813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259861345668219741333386417 194896009251164806000039813)
        ·
          refine ⟨36543001734593401125007465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194896009251164806000039813 36543001734593401125007465)
          ·
            refine ⟨27407251300945050843755599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36543001734593401125007465 27407251300945050843755599)
            ·
              refine ⟨41110876951417576265633399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27407251300945050843755599 41110876951417576265633399)
              ·
                refine ⟨61666315427126364398450099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41110876951417576265633399 61666315427126364398450099)
                ·
                  refine ⟨92499473140689546597675149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61666315427126364398450099 92499473140689546597675149)
                  ·
                    refine ⟨34687302427758579974128181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92499473140689546597675149 34687302427758579974128181)
                    ·
                      refine ⟨3251934602602366872574517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34687302427758579974128181 3251934602602366872574517)
                      ·
                        rfl

theorem cell23_6333120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 5].length) (baseStart_6333120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333120 prefixEnd_6333120 := by exact prefixLift 6333120
  have htrace : WordTrace (prefixWord ++ tailWord_6333120) baseStart_6333120 baseEnd_6333120 := by
    simpa [prefixWord, tailWord_6333120, baseEnd_6333120] using wordTrace_append hprefix tailTrace_6333120
  have hstable : (prefixWord ++ tailWord_6333120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333120).length < 2 ^ (prefixWord ++ tailWord_6333120).sum := by decide
  have hdescent : baseEnd_6333120 < baseStart_6333120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333151 : List Nat := [1, 1, 2, 3, 2, 4, 1, 3, 2, 2, 2]
def baseStart_6333151 : Nat := 118140960795 + 6333151 * 2 ^ 59
def prefixEnd_6333151 : Nat := 4983230072969 + 3 ^ 40 * 6333151 * 2
def baseEnd_6333151 : Nat := 3251950520502656251286875

theorem tailTrace_6333151 : CollatzResearch.WordTrace tailWord_6333151 prefixEnd_6333151 3251950520502656251286875 := by
  unfold tailWord_6333151
  simp only [CollatzResearch.WordTrace]
  refine ⟨230988993479083017924055307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153992662319388678616036871 230988993479083017924055307)
  ·
    refine ⟨346483490218624526886082961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230988993479083017924055307 346483490218624526886082961)
    ·
      refine ⟨259862617663968395164562221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346483490218624526886082961 259862617663968395164562221)
      ·
        refine ⟨97448481623988148186710833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259862617663968395164562221 97448481623988148186710833)
        ·
          refine ⟨73086361217991111140033125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97448481623988148186710833 73086361217991111140033125)
          ·
            refine ⟨13703692728373333338756211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73086361217991111140033125 13703692728373333338756211)
            ·
              refine ⟨20555539092560000008134317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13703692728373333338756211 20555539092560000008134317)
              ·
                refine ⟨7708327159710000003050369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20555539092560000008134317 7708327159710000003050369)
                ·
                  refine ⟨5781245369782500002287777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7708327159710000003050369 5781245369782500002287777)
                  ·
                    refine ⟨4335934027336875001715833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5781245369782500002287777 4335934027336875001715833)
                    ·
                      refine ⟨3251950520502656251286875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4335934027336875001715833 3251950520502656251286875)
                      ·
                        rfl

theorem cell23_6333151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 3, 2, 2, 2].length) (baseStart_6333151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333151 prefixEnd_6333151 := by exact prefixLift 6333151
  have htrace : WordTrace (prefixWord ++ tailWord_6333151) baseStart_6333151 baseEnd_6333151 := by
    simpa [prefixWord, tailWord_6333151, baseEnd_6333151] using wordTrace_append hprefix tailTrace_6333151
  have hstable : (prefixWord ++ tailWord_6333151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333151).length < 2 ^ (prefixWord ++ tailWord_6333151).sum := by decide
  have hdescent : baseEnd_6333151 < baseStart_6333151 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333172 : List Nat := [2, 6, 1, 1, 2, 1, 3, 1, 1, 3, 2]
def baseStart_6333172 : Nat := 118140960795 + 6333172 * 2 ^ 59
def prefixEnd_6333172 : Nat := 4983230072969 + 3 ^ 40 * 6333172 * 2
def baseEnd_6333172 : Nat := 3251961303596400669124279

theorem tailTrace_6333172 : CollatzResearch.WordTrace tailWord_6333172 prefixEnd_6333172 3251961303596400669124279 := by
  unfold tailWord_6333172
  simp only [CollatzResearch.WordTrace]
  refine ⟨115494879706003469255284885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153993172941337959007046513 115494879706003469255284885)
  ·
    refine ⟨5413822486218912621341479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 115494879706003469255284885 5413822486218912621341479)
    ·
      refine ⟨8120733729328368932012219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5413822486218912621341479 8120733729328368932012219)
      ·
        refine ⟨12181100593992553398018329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8120733729328368932012219 12181100593992553398018329)
        ·
          refine ⟨9135825445494415048513747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12181100593992553398018329 9135825445494415048513747)
          ·
            refine ⟨13703738168241622572770621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9135825445494415048513747 13703738168241622572770621)
            ·
              refine ⟨5138901813090608464788983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13703738168241622572770621 5138901813090608464788983)
              ·
                refine ⟨7708352719635912697183475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5138901813090608464788983 7708352719635912697183475)
                ·
                  refine ⟨11562529079453869045775213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7708352719635912697183475 11562529079453869045775213)
                  ·
                    refine ⟨4335948404795200892165705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11562529079453869045775213 4335948404795200892165705)
                    ·
                      refine ⟨3251961303596400669124279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4335948404795200892165705 3251961303596400669124279)
                      ·
                        rfl

theorem cell23_6333172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_6333172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333172 prefixEnd_6333172 := by exact prefixLift 6333172
  have htrace : WordTrace (prefixWord ++ tailWord_6333172) baseStart_6333172 baseEnd_6333172 := by
    simpa [prefixWord, tailWord_6333172, baseEnd_6333172] using wordTrace_append hprefix tailTrace_6333172
  have hstable : (prefixWord ++ tailWord_6333172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333172).length < 2 ^ (prefixWord ++ tailWord_6333172).sum := by decide
  have hdescent : baseEnd_6333172 < baseStart_6333172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333174 : List Nat := [5, 1, 1, 1, 1, 2, 2, 5, 5]
def baseStart_6333174 : Nat := 118140960795 + 6333174 * 2 ^ 59
def prefixEnd_6333174 : Nat := 4983230072969 + 3 ^ 40 * 6333174 * 2
def baseEnd_6333174 : Nat := 361329147839745517922141

theorem tailTrace_6333174 : CollatzResearch.WordTrace tailWord_6333174 prefixEnd_6333174 361329147839745517922141 := by
  unfold tailWord_6333174
  simp only [CollatzResearch.WordTrace]
  refine ⟨14436864522374980803258911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153993221571999795234761717 14436864522374980803258911)
  ·
    refine ⟨21655296783562471204888367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14436864522374980803258911 21655296783562471204888367)
    ·
      refine ⟨32482945175343706807332551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21655296783562471204888367 32482945175343706807332551)
      ·
        refine ⟨48724417763015560210998827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32482945175343706807332551 48724417763015560210998827)
        ·
          refine ⟨73086626644523340316498241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48724417763015560210998827 73086626644523340316498241)
          ·
            refine ⟨54814969983392505237373681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73086626644523340316498241 54814969983392505237373681)
            ·
              refine ⟨41111227487544378928030261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54814969983392505237373681 41111227487544378928030261)
              ·
                refine ⟨3854177576957285524502837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41111227487544378928030261 3854177576957285524502837)
                ·
                  refine ⟨361329147839745517922141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3854177576957285524502837 361329147839745517922141)
                  ·
                    rfl

theorem cell23_6333174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_6333174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333174 prefixEnd_6333174 := by exact prefixLift 6333174
  have htrace : WordTrace (prefixWord ++ tailWord_6333174) baseStart_6333174 baseEnd_6333174 := by
    simpa [prefixWord, tailWord_6333174, baseEnd_6333174] using wordTrace_append hprefix tailTrace_6333174
  have hstable : (prefixWord ++ tailWord_6333174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333174).length < 2 ^ (prefixWord ++ tailWord_6333174).sum := by decide
  have hdescent : baseEnd_6333174 < baseStart_6333174 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333177 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 4, 5, 2]
def baseStart_6333177 : Nat := 118140960795 + 6333177 * 2 ^ 59
def prefixEnd_6333177 : Nat := 4983230072969 + 3 ^ 40 * 6333177 * 2
def baseEnd_6333177 : Nat := 3251963870999673149561755

theorem tailTrace_6333177 : CollatzResearch.WordTrace tailWord_6333177 prefixEnd_6333177 3251963870999673149561755 := by
  unfold tailWord_6333177
  simp only [CollatzResearch.WordTrace]
  refine ⟨230989941776988824364501785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153993294517992549576334523 230989941776988824364501785)
  ·
    refine ⟨173242456332741618273376339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230989941776988824364501785 173242456332741618273376339)
    ·
      refine ⟨259863684499112427410064509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173242456332741618273376339 259863684499112427410064509)
      ·
        refine ⟨97448881687167160278774191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259863684499112427410064509 97448881687167160278774191)
        ·
          refine ⟨146173322530750740418161287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97448881687167160278774191 146173322530750740418161287)
          ·
            refine ⟨219259983796126110627241931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146173322530750740418161287 219259983796126110627241931)
            ·
              refine ⟨328889975694189165940862897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219259983796126110627241931 328889975694189165940862897)
              ·
                refine ⟨246667481770641874455647173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 328889975694189165940862897 246667481770641874455647173)
                ·
                  refine ⟨46250152831995351460433845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 246667481770641874455647173 46250152831995351460433845)
                  ·
                    refine ⟨4335951827999564199415673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46250152831995351460433845 4335951827999564199415673)
                    ·
                      refine ⟨3251963870999673149561755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4335951827999564199415673 3251963870999673149561755)
                      ·
                        rfl

theorem cell23_6333177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 5, 2].length) (baseStart_6333177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333177 prefixEnd_6333177 := by exact prefixLift 6333177
  have htrace : WordTrace (prefixWord ++ tailWord_6333177) baseStart_6333177 baseEnd_6333177 := by
    simpa [prefixWord, tailWord_6333177, baseEnd_6333177] using wordTrace_append hprefix tailTrace_6333177
  have hstable : (prefixWord ++ tailWord_6333177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333177).length < 2 ^ (prefixWord ++ tailWord_6333177).sum := by decide
  have hdescent : baseEnd_6333177 < baseStart_6333177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333191 : List Nat := [1, 1, 4, 4, 1, 1, 4, 2, 5]
def baseStart_6333191 : Nat := 118140960795 + 6333191 * 2 ^ 59
def prefixEnd_6333191 : Nat := 4983230072969 + 3 ^ 40 * 6333191 * 2
def baseEnd_6333191 : Nat := 361330117747648454976299

theorem tailTrace_6333191 : CollatzResearch.WordTrace tailWord_6333191 prefixEnd_6333191 361330117747648454976299 := by
  unfold tailWord_6333191
  simp only [CollatzResearch.WordTrace]
  refine ⟨230990452398938104755511427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153993634932625403170340951 230990452398938104755511427)
  ·
    refine ⟨346485678598407157133267141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230990452398938104755511427 346485678598407157133267141)
    ·
      refine ⟨64966064737201341962487589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 346485678598407157133267141 64966064737201341962487589)
      ·
        refine ⟨12181137138225251617966423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64966064737201341962487589 12181137138225251617966423)
        ·
          refine ⟨18271705707337877426949635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12181137138225251617966423 18271705707337877426949635)
          ·
            refine ⟨27407558561006816140424453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18271705707337877426949635 27407558561006816140424453)
            ·
              refine ⟨5138917230188778026329585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27407558561006816140424453 5138917230188778026329585)
              ·
                refine ⟨3854187922641583519747189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5138917230188778026329585 3854187922641583519747189)
                ·
                  refine ⟨361330117747648454976299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3854187922641583519747189 361330117747648454976299)
                  ·
                    rfl

theorem cell23_6333191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 2, 5].length) (baseStart_6333191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333191 prefixEnd_6333191 := by exact prefixLift 6333191
  have htrace : WordTrace (prefixWord ++ tailWord_6333191) baseStart_6333191 baseEnd_6333191 := by
    simpa [prefixWord, tailWord_6333191, baseEnd_6333191] using wordTrace_append hprefix tailTrace_6333191
  have hstable : (prefixWord ++ tailWord_6333191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333191).length < 2 ^ (prefixWord ++ tailWord_6333191).sum := by decide
  have hdescent : baseEnd_6333191 < baseStart_6333191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333224 : List Nat := [2, 1, 5, 1, 1, 1, 1, 2, 1, 6, 2]
def baseStart_6333224 : Nat := 118140960795 + 6333224 * 2 ^ 59
def prefixEnd_6333224 : Nat := 4983230072969 + 3 ^ 40 * 6333224 * 2
def baseEnd_6333224 : Nat := 3251988004590434465674039

theorem tailTrace_6333224 : CollatzResearch.WordTrace tailWord_6333224 prefixEnd_6333224 3251988004590434465674039 := by
  unfold tailWord_6333224
  simp only [CollatzResearch.WordTrace]
  refine ⟨115495828003909275695731363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153994437338545700927641817 115495828003909275695731363)
  ·
    refine ⟨173243742005863913543597045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115495828003909275695731363 173243742005863913543597045)
    ·
      refine ⟨16241600813049741894712223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 173243742005863913543597045 16241600813049741894712223)
      ·
        refine ⟨24362401219574612842068335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16241600813049741894712223 24362401219574612842068335)
        ·
          refine ⟨36543601829361919263102503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24362401219574612842068335 36543601829361919263102503)
          ·
            refine ⟨54815402744042878894653755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36543601829361919263102503 54815402744042878894653755)
            ·
              refine ⟨82223104116064318341980633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54815402744042878894653755 82223104116064318341980633)
              ·
                refine ⟨61667328087048238756485475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82223104116064318341980633 61667328087048238756485475)
                ·
                  refine ⟨92500992130572358134728213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61667328087048238756485475 92500992130572358134728213)
                  ·
                    refine ⟨4335984006120579287565385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 92500992130572358134728213 4335984006120579287565385)
                    ·
                      refine ⟨3251988004590434465674039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4335984006120579287565385 3251988004590434465674039)
                      ·
                        rfl

theorem cell23_6333224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_6333224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333224 prefixEnd_6333224 := by exact prefixLift 6333224
  have htrace : WordTrace (prefixWord ++ tailWord_6333224) baseStart_6333224 baseEnd_6333224 := by
    simpa [prefixWord, tailWord_6333224, baseEnd_6333224] using wordTrace_append hprefix tailTrace_6333224
  have hstable : (prefixWord ++ tailWord_6333224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333224).length < 2 ^ (prefixWord ++ tailWord_6333224).sum := by decide
  have hdescent : baseEnd_6333224 < baseStart_6333224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333237 : List Nat := [1, 3, 3, 1, 3, 1, 1, 1, 2, 1, 6]
def baseStart_6333237 : Nat := 118140960795 + 6333237 * 2 ^ 59
def prefixEnd_6333237 : Nat := 4983230072969 + 3 ^ 40 * 6333237 * 2
def baseEnd_6333237 : Nat := 3251994679838942914811479

theorem tailTrace_6333237 : CollatzResearch.WordTrace tailWord_6333237 prefixEnd_6333237 3251994679838942914811479 := by
  unfold tailWord_6333237
  simp only [CollatzResearch.WordTrace]
  refine ⟨230992130156771454611685965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153994753437847636407790643 230992130156771454611685965)
  ·
    refine ⟨86622048808789295479382237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230992130156771454611685965 86622048808789295479382237)
    ·
      refine ⟨32483268303295985804768339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86622048808789295479382237 32483268303295985804768339)
      ·
        refine ⟨48724902454943978707152509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32483268303295985804768339 48724902454943978707152509)
        ·
          refine ⟨18271838420603992015182191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48724902454943978707152509 18271838420603992015182191)
          ·
            refine ⟨27407757630905988022773287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18271838420603992015182191 27407757630905988022773287)
            ·
              refine ⟨41111636446358982034159931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27407757630905988022773287 41111636446358982034159931)
              ·
                refine ⟨61667454669538473051239897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41111636446358982034159931 61667454669538473051239897)
                ·
                  refine ⟨46250591002153854788429923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61667454669538473051239897 46250591002153854788429923)
                  ·
                    refine ⟨69375886503230782182644885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46250591002153854788429923 69375886503230782182644885)
                    ·
                      refine ⟨3251994679838942914811479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69375886503230782182644885 3251994679838942914811479)
                      ·
                        rfl

theorem cell23_6333237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_6333237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333237 prefixEnd_6333237 := by exact prefixLift 6333237
  have htrace : WordTrace (prefixWord ++ tailWord_6333237) baseStart_6333237 baseEnd_6333237 := by
    simpa [prefixWord, tailWord_6333237, baseEnd_6333237] using wordTrace_append hprefix tailTrace_6333237
  have hstable : (prefixWord ++ tailWord_6333237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333237).length < 2 ^ (prefixWord ++ tailWord_6333237).sum := by decide
  have hdescent : baseEnd_6333237 < baseStart_6333237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333247 : List Nat := [1, 1, 2, 2, 5, 2, 1, 1, 8]
def baseStart_6333247 : Nat := 118140960795 + 6333247 * 2 ^ 59
def prefixEnd_6333247 : Nat := 4983230072969 + 3 ^ 40 * 6333247 * 2
def baseEnd_6333247 : Nat := 361333312738387541742937

theorem tailTrace_6333247 : CollatzResearch.WordTrace tailWord_6333247 prefixEnd_6333247 361333312738387541742937 := by
  unfold tailWord_6333247
  simp only [CollatzResearch.WordTrace]
  refine ⟨230992494886735226319549995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153994996591156817546366663 230992494886735226319549995)
  ·
    refine ⟨346488742330102839479324993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230992494886735226319549995 346488742330102839479324993)
    ·
      refine ⟨259866556747577129609493745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346488742330102839479324993 259866556747577129609493745)
      ·
        refine ⟨194899917560682847207120309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259866556747577129609493745 194899917560682847207120309)
        ·
          refine ⟨18271867271314016925667529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 194899917560682847207120309 18271867271314016925667529)
          ·
            refine ⟨13703900453485512694250647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18271867271314016925667529 13703900453485512694250647)
            ·
              refine ⟨20555850680228269041375971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13703900453485512694250647 20555850680228269041375971)
              ·
                refine ⟨30833776020342403562063957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20555850680228269041375971 30833776020342403562063957)
                ·
                  refine ⟨361333312738387541742937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30833776020342403562063957 361333312738387541742937)
                  ·
                    rfl

theorem cell23_6333247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 8].length) (baseStart_6333247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333247 prefixEnd_6333247 := by exact prefixLift 6333247
  have htrace : WordTrace (prefixWord ++ tailWord_6333247) baseStart_6333247 baseEnd_6333247 := by
    simpa [prefixWord, tailWord_6333247, baseEnd_6333247] using wordTrace_append hprefix tailTrace_6333247
  have hstable : (prefixWord ++ tailWord_6333247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333247).length < 2 ^ (prefixWord ++ tailWord_6333247).sum := by decide
  have hdescent : baseEnd_6333247 < baseStart_6333247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333301 : List Nat := [1, 3, 4, 1, 1, 2, 1, 1, 4, 3, 2]
def baseStart_6333301 : Nat := 118140960795 + 6333301 * 2 ^ 59
def prefixEnd_6333301 : Nat := 4983230072969 + 3 ^ 40 * 6333301 * 2
def baseEnd_6333301 : Nat := 3252027542600830664411185

theorem tailTrace_6333301 : CollatzResearch.WordTrace tailWord_6333301 prefixEnd_6333301 3252027542600830664411185 := by
  unfold tailWord_6333301
  simp only [CollatzResearch.WordTrace]
  refine ⟨230994464428539593542015757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153996309619026395694677171 230994464428539593542015757)
  ·
    refine ⟨86622924160702347578255909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230994464428539593542015757 86622924160702347578255909)
    ·
      refine ⟨16241798280131690170922983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86622924160702347578255909 16241798280131690170922983)
      ·
        refine ⟨24362697420197535256384475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16241798280131690170922983 24362697420197535256384475)
        ·
          refine ⟨36544046130296302884576713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24362697420197535256384475 36544046130296302884576713)
          ·
            refine ⟨27408034597722227163432535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36544046130296302884576713 27408034597722227163432535)
            ·
              refine ⟨41112051896583340745148803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27408034597722227163432535 41112051896583340745148803)
              ·
                refine ⟨61668077844875011117723205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41112051896583340745148803 61668077844875011117723205)
                ·
                  refine ⟨11562764595914064584573101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61668077844875011117723205 11562764595914064584573101)
                  ·
                    refine ⟨4336036723467774219214913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11562764595914064584573101 4336036723467774219214913)
                    ·
                      refine ⟨3252027542600830664411185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4336036723467774219214913 3252027542600830664411185)
                      ·
                        rfl

theorem cell23_6333301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_6333301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333301 prefixEnd_6333301 := by exact prefixLift 6333301
  have htrace : WordTrace (prefixWord ++ tailWord_6333301) baseStart_6333301 baseEnd_6333301 := by
    simpa [prefixWord, tailWord_6333301, baseEnd_6333301] using wordTrace_append hprefix tailTrace_6333301
  have hstable : (prefixWord ++ tailWord_6333301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333301).length < 2 ^ (prefixWord ++ tailWord_6333301).sum := by decide
  have hdescent : baseEnd_6333301 < baseStart_6333301 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333365 : List Nat := [1, 3, 3, 2, 1, 1, 3, 4, 1, 2, 2]
def baseStart_6333365 : Nat := 118140960795 + 6333365 * 2 ^ 59
def prefixEnd_6333365 : Nat := 4983230072969 + 3 ^ 40 * 6333365 * 2
def baseEnd_6333365 : Nat := 3252060405362718414010891

theorem tailTrace_6333365 : CollatzResearch.WordTrace tailWord_6333365 prefixEnd_6333365 3252060405362718414010891 := by
  unfold tailWord_6333365
  simp only [CollatzResearch.WordTrace]
  refine ⟨230996798700307732472345549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153997865800205154981563699 230996798700307732472345549)
  ·
    refine ⟨86623799512615399677129581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230996798700307732472345549 86623799512615399677129581)
    ·
      refine ⟨32483924817230774878923593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86623799512615399677129581 32483924817230774878923593)
      ·
        refine ⟨24362943612923081159192695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32483924817230774878923593 24362943612923081159192695)
        ·
          refine ⟨36544415419384621738789043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24362943612923081159192695 36544415419384621738789043)
          ·
            refine ⟨54816623129076932608183565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36544415419384621738789043 54816623129076932608183565)
            ·
              refine ⟨20556233673403849728068837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54816623129076932608183565 20556233673403849728068837)
              ·
                refine ⟨3854293813763221824012907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20556233673403849728068837 3854293813763221824012907)
                ·
                  refine ⟨5781440720644832736019361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3854293813763221824012907 5781440720644832736019361)
                  ·
                    refine ⟨4336080540483624552014521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5781440720644832736019361 4336080540483624552014521)
                    ·
                      refine ⟨3252060405362718414010891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4336080540483624552014521 3252060405362718414010891)
                      ·
                        rfl

theorem cell23_6333365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_6333365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333365 prefixEnd_6333365 := by exact prefixLift 6333365
  have htrace : WordTrace (prefixWord ++ tailWord_6333365) baseStart_6333365 baseEnd_6333365 := by
    simpa [prefixWord, tailWord_6333365, baseEnd_6333365] using wordTrace_append hprefix tailTrace_6333365
  have hstable : (prefixWord ++ tailWord_6333365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333365).length < 2 ^ (prefixWord ++ tailWord_6333365).sum := by decide
  have hdescent : baseEnd_6333365 < baseStart_6333365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333367 : List Nat := [1, 1, 3, 1, 3, 1, 3, 1, 2, 7]
def baseStart_6333367 : Nat := 118140960795 + 6333367 * 2 ^ 59
def prefixEnd_6333367 : Nat := 4983230072969 + 3 ^ 40 * 6333367 * 2
def baseEnd_6333367 : Nat := 1084020477441342468728627

theorem tailTrace_6333367 : CollatzResearch.WordTrace tailWord_6333367 prefixEnd_6333367 1084020477441342468728627 := by
  unfold tailWord_6333367
  simp only [CollatzResearch.WordTrace]
  refine ⟨230996871646300486813918355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153997914430866991209278903 230996871646300486813918355)
  ·
    refine ⟨346495307469450730220877533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230996871646300486813918355 346495307469450730220877533)
    ·
      refine ⟨129935740301044023832829075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 346495307469450730220877533 129935740301044023832829075)
      ·
        refine ⟨194903610451566035749243613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129935740301044023832829075 194903610451566035749243613)
        ·
          refine ⟨73088853919337263405966355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194903610451566035749243613 73088853919337263405966355)
          ·
            refine ⟨109633280879005895108949533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73088853919337263405966355 109633280879005895108949533)
            ·
              refine ⟨41112480329627210665856075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109633280879005895108949533 41112480329627210665856075)
              ·
                refine ⟨61668720494440815998784113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41112480329627210665856075 61668720494440815998784113)
                ·
                  refine ⟨46251540370830611999088085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61668720494440815998784113 46251540370830611999088085)
                  ·
                    refine ⟨1084020477441342468728627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46251540370830611999088085 1084020477441342468728627)
                    ·
                      rfl

theorem cell23_6333367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 7].length) (baseStart_6333367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333367 prefixEnd_6333367 := by exact prefixLift 6333367
  have htrace : WordTrace (prefixWord ++ tailWord_6333367) baseStart_6333367 baseEnd_6333367 := by
    simpa [prefixWord, tailWord_6333367, baseEnd_6333367] using wordTrace_append hprefix tailTrace_6333367
  have hstable : (prefixWord ++ tailWord_6333367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333367).length < 2 ^ (prefixWord ++ tailWord_6333367).sum := by decide
  have hdescent : baseEnd_6333367 < baseStart_6333367 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333391 : List Nat := [1, 1, 2, 1, 1, 6, 2, 1, 3, 3, 2]
def baseStart_6333391 : Nat := 118140960795 + 6333391 * 2 ^ 59
def prefixEnd_6333391 : Nat := 4983230072969 + 3 ^ 40 * 6333391 * 2
def baseEnd_6333391 : Nat := 3252073755859735312285771

theorem tailTrace_6333391 : CollatzResearch.WordTrace tailWord_6333391 prefixEnd_6333391 3252073755859735312285771 := by
  unfold tailWord_6333391
  simp only [CollatzResearch.WordTrace]
  refine ⟨230997746998213538912792027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153998497998809025941861351 230997746998213538912792027)
  ·
    refine ⟨346496620497320308369188041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230997746998213538912792027 346496620497320308369188041)
    ·
      refine ⟨259872465372990231276891031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346496620497320308369188041 259872465372990231276891031)
      ·
        refine ⟨389808698059485346915336547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259872465372990231276891031 389808698059485346915336547)
        ·
          refine ⟨584713047089228020373004821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389808698059485346915336547 584713047089228020373004821)
          ·
            refine ⟨27408424082307563454984601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 584713047089228020373004821 27408424082307563454984601)
            ·
              refine ⟨20556318061730672591238451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27408424082307563454984601 20556318061730672591238451)
              ·
                refine ⟨30834477092596008886857677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20556318061730672591238451 30834477092596008886857677)
                ·
                  refine ⟨11562928909723503332571629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30834477092596008886857677 11562928909723503332571629)
                  ·
                    refine ⟨4336098341146313749714361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11562928909723503332571629 4336098341146313749714361)
                    ·
                      refine ⟨3252073755859735312285771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4336098341146313749714361 3252073755859735312285771)
                      ·
                        rfl

theorem cell23_6333391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 3, 3, 2].length) (baseStart_6333391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333391 prefixEnd_6333391 := by exact prefixLift 6333391
  have htrace : WordTrace (prefixWord ++ tailWord_6333391) baseStart_6333391 baseEnd_6333391 := by
    simpa [prefixWord, tailWord_6333391, baseEnd_6333391] using wordTrace_append hprefix tailTrace_6333391
  have hstable : (prefixWord ++ tailWord_6333391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333391).length < 2 ^ (prefixWord ++ tailWord_6333391).sum := by decide
  have hdescent : baseEnd_6333391 < baseStart_6333391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333398 : List Nat := [5, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3]
def baseStart_6333398 : Nat := 118140960795 + 6333398 * 2 ^ 59
def prefixEnd_6333398 : Nat := 4983230072969 + 3 ^ 40 * 6333398 * 2
def baseEnd_6333398 : Nat := 3252077350224316784898239

theorem tailTrace_6333398 : CollatzResearch.WordTrace tailWord_6333398 prefixEnd_6333398 3252077350224316784898239 := by
  unfold tailWord_6333398
  simp only [CollatzResearch.WordTrace]
  refine ⟨14437375144324261194268553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153998668206125452738864565 14437375144324261194268553)
  ·
    refine ⟨10828031358243195895701415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14437375144324261194268553 10828031358243195895701415)
    ·
      refine ⟨16242047037364793843552123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10828031358243195895701415 16242047037364793843552123)
      ·
        refine ⟨24363070556047190765328185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16242047037364793843552123 24363070556047190765328185)
        ·
          refine ⟨18272302917035393073996139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24363070556047190765328185 18272302917035393073996139)
          ·
            refine ⟨27408454375553089610994209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18272302917035393073996139 27408454375553089610994209)
            ·
              refine ⟨20556340781664817208245657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27408454375553089610994209 20556340781664817208245657)
              ·
                refine ⟨15417255586248612906184243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20556340781664817208245657 15417255586248612906184243)
                ·
                  refine ⟨23125883379372919359276365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15417255586248612906184243 23125883379372919359276365)
                  ·
                    refine ⟨8672206267264844759728637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23125883379372919359276365 8672206267264844759728637)
                    ·
                      refine ⟨3252077350224316784898239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8672206267264844759728637 3252077350224316784898239)
                      ·
                        rfl

theorem cell23_6333398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_6333398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333398 prefixEnd_6333398 := by exact prefixLift 6333398
  have htrace : WordTrace (prefixWord ++ tailWord_6333398) baseStart_6333398 baseEnd_6333398 := by
    simpa [prefixWord, tailWord_6333398, baseEnd_6333398] using wordTrace_append hprefix tailTrace_6333398
  have hstable : (prefixWord ++ tailWord_6333398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333398).length < 2 ^ (prefixWord ++ tailWord_6333398).sum := by decide
  have hdescent : baseEnd_6333398 < baseStart_6333398 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333415 : List Nat := [1, 1, 5, 2, 2, 3, 1, 2, 2, 1, 3]
def baseStart_6333415 : Nat := 118140960795 + 6333415 * 2 ^ 59
def prefixEnd_6333415 : Nat := 4983230072969 + 3 ^ 40 * 6333415 * 2
def baseEnd_6333415 : Nat := 3252086079395443218385661

theorem tailTrace_6333415 : CollatzResearch.WordTrace tailWord_6333415 prefixEnd_6333415 3252086079395443218385661 := by
  unfold tailWord_6333415
  simp only [CollatzResearch.WordTrace]
  refine ⟨230998622350126591011665699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153999081566751060674443799 230998622350126591011665699)
  ·
    refine ⟨346497933525189886517498549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230998622350126591011665699 346497933525189886517498549)
    ·
      refine ⟨32484181267986551861015489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 346497933525189886517498549 32484181267986551861015489)
      ·
        refine ⟨24363135950989913895761617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32484181267986551861015489 24363135950989913895761617)
        ·
          refine ⟨18272351963242435421821213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24363135950989913895761617 18272351963242435421821213)
          ·
            refine ⟨6852131986215913283182955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18272351963242435421821213 6852131986215913283182955)
            ·
              refine ⟨10278197979323869924774433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6852131986215913283182955 10278197979323869924774433)
              ·
                refine ⟨7708648484492902443580825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10278197979323869924774433 7708648484492902443580825)
                ·
                  refine ⟨5781486363369676832685619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7708648484492902443580825 5781486363369676832685619)
                  ·
                    refine ⟨8672229545054515249028429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5781486363369676832685619 8672229545054515249028429)
                    ·
                      refine ⟨3252086079395443218385661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8672229545054515249028429 3252086079395443218385661)
                      ·
                        rfl

theorem cell23_6333415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_6333415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333415 prefixEnd_6333415 := by exact prefixLift 6333415
  have htrace : WordTrace (prefixWord ++ tailWord_6333415) baseStart_6333415 baseEnd_6333415 := by
    simpa [prefixWord, tailWord_6333415, baseEnd_6333415] using wordTrace_append hprefix tailTrace_6333415
  have hstable : (prefixWord ++ tailWord_6333415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333415).length < 2 ^ (prefixWord ++ tailWord_6333415).sum := by decide
  have hdescent : baseEnd_6333415 < baseStart_6333415 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333484 : List Nat := [2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 5]
def baseStart_6333484 : Nat := 118140960795 + 6333484 * 2 ^ 59
def prefixEnd_6333484 : Nat := 4983230072969 + 3 ^ 40 * 6333484 * 2
def baseEnd_6333484 : Nat := 3252121509560603448422843

theorem tailTrace_6333484 : CollatzResearch.WordTrace tailWord_6333484 prefixEnd_6333484 3252121509560603448422843 := by
  unfold tailWord_6333484
  simp only [CollatzResearch.WordTrace]
  refine ⟨115500569493438307897963753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154000759324584410530618337 115500569493438307897963753)
  ·
    refine ⟨86625427120078730923472815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115500569493438307897963753 86625427120078730923472815)
    ·
      refine ⟨129938140680118096385209223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86625427120078730923472815 129938140680118096385209223)
      ·
        refine ⟨194907211020177144577813835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129938140680118096385209223 194907211020177144577813835)
        ·
          refine ⟨292360816530265716866720753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194907211020177144577813835 292360816530265716866720753)
          ·
            refine ⟨219270612397699287650040565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292360816530265716866720753 219270612397699287650040565)
            ·
              refine ⟨20556619912284308217191303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 219270612397699287650040565 20556619912284308217191303)
              ·
                refine ⟨30834929868426462325786955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20556619912284308217191303 30834929868426462325786955)
                ·
                  refine ⟨46252394802639693488680433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30834929868426462325786955 46252394802639693488680433)
                  ·
                    refine ⟨34689296101979770116510325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46252394802639693488680433 34689296101979770116510325)
                    ·
                      refine ⟨3252121509560603448422843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34689296101979770116510325 3252121509560603448422843)
                      ·
                        rfl

theorem cell23_6333484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 5].length) (baseStart_6333484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333484 prefixEnd_6333484 := by exact prefixLift 6333484
  have htrace : WordTrace (prefixWord ++ tailWord_6333484) baseStart_6333484 baseEnd_6333484 := by
    simpa [prefixWord, tailWord_6333484, baseEnd_6333484] using wordTrace_append hprefix tailTrace_6333484
  have hstable : (prefixWord ++ tailWord_6333484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333484).length < 2 ^ (prefixWord ++ tailWord_6333484).sum := by decide
  have hdescent : baseEnd_6333484 < baseStart_6333484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333511 : List Nat := [1, 1, 4, 1, 3, 2, 1, 3, 2, 1, 4]
def baseStart_6333511 : Nat := 118140960795 + 6333511 * 2 ^ 59
def prefixEnd_6333511 : Nat := 4983230072969 + 3 ^ 40 * 6333511 * 2
def baseEnd_6333511 : Nat := 3252135373538274842785219

theorem tailTrace_6333511 : CollatzResearch.WordTrace tailWord_6333511 prefixEnd_6333511 3252135373538274842785219 := by
  unfold tailWord_6333511
  simp only [CollatzResearch.WordTrace]
  refine ⟨231002123757778799407160387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154001415838519199604773591 231002123757778799407160387)
  ·
    refine ⟨346503185636668199110740581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231002123757778799407160387 346503185636668199110740581)
    ·
      refine ⟨64969347306875287333263859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 346503185636668199110740581 64969347306875287333263859)
      ·
        refine ⟨97454020960312930999895789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64969347306875287333263859 97454020960312930999895789)
        ·
          refine ⟨36545257860117349124960921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97454020960312930999895789 36545257860117349124960921)
          ·
            refine ⟨27408943395088011843720691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36545257860117349124960921 27408943395088011843720691)
            ·
              refine ⟨41113415092632017765581037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27408943395088011843720691 41113415092632017765581037)
              ·
                refine ⟨15417530659737006662092889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41113415092632017765581037 15417530659737006662092889)
                ·
                  refine ⟨11563147994802754996569667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15417530659737006662092889 11563147994802754996569667)
                  ·
                    refine ⟨17344721992204132494854501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11563147994802754996569667 17344721992204132494854501)
                    ·
                      refine ⟨3252135373538274842785219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17344721992204132494854501 3252135373538274842785219)
                      ·
                        rfl

theorem cell23_6333511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_6333511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333511 prefixEnd_6333511 := by exact prefixLift 6333511
  have htrace : WordTrace (prefixWord ++ tailWord_6333511) baseStart_6333511 baseEnd_6333511 := by
    simpa [prefixWord, tailWord_6333511, baseEnd_6333511] using wordTrace_append hprefix tailTrace_6333511
  have hstable : (prefixWord ++ tailWord_6333511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333511).length < 2 ^ (prefixWord ++ tailWord_6333511).sum := by decide
  have hdescent : baseEnd_6333511 < baseStart_6333511 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333578 : List Nat := [3, 1, 2, 3, 1, 1, 1, 2, 5, 1, 3]
def baseStart_6333578 : Nat := 118140960795 + 6333578 * 2 ^ 59
def prefixEnd_6333578 : Nat := 4983230072969 + 3 ^ 40 * 6333578 * 2
def baseEnd_6333578 : Nat := 3252169776742126080647411

theorem tailTrace_6333578 : CollatzResearch.WordTrace tailWord_6333578 prefixEnd_6333578 3252169776742126080647411 := by
  unfold tailWord_6333578
  simp only [CollatzResearch.WordTrace]
  refine ⟨57751141862134017462462347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154003044965690713233232925 57751141862134017462462347)
  ·
    refine ⟨86626712793201026193693521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57751141862134017462462347 86626712793201026193693521)
    ·
      refine ⟨64970034594900769645270141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86626712793201026193693521 64970034594900769645270141)
      ·
        refine ⟨24363762973087788616976303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64970034594900769645270141 24363762973087788616976303)
        ·
          refine ⟨36545644459631682925464455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24363762973087788616976303 36545644459631682925464455)
          ·
            refine ⟨54818466689447524388196683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36545644459631682925464455 54818466689447524388196683)
            ·
              refine ⟨82227700034171286582295025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54818466689447524388196683 82227700034171286582295025)
              ·
                refine ⟨61670775025628464936721269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82227700034171286582295025 61670775025628464936721269)
                ·
                  refine ⟨5781635158652668587817619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61670775025628464936721269 5781635158652668587817619)
                  ·
                    refine ⟨8672452737979002881726429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5781635158652668587817619 8672452737979002881726429)
                    ·
                      refine ⟨3252169776742126080647411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8672452737979002881726429 3252169776742126080647411)
                      ·
                        rfl

theorem cell23_6333578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_6333578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333578 prefixEnd_6333578 := by exact prefixLift 6333578
  have htrace : WordTrace (prefixWord ++ tailWord_6333578) baseStart_6333578 baseEnd_6333578 := by
    simpa [prefixWord, tailWord_6333578, baseEnd_6333578] using wordTrace_append hprefix tailTrace_6333578
  have hstable : (prefixWord ++ tailWord_6333578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333578).length < 2 ^ (prefixWord ++ tailWord_6333578).sum := by decide
  have hdescent : baseEnd_6333578 < baseStart_6333578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333618 : List Nat := [3, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4]
def baseStart_6333618 : Nat := 118140960795 + 6333618 * 2 ^ 59
def prefixEnd_6333618 : Nat := 4983230072969 + 3 ^ 40 * 6333618 * 2
def baseEnd_6333618 : Nat := 3252190315968305924147227

theorem tailTrace_6333618 : CollatzResearch.WordTrace tailWord_6333618 prefixEnd_6333618 3252190315968305924147227 := by
  unfold tailWord_6333618
  simp only [CollatzResearch.WordTrace]
  refine ⟨57751506592097789170326377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154004017578927437787537005 57751506592097789170326377)
  ·
    refine ⟨43313629944073341877744783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57751506592097789170326377 43313629944073341877744783)
    ·
      refine ⟨64970444916110012816617175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43313629944073341877744783 64970444916110012816617175)
      ·
        refine ⟨97455667374165019224925763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64970444916110012816617175 97455667374165019224925763)
        ·
          refine ⟨146183501061247528837388645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97455667374165019224925763 146183501061247528837388645)
          ·
            refine ⟨27409406448983911657010371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146183501061247528837388645 27409406448983911657010371)
            ·
              refine ⟨41114109673475867485515557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27409406448983911657010371 41114109673475867485515557)
              ·
                refine ⟨7708895563776725153534167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41114109673475867485515557 7708895563776725153534167)
                ·
                  refine ⟨11563343345665087730301251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7708895563776725153534167 11563343345665087730301251)
                  ·
                    refine ⟨17345015018497631595451877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11563343345665087730301251 17345015018497631595451877)
                    ·
                      refine ⟨3252190315968305924147227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17345015018497631595451877 3252190315968305924147227)
                      ·
                        rfl

theorem cell23_6333618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4].length) (baseStart_6333618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333618 prefixEnd_6333618 := by exact prefixLift 6333618
  have htrace : WordTrace (prefixWord ++ tailWord_6333618) baseStart_6333618 baseEnd_6333618 := by
    simpa [prefixWord, tailWord_6333618, baseEnd_6333618] using wordTrace_append hprefix tailTrace_6333618
  have hstable : (prefixWord ++ tailWord_6333618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333618).length < 2 ^ (prefixWord ++ tailWord_6333618).sum := by decide
  have hdescent : baseEnd_6333618 < baseStart_6333618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333628 : List Nat := [2, 2, 2, 3, 2, 1, 1, 2, 4, 4]
def baseStart_6333628 : Nat := 118140960795 + 6333628 * 2 ^ 59
def prefixEnd_6333628 : Nat := 4983230072969 + 3 ^ 40 * 6333628 * 2
def baseEnd_6333628 : Nat := 1084065150258283628340727

theorem tailTrace_6333628 : CollatzResearch.WordTrace tailWord_6333628 prefixEnd_6333628 1084065150258283628340727 := by
  unfold tailWord_6333628
  simp only [CollatzResearch.WordTrace]
  refine ⟨115503195549177464194584769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154004260732236618926113025 115503195549177464194584769)
  ·
    refine ⟨86627396661883098145938577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115503195549177464194584769 86627396661883098145938577)
    ·
      refine ⟨64970547496412323609453933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86627396661883098145938577 64970547496412323609453933)
      ·
        refine ⟨24363955311154621353545225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64970547496412323609453933 24363955311154621353545225)
        ·
          refine ⟨18272966483365966015158919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24363955311154621353545225 18272966483365966015158919)
          ·
            refine ⟨27409449725048949022738379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18272966483365966015158919 27409449725048949022738379)
            ·
              refine ⟨41114174587573423534107569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27409449725048949022738379 41114174587573423534107569)
              ·
                refine ⟨30835630940680067650580677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41114174587573423534107569 30835630940680067650580677)
                ·
                  refine ⟨5781680801377512684483877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30835630940680067650580677 5781680801377512684483877)
                  ·
                    refine ⟨1084065150258283628340727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5781680801377512684483877 1084065150258283628340727)
                    ·
                      rfl

theorem cell23_6333628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 4, 4].length) (baseStart_6333628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333628 prefixEnd_6333628 := by exact prefixLift 6333628
  have htrace : WordTrace (prefixWord ++ tailWord_6333628) baseStart_6333628 baseEnd_6333628 := by
    simpa [prefixWord, tailWord_6333628, baseEnd_6333628] using wordTrace_append hprefix tailTrace_6333628
  have hstable : (prefixWord ++ tailWord_6333628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333628).length < 2 ^ (prefixWord ++ tailWord_6333628).sum := by decide
  have hdescent : baseEnd_6333628 < baseStart_6333628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333631 : List Nat := [1, 1, 2, 2, 2, 2, 2, 4, 1, 2, 4]
def baseStart_6333631 : Nat := 118140960795 + 6333631 * 2 ^ 59
def prefixEnd_6333631 : Nat := 4983230072969 + 3 ^ 40 * 6333631 * 2
def baseEnd_6333631 : Nat := 3252196991216814373284667

theorem tailTrace_6333631 : CollatzResearch.WordTrace tailWord_6333631 prefixEnd_6333631 3252196991216814373284667 := by
  unfold tailWord_6333631
  simp only [CollatzResearch.WordTrace]
  refine ⟨231006500517344059901528747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154004333678229373267685831 231006500517344059901528747)
  ·
    refine ⟨346509750776016089852293121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231006500517344059901528747 346509750776016089852293121)
    ·
      refine ⟨259882313082012067389219841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346509750776016089852293121 259882313082012067389219841)
      ·
        refine ⟨194911734811509050541914881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259882313082012067389219841 194911734811509050541914881)
        ·
          refine ⟨146183801108631787906436161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194911734811509050541914881 146183801108631787906436161)
          ·
            refine ⟨109637850831473840929827121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146183801108631787906436161 109637850831473840929827121)
            ·
              refine ⟨82228388123605380697370341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109637850831473840929827121 82228388123605380697370341)
              ·
                refine ⟨15417822773176008880756939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82228388123605380697370341 15417822773176008880756939)
                ·
                  refine ⟨23126734159764013321135409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15417822773176008880756939 23126734159764013321135409)
                  ·
                    refine ⟨17345050619823009990851557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23126734159764013321135409 17345050619823009990851557)
                    ·
                      refine ⟨3252196991216814373284667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17345050619823009990851557 3252196991216814373284667)
                      ·
                        rfl

theorem cell23_6333631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 2, 4].length) (baseStart_6333631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333631 prefixEnd_6333631 := by exact prefixLift 6333631
  have htrace : WordTrace (prefixWord ++ tailWord_6333631) baseStart_6333631 baseEnd_6333631 := by
    simpa [prefixWord, tailWord_6333631, baseEnd_6333631] using wordTrace_append hprefix tailTrace_6333631
  have hstable : (prefixWord ++ tailWord_6333631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333631).length < 2 ^ (prefixWord ++ tailWord_6333631).sum := by decide
  have hdescent : baseEnd_6333631 < baseStart_6333631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333651 : List Nat := [1, 1, 1, 2, 1, 1, 1, 6, 3, 3, 3]
def baseStart_6333651 : Nat := 118140960795 + 6333651 * 2 ^ 59
def prefixEnd_6333651 : Nat := 4983230072969 + 3 ^ 40 * 6333651 * 2
def baseEnd_6333651 : Nat := 3252207260829904295034575

theorem tailTrace_6333651 : CollatzResearch.WordTrace tailWord_6333651 prefixEnd_6333651 3252207260829904295034575 := by
  unfold tailWord_6333651
  simp only [CollatzResearch.WordTrace]
  refine ⟨231007229977271603317256807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154004819984847735544837871 231007229977271603317256807)
  ·
    refine ⟨346510844965907404975885211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231007229977271603317256807 346510844965907404975885211)
    ·
      refine ⟨519766267448861107463827817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346510844965907404975885211 519766267448861107463827817)
      ·
        refine ⟨389824700586645830597870863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 519766267448861107463827817 389824700586645830597870863)
        ·
          refine ⟨584737050879968745896806295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389824700586645830597870863 584737050879968745896806295)
          ·
            refine ⟨877105576319953118845209443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 584737050879968745896806295 877105576319953118845209443)
            ·
              refine ⟨1315658364479929678267814165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 877105576319953118845209443 1315658364479929678267814165)
              ·
                refine ⟨61671485834996703668803789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1315658364479929678267814165 61671485834996703668803789)
                ·
                  refine ⟨23126807188123763875801421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61671485834996703668803789 23126807188123763875801421)
                  ·
                    refine ⟨8672552695546411453425533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23126807188123763875801421 8672552695546411453425533)
                    ·
                      refine ⟨3252207260829904295034575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8672552695546411453425533 3252207260829904295034575)
                      ·
                        rfl

theorem cell23_6333651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 3, 3].length) (baseStart_6333651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333651 prefixEnd_6333651 := by exact prefixLift 6333651
  have htrace : WordTrace (prefixWord ++ tailWord_6333651) baseStart_6333651 baseEnd_6333651 := by
    simpa [prefixWord, tailWord_6333651, baseEnd_6333651] using wordTrace_append hprefix tailTrace_6333651
  have hstable : (prefixWord ++ tailWord_6333651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333651).length < 2 ^ (prefixWord ++ tailWord_6333651).sum := by decide
  have hdescent : baseEnd_6333651 < baseStart_6333651 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333701 : List Nat := [1, 3, 1, 1, 2, 1, 4, 2, 2, 6]
def baseStart_6333701 : Nat := 118140960795 + 6333701 * 2 ^ 59
def prefixEnd_6333701 : Nat := 4983230072969 + 3 ^ 40 * 6333701 * 2
def baseEnd_6333701 : Nat := 1084077644954209699803115

theorem tailTrace_6333701 : CollatzResearch.WordTrace tailWord_6333701 prefixEnd_6333701 1084077644954209699803115 := by
  unfold tailWord_6333701
  simp only [CollatzResearch.WordTrace]
  refine ⟨231009053627090461856576957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154006035751393641237717971 231009053627090461856576957)
  ·
    refine ⟨86628395110158923196216359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231009053627090461856576957 86628395110158923196216359)
    ·
      refine ⟨129942592665238384794324539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86628395110158923196216359 129942592665238384794324539)
      ·
        refine ⟨194913888997857577191486809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129942592665238384794324539 194913888997857577191486809)
        ·
          refine ⟨146185416748393182893615107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194913888997857577191486809 146185416748393182893615107)
          ·
            refine ⟨219278125122589774340422661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146185416748393182893615107 219278125122589774340422661)
            ·
              refine ⟨41114648460485582688829249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 219278125122589774340422661 41114648460485582688829249)
              ·
                refine ⟨30835986345364187016621937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41114648460485582688829249 30835986345364187016621937)
                ·
                  refine ⟨23126989759023140262466453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30835986345364187016621937 23126989759023140262466453)
                  ·
                    refine ⟨1084077644954209699803115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23126989759023140262466453 1084077644954209699803115)
                    ·
                      rfl

theorem cell23_6333701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 6].length) (baseStart_6333701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333701 prefixEnd_6333701 := by exact prefixLift 6333701
  have htrace : WordTrace (prefixWord ++ tailWord_6333701) baseStart_6333701 baseEnd_6333701 := by
    simpa [prefixWord, tailWord_6333701, baseEnd_6333701] using wordTrace_append hprefix tailTrace_6333701
  have hstable : (prefixWord ++ tailWord_6333701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333701).length < 2 ^ (prefixWord ++ tailWord_6333701).sum := by decide
  have hdescent : baseEnd_6333701 < baseStart_6333701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333731 : List Nat := [1, 1, 1, 4, 2, 3, 1, 1, 9]
def baseStart_6333731 : Nat := 118140960795 + 6333731 * 2 ^ 59
def prefixEnd_6333731 : Nat := 4983230072969 + 3 ^ 40 * 6333731 * 2
def baseEnd_6333731 : Nat := 361360926586918220226023

theorem tailTrace_6333731 : CollatzResearch.WordTrace tailWord_6333731 prefixEnd_6333731 361360926586918220226023 := by
  unfold tailWord_6333731
  simp only [CollatzResearch.WordTrace]
  refine ⟨231010147816981776980169047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154006765211321184653446031 231010147816981776980169047)
  ·
    refine ⟨346515221725472665470253571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231010147816981776980169047 346515221725472665470253571)
    ·
      refine ⟨519772832588208998205380357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346515221725472665470253571 519772832588208998205380357)
      ·
        refine ⟨97457406110289187163508817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 519772832588208998205380357 97457406110289187163508817)
        ·
          refine ⟨73093054582716890372631613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97457406110289187163508817 73093054582716890372631613)
          ·
            refine ⟨27409895468518833889736855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73093054582716890372631613 27409895468518833889736855)
            ·
              refine ⟨41114843202778250834605283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27409895468518833889736855 41114843202778250834605283)
              ·
                refine ⟨61672264804167376251907925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41114843202778250834605283 61672264804167376251907925)
                ·
                  refine ⟨361360926586918220226023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 61672264804167376251907925 361360926586918220226023)
                  ·
                    rfl

theorem cell23_6333731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 9].length) (baseStart_6333731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333731 prefixEnd_6333731 := by exact prefixLift 6333731
  have htrace : WordTrace (prefixWord ++ tailWord_6333731) baseStart_6333731 baseEnd_6333731 := by
    simpa [prefixWord, tailWord_6333731, baseEnd_6333731] using wordTrace_append hprefix tailTrace_6333731
  have hstable : (prefixWord ++ tailWord_6333731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333731).length < 2 ^ (prefixWord ++ tailWord_6333731).sum := by decide
  have hdescent : baseEnd_6333731 < baseStart_6333731 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333748 : List Nat := [2, 5, 1, 1, 1, 1, 1, 2, 9]
def baseStart_6333748 : Nat := 118140960795 + 6333748 * 2 ^ 59
def prefixEnd_6333748 : Nat := 4983230072969 + 3 ^ 40 * 6333748 * 2
def baseEnd_6333748 : Nat := 361361896494821157280181

theorem tailTrace_6333748 : CollatzResearch.WordTrace tailWord_6333748 prefixEnd_6333748 361361896494821157280181 := by
  unfold tailWord_6333748
  simp only [CollatzResearch.WordTrace]
  refine ⟨115505383928960094441768949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154007178571946792589025265 115505383928960094441768949)
  ·
    refine ⟨10828629743340008853915839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115505383928960094441768949 10828629743340008853915839)
    ·
      refine ⟨16242944615010013280873759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10828629743340008853915839 16242944615010013280873759)
      ·
        refine ⟨24364416922515019921310639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16242944615010013280873759 24364416922515019921310639)
        ·
          refine ⟨36546625383772529881965959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24364416922515019921310639 36546625383772529881965959)
          ·
            refine ⟨54819938075658794822948939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36546625383772529881965959 54819938075658794822948939)
            ·
              refine ⟨82229907113488192234423409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54819938075658794822948939 82229907113488192234423409)
              ·
                refine ⟨61672430335116144175817557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82229907113488192234423409 61672430335116144175817557)
                ·
                  refine ⟨361361896494821157280181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 61672430335116144175817557 361361896494821157280181)
                  ·
                    rfl

theorem cell23_6333748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_6333748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333748 prefixEnd_6333748 := by exact prefixLift 6333748
  have htrace : WordTrace (prefixWord ++ tailWord_6333748) baseStart_6333748 baseEnd_6333748 := by
    simpa [prefixWord, tailWord_6333748, baseEnd_6333748] using wordTrace_append hprefix tailTrace_6333748
  have hstable : (prefixWord ++ tailWord_6333748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333748).length < 2 ^ (prefixWord ++ tailWord_6333748).sum := by decide
  have hdescent : baseEnd_6333748 < baseStart_6333748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333759 : List Nat := [1, 1, 2, 2, 4, 4, 1, 2, 2, 2, 2]
def baseStart_6333759 : Nat := 118140960795 + 6333759 * 2 ^ 59
def prefixEnd_6333759 : Nat := 4983230072969 + 3 ^ 40 * 6333759 * 2
def baseEnd_6333759 : Nat := 3252262716740589872484079

theorem tailTrace_6333759 : CollatzResearch.WordTrace tailWord_6333759 prefixEnd_6333759 3252262716740589872484079 := by
  unfold tailWord_6333759
  simp only [CollatzResearch.WordTrace]
  refine ⟨231011169060880337762188331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154007446040586891841458887 231011169060880337762188331)
  ·
    refine ⟨346516753591320506643282497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231011169060880337762188331 346516753591320506643282497)
    ·
      refine ⟨259887565193490379982461873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346516753591320506643282497 259887565193490379982461873)
      ·
        refine ⟨194915673895117784986846405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259887565193490379982461873 194915673895117784986846405)
        ·
          refine ⟨36546688855334584685033701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194915673895117784986846405 36546688855334584685033701)
          ·
            refine ⟨6852504160375234628443819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36546688855334584685033701 6852504160375234628443819)
            ·
              refine ⟨10278756240562851942665729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6852504160375234628443819 10278756240562851942665729)
              ·
                refine ⟨7709067180422138956999297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10278756240562851942665729 7709067180422138956999297)
                ·
                  refine ⟨5781800385316604217749473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7709067180422138956999297 5781800385316604217749473)
                  ·
                    refine ⟨4336350288987453163312105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5781800385316604217749473 4336350288987453163312105)
                    ·
                      refine ⟨3252262716740589872484079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4336350288987453163312105 3252262716740589872484079)
                      ·
                        rfl

theorem cell23_6333759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 2, 2, 2, 2].length) (baseStart_6333759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333759 prefixEnd_6333759 := by exact prefixLift 6333759
  have htrace : WordTrace (prefixWord ++ tailWord_6333759) baseStart_6333759 baseEnd_6333759 := by
    simpa [prefixWord, tailWord_6333759, baseEnd_6333759] using wordTrace_append hprefix tailTrace_6333759
  have hstable : (prefixWord ++ tailWord_6333759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333759).length < 2 ^ (prefixWord ++ tailWord_6333759).sum := by decide
  have hdescent : baseEnd_6333759 < baseStart_6333759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333771 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 5]
def baseStart_6333771 : Nat := 118140960795 + 6333771 * 2 ^ 59
def prefixEnd_6333771 : Nat := 4983230072969 + 3 ^ 40 * 6333771 * 2
def baseEnd_6333771 : Nat := 3252268878508443825534023

theorem tailTrace_6333771 : CollatzResearch.WordTrace tailWord_6333771 prefixEnd_6333771 3252268878508443825534023 := by
  unfold tailWord_6333771
  simp only [CollatzResearch.WordTrace]
  refine ⟨231011606736836863811625167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154007737824557909207750111 231011606736836863811625167)
  ·
    refine ⟨346517410105255295717437751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231011606736836863811625167 346517410105255295717437751)
    ·
      refine ⟨519776115157882943576156627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346517410105255295717437751 519776115157882943576156627)
      ·
        refine ⟨779664172736824415364234941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 519776115157882943576156627 779664172736824415364234941)
        ·
          refine ⟨292374064776309155761588103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 779664172736824415364234941 292374064776309155761588103)
          ·
            refine ⟨438561097164463733642382155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292374064776309155761588103 438561097164463733642382155)
            ·
              refine ⟨657841645746695600463573233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 438561097164463733642382155 657841645746695600463573233)
              ·
                refine ⟨493381234310021700347679925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 657841645746695600463573233 493381234310021700347679925)
                ·
                  refine ⟨46254490716564534407594993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 493381234310021700347679925 46254490716564534407594993)
                  ·
                    refine ⟨34690868037423400805696245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46254490716564534407594993 34690868037423400805696245)
                    ·
                      refine ⟨3252268878508443825534023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34690868037423400805696245 3252268878508443825534023)
                      ·
                        rfl

theorem cell23_6333771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 5].length) (baseStart_6333771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333771 prefixEnd_6333771 := by exact prefixLift 6333771
  have htrace : WordTrace (prefixWord ++ tailWord_6333771) baseStart_6333771 baseEnd_6333771 := by
    simpa [prefixWord, tailWord_6333771, baseEnd_6333771] using wordTrace_append hprefix tailTrace_6333771
  have hstable : (prefixWord ++ tailWord_6333771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333771).length < 2 ^ (prefixWord ++ tailWord_6333771).sum := by decide
  have hdescent : baseEnd_6333771 < baseStart_6333771 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333791 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 1, 10]
def baseStart_6333791 : Nat := 118140960795 + 6333791 * 2 ^ 59
def prefixEnd_6333791 : Nat := 4983230072969 + 3 ^ 40 * 6333791 * 2
def baseEnd_6333791 : Nat := 1084093049373844582427977

theorem tailTrace_6333791 : CollatzResearch.WordTrace tailWord_6333791 prefixEnd_6333791 1084093049373844582427977 := by
  unfold tailWord_6333791
  simp only [CollatzResearch.WordTrace]
  refine ⟨231012336196764407227353227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154008224131176271484902151 231012336196764407227353227)
  ·
    refine ⟨346518504295146610841029841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231012336196764407227353227 346518504295146610841029841)
    ·
      refine ⟨259888878221359958130772381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346518504295146610841029841 259888878221359958130772381)
      ·
        refine ⟨97458329333009984299039643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259888878221359958130772381 97458329333009984299039643)
        ·
          refine ⟨146187493999514976448559465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97458329333009984299039643 146187493999514976448559465)
          ·
            refine ⟨109640620499636232336419599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146187493999514976448559465 109640620499636232336419599)
            ·
              refine ⟨164460930749454348504629399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109640620499636232336419599 164460930749454348504629399)
              ·
                refine ⟨246691396124181522756944099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164460930749454348504629399 246691396124181522756944099)
                ·
                  refine ⟨370037094186272284135416149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 246691396124181522756944099 370037094186272284135416149)
                  ·
                    refine ⟨1084093049373844582427977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 370037094186272284135416149 1084093049373844582427977)
                    ·
                      rfl

theorem cell23_6333791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 10].length) (baseStart_6333791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333791 prefixEnd_6333791 := by exact prefixLift 6333791
  have htrace : WordTrace (prefixWord ++ tailWord_6333791) baseStart_6333791 baseEnd_6333791 := by
    simpa [prefixWord, tailWord_6333791, baseEnd_6333791] using wordTrace_append hprefix tailTrace_6333791
  have hstable : (prefixWord ++ tailWord_6333791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333791).length < 2 ^ (prefixWord ++ tailWord_6333791).sum := by decide
  have hdescent : baseEnd_6333791 < baseStart_6333791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333799 : List Nat := [1, 1, 5, 1, 5, 1, 1, 3, 5]
def baseStart_6333799 : Nat := 118140960795 + 6333799 * 2 ^ 59
def prefixEnd_6333799 : Nat := 4983230072969 + 3 ^ 40 * 6333799 * 2
def baseEnd_6333799 : Nat := 361364806218529968442655

theorem tailTrace_6333799 : CollatzResearch.WordTrace tailWord_6333799 prefixEnd_6333799 361364806218529968442655 := by
  unfold tailWord_6333799
  simp only [CollatzResearch.WordTrace]
  refine ⟨231012627980735424593644451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154008418653823616395762967 231012627980735424593644451)
  ·
    refine ⟨346518941971103136890466677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231012627980735424593644451 346518941971103136890466677)
    ·
      refine ⟨32486150809790919083481251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 346518941971103136890466677 32486150809790919083481251)
      ·
        refine ⟨48729226214686378625221877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32486150809790919083481251 48729226214686378625221877)
        ·
          refine ⟨4568364957626847996114551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48729226214686378625221877 4568364957626847996114551)
          ·
            refine ⟨6852547436440271994171827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4568364957626847996114551 6852547436440271994171827)
            ·
              refine ⟨10278821154660407991257741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6852547436440271994171827 10278821154660407991257741)
              ·
                refine ⟨3854557932997652996721653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10278821154660407991257741 3854557932997652996721653)
                ·
                  refine ⟨361364806218529968442655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3854557932997652996721653 361364806218529968442655)
                  ·
                    rfl

theorem cell23_6333799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 3, 5].length) (baseStart_6333799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333799 prefixEnd_6333799 := by exact prefixLift 6333799
  have htrace : WordTrace (prefixWord ++ tailWord_6333799) baseStart_6333799 baseEnd_6333799 := by
    simpa [prefixWord, tailWord_6333799, baseEnd_6333799] using wordTrace_append hprefix tailTrace_6333799
  have hstable : (prefixWord ++ tailWord_6333799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333799).length < 2 ^ (prefixWord ++ tailWord_6333799).sum := by decide
  have hdescent : baseEnd_6333799 < baseStart_6333799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333928 : List Nat := [2, 1, 4, 1, 1, 2, 12]
def baseStart_6333928 : Nat := 118140960795 + 6333928 * 2 ^ 59
def prefixEnd_6333928 : Nat := 4983230072969 + 3 ^ 40 * 6333928 * 2
def baseEnd_6333928 : Nat := 40152462900879008781121

theorem tailTrace_6333928 : CollatzResearch.WordTrace tailWord_6333928 prefixEnd_6333928 40152462900879008781121 := by
  unfold tailWord_6333928
  simp only [CollatzResearch.WordTrace]
  refine ⟨115508666498634039812545219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154011555331512053083393625 115508666498634039812545219)
  ·
    refine ⟨173262999747951059718817829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115508666498634039812545219 173262999747951059718817829)
    ·
      refine ⟨32486812452740823697278343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173262999747951059718817829 32486812452740823697278343)
      ·
        refine ⟨48730218679111235545917515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32486812452740823697278343 48730218679111235545917515)
        ·
          refine ⟨73095328018666853318876273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48730218679111235545917515 73095328018666853318876273)
          ·
            refine ⟨54821496014000139989157205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73095328018666853318876273 54821496014000139989157205)
            ·
              refine ⟨40152462900879008781121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 54821496014000139989157205 40152462900879008781121)
              ·
                rfl

theorem cell23_6333928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 12].length) (baseStart_6333928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333928 prefixEnd_6333928 := by exact prefixLift 6333928
  have htrace : WordTrace (prefixWord ++ tailWord_6333928) baseStart_6333928 baseEnd_6333928 := by
    simpa [prefixWord, tailWord_6333928, baseEnd_6333928] using wordTrace_append hprefix tailTrace_6333928
  have hstable : (prefixWord ++ tailWord_6333928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333928).length < 2 ^ (prefixWord ++ tailWord_6333928).sum := by decide
  have hdescent : baseEnd_6333928 < baseStart_6333928 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333942 : List Nat := [5, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5]
def baseStart_6333942 : Nat := 118140960795 + 6333942 * 2 ^ 59
def prefixEnd_6333942 : Nat := 4983230072969 + 3 ^ 40 * 6333942 * 2
def baseEnd_6333942 : Nat := 3252356683700362656495737

theorem tailTrace_6333942 : CollatzResearch.WordTrace tailWord_6333942 prefixEnd_6333942 3252356683700362656495737 := by
  unfold tailWord_6333942
  simp only [CollatzResearch.WordTrace]
  refine ⟨14438615226201085001006255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154011895746144906677400053 14438615226201085001006255)
  ·
    refine ⟨21657922839301627501509383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14438615226201085001006255 21657922839301627501509383)
    ·
      refine ⟨32486884258952441252264075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21657922839301627501509383 32486884258952441252264075)
      ·
        refine ⟨48730326388428661878396113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32486884258952441252264075 48730326388428661878396113)
        ·
          refine ⟨36547744791321496408797085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48730326388428661878396113 36547744791321496408797085)
          ·
            refine ⟨13705404296745561153298907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36547744791321496408797085 13705404296745561153298907)
            ·
              refine ⟨20558106445118341729948361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13705404296745561153298907 20558106445118341729948361)
              ·
                refine ⟨15418579833838756297461271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20558106445118341729948361 15418579833838756297461271)
                ·
                  refine ⟨23127869750758134446191907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15418579833838756297461271 23127869750758134446191907)
                  ·
                    refine ⟨34691804626137201669287861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23127869750758134446191907 34691804626137201669287861)
                    ·
                      refine ⟨3252356683700362656495737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34691804626137201669287861 3252356683700362656495737)
                      ·
                        rfl

theorem cell23_6333942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_6333942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333942 prefixEnd_6333942 := by exact prefixLift 6333942
  have htrace : WordTrace (prefixWord ++ tailWord_6333942) baseStart_6333942 baseEnd_6333942 := by
    simpa [prefixWord, tailWord_6333942, baseEnd_6333942] using wordTrace_append hprefix tailTrace_6333942
  have hstable : (prefixWord ++ tailWord_6333942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333942).length < 2 ^ (prefixWord ++ tailWord_6333942).sum := by decide
  have hdescent : baseEnd_6333942 < baseStart_6333942 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333949 : List Nat := [1, 4, 1, 1, 1, 5, 3, 1, 2, 4]
def baseStart_6333949 : Nat := 118140960795 + 6333949 * 2 ^ 59
def prefixEnd_6333949 : Nat := 4983230072969 + 3 ^ 40 * 6333949 * 2
def baseEnd_6333949 : Nat := 1084120092688314709702735

theorem tailTrace_6333949 : CollatzResearch.WordTrace tailWord_6333949 prefixEnd_6333949 1084120092688314709702735 := by
  unfold tailWord_6333949
  simp only [CollatzResearch.WordTrace]
  refine ⟨231018098930192000211604901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154012065953461333474403267 231018098930192000211604901)
  ·
    refine ⟨43315893549411000039675919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231018098930192000211604901 43315893549411000039675919)
    ·
      refine ⟨64973840324116500059513879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43315893549411000039675919 64973840324116500059513879)
      ·
        refine ⟨97460760486174750089270819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64973840324116500059513879 97460760486174750089270819)
        ·
          refine ⟨146191140729262125133906229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97460760486174750089270819 146191140729262125133906229)
          ·
            refine ⟨13705419443368324231303709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 146191140729262125133906229 13705419443368324231303709)
            ·
              refine ⟨5139532291263121586738891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13705419443368324231303709 5139532291263121586738891)
              ·
                refine ⟨7709298436894682380108337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5139532291263121586738891 7709298436894682380108337)
                ·
                  refine ⟨5781973827671011785081253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7709298436894682380108337 5781973827671011785081253)
                  ·
                    refine ⟨1084120092688314709702735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5781973827671011785081253 1084120092688314709702735)
                    ·
                      rfl

theorem cell23_6333949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 1, 2, 4].length) (baseStart_6333949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333949 prefixEnd_6333949 := by exact prefixLift 6333949
  have htrace : WordTrace (prefixWord ++ tailWord_6333949) baseStart_6333949 baseEnd_6333949 := by
    simpa [prefixWord, tailWord_6333949, baseEnd_6333949] using wordTrace_append hprefix tailTrace_6333949
  have hstable : (prefixWord ++ tailWord_6333949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333949).length < 2 ^ (prefixWord ++ tailWord_6333949).sum := by decide
  have hdescent : baseEnd_6333949 < baseStart_6333949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333955 : List Nat := [1, 1, 1, 3, 2, 1, 2, 5, 1, 3, 3]
def baseStart_6333955 : Nat := 118140960795 + 6333955 * 2 ^ 59
def prefixEnd_6333955 : Nat := 4983230072969 + 3 ^ 40 * 6333955 * 2
def baseEnd_6333955 : Nat := 3252363358948871105633177

theorem tailTrace_6333955 : CollatzResearch.WordTrace tailWord_6333955 prefixEnd_6333955 3252363358948871105633177 := by
  unfold tailWord_6333955
  simp only [CollatzResearch.WordTrace]
  refine ⟨231018317768170263236323319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154012211845446842157548879 231018317768170263236323319)
  ·
    refine ⟨346527476652255394854484979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231018317768170263236323319 346527476652255394854484979)
    ·
      refine ⟨519791214978383092281727469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346527476652255394854484979 519791214978383092281727469)
      ·
        refine ⟨194921705616893659605647801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 519791214978383092281727469 194921705616893659605647801)
        ·
          refine ⟨146191279212670244704235851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194921705616893659605647801 146191279212670244704235851)
          ·
            refine ⟨219286918819005367056353777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146191279212670244704235851 219286918819005367056353777)
            ·
              refine ⟨164465189114254025292265333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219286918819005367056353777 164465189114254025292265333)
              ·
                refine ⟨15418611479461314871149875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 164465189114254025292265333 15418611479461314871149875)
                ·
                  refine ⟨23127917219191972306724813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15418611479461314871149875 23127917219191972306724813)
                  ·
                    refine ⟨8672968957196989615021805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23127917219191972306724813 8672968957196989615021805)
                    ·
                      refine ⟨3252363358948871105633177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8672968957196989615021805 3252363358948871105633177)
                      ·
                        rfl

theorem cell23_6333955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 3, 3].length) (baseStart_6333955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333955 prefixEnd_6333955 := by exact prefixLift 6333955
  have htrace : WordTrace (prefixWord ++ tailWord_6333955) baseStart_6333955 baseEnd_6333955 := by
    simpa [prefixWord, tailWord_6333955, baseEnd_6333955] using wordTrace_append hprefix tailTrace_6333955
  have hstable : (prefixWord ++ tailWord_6333955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333955).length < 2 ^ (prefixWord ++ tailWord_6333955).sum := by decide
  have hdescent : baseEnd_6333955 < baseStart_6333955 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333959 : List Nat := [1, 1, 4, 3, 2, 2, 2, 2, 1, 2, 3]
def baseStart_6333959 : Nat := 118140960795 + 6333959 * 2 ^ 59
def prefixEnd_6333959 : Nat := 4983230072969 + 3 ^ 40 * 6333959 * 2
def baseEnd_6333959 : Nat := 3252365412871489089983159

theorem tailTrace_6333959 : CollatzResearch.WordTrace tailWord_6333959 prefixEnd_6333959 3252365412871489089983159 := by
  unfold tailWord_6333959
  simp only [CollatzResearch.WordTrace]
  refine ⟨231018463660155771919468931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154012309106770514612979287 231018463660155771919468931)
  ·
    refine ⟨346527695490233657879203397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231018463660155771919468931 346527695490233657879203397)
    ·
      refine ⟨64973942904418810852350637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 346527695490233657879203397 64973942904418810852350637)
      ·
        refine ⟨24365228589157054069631489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64973942904418810852350637 24365228589157054069631489)
        ·
          refine ⟨18273921441867790552223617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24365228589157054069631489 18273921441867790552223617)
          ·
            refine ⟨13705441081400842914167713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18273921441867790552223617 13705441081400842914167713)
            ·
              refine ⟨10279080811050632185625785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13705441081400842914167713 10279080811050632185625785)
              ·
                refine ⟨7709310608287974139219339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10279080811050632185625785 7709310608287974139219339)
                ·
                  refine ⟨11563965912431961208829009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7709310608287974139219339 11563965912431961208829009)
                  ·
                    refine ⟨8672974434323970906621757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11563965912431961208829009 8672974434323970906621757)
                    ·
                      refine ⟨3252365412871489089983159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8672974434323970906621757 3252365412871489089983159)
                      ·
                        rfl

theorem cell23_6333959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_6333959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333959 prefixEnd_6333959 := by exact prefixLift 6333959
  have htrace : WordTrace (prefixWord ++ tailWord_6333959) baseStart_6333959 baseEnd_6333959 := by
    simpa [prefixWord, tailWord_6333959, baseEnd_6333959] using wordTrace_append hprefix tailTrace_6333959
  have hstable : (prefixWord ++ tailWord_6333959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333959).length < 2 ^ (prefixWord ++ tailWord_6333959).sum := by decide
  have hdescent : baseEnd_6333959 < baseStart_6333959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333962 : List Nat := [3, 1, 2, 2, 2, 4, 2, 7]
def baseStart_6333962 : Nat := 118140960795 + 6333962 * 2 ^ 59
def prefixEnd_6333962 : Nat := 4983230072969 + 3 ^ 40 * 6333962 * 2
def baseEnd_6333962 : Nat := 120458035307905651046135

theorem tailTrace_6333962 : CollatzResearch.WordTrace tailWord_6333962 prefixEnd_6333962 120458035307905651046135 := by
  unfold tailWord_6333962
  simp only [CollatzResearch.WordTrace]
  refine ⟨57754643269786225857957035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154012382052763268954552093 57754643269786225857957035)
  ·
    refine ⟨86631964904679338786935553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57754643269786225857957035 86631964904679338786935553)
    ·
      refine ⟨64973973678509504090201665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86631964904679338786935553 64973973678509504090201665)
      ·
        refine ⟨48730480258882128067651249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64973973678509504090201665 48730480258882128067651249)
        ·
          refine ⟨36547860194161596050738437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48730480258882128067651249 36547860194161596050738437)
          ·
            refine ⟨6852723786405299259513457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36547860194161596050738437 6852723786405299259513457)
            ·
              refine ⟨5139542839803974444635093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6852723786405299259513457 5139542839803974444635093)
              ·
                refine ⟨120458035307905651046135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5139542839803974444635093 120458035307905651046135)
                ·
                  rfl

theorem cell23_6333962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 7].length) (baseStart_6333962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333962 prefixEnd_6333962 := by exact prefixLift 6333962
  have htrace : WordTrace (prefixWord ++ tailWord_6333962) baseStart_6333962 baseEnd_6333962 := by
    simpa [prefixWord, tailWord_6333962, baseEnd_6333962] using wordTrace_append hprefix tailTrace_6333962
  have hstable : (prefixWord ++ tailWord_6333962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333962).length < 2 ^ (prefixWord ++ tailWord_6333962).sum := by decide
  have hdescent : baseEnd_6333962 < baseStart_6333962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6333973 : List Nat := [1, 3, 2, 1, 3, 4, 1, 3, 1, 2, 2]
def baseStart_6333973 : Nat := 118140960795 + 6333973 * 2 ^ 59
def prefixEnd_6333973 : Nat := 4983230072969 + 3 ^ 40 * 6333973 * 2
def baseEnd_6333973 : Nat := 3252372601600652035208095

theorem tailTrace_6333973 : CollatzResearch.WordTrace tailWord_6333973 prefixEnd_6333973 3252372601600652035208095 := by
  unfold tailWord_6333973
  simp only [CollatzResearch.WordTrace]
  refine ⟨231018974282105052310478573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154012649521403368206985715 231018974282105052310478573)
  ·
    refine ⟨86632115355789394616429465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231018974282105052310478573 86632115355789394616429465)
    ·
      refine ⟨64974086516842045962322099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86632115355789394616429465 64974086516842045962322099)
      ·
        refine ⟨97461129775263068943483149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64974086516842045962322099 97461129775263068943483149)
        ·
          refine ⟨36547923665723650853806181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97461129775263068943483149 36547923665723650853806181)
          ·
            refine ⟨6852735687323184535088659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36547923665723650853806181 6852735687323184535088659)
            ·
              refine ⟨10279103530984776802632989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6852735687323184535088659 10279103530984776802632989)
              ·
                refine ⟨3854663824119291300987371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10279103530984776802632989 3854663824119291300987371)
                ·
                  refine ⟨5781995736178936951481057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3854663824119291300987371 5781995736178936951481057)
                  ·
                    refine ⟨4336496802134202713610793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5781995736178936951481057 4336496802134202713610793)
                    ·
                      refine ⟨3252372601600652035208095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4336496802134202713610793 3252372601600652035208095)
                      ·
                        rfl

theorem cell23_6333973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 3, 1, 2, 2].length) (baseStart_6333973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6333973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6333973 prefixEnd_6333973 := by exact prefixLift 6333973
  have htrace : WordTrace (prefixWord ++ tailWord_6333973) baseStart_6333973 baseEnd_6333973 := by
    simpa [prefixWord, tailWord_6333973, baseEnd_6333973] using wordTrace_append hprefix tailTrace_6333973
  have hstable : (prefixWord ++ tailWord_6333973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6333973).length < 2 ^ (prefixWord ++ tailWord_6333973).sum := by decide
  have hdescent : baseEnd_6333973 < baseStart_6333973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6333973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334015 : List Nat := [1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 5]
def baseStart_6334015 : Nat := 118140960795 + 6334015 * 2 ^ 59
def prefixEnd_6334015 : Nat := 4983230072969 + 3 ^ 40 * 6334015 * 2
def baseEnd_6334015 : Nat := 3252394167788140870882901

theorem tailTrace_6334015 : CollatzResearch.WordTrace tailWord_6334015 prefixEnd_6334015 3252394167788140870882901 := by
  unfold tailWord_6334015
  simp only [CollatzResearch.WordTrace]
  refine ⟨231020506147952893483507499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154013670765301928989004999 231020506147952893483507499)
  ·
    refine ⟨346530759221929340225261249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231020506147952893483507499 346530759221929340225261249)
    ·
      refine ⟨259898069416447005168945937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346530759221929340225261249 259898069416447005168945937)
      ·
        refine ⟨194923552062335253876709453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259898069416447005168945937 194923552062335253876709453)
        ·
          refine ⟨73096332023375720203766045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194923552062335253876709453 73096332023375720203766045)
          ·
            refine ⟨27411124508765895076412267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73096332023375720203766045 27411124508765895076412267)
            ·
              refine ⟨41116686763148842614618401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27411124508765895076412267 41116686763148842614618401)
              ·
                refine ⟨30837515072361631960963801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41116686763148842614618401 30837515072361631960963801)
                ·
                  refine ⟨23128136304271223970722851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30837515072361631960963801 23128136304271223970722851)
                  ·
                    refine ⟨34692204456406835956084277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23128136304271223970722851 34692204456406835956084277)
                    ·
                      refine ⟨3252394167788140870882901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34692204456406835956084277 3252394167788140870882901)
                      ·
                        rfl

theorem cell23_6334015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 5].length) (baseStart_6334015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334015 prefixEnd_6334015 := by exact prefixLift 6334015
  have htrace : WordTrace (prefixWord ++ tailWord_6334015) baseStart_6334015 baseEnd_6334015 := by
    simpa [prefixWord, tailWord_6334015, baseEnd_6334015] using wordTrace_append hprefix tailTrace_6334015
  have hstable : (prefixWord ++ tailWord_6334015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334015).length < 2 ^ (prefixWord ++ tailWord_6334015).sum := by decide
  have hdescent : baseEnd_6334015 < baseStart_6334015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334065 : List Nat := [1, 2, 2, 2, 1, 1, 1, 4, 4, 5]
def baseStart_6334065 : Nat := 118140960795 + 6334065 * 2 ^ 59
def prefixEnd_6334065 : Nat := 4983230072969 + 3 ^ 40 * 6334065 * 2
def baseEnd_6334065 : Nat := 1084139947273621891752557

theorem tailTrace_6334065 : CollatzResearch.WordTrace tailWord_6334065 prefixEnd_6334065 1084139947273621891752557 := by
  unfold tailWord_6334065
  simp only [CollatzResearch.WordTrace]
  refine ⟨231022329797771752022827649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154014886531847834681885099 231022329797771752022827649)
  ·
    refine ⟨173266747348328814017120737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231022329797771752022827649 173266747348328814017120737)
    ·
      refine ⟨129950060511246610512840553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173266747348328814017120737 129950060511246610512840553)
      ·
        refine ⟨97462545383434957884630415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129950060511246610512840553 97462545383434957884630415)
        ·
          refine ⟨146193818075152436826945623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97462545383434957884630415 146193818075152436826945623)
          ·
            refine ⟨219290727112728655240418435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146193818075152436826945623 219290727112728655240418435)
            ·
              refine ⟨328936090669092982860627653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219290727112728655240418435 328936090669092982860627653)
              ·
                refine ⟨61675517000454934286367685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 328936090669092982860627653 61675517000454934286367685)
                ·
                  refine ⟨11564159437585300178693941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61675517000454934286367685 11564159437585300178693941)
                  ·
                    refine ⟨1084139947273621891752557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11564159437585300178693941 1084139947273621891752557)
                    ·
                      rfl

theorem cell23_6334065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 4, 5].length) (baseStart_6334065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334065 prefixEnd_6334065 := by exact prefixLift 6334065
  have htrace : WordTrace (prefixWord ++ tailWord_6334065) baseStart_6334065 baseEnd_6334065 := by
    simpa [prefixWord, tailWord_6334065, baseEnd_6334065] using wordTrace_append hprefix tailTrace_6334065
  have hstable : (prefixWord ++ tailWord_6334065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334065).length < 2 ^ (prefixWord ++ tailWord_6334065).sum := by decide
  have hdescent : baseEnd_6334065 < baseStart_6334065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
