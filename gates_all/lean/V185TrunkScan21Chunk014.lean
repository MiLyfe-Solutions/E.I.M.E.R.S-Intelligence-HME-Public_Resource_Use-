import V185TrunkScan21Chunk013

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_168562 : List Nat := [3, 2, 1, 2, 4, 2, 2, 1, 4]
def baseStart_168562 : Nat := 118140960795 + 168562 * 2 ^ 59
def prefixEnd_168562 : Nat := 4983230072969 + 3 ^ 40 * 168562 * 2
def baseEnd_168562 : Nat := 38468144925899881822135

theorem tailTrace_168562 : CollatzResearch.WordTrace tailWord_168562 prefixEnd_168562 38468144925899881822135 := by
  unfold tailWord_168562
  simp only [CollatzResearch.WordTrace]
  refine ⟨1536990303834034235692985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4098640810224091295181293 1536990303834034235692985)
  ·
    refine ⟨1152742727875525676769739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1536990303834034235692985 1152742727875525676769739)
    ·
      refine ⟨1729114091813288515154609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1152742727875525676769739 1729114091813288515154609)
      ·
        refine ⟨1296835568859966386365957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1729114091813288515154609 1296835568859966386365957)
        ·
          refine ⟨243156669161243697443617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1296835568859966386365957 243156669161243697443617)
          ·
            refine ⟨182367501870932773082713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243156669161243697443617 182367501870932773082713)
            ·
              refine ⟨136775626403199579812035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182367501870932773082713 136775626403199579812035)
              ·
                refine ⟨205163439604799369718053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136775626403199579812035 205163439604799369718053)
                ·
                  refine ⟨38468144925899881822135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 205163439604799369718053 38468144925899881822135)
                  ·
                    rfl

theorem cell21_168562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_168562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_168562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_168562 prefixEnd_168562 := by exact prefixLift 168562
  have htrace : WordTrace (prefixWord ++ tailWord_168562) baseStart_168562 baseEnd_168562 := by
    simpa [prefixWord, tailWord_168562, baseEnd_168562] using wordTrace_append hprefix tailTrace_168562
  have hstable : (prefixWord ++ tailWord_168562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168562).length < 2 ^ (prefixWord ++ tailWord_168562).sum := by decide
  have hdescent : baseEnd_168562 < baseStart_168562 := by decide
  rcases family_descends (prefixWord ++ tailWord_168562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168590 : List Nat := [4, 1, 1, 3, 1, 1, 2, 5, 3]
def baseStart_168590 : Nat := 118140960795 + 168590 * 2 ^ 59
def prefixEnd_168590 : Nat := 4983230072969 + 3 ^ 40 * 168590 * 2
def baseEnd_168590 : Nat := 38474534907378055355411

theorem tailTrace_168590 : CollatzResearch.WordTrace tailWord_168590 prefixEnd_168590 38474534907378055355411 := by
  unfold tailWord_168590
  simp only [CollatzResearch.WordTrace]
  refine ⟨768622807404337215598903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4099321639489798483194149 768622807404337215598903)
  ·
    refine ⟨1152934211106505823398355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 768622807404337215598903 1152934211106505823398355)
    ·
      refine ⟨1729401316659758735097533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1152934211106505823398355 1729401316659758735097533)
      ·
        refine ⟨648525493747409525661575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1729401316659758735097533 648525493747409525661575)
        ·
          refine ⟨972788240621114288492363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 648525493747409525661575 972788240621114288492363)
          ·
            refine ⟨1459182360931671432738545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 972788240621114288492363 1459182360931671432738545)
            ·
              refine ⟨1094386770698753574553909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1459182360931671432738545 1094386770698753574553909)
              ·
                refine ⟨102598759753008147614429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1094386770698753574553909 102598759753008147614429)
                ·
                  refine ⟨38474534907378055355411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102598759753008147614429 38474534907378055355411)
                  ·
                    rfl

theorem cell21_168590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 5, 3].length) (baseStart_168590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_168590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_168590 prefixEnd_168590 := by exact prefixLift 168590
  have htrace : WordTrace (prefixWord ++ tailWord_168590) baseStart_168590 baseEnd_168590 := by
    simpa [prefixWord, tailWord_168590, baseEnd_168590] using wordTrace_append hprefix tailTrace_168590
  have hstable : (prefixWord ++ tailWord_168590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168590).length < 2 ^ (prefixWord ++ tailWord_168590).sum := by decide
  have hdescent : baseEnd_168590 < baseStart_168590 := by decide
  rcases family_descends (prefixWord ++ tailWord_168590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168604 : List Nat := [2, 2, 3, 2, 2, 1, 1, 4, 4]
def baseStart_168604 : Nat := 118140960795 + 168604 * 2 ^ 59
def prefixEnd_168604 : Nat := 4983230072969 + 3 ^ 40 * 168604 * 2
def baseEnd_168604 : Nat := 38477729898117142122049

theorem tailTrace_168604 : CollatzResearch.WordTrace tailWord_168604 prefixEnd_168604 38477729898117142122049 := by
  unfold tailWord_168604
  simp only [CollatzResearch.WordTrace]
  refine ⟨3074746540591989057900433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4099662054122652077200577 3074746540591989057900433)
  ·
    refine ⟨2306059905443991793425325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3074746540591989057900433 2306059905443991793425325)
    ·
      refine ⟨864772464541496922534497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2306059905443991793425325 864772464541496922534497)
      ·
        refine ⟨648579348406122691900873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 864772464541496922534497 648579348406122691900873)
        ·
          refine ⟨486434511304592018925655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 648579348406122691900873 486434511304592018925655)
          ·
            refine ⟨729651766956888028388483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 486434511304592018925655 729651766956888028388483)
            ·
              refine ⟨1094477650435332042582725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 729651766956888028388483 1094477650435332042582725)
              ·
                refine ⟨205214559456624757984261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1094477650435332042582725 205214559456624757984261)
                ·
                  refine ⟨38477729898117142122049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 205214559456624757984261 38477729898117142122049)
                  ·
                    rfl

theorem cell21_168604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 4, 4].length) (baseStart_168604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_168604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_168604 prefixEnd_168604 := by exact prefixLift 168604
  have htrace : WordTrace (prefixWord ++ tailWord_168604) baseStart_168604 baseEnd_168604 := by
    simpa [prefixWord, tailWord_168604, baseEnd_168604] using wordTrace_append hprefix tailTrace_168604
  have hstable : (prefixWord ++ tailWord_168604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168604).length < 2 ^ (prefixWord ++ tailWord_168604).sum := by decide
  have hdescent : baseEnd_168604 < baseStart_168604 := by decide
  rcases family_descends (prefixWord ++ tailWord_168604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168663 : List Nat := [1, 1, 3, 2, 1, 5, 1, 1, 6]
def baseStart_168663 : Nat := 118140960795 + 168663 * 2 ^ 59
def prefixEnd_168663 : Nat := 4983230072969 + 3 ^ 40 * 168663 * 2
def baseEnd_168663 : Nat := 38491194501946150638595

theorem tailTrace_168663 : CollatzResearch.WordTrace tailWord_168663 prefixEnd_168663 38491194501946150638595 := by
  unfold tailWord_168663
  simp only [CollatzResearch.WordTrace]
  refine ⟨6151644987970231192198643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4101096658646820794799095 6151644987970231192198643)
  ·
    refine ⟨9227467481955346788297965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6151644987970231192198643 9227467481955346788297965)
    ·
      refine ⟨3460300305733255045611737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9227467481955346788297965 3460300305733255045611737)
      ·
        refine ⟨2595225229299941284208803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3460300305733255045611737 2595225229299941284208803)
        ·
          refine ⟨3892837843949911926313205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2595225229299941284208803 3892837843949911926313205)
          ·
            refine ⟨364953547870304243091863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3892837843949911926313205 364953547870304243091863)
            ·
              refine ⟨547430321805456364637795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 364953547870304243091863 547430321805456364637795)
              ·
                refine ⟨821145482708184546956693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 547430321805456364637795 821145482708184546956693)
                ·
                  refine ⟨38491194501946150638595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 821145482708184546956693 38491194501946150638595)
                  ·
                    rfl

theorem cell21_168663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 6].length) (baseStart_168663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_168663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_168663 prefixEnd_168663 := by exact prefixLift 168663
  have htrace : WordTrace (prefixWord ++ tailWord_168663) baseStart_168663 baseEnd_168663 := by
    simpa [prefixWord, tailWord_168663, baseEnd_168663] using wordTrace_append hprefix tailTrace_168663
  have hstable : (prefixWord ++ tailWord_168663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168663).length < 2 ^ (prefixWord ++ tailWord_168663).sum := by decide
  have hdescent : baseEnd_168663 < baseStart_168663 := by decide
  rcases family_descends (prefixWord ++ tailWord_168663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168694 : List Nat := [5, 1, 1, 1, 1, 2, 3, 7]
def baseStart_168694 : Nat := 118140960795 + 168694 * 2 ^ 59
def prefixEnd_168694 : Nat := 4983230072969 + 3 ^ 40 * 168694 * 2
def baseEnd_168694 : Nat := 12832756374765661873955

theorem tailTrace_168694 : CollatzResearch.WordTrace tailWord_168694 prefixEnd_168694 12832756374765661873955 := by
  unfold tailWord_168694
  simp only [CollatzResearch.WordTrace]
  refine ⟨384548478178620217911071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4101850433905282324384757 384548478178620217911071)
  ·
    refine ⟨576822717267930326866607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 384548478178620217911071 576822717267930326866607)
    ·
      refine ⟨865234075901895490299911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 576822717267930326866607 865234075901895490299911)
      ·
        refine ⟨1297851113852843235449867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 865234075901895490299911 1297851113852843235449867)
        ·
          refine ⟨1946776670779264853174801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1297851113852843235449867 1946776670779264853174801)
          ·
            refine ⟨1460082503084448639881101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1946776670779264853174801 1460082503084448639881101)
            ·
              refine ⟨547530938656668239955413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1460082503084448639881101 547530938656668239955413)
              ·
                refine ⟨12832756374765661873955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 547530938656668239955413 12832756374765661873955)
                ·
                  rfl

theorem cell21_168694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_168694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_168694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_168694 prefixEnd_168694 := by exact prefixLift 168694
  have htrace : WordTrace (prefixWord ++ tailWord_168694) baseStart_168694 baseEnd_168694 := by
    simpa [prefixWord, tailWord_168694, baseEnd_168694] using wordTrace_append hprefix tailTrace_168694
  have hstable : (prefixWord ++ tailWord_168694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168694).length < 2 ^ (prefixWord ++ tailWord_168694).sum := by decide
  have hdescent : baseEnd_168694 < baseStart_168694 := by decide
  rcases family_descends (prefixWord ++ tailWord_168694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168753 : List Nat := [1, 2, 2, 3, 2, 1, 1, 9]
def baseStart_168753 : Nat := 118140960795 + 168753 * 2 ^ 59
def prefixEnd_168753 : Nat := 4983230072969 + 3 ^ 40 * 168753 * 2
def baseEnd_168753 : Nat := 12837244576041998046137

theorem tailTrace_168753 : CollatzResearch.WordTrace tailWord_168753 prefixEnd_168753 12837244576041998046137 := by
  unfold tailWord_168753
  simp only [CollatzResearch.WordTrace]
  refine ⟨6154927557644176562974913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4103285038429451041983275 6154927557644176562974913)
  ·
    refine ⟨4616195668233132422231185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6154927557644176562974913 4616195668233132422231185)
    ·
      refine ⟨3462146751174849316673389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4616195668233132422231185 3462146751174849316673389)
      ·
        refine ⟨1298305031690568493752521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3462146751174849316673389 1298305031690568493752521)
        ·
          refine ⟨973728773767926370314391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1298305031690568493752521 973728773767926370314391)
          ·
            refine ⟨1460593160651889555471587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 973728773767926370314391 1460593160651889555471587)
            ·
              refine ⟨2190889740977834333207381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1460593160651889555471587 2190889740977834333207381)
              ·
                refine ⟨12837244576041998046137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2190889740977834333207381 12837244576041998046137)
                ·
                  rfl

theorem cell21_168753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 9].length) (baseStart_168753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_168753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_168753 prefixEnd_168753 := by exact prefixLift 168753
  have htrace : WordTrace (prefixWord ++ tailWord_168753) baseStart_168753 baseEnd_168753 := by
    simpa [prefixWord, tailWord_168753, baseEnd_168753] using wordTrace_append hprefix tailTrace_168753
  have hstable : (prefixWord ++ tailWord_168753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168753).length < 2 ^ (prefixWord ++ tailWord_168753).sum := by decide
  have hdescent : baseEnd_168753 < baseStart_168753 := by decide
  rcases family_descends (prefixWord ++ tailWord_168753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168863 : List Nat := [1, 1, 2, 5, 2, 3, 2, 5]
def baseStart_168863 : Nat := 118140960795 + 168863 * 2 ^ 59
def prefixEnd_168863 : Nat := 4983230072969 + 3 ^ 40 * 168863 * 2
def baseEnd_168863 : Nat := 12845612408930082434951

theorem tailTrace_168863 : CollatzResearch.WordTrace tailWord_168863 prefixEnd_168863 12845612408930082434951 := by
  unfold tailWord_168863
  simp only [CollatzResearch.WordTrace]
  refine ⟨6158939587245665349479243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4105959724830443566319495 6158939587245665349479243)
  ·
    refine ⟨9238409380868498024218865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6158939587245665349479243 9238409380868498024218865)
    ·
      refine ⟨6928807035651373518164149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9238409380868498024218865 6928807035651373518164149)
      ·
        refine ⟨649575659592316267327889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6928807035651373518164149 649575659592316267327889)
        ·
          refine ⟨487181744694237200495917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 649575659592316267327889 487181744694237200495917)
          ·
            refine ⟨182693154260338950185969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 487181744694237200495917 182693154260338950185969)
            ·
              refine ⟨137019865695254212639477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182693154260338950185969 137019865695254212639477)
              ·
                refine ⟨12845612408930082434951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 137019865695254212639477 12845612408930082434951)
                ·
                  rfl

theorem cell21_168863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 5].length) (baseStart_168863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_168863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_168863 prefixEnd_168863 := by exact prefixLift 168863
  have htrace : WordTrace (prefixWord ++ tailWord_168863) baseStart_168863 baseEnd_168863 := by
    simpa [prefixWord, tailWord_168863, baseEnd_168863] using wordTrace_append hprefix tailTrace_168863
  have hstable : (prefixWord ++ tailWord_168863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168863).length < 2 ^ (prefixWord ++ tailWord_168863).sum := by decide
  have hdescent : baseEnd_168863 < baseStart_168863 := by decide
  rcases family_descends (prefixWord ++ tailWord_168863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168886 : List Nat := [5, 1, 4, 1, 1, 1, 3, 2, 3]
def baseStart_168886 : Nat := 118140960795 + 168886 * 2 ^ 59
def prefixEnd_168886 : Nat := 4983230072969 + 3 ^ 40 * 168886 * 2
def baseEnd_168886 : Nat := 38542086140147318421473

theorem tailTrace_168886 : CollatzResearch.WordTrace tailWord_168886 prefixEnd_168886 38542086140147318421473 := by
  unfold tailWord_168886
  simp only [CollatzResearch.WordTrace]
  refine ⟨384986154135146267347907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4106518977441560185044341 384986154135146267347907)
  ·
    refine ⟨577479231202719401021861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 384986154135146267347907 577479231202719401021861)
    ·
      refine ⟨108277355850509887691599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 577479231202719401021861 108277355850509887691599)
      ·
        refine ⟨162416033775764831537399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108277355850509887691599 162416033775764831537399)
        ·
          refine ⟨243624050663647247306099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162416033775764831537399 243624050663647247306099)
          ·
            refine ⟨365436075995470870959149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243624050663647247306099 365436075995470870959149)
            ·
              refine ⟨137038528498301576609681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 365436075995470870959149 137038528498301576609681)
              ·
                refine ⟨102778896373726182457261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137038528498301576609681 102778896373726182457261)
                ·
                  refine ⟨38542086140147318421473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102778896373726182457261 38542086140147318421473)
                  ·
                    rfl

theorem cell21_168886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_168886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_168886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_168886 prefixEnd_168886 := by exact prefixLift 168886
  have htrace : WordTrace (prefixWord ++ tailWord_168886) baseStart_168886 baseEnd_168886 := by
    simpa [prefixWord, tailWord_168886, baseEnd_168886] using wordTrace_append hprefix tailTrace_168886
  have hstable : (prefixWord ++ tailWord_168886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168886).length < 2 ^ (prefixWord ++ tailWord_168886).sum := by decide
  have hdescent : baseEnd_168886 < baseStart_168886 := by decide
  rcases family_descends (prefixWord ++ tailWord_168886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168953 : List Nat := [1, 2, 1, 3, 1, 3, 3, 4, 3]
def baseStart_168953 : Nat := 118140960795 + 168953 * 2 ^ 59
def prefixEnd_168953 : Nat := 4983230072969 + 3 ^ 40 * 168953 * 2
def baseEnd_168953 : Nat := 38557376452970090804669

theorem tailTrace_168953 : CollatzResearch.WordTrace tailWord_168953 prefixEnd_168953 38557376452970090804669 := by
  unfold tailWord_168953
  simp only [CollatzResearch.WordTrace]
  refine ⟨6162222156919610720255513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4108148104613073813503675 6162222156919610720255513)
  ·
    refine ⟨4621666617689708040191635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6162222156919610720255513 4621666617689708040191635)
    ·
      refine ⟨6932499926534562060287453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4621666617689708040191635 6932499926534562060287453)
      ·
        refine ⟨2599687472450460772607795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6932499926534562060287453 2599687472450460772607795)
        ·
          refine ⟨3899531208675691158911693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2599687472450460772607795 3899531208675691158911693)
          ·
            refine ⟨1462324203253384184591885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3899531208675691158911693 1462324203253384184591885)
            ·
              refine ⟨548371576220019069221957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1462324203253384184591885 548371576220019069221957)
              ·
                refine ⟨102819670541253575479117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 548371576220019069221957 102819670541253575479117)
                ·
                  refine ⟨38557376452970090804669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102819670541253575479117 38557376452970090804669)
                  ·
                    rfl

theorem cell21_168953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 4, 3].length) (baseStart_168953 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_168953 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_168953 prefixEnd_168953 := by exact prefixLift 168953
  have htrace : WordTrace (prefixWord ++ tailWord_168953) baseStart_168953 baseEnd_168953 := by
    simpa [prefixWord, tailWord_168953, baseEnd_168953] using wordTrace_append hprefix tailTrace_168953
  have hstable : (prefixWord ++ tailWord_168953).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168953).length < 2 ^ (prefixWord ++ tailWord_168953).sum := by decide
  have hdescent : baseEnd_168953 < baseStart_168953 := by decide
  rcases family_descends (prefixWord ++ tailWord_168953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168967 : List Nat := [1, 1, 4, 3, 1, 1, 1, 5, 4]
def baseStart_168967 : Nat := 118140960795 + 168967 * 2 ^ 59
def prefixEnd_168967 : Nat := 4983230072969 + 3 ^ 40 * 168967 * 2
def baseEnd_168967 : Nat := 38560571443709177571307

theorem tailTrace_168967 : CollatzResearch.WordTrace tailWord_168967 prefixEnd_168967 38560571443709177571307 := by
  unfold tailWord_168967
  simp only [CollatzResearch.WordTrace]
  refine ⟨6162732778868891111265155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4108488519245927407510103 6162732778868891111265155)
  ·
    refine ⟨9244099168303336666897733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6162732778868891111265155 9244099168303336666897733)
    ·
      refine ⟨1733268594056875625043325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9244099168303336666897733 1733268594056875625043325)
      ·
        refine ⟨649975722771328359391247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1733268594056875625043325 649975722771328359391247)
        ·
          refine ⟨974963584156992539086871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 649975722771328359391247 974963584156992539086871)
          ·
            refine ⟨1462445376235488808630307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 974963584156992539086871 1462445376235488808630307)
            ·
              refine ⟨2193668064353233212945461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1462445376235488808630307 2193668064353233212945461)
              ·
                refine ⟨205656381033115613713637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2193668064353233212945461 205656381033115613713637)
                ·
                  refine ⟨38560571443709177571307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 205656381033115613713637 38560571443709177571307)
                  ·
                    rfl

theorem cell21_168967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 5, 4].length) (baseStart_168967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_168967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_168967 prefixEnd_168967 := by exact prefixLift 168967
  have htrace : WordTrace (prefixWord ++ tailWord_168967) baseStart_168967 baseEnd_168967 := by
    simpa [prefixWord, tailWord_168967, baseEnd_168967] using wordTrace_append hprefix tailTrace_168967
  have hstable : (prefixWord ++ tailWord_168967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168967).length < 2 ^ (prefixWord ++ tailWord_168967).sum := by decide
  have hdescent : baseEnd_168967 < baseStart_168967 := by decide
  rcases family_descends (prefixWord ++ tailWord_168967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169077 : List Nat := [1, 3, 4, 3, 1, 1, 1, 3, 4]
def baseStart_169077 : Nat := 118140960795 + 169077 * 2 ^ 59
def prefixEnd_169077 : Nat := 4983230072969 + 3 ^ 40 * 169077 * 2
def baseEnd_169077 : Nat := 38585674942373430737749

theorem tailTrace_169077 : CollatzResearch.WordTrace tailWord_169077 prefixEnd_169077 38585674942373430737749 := by
  unfold tailWord_169077
  simp only [CollatzResearch.WordTrace]
  refine ⟨6166744808470379897769485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4111163205646919931846323 6166744808470379897769485)
  ·
    refine ⟨2312529303176392461663557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6166744808470379897769485 2312529303176392461663557)
    ·
      refine ⟨433599244345573586561917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2312529303176392461663557 433599244345573586561917)
      ·
        refine ⟨162599716629590094960719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 433599244345573586561917 162599716629590094960719)
        ·
          refine ⟨243899574944385142441079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162599716629590094960719 243899574944385142441079)
          ·
            refine ⟨365849362416577713661619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243899574944385142441079 365849362416577713661619)
            ·
              refine ⟨548774043624866570492429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 365849362416577713661619 548774043624866570492429)
              ·
                refine ⟨205790266359324963934661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 548774043624866570492429 205790266359324963934661)
                ·
                  refine ⟨38585674942373430737749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 205790266359324963934661 38585674942373430737749)
                  ·
                    rfl

theorem cell21_169077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 3, 4].length) (baseStart_169077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_169077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_169077 prefixEnd_169077 := by exact prefixLift 169077
  have htrace : WordTrace (prefixWord ++ tailWord_169077) baseStart_169077 baseEnd_169077 := by
    simpa [prefixWord, tailWord_169077, baseEnd_169077] using wordTrace_append hprefix tailTrace_169077
  have hstable : (prefixWord ++ tailWord_169077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169077).length < 2 ^ (prefixWord ++ tailWord_169077).sum := by decide
  have hdescent : baseEnd_169077 < baseStart_169077 := by decide
  rcases family_descends (prefixWord ++ tailWord_169077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169240 : List Nat := [2, 1, 2, 3, 1, 3, 3, 1, 5]
def baseStart_169240 : Nat := 118140960795 + 169240 * 2 ^ 59
def prefixEnd_169240 : Nat := 4983230072969 + 3 ^ 40 * 169240 * 2
def baseEnd_169240 : Nat := 38622873763121369520749

theorem tailTrace_169240 : CollatzResearch.WordTrace tailWord_169240 prefixEnd_169240 38622873763121369520749 := by
  unfold tailWord_169240
  simp only [CollatzResearch.WordTrace]
  refine ⟨3086344953439929367976587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4115126604586572490635449 3086344953439929367976587)
  ·
    refine ⟨4629517430159894051964881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3086344953439929367976587 4629517430159894051964881)
    ·
      refine ⟨3472138072619920538973661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4629517430159894051964881 3472138072619920538973661)
      ·
        refine ⟨1302051777232470202115123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3472138072619920538973661 1302051777232470202115123)
        ·
          refine ⟨1953077665848705303172685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1302051777232470202115123 1953077665848705303172685)
          ·
            refine ⟨732404124693264488689757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1953077665848705303172685 732404124693264488689757)
            ·
              refine ⟨274651546759974183258659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 732404124693264488689757 274651546759974183258659)
              ·
                refine ⟨411977320139961274887989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 274651546759974183258659 411977320139961274887989)
                ·
                  refine ⟨38622873763121369520749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 411977320139961274887989 38622873763121369520749)
                  ·
                    rfl

theorem cell21_169240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 5].length) (baseStart_169240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_169240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_169240 prefixEnd_169240 := by exact prefixLift 169240
  have htrace : WordTrace (prefixWord ++ tailWord_169240) baseStart_169240 baseEnd_169240 := by
    simpa [prefixWord, tailWord_169240, baseEnd_169240] using wordTrace_append hprefix tailTrace_169240
  have hstable : (prefixWord ++ tailWord_169240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169240).length < 2 ^ (prefixWord ++ tailWord_169240).sum := by decide
  have hdescent : baseEnd_169240 < baseStart_169240 := by decide
  rcases family_descends (prefixWord ++ tailWord_169240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169299 : List Nat := [1, 1, 1, 2, 1, 1, 6, 3, 5]
def baseStart_169299 : Nat := 118140960795 + 169299 * 2 ^ 59
def prefixEnd_169299 : Nat := 4983230072969 + 3 ^ 40 * 169299 * 2
def baseEnd_169299 : Nat := 38636338366950378037295

theorem tailTrace_169299 : CollatzResearch.WordTrace tailWord_169299 prefixEnd_169299 38636338366950378037295 := by
  unfold tailWord_169299
  simp only [CollatzResearch.WordTrace]
  refine ⟨6174841813666111812350951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4116561209110741208233967 6174841813666111812350951)
  ·
    refine ⟨9262262720499167718526427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6174841813666111812350951 9262262720499167718526427)
    ·
      refine ⟨13893394080748751577789641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9262262720499167718526427 13893394080748751577789641)
      ·
        refine ⟨10420045560561563683342231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13893394080748751577789641 10420045560561563683342231)
        ·
          refine ⟨15630068340842345525013347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10420045560561563683342231 15630068340842345525013347)
          ·
            refine ⟨23445102511263518287520021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15630068340842345525013347 23445102511263518287520021)
            ·
              refine ⟨1098989180215477419727501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23445102511263518287520021 1098989180215477419727501)
              ·
                refine ⟨412120942580804032397813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1098989180215477419727501 412120942580804032397813)
                ·
                  refine ⟨38636338366950378037295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 412120942580804032397813 38636338366950378037295)
                  ·
                    rfl

theorem cell21_169299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 5].length) (baseStart_169299 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_169299 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_169299 prefixEnd_169299 := by exact prefixLift 169299
  have htrace : WordTrace (prefixWord ++ tailWord_169299) baseStart_169299 baseEnd_169299 := by
    simpa [prefixWord, tailWord_169299, baseEnd_169299] using wordTrace_append hprefix tailTrace_169299
  have hstable : (prefixWord ++ tailWord_169299).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169299).length < 2 ^ (prefixWord ++ tailWord_169299).sum := by decide
  have hdescent : baseEnd_169299 < baseStart_169299 := by decide
  rcases family_descends (prefixWord ++ tailWord_169299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169316 : List Nat := [2, 3, 1, 1, 3, 3, 1, 2, 5]
def baseStart_169316 : Nat := 118140960795 + 169316 * 2 ^ 59
def prefixEnd_169316 : Nat := 4983230072969 + 3 ^ 40 * 169316 * 2
def baseEnd_169316 : Nat := 38640217998562126253927

theorem tailTrace_169316 : CollatzResearch.WordTrace tailWord_169316 prefixEnd_169316 38640217998562126253927 := by
  unfold tailWord_169316
  simp only [CollatzResearch.WordTrace]
  refine ⟨3087730927302261857859901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4116974569736349143813201 3087730927302261857859901)
  ·
    refine ⟨1157899097738348196697463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3087730927302261857859901 1157899097738348196697463)
    ·
      refine ⟨1736848646607522295046195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1157899097738348196697463 1736848646607522295046195)
      ·
        refine ⟨2605272969911283442569293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1736848646607522295046195 2605272969911283442569293)
        ·
          refine ⟨976977363716731290963485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2605272969911283442569293 976977363716731290963485)
          ·
            refine ⟨366366511393774234111307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 976977363716731290963485 366366511393774234111307)
            ·
              refine ⟨549549767090661351166961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 366366511393774234111307 549549767090661351166961)
              ·
                refine ⟨412162325317996013375221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 549549767090661351166961 412162325317996013375221)
                ·
                  refine ⟨38640217998562126253927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 412162325317996013375221 38640217998562126253927)
                  ·
                    rfl

theorem cell21_169316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_169316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_169316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_169316 prefixEnd_169316 := by exact prefixLift 169316
  have htrace : WordTrace (prefixWord ++ tailWord_169316) baseStart_169316 baseEnd_169316 := by
    simpa [prefixWord, tailWord_169316, baseEnd_169316] using wordTrace_append hprefix tailTrace_169316
  have hstable : (prefixWord ++ tailWord_169316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169316).length < 2 ^ (prefixWord ++ tailWord_169316).sum := by decide
  have hdescent : baseEnd_169316 < baseStart_169316 := by decide
  rcases family_descends (prefixWord ++ tailWord_169316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169330 : List Nat := [3, 2, 1, 2, 1, 2, 2, 2, 6]
def baseStart_169330 : Nat := 118140960795 + 169330 * 2 ^ 59
def prefixEnd_169330 : Nat := 4983230072969 + 3 ^ 40 * 169330 * 2
def baseEnd_169330 : Nat := 38643412989301213020565

theorem tailTrace_169330 : CollatzResearch.WordTrace tailWord_169330 prefixEnd_169330 38643412989301213020565 := by
  unfold tailWord_169330
  simp only [CollatzResearch.WordTrace]
  refine ⟨1543993119138451026682361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4117314984369202737819629 1543993119138451026682361)
  ·
    refine ⟨1157994839353838270011771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1543993119138451026682361 1157994839353838270011771)
    ·
      refine ⟨1736992259030757405017657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1157994839353838270011771 1736992259030757405017657)
      ·
        refine ⟨1302744194273068053763243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1736992259030757405017657 1302744194273068053763243)
        ·
          refine ⟨1954116291409602080644865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1302744194273068053763243 1954116291409602080644865)
          ·
            refine ⟨1465587218557201560483649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1954116291409602080644865 1465587218557201560483649)
            ·
              refine ⟨1099190413917901170362737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1465587218557201560483649 1099190413917901170362737)
              ·
                refine ⟨824392810438425877772053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1099190413917901170362737 824392810438425877772053)
                ·
                  refine ⟨38643412989301213020565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 824392810438425877772053 38643412989301213020565)
                  ·
                    rfl

theorem cell21_169330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_169330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_169330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_169330 prefixEnd_169330 := by exact prefixLift 169330
  have htrace : WordTrace (prefixWord ++ tailWord_169330) baseStart_169330 baseEnd_169330 := by
    simpa [prefixWord, tailWord_169330, baseEnd_169330] using wordTrace_append hprefix tailTrace_169330
  have hstable : (prefixWord ++ tailWord_169330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169330).length < 2 ^ (prefixWord ++ tailWord_169330).sum := by decide
  have hdescent : baseEnd_169330 < baseStart_169330 := by decide
  rcases family_descends (prefixWord ++ tailWord_169330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169347 : List Nat := [1, 1, 1, 3, 5, 1, 3, 2, 4]
def baseStart_169347 : Nat := 118140960795 + 169347 * 2 ^ 59
def prefixEnd_169347 : Nat := 4983230072969 + 3 ^ 40 * 169347 * 2
def baseEnd_169347 : Nat := 38647292620912961237197

theorem tailTrace_169347 : CollatzResearch.WordTrace tailWord_169347 prefixEnd_169347 38647292620912961237197 := by
  unfold tailWord_169347
  simp only [CollatzResearch.WordTrace]
  refine ⟨6176592517492216010098295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4117728344994810673398863 6176592517492216010098295)
  ·
    refine ⟨9264888776238324015147443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6176592517492216010098295 9264888776238324015147443)
    ·
      refine ⟨13897333164357486022721165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9264888776238324015147443 13897333164357486022721165)
      ·
        refine ⟨5211499936634057258520437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13897333164357486022721165 5211499936634057258520437)
        ·
          refine ⟨488578119059442867986291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5211499936634057258520437 488578119059442867986291)
          ·
            refine ⟨732867178589164301979437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 488578119059442867986291 732867178589164301979437)
            ·
              refine ⟨274825191970936613242289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 732867178589164301979437 274825191970936613242289)
              ·
                refine ⟨206118893978202459931717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 274825191970936613242289 206118893978202459931717)
                ·
                  refine ⟨38647292620912961237197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 206118893978202459931717 38647292620912961237197)
                  ·
                    rfl

theorem cell21_169347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 2, 4].length) (baseStart_169347 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_169347 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_169347 prefixEnd_169347 := by exact prefixLift 169347
  have htrace : WordTrace (prefixWord ++ tailWord_169347) baseStart_169347 baseEnd_169347 := by
    simpa [prefixWord, tailWord_169347, baseEnd_169347] using wordTrace_append hprefix tailTrace_169347
  have hstable : (prefixWord ++ tailWord_169347).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169347).length < 2 ^ (prefixWord ++ tailWord_169347).sum := by decide
  have hdescent : baseEnd_169347 < baseStart_169347 := by decide
  rcases family_descends (prefixWord ++ tailWord_169347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169378 : List Nat := [3, 3, 1, 2, 1, 2, 4, 5]
def baseStart_169378 : Nat := 118140960795 + 169378 * 2 ^ 59
def prefixEnd_169378 : Nat := 4983230072969 + 3 ^ 40 * 169378 * 2
def baseEnd_169378 : Nat := 12884789081087932073489

theorem tailTrace_169378 : CollatzResearch.WordTrace tailWord_169378 prefixEnd_169378 12884789081087932073489 := by
  unfold tailWord_169378
  simp only [CollatzResearch.WordTrace]
  refine ⟨1544430795094977076119197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4118482120253272202984525 1544430795094977076119197)
  ·
    refine ⟨579161548160616403544699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1544430795094977076119197 579161548160616403544699)
    ·
      refine ⟨868742322240924605317049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 579161548160616403544699 868742322240924605317049)
      ·
        refine ⟨651556741680693453987787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 868742322240924605317049 651556741680693453987787)
        ·
          refine ⟨977335112521040180981681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 651556741680693453987787 977335112521040180981681)
          ·
            refine ⟨733001334390780135736261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 977335112521040180981681 733001334390780135736261)
            ·
              refine ⟨137437750198271275450549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 733001334390780135736261 137437750198271275450549)
              ·
                refine ⟨12884789081087932073489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 137437750198271275450549 12884789081087932073489)
                ·
                  rfl

theorem cell21_169378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 5].length) (baseStart_169378 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_169378 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_169378 prefixEnd_169378 := by exact prefixLift 169378
  have htrace : WordTrace (prefixWord ++ tailWord_169378) baseStart_169378 baseEnd_169378 := by
    simpa [prefixWord, tailWord_169378, baseEnd_169378] using wordTrace_append hprefix tailTrace_169378
  have hstable : (prefixWord ++ tailWord_169378).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169378).length < 2 ^ (prefixWord ++ tailWord_169378).sum := by decide
  have hdescent : baseEnd_169378 < baseStart_169378 := by decide
  rcases family_descends (prefixWord ++ tailWord_169378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169384 : List Nat := [2, 1, 6, 1, 3, 1, 1, 3, 3]
def baseStart_169384 : Nat := 118140960795 + 169384 * 2 ^ 59
def prefixEnd_169384 : Nat := 4983230072969 + 3 ^ 40 * 169384 * 2
def baseEnd_169384 : Nat := 38655736525009119120455

theorem tailTrace_169384 : CollatzResearch.WordTrace tailWord_169384 prefixEnd_169384 38655736525009119120455 := by
  unfold tailWord_169384
  simp only [CollatzResearch.WordTrace]
  refine ⟨3088971009179085664597603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4118628012238780886130137 3088971009179085664597603)
  ·
    refine ⟨4633456513768628496896405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3088971009179085664597603 4633456513768628496896405)
    ·
      refine ⟨217193274082904460792019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4633456513768628496896405 217193274082904460792019)
      ·
        refine ⟨325789911124356691188029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217193274082904460792019 325789911124356691188029)
        ·
          refine ⟨122171216671633759195511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 325789911124356691188029 122171216671633759195511)
          ·
            refine ⟨183256825007450638793267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122171216671633759195511 183256825007450638793267)
            ·
              refine ⟨274885237511175958189901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183256825007450638793267 274885237511175958189901)
              ·
                refine ⟨103081964066690984321213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 274885237511175958189901 103081964066690984321213)
                ·
                  refine ⟨38655736525009119120455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103081964066690984321213 38655736525009119120455)
                  ·
                    rfl

theorem cell21_169384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 3, 3].length) (baseStart_169384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_169384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_169384 prefixEnd_169384 := by exact prefixLift 169384
  have htrace : WordTrace (prefixWord ++ tailWord_169384) baseStart_169384 baseEnd_169384 := by
    simpa [prefixWord, tailWord_169384, baseEnd_169384] using wordTrace_append hprefix tailTrace_169384
  have hstable : (prefixWord ++ tailWord_169384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169384).length < 2 ^ (prefixWord ++ tailWord_169384).sum := by decide
  have hdescent : baseEnd_169384 < baseStart_169384 := by decide
  rcases family_descends (prefixWord ++ tailWord_169384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169392 : List Nat := [2, 1, 1, 1, 2, 1, 1, 9, 3]
def baseStart_169392 : Nat := 118140960795 + 169392 * 2 ^ 59
def prefixEnd_169392 : Nat := 4983230072969 + 3 ^ 40 * 169392 * 2
def baseEnd_169392 : Nat := 38657562234002882987105

theorem tailTrace_169392 : CollatzResearch.WordTrace tailWord_169392 prefixEnd_169392 38657562234002882987105 := by
  unfold tailWord_169392
  simp only [CollatzResearch.WordTrace]
  refine ⟨3089116901164594347743215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4118822534886125796990953 3089116901164594347743215)
  ·
    refine ⟨4633675351746891521614823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3089116901164594347743215 4633675351746891521614823)
    ·
      refine ⟨6950513027620337282422235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4633675351746891521614823 6950513027620337282422235)
      ·
        refine ⟨10425769541430505923633353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6950513027620337282422235 10425769541430505923633353)
        ·
          refine ⟨7819327156072879442725015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10425769541430505923633353 7819327156072879442725015)
          ·
            refine ⟨11728990734109319164087523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7819327156072879442725015 11728990734109319164087523)
            ·
              refine ⟨17593486101163978746131285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11728990734109319164087523 17593486101163978746131285)
              ·
                refine ⟨103086832624007687965613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17593486101163978746131285 103086832624007687965613)
                ·
                  refine ⟨38657562234002882987105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103086832624007687965613 38657562234002882987105)
                  ·
                    rfl

theorem cell21_169392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 9, 3].length) (baseStart_169392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_169392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_169392 prefixEnd_169392 := by exact prefixLift 169392
  have htrace : WordTrace (prefixWord ++ tailWord_169392) baseStart_169392 baseEnd_169392 := by
    simpa [prefixWord, tailWord_169392, baseEnd_169392] using wordTrace_append hprefix tailTrace_169392
  have hstable : (prefixWord ++ tailWord_169392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169392).length < 2 ^ (prefixWord ++ tailWord_169392).sum := by decide
  have hdescent : baseEnd_169392 < baseStart_169392 := by decide
  rcases family_descends (prefixWord ++ tailWord_169392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169423 : List Nat := [1, 1, 2, 1, 1, 4, 6, 1, 4]
def baseStart_169423 : Nat := 118140960795 + 169423 * 2 ^ 59
def prefixEnd_169423 : Nat := 4983230072969 + 3 ^ 40 * 169423 * 2
def baseEnd_169423 : Nat := 38664636856353717970375

theorem tailTrace_169423 : CollatzResearch.WordTrace tailWord_169423 prefixEnd_169423 38664636856353717970375 := by
  unfold tailWord_169423
  simp only [CollatzResearch.WordTrace]
  refine ⟨6179364465216880989864923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4119576310144587326576615 6179364465216880989864923)
  ·
    refine ⟨9269046697825321484797385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6179364465216880989864923 9269046697825321484797385)
    ·
      refine ⟨6951785023368991113598039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9269046697825321484797385 6951785023368991113598039)
      ·
        refine ⟨10427677535053486670397059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6951785023368991113598039 10427677535053486670397059)
        ·
          refine ⟨15641516302580230005595589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10427677535053486670397059 15641516302580230005595589)
          ·
            refine ⟨2932784306733793126049173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15641516302580230005595589 2932784306733793126049173)
            ·
              refine ⟨137474264378146552783555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2932784306733793126049173 137474264378146552783555)
              ·
                refine ⟨206211396567219829175333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137474264378146552783555 206211396567219829175333)
                ·
                  refine ⟨38664636856353717970375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 206211396567219829175333 38664636856353717970375)
                  ·
                    rfl

theorem cell21_169423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 1, 4].length) (baseStart_169423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_169423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_169423 prefixEnd_169423 := by exact prefixLift 169423
  have htrace : WordTrace (prefixWord ++ tailWord_169423) baseStart_169423 baseEnd_169423 := by
    simpa [prefixWord, tailWord_169423, baseEnd_169423] using wordTrace_append hprefix tailTrace_169423
  have hstable : (prefixWord ++ tailWord_169423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169423).length < 2 ^ (prefixWord ++ tailWord_169423).sum := by decide
  have hdescent : baseEnd_169423 < baseStart_169423 := by decide
  rcases family_descends (prefixWord ++ tailWord_169423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169437 : List Nat := [1, 4, 3, 1, 1, 2, 2, 7]
def baseStart_169437 : Nat := 118140960795 + 169437 * 2 ^ 59
def prefixEnd_169437 : Nat := 4983230072969 + 3 ^ 40 * 169437 * 2
def baseEnd_169437 : Nat := 12889277282364268245671

theorem tailTrace_169437 : CollatzResearch.WordTrace tailWord_169437 prefixEnd_169437 12889277282364268245671 := by
  unfold tailWord_169437
  simp only [CollatzResearch.WordTrace]
  refine ⟨6179875087166161380874565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4119916724777440920583043 6179875087166161380874565)
  ·
    refine ⟨1158726578843655258913981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6179875087166161380874565 1158726578843655258913981)
    ·
      refine ⟨434522467066370722092743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1158726578843655258913981 434522467066370722092743)
      ·
        refine ⟨651783700599556083139115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434522467066370722092743 651783700599556083139115)
        ·
          refine ⟨977675550899334124708673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 651783700599556083139115 977675550899334124708673)
          ·
            refine ⟨733256663174500593531505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 977675550899334124708673 733256663174500593531505)
            ·
              refine ⟨549942497380875445148629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 733256663174500593531505 549942497380875445148629)
              ·
                refine ⟨12889277282364268245671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 549942497380875445148629 12889277282364268245671)
                ·
                  rfl

theorem cell21_169437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 7].length) (baseStart_169437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_169437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_169437 prefixEnd_169437 := by exact prefixLift 169437
  have htrace : WordTrace (prefixWord ++ tailWord_169437) baseStart_169437 baseEnd_169437 := by
    simpa [prefixWord, tailWord_169437, baseEnd_169437] using wordTrace_append hprefix tailTrace_169437
  have hstable : (prefixWord ++ tailWord_169437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169437).length < 2 ^ (prefixWord ++ tailWord_169437).sum := by decide
  have hdescent : baseEnd_169437 < baseStart_169437 := by decide
  rcases family_descends (prefixWord ++ tailWord_169437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169527 : List Nat := [1, 1, 3, 1, 2, 4, 1, 3, 5]
def baseStart_169527 : Nat := 118140960795 + 169527 * 2 ^ 59
def prefixEnd_169527 : Nat := 4983230072969 + 3 ^ 40 * 169527 * 2
def baseEnd_169527 : Nat := 38688371073272648236829

theorem tailTrace_169527 : CollatzResearch.WordTrace tailWord_169527 prefixEnd_169527 38688371073272648236829 := by
  unfold tailWord_169527
  simp only [CollatzResearch.WordTrace]
  refine ⟨6183157656840106751650835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4122105104560071167767223 6183157656840106751650835)
  ·
    refine ⟨9274736485260160127476253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6183157656840106751650835 9274736485260160127476253)
    ·
      refine ⟨3478026181972560047803595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9274736485260160127476253 3478026181972560047803595)
      ·
        refine ⟨5217039272958840071705393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3478026181972560047803595 5217039272958840071705393)
        ·
          refine ⟨3912779454719130053779045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5217039272958840071705393 3912779454719130053779045)
          ·
            refine ⟨733646147759836885083571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3912779454719130053779045 733646147759836885083571)
            ·
              refine ⟨1100469221639755327625357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 733646147759836885083571 1100469221639755327625357)
              ·
                refine ⟨412675958114908247859509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1100469221639755327625357 412675958114908247859509)
                ·
                  refine ⟨38688371073272648236829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 412675958114908247859509 38688371073272648236829)
                  ·
                    rfl

theorem cell21_169527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 5].length) (baseStart_169527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_169527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_169527 prefixEnd_169527 := by exact prefixLift 169527
  have htrace : WordTrace (prefixWord ++ tailWord_169527) baseStart_169527 baseEnd_169527 := by
    simpa [prefixWord, tailWord_169527, baseEnd_169527] using wordTrace_append hprefix tailTrace_169527
  have hstable : (prefixWord ++ tailWord_169527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169527).length < 2 ^ (prefixWord ++ tailWord_169527).sum := by decide
  have hdescent : baseEnd_169527 < baseStart_169527 := by decide
  rcases family_descends (prefixWord ++ tailWord_169527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169572 : List Nat := [2, 3, 1, 1, 2, 3, 9]
def baseStart_169572 : Nat := 118140960795 + 169572 * 2 ^ 59
def prefixEnd_169572 : Nat := 4983230072969 + 3 ^ 40 * 169572 * 2
def baseEnd_169572 : Nat := 4299848965151396665193

theorem tailTrace_169572 : CollatzResearch.WordTrace tailWord_169572 prefixEnd_169572 4299848965151396665193 := by
  unfold tailWord_169572
  simp only [CollatzResearch.WordTrace]
  refine ⟨3092399470838539718519485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4123199294451386291359313 3092399470838539718519485)
  ·
    refine ⟨1159649801564452394444807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3092399470838539718519485 1159649801564452394444807)
    ·
      refine ⟨1739474702346678591667211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1159649801564452394444807 1739474702346678591667211)
      ·
        refine ⟨2609212053520017887500817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1739474702346678591667211 2609212053520017887500817)
        ·
          refine ⟨1956909040140013415625613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2609212053520017887500817 1956909040140013415625613)
          ·
            refine ⟨733840890052505030859605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1956909040140013415625613 733840890052505030859605)
            ·
              refine ⟨4299848965151396665193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 733840890052505030859605 4299848965151396665193)
              ·
                rfl

theorem cell21_169572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 9].length) (baseStart_169572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_169572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_169572 prefixEnd_169572 := by exact prefixLift 169572
  have htrace : WordTrace (prefixWord ++ tailWord_169572) baseStart_169572 baseEnd_169572 := by
    simpa [prefixWord, tailWord_169572, baseEnd_169572] using wordTrace_append hprefix tailTrace_169572
  have hstable : (prefixWord ++ tailWord_169572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169572).length < 2 ^ (prefixWord ++ tailWord_169572).sum := by decide
  have hdescent : baseEnd_169572 < baseStart_169572 := by decide
  rcases family_descends (prefixWord ++ tailWord_169572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169578 : List Nat := [3, 1, 3, 2, 1, 3, 3, 2, 3]
def baseStart_169578 : Nat := 118140960795 + 169578 * 2 ^ 59
def prefixEnd_169578 : Nat := 4983230072969 + 3 ^ 40 * 169578 * 2
def baseEnd_169578 : Nat := 38700009968107892886725

theorem tailTrace_169578 : CollatzResearch.WordTrace tailWord_169578 prefixEnd_169578 38700009968107892886725 := by
  unfold tailWord_169578
  simp only [CollatzResearch.WordTrace]
  refine ⟨1546254444913835615439347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4123345186436894974504925 1546254444913835615439347)
  ·
    refine ⟨2319381667370753423159021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1546254444913835615439347 2319381667370753423159021)
    ·
      refine ⟨869768125264032533684633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2319381667370753423159021 869768125264032533684633)
      ·
        refine ⟨652326093948024400263475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 869768125264032533684633 652326093948024400263475)
        ·
          refine ⟨978489140922036600395213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 652326093948024400263475 978489140922036600395213)
          ·
            refine ⟨366933427845763725148205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 978489140922036600395213 366933427845763725148205)
            ·
              refine ⟨137600035442161396930577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 366933427845763725148205 137600035442161396930577)
              ·
                refine ⟨103200026581621047697933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137600035442161396930577 103200026581621047697933)
                ·
                  refine ⟨38700009968107892886725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103200026581621047697933 38700009968107892886725)
                  ·
                    rfl

theorem cell21_169578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 2, 3].length) (baseStart_169578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_169578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_169578 prefixEnd_169578 := by exact prefixLift 169578
  have htrace : WordTrace (prefixWord ++ tailWord_169578) baseStart_169578 baseEnd_169578 := by
    simpa [prefixWord, tailWord_169578, baseEnd_169578] using wordTrace_append hprefix tailTrace_169578
  have hstable : (prefixWord ++ tailWord_169578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169578).length < 2 ^ (prefixWord ++ tailWord_169578).sum := by decide
  have hdescent : baseEnd_169578 < baseStart_169578 := by decide
  rcases family_descends (prefixWord ++ tailWord_169578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169589 : List Nat := [1, 3, 4, 2, 1, 1, 1, 8]
def baseStart_169589 : Nat := 118140960795 + 169589 * 2 ^ 59
def prefixEnd_169589 : Nat := 4983230072969 + 3 ^ 40 * 169589 * 2
def baseEnd_169589 : Nat := 12900840105991439401123

theorem tailTrace_169589 : CollatzResearch.WordTrace tailWord_169589 prefixEnd_169589 12900840105991439401123 := by
  unfold tailWord_169589
  simp only [CollatzResearch.WordTrace]
  refine ⟨6185418982615491340407821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4123612655076994226938547 6185418982615491340407821)
  ·
    refine ⟨2319532118480809252652933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6185418982615491340407821 2319532118480809252652933)
    ·
      refine ⟨434912272215151734872425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2319532118480809252652933 434912272215151734872425)
      ·
        refine ⟨326184204161363801154319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 434912272215151734872425 326184204161363801154319)
        ·
          refine ⟨489276306242045701731479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326184204161363801154319 489276306242045701731479)
          ·
            refine ⟨733914459363068552597219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 489276306242045701731479 733914459363068552597219)
            ·
              refine ⟨1100871689044602828895829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 733914459363068552597219 1100871689044602828895829)
              ·
                refine ⟨12900840105991439401123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1100871689044602828895829 12900840105991439401123)
                ·
                  rfl

theorem cell21_169589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 8].length) (baseStart_169589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_169589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_169589 prefixEnd_169589 := by exact prefixLift 169589
  have htrace : WordTrace (prefixWord ++ tailWord_169589) baseStart_169589 baseEnd_169589 := by
    simpa [prefixWord, tailWord_169589, baseEnd_169589] using wordTrace_append hprefix tailTrace_169589
  have hstable : (prefixWord ++ tailWord_169589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169589).length < 2 ^ (prefixWord ++ tailWord_169589).sum := by decide
  have hdescent : baseEnd_169589 < baseStart_169589 := by decide
  rcases family_descends (prefixWord ++ tailWord_169589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169617 : List Nat := [1, 2, 2, 1, 1, 1, 1, 6, 6]
def baseStart_169617 : Nat := 118140960795 + 169617 * 2 ^ 59
def prefixEnd_169617 : Nat := 4983230072969 + 3 ^ 40 * 169617 * 2
def baseEnd_169617 : Nat := 38708910299452491736645

theorem tailTrace_169617 : CollatzResearch.WordTrace tailWord_169617 prefixEnd_169617 38708910299452491736645 := by
  unfold tailWord_169617
  simp only [CollatzResearch.WordTrace]
  refine ⟨6186440226514052122427105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4124293484342701414951403 6186440226514052122427105)
  ·
    refine ⟨4639830169885539091820329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6186440226514052122427105 4639830169885539091820329)
    ·
      refine ⟨3479872627414154318865247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4639830169885539091820329 3479872627414154318865247)
      ·
        refine ⟨5219808941121231478297871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3479872627414154318865247 5219808941121231478297871)
        ·
          refine ⟨7829713411681847217446807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5219808941121231478297871 7829713411681847217446807)
          ·
            refine ⟨11744570117522770826170211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7829713411681847217446807 11744570117522770826170211)
            ·
              refine ⟨17616855176284156239255317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11744570117522770826170211 17616855176284156239255317)
              ·
                refine ⟨825790086388319823715093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17616855176284156239255317 825790086388319823715093)
                ·
                  refine ⟨38708910299452491736645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 825790086388319823715093 38708910299452491736645)
                  ·
                    rfl

theorem cell21_169617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 6].length) (baseStart_169617 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_169617 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_169617 prefixEnd_169617 := by exact prefixLift 169617
  have htrace : WordTrace (prefixWord ++ tailWord_169617) baseStart_169617 baseEnd_169617 := by
    simpa [prefixWord, tailWord_169617, baseEnd_169617] using wordTrace_append hprefix tailTrace_169617
  have hstable : (prefixWord ++ tailWord_169617).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169617).length < 2 ^ (prefixWord ++ tailWord_169617).sum := by decide
  have hdescent : baseEnd_169617 < baseStart_169617 := by decide
  rcases family_descends (prefixWord ++ tailWord_169617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169637 : List Nat := [1, 3, 1, 2, 1, 2, 6, 2, 3]
def baseStart_169637 : Nat := 118140960795 + 169637 * 2 ^ 59
def prefixEnd_169637 : Nat := 4983230072969 + 3 ^ 40 * 169637 * 2
def baseEnd_169637 : Nat := 38713474571936901403271

theorem tailTrace_169637 : CollatzResearch.WordTrace tailWord_169637 prefixEnd_169637 38713474571936901403271 := by
  unfold tailWord_169637
  simp only [CollatzResearch.WordTrace]
  refine ⟨6187169686441595538155165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4124779790961063692103443 6187169686441595538155165)
  ·
    refine ⟨2320188632415598326808187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6187169686441595538155165 2320188632415598326808187)
    ·
      refine ⟨3480282948623397490212281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2320188632415598326808187 3480282948623397490212281)
      ·
        refine ⟨2610212211467548117659211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3480282948623397490212281 2610212211467548117659211)
        ·
          refine ⟨3915318317201322176488817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2610212211467548117659211 3915318317201322176488817)
          ·
            refine ⟨2936488737900991632366613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3915318317201322176488817 2936488737900991632366613)
            ·
              refine ⟨137647909589108982767185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2936488737900991632366613 137647909589108982767185)
              ·
                refine ⟨103235932191831737075389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137647909589108982767185 103235932191831737075389)
                ·
                  refine ⟨38713474571936901403271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103235932191831737075389 38713474571936901403271)
                  ·
                    rfl

theorem cell21_169637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 2, 3].length) (baseStart_169637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_169637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_169637 prefixEnd_169637 := by exact prefixLift 169637
  have htrace : WordTrace (prefixWord ++ tailWord_169637) baseStart_169637 baseEnd_169637 := by
    simpa [prefixWord, tailWord_169637, baseEnd_169637] using wordTrace_append hprefix tailTrace_169637
  have hstable : (prefixWord ++ tailWord_169637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169637).length < 2 ^ (prefixWord ++ tailWord_169637).sum := by decide
  have hdescent : baseEnd_169637 < baseStart_169637 := by decide
  rcases family_descends (prefixWord ++ tailWord_169637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169640 : List Nat := [2, 1, 7, 1, 1, 2, 1, 6]
def baseStart_169640 : Nat := 118140960795 + 169640 * 2 ^ 59
def prefixEnd_169640 : Nat := 4983230072969 + 3 ^ 40 * 169640 * 2
def baseEnd_169640 : Nat := 12904719737603187617755

theorem tailTrace_169640 : CollatzResearch.WordTrace tailWord_169640 prefixEnd_169640 12904719737603187617755 := by
  unfold tailWord_169640
  simp only [CollatzResearch.WordTrace]
  refine ⟨3093639552715363525257187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4124852736953818033676249 3093639552715363525257187)
  ·
    refine ⟨4640459329073045287885781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3093639552715363525257187 4640459329073045287885781)
    ·
      refine ⟨108760765525149498934823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 4640459329073045287885781 108760765525149498934823)
      ·
        refine ⟨163141148287724248402235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108760765525149498934823 163141148287724248402235)
        ·
          refine ⟨244711722431586372603353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163141148287724248402235 244711722431586372603353)
          ·
            refine ⟨183533791823689779452515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 244711722431586372603353 183533791823689779452515)
            ·
              refine ⟨275300687735534669178773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183533791823689779452515 275300687735534669178773)
              ·
                refine ⟨12904719737603187617755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 275300687735534669178773 12904719737603187617755)
                ·
                  rfl

theorem cell21_169640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 6].length) (baseStart_169640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_169640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_169640 prefixEnd_169640 := by exact prefixLift 169640
  have htrace : WordTrace (prefixWord ++ tailWord_169640) baseStart_169640 baseEnd_169640 := by
    simpa [prefixWord, tailWord_169640, baseEnd_169640] using wordTrace_append hprefix tailTrace_169640
  have hstable : (prefixWord ++ tailWord_169640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169640).length < 2 ^ (prefixWord ++ tailWord_169640).sum := by decide
  have hdescent : baseEnd_169640 < baseStart_169640 := by decide
  rcases family_descends (prefixWord ++ tailWord_169640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169648 : List Nat := [2, 1, 1, 1, 2, 1, 7, 6]
def baseStart_169648 : Nat := 118140960795 + 169648 * 2 ^ 59
def prefixEnd_169648 : Nat := 4983230072969 + 3 ^ 40 * 169648 * 2
def baseEnd_169648 : Nat := 12905328307267775573305

theorem tailTrace_169648 : CollatzResearch.WordTrace tailWord_169648 prefixEnd_169648 12905328307267775573305 := by
  unfold tailWord_169648
  simp only [CollatzResearch.WordTrace]
  refine ⟨3093785444700872208402799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4125047259601162944537065 3093785444700872208402799)
  ·
    refine ⟨4640678167051308312604199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3093785444700872208402799 4640678167051308312604199)
    ·
      refine ⟨6961017250576962468906299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4640678167051308312604199 6961017250576962468906299)
      ·
        refine ⟨10441525875865443703359449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6961017250576962468906299 10441525875865443703359449)
        ·
          refine ⟨7831144406899082777519587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10441525875865443703359449 7831144406899082777519587)
          ·
            refine ⟨11746716610348624166279381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7831144406899082777519587 11746716610348624166279381)
            ·
              refine ⟨275313670555045878897173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 11746716610348624166279381 275313670555045878897173)
              ·
                refine ⟨12905328307267775573305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 275313670555045878897173 12905328307267775573305)
                ·
                  rfl

theorem cell21_169648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 6].length) (baseStart_169648 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_169648 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_169648 prefixEnd_169648 := by exact prefixLift 169648
  have htrace : WordTrace (prefixWord ++ tailWord_169648) baseStart_169648 baseEnd_169648 := by
    simpa [prefixWord, tailWord_169648, baseEnd_169648] using wordTrace_append hprefix tailTrace_169648
  have hstable : (prefixWord ++ tailWord_169648).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169648).length < 2 ^ (prefixWord ++ tailWord_169648).sum := by decide
  have hdescent : baseEnd_169648 < baseStart_169648 := by decide
  rcases family_descends (prefixWord ++ tailWord_169648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169696 : List Nat := [2, 1, 1, 3, 1, 2, 4, 4, 3]
def baseStart_169696 : Nat := 118140960795 + 169696 * 2 ^ 59
def prefixEnd_169696 : Nat := 4983230072969 + 3 ^ 40 * 169696 * 2
def baseEnd_169696 : Nat := 38726939175765909919817

theorem tailTrace_169696 : CollatzResearch.WordTrace tailWord_169696 prefixEnd_169696 38726939175765909919817 := by
  unfold tailWord_169696
  simp only [CollatzResearch.WordTrace]
  refine ⟨3094660796613924307276471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4126214395485232409701961 3094660796613924307276471)
  ·
    refine ⟨4641991194920886460914707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3094660796613924307276471 4641991194920886460914707)
    ·
      refine ⟨6962986792381329691372061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4641991194920886460914707 6962986792381329691372061)
      ·
        refine ⟨2611120047142998634264523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6962986792381329691372061 2611120047142998634264523)
        ·
          refine ⟨3916680070714497951396785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2611120047142998634264523 3916680070714497951396785)
          ·
            refine ⟨2937510053035873463547589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3916680070714497951396785 2937510053035873463547589)
            ·
              refine ⟨550783134944226274415173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2937510053035873463547589 550783134944226274415173)
              ·
                refine ⟨103271837802042426452845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 550783134944226274415173 103271837802042426452845)
                ·
                  refine ⟨38726939175765909919817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103271837802042426452845 38726939175765909919817)
                  ·
                    rfl

theorem cell21_169696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 4, 3].length) (baseStart_169696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_169696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_169696 prefixEnd_169696 := by exact prefixLift 169696
  have htrace : WordTrace (prefixWord ++ tailWord_169696) baseStart_169696 baseEnd_169696 := by
    simpa [prefixWord, tailWord_169696, baseEnd_169696] using wordTrace_append hprefix tailTrace_169696
  have hstable : (prefixWord ++ tailWord_169696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169696).length < 2 ^ (prefixWord ++ tailWord_169696).sum := by decide
  have hdescent : baseEnd_169696 < baseStart_169696 := by decide
  rcases family_descends (prefixWord ++ tailWord_169696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169716 : List Nat := [2, 6, 1, 1, 1, 3, 2, 5]
def baseStart_169716 : Nat := 118140960795 + 169716 * 2 ^ 59
def prefixEnd_169716 : Nat := 4983230072969 + 3 ^ 40 * 169716 * 2
def baseEnd_169716 : Nat := 12910501149416773195481

theorem tailTrace_169716 : CollatzResearch.WordTrace tailWord_169716 prefixEnd_169716 12910501149416773195481 := by
  unfold tailWord_169716
  simp only [CollatzResearch.WordTrace]
  refine ⟨3095025526577696015140501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4126700702103594686854001 3095025526577696015140501)
  ·
    refine ⟨145079321558329500709711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3095025526577696015140501 145079321558329500709711)
    ·
      refine ⟨217618982337494251064567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145079321558329500709711 217618982337494251064567)
      ·
        refine ⟨326428473506241376596851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217618982337494251064567 326428473506241376596851)
        ·
          refine ⟨489642710259362064895277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326428473506241376596851 489642710259362064895277)
          ·
            refine ⟨183616016347260774335729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 489642710259362064895277 183616016347260774335729)
            ·
              refine ⟨137712012260445580751797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183616016347260774335729 137712012260445580751797)
              ·
                refine ⟨12910501149416773195481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 137712012260445580751797 12910501149416773195481)
                ·
                  rfl

theorem cell21_169716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 5].length) (baseStart_169716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_169716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_169716 prefixEnd_169716 := by exact prefixLift 169716
  have htrace : WordTrace (prefixWord ++ tailWord_169716) baseStart_169716 baseEnd_169716 := by
    simpa [prefixWord, tailWord_169716, baseEnd_169716] using wordTrace_append hprefix tailTrace_169716
  have hstable : (prefixWord ++ tailWord_169716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169716).length < 2 ^ (prefixWord ++ tailWord_169716).sum := by decide
  have hdescent : baseEnd_169716 < baseStart_169716 := by decide
  rcases family_descends (prefixWord ++ tailWord_169716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169724 : List Nat := [2, 2, 2, 1, 3, 1, 3, 7]
def baseStart_169724 : Nat := 118140960795 + 169724 * 2 ^ 59
def prefixEnd_169724 : Nat := 4983230072969 + 3 ^ 40 * 169724 * 2
def baseEnd_169724 : Nat := 12911109719081361151031

theorem tailTrace_169724 : CollatzResearch.WordTrace tailWord_169724 prefixEnd_169724 12911109719081361151031 := by
  unfold tailWord_169724
  simp only [CollatzResearch.WordTrace]
  refine ⟨3095171418563204698286113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4126895224750939597714817 3095171418563204698286113)
  ·
    refine ⟨2321378563922403523714585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3095171418563204698286113 2321378563922403523714585)
    ·
      refine ⟨1741033922941802642785939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2321378563922403523714585 1741033922941802642785939)
      ·
        refine ⟨2611550884412703964178909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1741033922941802642785939 2611550884412703964178909)
        ·
          refine ⟨979331581654763986567091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2611550884412703964178909 979331581654763986567091)
          ·
            refine ⟨1468997372482145979850637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 979331581654763986567091 1468997372482145979850637)
            ·
              refine ⟨550874014680804742443989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1468997372482145979850637 550874014680804742443989)
              ·
                refine ⟨12911109719081361151031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 550874014680804742443989 12911109719081361151031)
                ·
                  rfl

theorem cell21_169724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 7].length) (baseStart_169724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_169724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_169724 prefixEnd_169724 := by exact prefixLift 169724
  have htrace : WordTrace (prefixWord ++ tailWord_169724) baseStart_169724 baseEnd_169724 := by
    simpa [prefixWord, tailWord_169724, baseEnd_169724] using wordTrace_append hprefix tailTrace_169724
  have hstable : (prefixWord ++ tailWord_169724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169724).length < 2 ^ (prefixWord ++ tailWord_169724).sum := by decide
  have hdescent : baseEnd_169724 < baseStart_169724 := by decide
  rcases family_descends (prefixWord ++ tailWord_169724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169831 : List Nat := [1, 1, 5, 1, 2, 1, 3, 2, 5]
def baseStart_169831 : Nat := 118140960795 + 169831 * 2 ^ 59
def prefixEnd_169831 : Nat := 4983230072969 + 3 ^ 40 * 169831 * 2
def baseEnd_169831 : Nat := 38757748015035675169541

theorem tailTrace_169831 : CollatzResearch.WordTrace tailWord_169831 prefixEnd_169831 38757748015035675169541 := by
  unfold tailWord_169831
  simp only [CollatzResearch.WordTrace]
  refine ⟨6194245447738766670717347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4129496965159177780478231 6194245447738766670717347)
  ·
    refine ⟨9291368171608150006076021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6194245447738766670717347 9291368171608150006076021)
    ·
      refine ⟨871065766088264063069627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9291368171608150006076021 871065766088264063069627)
      ·
        refine ⟨1306598649132396094604441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 871065766088264063069627 1306598649132396094604441)
        ·
          refine ⟨979948986849297070953331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1306598649132396094604441 979948986849297070953331)
          ·
            refine ⟨1469923480273945606429997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 979948986849297070953331 1469923480273945606429997)
            ·
              refine ⟨551221305102729602411249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1469923480273945606429997 551221305102729602411249)
              ·
                refine ⟨413415978827047201808437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 551221305102729602411249 413415978827047201808437)
                ·
                  refine ⟨38757748015035675169541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 413415978827047201808437 38757748015035675169541)
                  ·
                    rfl

theorem cell21_169831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 5].length) (baseStart_169831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_169831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_169831 prefixEnd_169831 := by exact prefixLift 169831
  have htrace : WordTrace (prefixWord ++ tailWord_169831) baseStart_169831 baseEnd_169831 := by
    simpa [prefixWord, tailWord_169831, baseEnd_169831] using wordTrace_append hprefix tailTrace_169831
  have hstable : (prefixWord ++ tailWord_169831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169831).length < 2 ^ (prefixWord ++ tailWord_169831).sum := by decide
  have hdescent : baseEnd_169831 < baseStart_169831 := by decide
  rcases family_descends (prefixWord ++ tailWord_169831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169879 : List Nat := [1, 1, 3, 3, 1, 4, 3, 1, 4]
def baseStart_169879 : Nat := 118140960795 + 169879 * 2 ^ 59
def prefixEnd_169879 : Nat := 4983230072969 + 3 ^ 40 * 169879 * 2
def baseEnd_169879 : Nat := 38768702268998258369443

theorem tailTrace_169879 : CollatzResearch.WordTrace tailWord_169879 prefixEnd_169879 38768702268998258369443 := by
  unfold tailWord_169879
  simp only [CollatzResearch.WordTrace]
  refine ⟨6195996151564870868464691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4130664101043247245643127 6195996151564870868464691)
  ·
    refine ⟨9293994227347306302697037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6195996151564870868464691 9293994227347306302697037)
    ·
      refine ⟨3485247835255239863511389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9293994227347306302697037 3485247835255239863511389)
      ·
        refine ⟨1306967938220714948816771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3485247835255239863511389 1306967938220714948816771)
        ·
          refine ⟨1960451907331072423225157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1306967938220714948816771 1960451907331072423225157)
          ·
            refine ⟨367584732624576079354717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1960451907331072423225157 367584732624576079354717)
            ·
              refine ⟨137844274734216029758019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 367584732624576079354717 137844274734216029758019)
              ·
                refine ⟨206766412101324044637029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137844274734216029758019 206766412101324044637029)
                ·
                  refine ⟨38768702268998258369443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 206766412101324044637029 38768702268998258369443)
                  ·
                    rfl

theorem cell21_169879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 1, 4].length) (baseStart_169879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_169879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_169879 prefixEnd_169879 := by exact prefixLift 169879
  have htrace : WordTrace (prefixWord ++ tailWord_169879) baseStart_169879 baseEnd_169879 := by
    simpa [prefixWord, tailWord_169879, baseEnd_169879] using wordTrace_append hprefix tailTrace_169879
  have hstable : (prefixWord ++ tailWord_169879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169879).length < 2 ^ (prefixWord ++ tailWord_169879).sum := by decide
  have hdescent : baseEnd_169879 < baseStart_169879 := by decide
  rcases family_descends (prefixWord ++ tailWord_169879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170017 : List Nat := [1, 2, 3, 2, 4, 1, 2, 3, 3]
def baseStart_170017 : Nat := 118140960795 + 170017 * 2 ^ 59
def prefixEnd_170017 : Nat := 4983230072969 + 3 ^ 40 * 170017 * 2
def baseEnd_170017 : Nat := 38800195749140685069161

theorem tailTrace_170017 : CollatzResearch.WordTrace tailWord_170017 prefixEnd_170017 38800195749140685069161 := by
  unfold tailWord_170017
  simp only [CollatzResearch.WordTrace]
  refine ⟨6201029425064920436988305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4134019616709946957992203 6201029425064920436988305)
  ·
    refine ⟨4650772068798690327741229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6201029425064920436988305 4650772068798690327741229)
    ·
      refine ⟨1744039525799508872902961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4650772068798690327741229 1744039525799508872902961)
      ·
        refine ⟨1308029644349631654677221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1744039525799508872902961 1308029644349631654677221)
        ·
          refine ⟨245255558315555935251979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1308029644349631654677221 245255558315555935251979)
          ·
            refine ⟨367883337473333902877969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245255558315555935251979 367883337473333902877969)
            ·
              refine ⟨275912503105000427158477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 367883337473333902877969 275912503105000427158477)
              ·
                refine ⟨103467188664375160184429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 275912503105000427158477 103467188664375160184429)
                ·
                  refine ⟨38800195749140685069161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103467188664375160184429 38800195749140685069161)
                  ·
                    rfl

theorem cell21_170017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 3, 3].length) (baseStart_170017 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_170017 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_170017 prefixEnd_170017 := by exact prefixLift 170017
  have htrace : WordTrace (prefixWord ++ tailWord_170017) baseStart_170017 baseEnd_170017 := by
    simpa [prefixWord, tailWord_170017, baseEnd_170017] using wordTrace_append hprefix tailTrace_170017
  have hstable : (prefixWord ++ tailWord_170017).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170017).length < 2 ^ (prefixWord ++ tailWord_170017).sum := by decide
  have hdescent : baseEnd_170017 < baseStart_170017 := by decide
  rcases family_descends (prefixWord ++ tailWord_170017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170093 : List Nat := [1, 5, 1, 1, 2, 1, 5, 2, 3]
def baseStart_170093 : Nat := 118140960795 + 170093 * 2 ^ 59
def prefixEnd_170093 : Nat := 4983230072969 + 3 ^ 40 * 170093 * 2
def baseEnd_170093 : Nat := 38817539984581441802339

theorem tailTrace_170093 : CollatzResearch.WordTrace tailWord_170093 prefixEnd_170093 38817539984581441802339 := by
  unfold tailWord_170093
  simp only [CollatzResearch.WordTrace]
  refine ⟨6203801372789585416754933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4135867581859723611169955 6203801372789585416754933)
  ·
    refine ⟨581606378699023632820775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6203801372789585416754933 581606378699023632820775)
    ·
      refine ⟨872409568048535449231163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 581606378699023632820775 872409568048535449231163)
      ·
        refine ⟨1308614352072803173846745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 872409568048535449231163 1308614352072803173846745)
        ·
          refine ⟨981460764054602380385059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1308614352072803173846745 981460764054602380385059)
          ·
            refine ⟨1472191146081903570577589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 981460764054602380385059 1472191146081903570577589)
            ·
              refine ⟨138017919945178459741649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1472191146081903570577589 138017919945178459741649)
              ·
                refine ⟨103513439958883844806237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138017919945178459741649 103513439958883844806237)
                ·
                  refine ⟨38817539984581441802339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103513439958883844806237 38817539984581441802339)
                  ·
                    rfl

theorem cell21_170093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_170093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_170093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_170093 prefixEnd_170093 := by exact prefixLift 170093
  have htrace : WordTrace (prefixWord ++ tailWord_170093) baseStart_170093 baseEnd_170093 := by
    simpa [prefixWord, tailWord_170093, baseEnd_170093] using wordTrace_append hprefix tailTrace_170093
  have hstable : (prefixWord ++ tailWord_170093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170093).length < 2 ^ (prefixWord ++ tailWord_170093).sum := by decide
  have hdescent : baseEnd_170093 < baseStart_170093 := by decide
  rcases family_descends (prefixWord ++ tailWord_170093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170225 : List Nat := [1, 2, 2, 2, 2, 1, 2, 5, 4]
def baseStart_170225 : Nat := 118140960795 + 170225 * 2 ^ 59
def prefixEnd_170225 : Nat := 4983230072969 + 3 ^ 40 * 170225 * 2
def baseEnd_170225 : Nat := 38847664182978545602069

theorem tailTrace_170225 : CollatzResearch.WordTrace tailWord_170225 prefixEnd_170225 38847664182978545602069 := by
  unfold tailWord_170225
  simp only [CollatzResearch.WordTrace]
  refine ⟨6208615808311371960560129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4139077205540914640373419 6208615808311371960560129)
  ·
    refine ⟨4656461856233528970420097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6208615808311371960560129 4656461856233528970420097)
    ·
      refine ⟨3492346392175146727815073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4656461856233528970420097 3492346392175146727815073)
      ·
        refine ⟨2619259794131360045861305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3492346392175146727815073 2619259794131360045861305)
        ·
          refine ⟨1964444845598520034395979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2619259794131360045861305 1964444845598520034395979)
          ·
            refine ⟨2946667268397780051593969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1964444845598520034395979 2946667268397780051593969)
            ·
              refine ⟨2210000451298335038695477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2946667268397780051593969 2210000451298335038695477)
              ·
                refine ⟨207187542309218909877701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2210000451298335038695477 207187542309218909877701)
                ·
                  refine ⟨38847664182978545602069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 207187542309218909877701 38847664182978545602069)
                  ·
                    rfl

theorem cell21_170225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 5, 4].length) (baseStart_170225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_170225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_170225 prefixEnd_170225 := by exact prefixLift 170225
  have htrace : WordTrace (prefixWord ++ tailWord_170225) baseStart_170225 baseEnd_170225 := by
    simpa [prefixWord, tailWord_170225, baseEnd_170225] using wordTrace_append hprefix tailTrace_170225
  have hstable : (prefixWord ++ tailWord_170225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170225).length < 2 ^ (prefixWord ++ tailWord_170225).sum := by decide
  have hdescent : baseEnd_170225 < baseStart_170225 := by decide
  rcases family_descends (prefixWord ++ tailWord_170225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170239 : List Nat := [1, 1, 2, 2, 1, 4, 3, 7]
def baseStart_170239 : Nat := 118140960795 + 170239 * 2 ^ 59
def prefixEnd_170239 : Nat := 4983230072969 + 3 ^ 40 * 170239 * 2
def baseEnd_170239 : Nat := 12950286391239210789569

theorem tailTrace_170239 : CollatzResearch.WordTrace tailWord_170239 prefixEnd_170239 12950286391239210789569 := by
  unfold tailWord_170239
  simp only [CollatzResearch.WordTrace]
  refine ⟨6209126430260652351569771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4139417620173768234379847 6209126430260652351569771)
  ·
    refine ⟨9313689645390978527354657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6209126430260652351569771 9313689645390978527354657)
    ·
      refine ⟨6985267234043233895515993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9313689645390978527354657 6985267234043233895515993)
      ·
        refine ⟨5238950425532425421636995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6985267234043233895515993 5238950425532425421636995)
        ·
          refine ⟨7858425638298638132455493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5238950425532425421636995 7858425638298638132455493)
          ·
            refine ⟨1473454807180994649835405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7858425638298638132455493 1473454807180994649835405)
            ·
              refine ⟨552545552692872993688277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1473454807180994649835405 552545552692872993688277)
              ·
                refine ⟨12950286391239210789569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 552545552692872993688277 12950286391239210789569)
                ·
                  rfl

theorem cell21_170239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 7].length) (baseStart_170239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_170239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_170239 prefixEnd_170239 := by exact prefixLift 170239
  have htrace : WordTrace (prefixWord ++ tailWord_170239) baseStart_170239 baseEnd_170239 := by
    simpa [prefixWord, tailWord_170239, baseEnd_170239] using wordTrace_append hprefix tailTrace_170239
  have hstable : (prefixWord ++ tailWord_170239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170239).length < 2 ^ (prefixWord ++ tailWord_170239).sum := by decide
  have hdescent : baseEnd_170239 < baseStart_170239 := by decide
  rcases family_descends (prefixWord ++ tailWord_170239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170242 : List Nat := [3, 4, 1, 1, 2, 1, 1, 2, 6]
def baseStart_170242 : Nat := 118140960795 + 170242 * 2 ^ 59
def prefixEnd_170242 : Nat := 4983230072969 + 3 ^ 40 * 170242 * 2
def baseEnd_170242 : Nat := 38851543814590293818701

theorem tailTrace_170242 : CollatzResearch.WordTrace tailWord_170242 prefixEnd_170242 38851543814590293818701 := by
  unfold tailWord_170242
  simp only [CollatzResearch.WordTrace]
  refine ⟨1552308962312445965982245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4139490566166522575952653 1552308962312445965982245)
  ·
    refine ⟨291057930433583618621671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1552308962312445965982245 291057930433583618621671)
    ·
      refine ⟨436586895650375427932507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291057930433583618621671 436586895650375427932507)
      ·
        refine ⟨654880343475563141898761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 436586895650375427932507 654880343475563141898761)
        ·
          refine ⟨491160257606672356424071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 654880343475563141898761 491160257606672356424071)
          ·
            refine ⟨736740386410008534636107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 491160257606672356424071 736740386410008534636107)
            ·
              refine ⟨1105110579615012801954161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 736740386410008534636107 1105110579615012801954161)
              ·
                refine ⟨828832934711259601465621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1105110579615012801954161 828832934711259601465621)
                ·
                  refine ⟨38851543814590293818701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 828832934711259601465621 38851543814590293818701)
                  ·
                    rfl

theorem cell21_170242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_170242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_170242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_170242 prefixEnd_170242 := by exact prefixLift 170242
  have htrace : WordTrace (prefixWord ++ tailWord_170242) baseStart_170242 baseEnd_170242 := by
    simpa [prefixWord, tailWord_170242, baseEnd_170242] using wordTrace_append hprefix tailTrace_170242
  have hstable : (prefixWord ++ tailWord_170242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170242).length < 2 ^ (prefixWord ++ tailWord_170242).sum := by decide
  have hdescent : baseEnd_170242 < baseStart_170242 := by decide
  rcases family_descends (prefixWord ++ tailWord_170242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170321 : List Nat := [1, 2, 2, 1, 4, 4, 2, 2, 3]
def baseStart_170321 : Nat := 118140960795 + 170321 * 2 ^ 59
def prefixEnd_170321 : Nat := 4983230072969 + 3 ^ 40 * 170321 * 2
def baseEnd_170321 : Nat := 38869572690903712001873

theorem tailTrace_170321 : CollatzResearch.WordTrace tailWord_170321 prefixEnd_170321 38869572690903712001873 := by
  unfold tailWord_170321
  simp only [CollatzResearch.WordTrace]
  refine ⟨6212117215963580356054817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4141411477309053570703211 6212117215963580356054817)
  ·
    refine ⟨4659087911972685267041113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6212117215963580356054817 4659087911972685267041113)
    ·
      refine ⟨3494315933979513950280835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4659087911972685267041113 3494315933979513950280835)
      ·
        refine ⟨5241473900969270925421253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3494315933979513950280835 5241473900969270925421253)
        ·
          refine ⟨982776356431738298516485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5241473900969270925421253 982776356431738298516485)
          ·
            refine ⟨184270566830950930971841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 982776356431738298516485 184270566830950930971841)
            ·
              refine ⟨138202925123213198228881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184270566830950930971841 138202925123213198228881)
              ·
                refine ⟨103652193842409898671661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138202925123213198228881 103652193842409898671661)
                ·
                  refine ⟨38869572690903712001873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103652193842409898671661 38869572690903712001873)
                  ·
                    rfl

theorem cell21_170321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 2, 3].length) (baseStart_170321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_170321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_170321 prefixEnd_170321 := by exact prefixLift 170321
  have htrace : WordTrace (prefixWord ++ tailWord_170321) baseStart_170321 baseEnd_170321 := by
    simpa [prefixWord, tailWord_170321, baseEnd_170321] using wordTrace_append hprefix tailTrace_170321
  have hstable : (prefixWord ++ tailWord_170321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170321).length < 2 ^ (prefixWord ++ tailWord_170321).sum := by decide
  have hdescent : baseEnd_170321 < baseStart_170321 := by decide
  rcases family_descends (prefixWord ++ tailWord_170321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170363 : List Nat := [1, 1, 1, 1, 1, 7, 1, 5, 3]
def baseStart_170363 : Nat := 118140960795 + 170363 * 2 ^ 59
def prefixEnd_170363 : Nat := 4983230072969 + 3 ^ 40 * 170363 * 2
def baseEnd_170363 : Nat := 38879157663120972301787

theorem tailTrace_170363 : CollatzResearch.WordTrace tailWord_170363 prefixEnd_170363 38879157663120972301787 := by
  unfold tailWord_170363
  simp only [CollatzResearch.WordTrace]
  refine ⟨6213649081811421529083743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4142432721207614352722495 6213649081811421529083743)
  ·
    refine ⟨9320473622717132293625615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6213649081811421529083743 9320473622717132293625615)
    ·
      refine ⟨13980710434075698440438423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9320473622717132293625615 13980710434075698440438423)
      ·
        refine ⟨20971065651113547660657635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13980710434075698440438423 20971065651113547660657635)
        ·
          refine ⟨31456598476670321490986453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20971065651113547660657635 31456598476670321490986453)
          ·
            refine ⟨737264026796960659944995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 31456598476670321490986453 737264026796960659944995)
            ·
              refine ⟨1105896040195440989917493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 737264026796960659944995 1105896040195440989917493)
              ·
                refine ⟨103677753768322592804765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1105896040195440989917493 103677753768322592804765)
                ·
                  refine ⟨38879157663120972301787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103677753768322592804765 38879157663120972301787)
                  ·
                    rfl

theorem cell21_170363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 5, 3].length) (baseStart_170363 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_170363 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_170363 prefixEnd_170363 := by exact prefixLift 170363
  have htrace : WordTrace (prefixWord ++ tailWord_170363) baseStart_170363 baseEnd_170363 := by
    simpa [prefixWord, tailWord_170363, baseEnd_170363] using wordTrace_append hprefix tailTrace_170363
  have hstable : (prefixWord ++ tailWord_170363).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170363).length < 2 ^ (prefixWord ++ tailWord_170363).sum := by decide
  have hdescent : baseEnd_170363 < baseStart_170363 := by decide
  rcases family_descends (prefixWord ++ tailWord_170363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170377 : List Nat := [1, 2, 1, 1, 6, 2, 1, 1, 6]
def baseStart_170377 : Nat := 118140960795 + 170377 * 2 ^ 59
def prefixEnd_170377 : Nat := 4983230072969 + 3 ^ 40 * 170377 * 2
def baseEnd_170377 : Nat := 38882352653860059068425

theorem tailTrace_170377 : CollatzResearch.WordTrace tailWord_170377 prefixEnd_170377 38882352653860059068425 := by
  unfold tailWord_170377
  simp only [CollatzResearch.WordTrace]
  refine ⟨6214159703760701920093385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4142773135840467946728923 6214159703760701920093385)
  ·
    refine ⟨4660619777820526440070039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6214159703760701920093385 4660619777820526440070039)
    ·
      refine ⟨6990929666730789660105059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4660619777820526440070039 6990929666730789660105059)
      ·
        refine ⟨10486394500096184490157589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6990929666730789660105059 10486394500096184490157589)
        ·
          refine ⟨491549742192008647976137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10486394500096184490157589 491549742192008647976137)
          ·
            refine ⟨368662306644006485982103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 491549742192008647976137 368662306644006485982103)
            ·
              refine ⟨552993459966009728973155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 368662306644006485982103 552993459966009728973155)
              ·
                refine ⟨829490189949014593459733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 552993459966009728973155 829490189949014593459733)
                ·
                  refine ⟨38882352653860059068425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 829490189949014593459733 38882352653860059068425)
                  ·
                    rfl

theorem cell21_170377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 6].length) (baseStart_170377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_170377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_170377 prefixEnd_170377 := by exact prefixLift 170377
  have htrace : WordTrace (prefixWord ++ tailWord_170377) baseStart_170377 baseEnd_170377 := by
    simpa [prefixWord, tailWord_170377, baseEnd_170377] using wordTrace_append hprefix tailTrace_170377
  have hstable : (prefixWord ++ tailWord_170377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170377).length < 2 ^ (prefixWord ++ tailWord_170377).sum := by decide
  have hdescent : baseEnd_170377 < baseStart_170377 := by decide
  rcases family_descends (prefixWord ++ tailWord_170377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170439 : List Nat := [1, 1, 4, 1, 1, 6, 1, 1, 5]
def baseStart_170439 : Nat := 118140960795 + 170439 * 2 ^ 59
def prefixEnd_170439 : Nat := 4983230072969 + 3 ^ 40 * 170439 * 2
def baseEnd_170439 : Nat := 38896501898561729034965

theorem tailTrace_170439 : CollatzResearch.WordTrace tailWord_170439 prefixEnd_170439 38896501898561729034965 := by
  unfold tailWord_170439
  simp only [CollatzResearch.WordTrace]
  refine ⟨6216421029536086508850371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4144280686357391005900247 6216421029536086508850371)
  ·
    refine ⟨9324631544304129763275557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6216421029536086508850371 9324631544304129763275557)
    ·
      refine ⟨1748368414557024330614167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9324631544304129763275557 1748368414557024330614167)
      ·
        refine ⟨2622552621835536495921251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1748368414557024330614167 2622552621835536495921251)
        ·
          refine ⟨3933828932753304743881877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2622552621835536495921251 3933828932753304743881877)
          ·
            refine ⟨184398231222811159869463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3933828932753304743881877 184398231222811159869463)
            ·
              refine ⟨276597346834216739804195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184398231222811159869463 276597346834216739804195)
              ·
                refine ⟨414896020251325109706293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 276597346834216739804195 414896020251325109706293)
                ·
                  refine ⟨38896501898561729034965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 414896020251325109706293 38896501898561729034965)
                  ·
                    rfl

theorem cell21_170439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 5].length) (baseStart_170439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_170439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_170439 prefixEnd_170439 := by exact prefixLift 170439
  have htrace : WordTrace (prefixWord ++ tailWord_170439) baseStart_170439 baseEnd_170439 := by
    simpa [prefixWord, tailWord_170439, baseEnd_170439] using wordTrace_append hprefix tailTrace_170439
  have hstable : (prefixWord ++ tailWord_170439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170439).length < 2 ^ (prefixWord ++ tailWord_170439).sum := by decide
  have hdescent : baseEnd_170439 < baseStart_170439 := by decide
  rcases family_descends (prefixWord ++ tailWord_170439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170574 : List Nat := [4, 1, 1, 1, 1, 2, 4, 2, 5]
def baseStart_170574 : Nat := 118140960795 + 170574 * 2 ^ 59
def prefixEnd_170574 : Nat := 4983230072969 + 3 ^ 40 * 170574 * 2
def baseEnd_170574 : Nat := 38927310737831494284689

theorem tailTrace_170574 : CollatzResearch.WordTrace tailWord_170574 prefixEnd_170574 38927310737831494284689 := by
  unfold tailWord_170574
  simp only [CollatzResearch.WordTrace]
  refine ⟨777668110505875570626847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4147563256031336376676517 777668110505875570626847)
  ·
    refine ⟨1166502165758813355940271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 777668110505875570626847 1166502165758813355940271)
    ·
      refine ⟨1749753248638220033910407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1166502165758813355940271 1749753248638220033910407)
      ·
        refine ⟨2624629872957330050865611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1749753248638220033910407 2624629872957330050865611)
        ·
          refine ⟨3936944809435995076298417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2624629872957330050865611 3936944809435995076298417)
          ·
            refine ⟨2952708607076996307223813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3936944809435995076298417 2952708607076996307223813)
            ·
              refine ⟨553632863826936807604465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2952708607076996307223813 553632863826936807604465)
              ·
                refine ⟨415224647870202605703349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 553632863826936807604465 415224647870202605703349)
                ·
                  refine ⟨38927310737831494284689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 415224647870202605703349 38927310737831494284689)
                  ·
                    rfl

theorem cell21_170574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_170574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_170574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_170574 prefixEnd_170574 := by exact prefixLift 170574
  have htrace : WordTrace (prefixWord ++ tailWord_170574) baseStart_170574 baseEnd_170574 := by
    simpa [prefixWord, tailWord_170574, baseEnd_170574] using wordTrace_append hprefix tailTrace_170574
  have hstable : (prefixWord ++ tailWord_170574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170574).length < 2 ^ (prefixWord ++ tailWord_170574).sum := by decide
  have hdescent : baseEnd_170574 < baseStart_170574 := by decide
  rcases family_descends (prefixWord ++ tailWord_170574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170594 : List Nat := [3, 3, 2, 3, 2, 1, 7]
def baseStart_170594 : Nat := 118140960795 + 170594 * 2 ^ 59
def prefixEnd_170594 : Nat := 4983230072969 + 3 ^ 40 * 170594 * 2
def baseEnd_170594 : Nat := 4325763890035100439035

theorem tailTrace_170594 : CollatzResearch.WordTrace tailWord_170594 prefixEnd_170594 4325763890035100439035 := by
  unfold tailWord_170594
  simp only [CollatzResearch.WordTrace]
  refine ⟨1555518585993636995185709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4148049562649698653828557 1555518585993636995185709)
  ·
    refine ⟨583319469747613873194641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1555518585993636995185709 583319469747613873194641)
    ·
      refine ⟨437489602310710404895981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 583319469747613873194641 437489602310710404895981)
      ·
        refine ⟨164058600866516401835993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 437489602310710404895981 164058600866516401835993)
        ·
          refine ⟨123043950649887301376995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164058600866516401835993 123043950649887301376995)
          ·
            refine ⟨184565925974830952065493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123043950649887301376995 184565925974830952065493)
            ·
              refine ⟨4325763890035100439035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 184565925974830952065493 4325763890035100439035)
              ·
                rfl

theorem cell21_170594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 7].length) (baseStart_170594 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_170594 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_170594 prefixEnd_170594 := by exact prefixLift 170594
  have htrace : WordTrace (prefixWord ++ tailWord_170594) baseStart_170594 baseEnd_170594 := by
    simpa [prefixWord, tailWord_170594, baseEnd_170594] using wordTrace_append hprefix tailTrace_170594
  have hstable : (prefixWord ++ tailWord_170594).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170594).length < 2 ^ (prefixWord ++ tailWord_170594).sum := by decide
  have hdescent : baseEnd_170594 < baseStart_170594 := by decide
  rcases family_descends (prefixWord ++ tailWord_170594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170605 : List Nat := [1, 5, 1, 1, 3, 1, 2, 1, 6]
def baseStart_170605 : Nat := 118140960795 + 170605 * 2 ^ 59
def prefixEnd_170605 : Nat := 4983230072969 + 3 ^ 40 * 170605 * 2
def baseEnd_170605 : Nat := 38934385360182329267959

theorem tailTrace_170605 : CollatzResearch.WordTrace tailWord_170605 prefixEnd_170605 38934385360182329267959 := by
  unfold tailWord_170605
  simp only [CollatzResearch.WordTrace]
  refine ⟨6222475546934696859393269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4148317031289797906262179 6222475546934696859393269)
  ·
    refine ⟨583357082525127830568119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6222475546934696859393269 583357082525127830568119)
    ·
      refine ⟨875035623787691745852179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 583357082525127830568119 875035623787691745852179)
      ·
        refine ⟨1312553435681537618778269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 875035623787691745852179 1312553435681537618778269)
        ·
          refine ⟨492207538380576607041851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1312553435681537618778269 492207538380576607041851)
          ·
            refine ⟨738311307570864910562777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 492207538380576607041851 738311307570864910562777)
            ·
              refine ⟨553733480678148682922083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 738311307570864910562777 553733480678148682922083)
              ·
                refine ⟨830600221017223024383125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 553733480678148682922083 830600221017223024383125)
                ·
                  refine ⟨38934385360182329267959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 830600221017223024383125 38934385360182329267959)
                  ·
                    rfl

theorem cell21_170605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_170605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_170605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_170605 prefixEnd_170605 := by exact prefixLift 170605
  have htrace : WordTrace (prefixWord ++ tailWord_170605) baseStart_170605 baseEnd_170605 := by
    simpa [prefixWord, tailWord_170605, baseEnd_170605] using wordTrace_append hprefix tailTrace_170605
  have hstable : (prefixWord ++ tailWord_170605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170605).length < 2 ^ (prefixWord ++ tailWord_170605).sum := by decide
  have hdescent : baseEnd_170605 < baseStart_170605 := by decide
  rcases family_descends (prefixWord ++ tailWord_170605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170608 : List Nat := [2, 1, 1, 1, 8, 1, 1, 1, 5]
def baseStart_170608 : Nat := 118140960795 + 170608 * 2 ^ 59
def prefixEnd_170608 : Nat := 4983230072969 + 3 ^ 40 * 170608 * 2
def baseEnd_170608 : Nat := 38935070001054990717953

theorem tailTrace_170608 : CollatzResearch.WordTrace tailWord_170608 prefixEnd_170608 38935070001054990717953 := by
  unfold tailWord_170608
  simp only [CollatzResearch.WordTrace]
  refine ⟨3111292482961914185876239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4148389977282552247834985 3111292482961914185876239)
  ·
    refine ⟨4666938724442871278814359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3111292482961914185876239 4666938724442871278814359)
    ·
      refine ⟨7000408086664306918221539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4666938724442871278814359 7000408086664306918221539)
      ·
        refine ⟨10500612129996460377332309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7000408086664306918221539 10500612129996460377332309)
        ·
          refine ⟨123054048398396020046863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 10500612129996460377332309 123054048398396020046863)
          ·
            refine ⟨184581072597594030070295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123054048398396020046863 184581072597594030070295)
            ·
              refine ⟨276871608896391045105443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184581072597594030070295 276871608896391045105443)
              ·
                refine ⟨415307413344586567658165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 276871608896391045105443 415307413344586567658165)
                ·
                  refine ⟨38935070001054990717953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 415307413344586567658165 38935070001054990717953)
                  ·
                    rfl

theorem cell21_170608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 5].length) (baseStart_170608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_170608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_170608 prefixEnd_170608 := by exact prefixLift 170608
  have htrace : WordTrace (prefixWord ++ tailWord_170608) baseStart_170608 baseEnd_170608 := by
    simpa [prefixWord, tailWord_170608, baseEnd_170608] using wordTrace_append hprefix tailTrace_170608
  have hstable : (prefixWord ++ tailWord_170608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170608).length < 2 ^ (prefixWord ++ tailWord_170608).sum := by decide
  have hdescent : baseEnd_170608 < baseStart_170608 := by decide
  rcases family_descends (prefixWord ++ tailWord_170608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170633 : List Nat := [1, 2, 1, 1, 4, 1, 1, 3, 7]
def baseStart_170633 : Nat := 118140960795 + 170633 * 2 ^ 59
def prefixEnd_170633 : Nat := 4983230072969 + 3 ^ 40 * 170633 * 2
def baseEnd_170633 : Nat := 38940775341660502801235

theorem tailTrace_170633 : CollatzResearch.WordTrace tailWord_170633 prefixEnd_170633 38940775341660502801235 := by
  unfold tailWord_170633
  simp only [CollatzResearch.WordTrace]
  refine ⟨6223496790833257641412553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4148997860555505094275035 6223496790833257641412553)
  ·
    refine ⟨4667622593124943231059415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6223496790833257641412553 4667622593124943231059415)
    ·
      refine ⟨7001433889687414846589123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4667622593124943231059415 7001433889687414846589123)
      ·
        refine ⟨10502150834531122269883685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7001433889687414846589123 10502150834531122269883685)
        ·
          refine ⟨1969153281474585425603191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10502150834531122269883685 1969153281474585425603191)
          ·
            refine ⟨2953729922211878138404787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1969153281474585425603191 2953729922211878138404787)
            ·
              refine ⟨4430594883317817207607181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2953729922211878138404787 4430594883317817207607181)
              ·
                refine ⟨1661473081244181452852693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4430594883317817207607181 1661473081244181452852693)
                ·
                  refine ⟨38940775341660502801235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1661473081244181452852693 38940775341660502801235)
                  ·
                    rfl

theorem cell21_170633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 7].length) (baseStart_170633 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_170633 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_170633 prefixEnd_170633 := by exact prefixLift 170633
  have htrace : WordTrace (prefixWord ++ tailWord_170633) baseStart_170633 baseEnd_170633 := by
    simpa [prefixWord, tailWord_170633, baseEnd_170633] using wordTrace_append hprefix tailTrace_170633
  have hstable : (prefixWord ++ tailWord_170633).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170633).length < 2 ^ (prefixWord ++ tailWord_170633).sum := by decide
  have hdescent : baseEnd_170633 < baseStart_170633 := by decide
  rcases family_descends (prefixWord ++ tailWord_170633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170760 : List Nat := [2, 1, 3, 2, 2, 4, 1, 3, 3]
def baseStart_170760 : Nat := 118140960795 + 170760 * 2 ^ 59
def prefixEnd_170760 : Nat := 4983230072969 + 3 ^ 40 * 170760 * 2
def baseEnd_170760 : Nat := 38969758471936504184309

theorem tailTrace_170760 : CollatzResearch.WordTrace tailWord_170760 prefixEnd_170760 38969758471936504184309 := by
  unfold tailWord_170760
  simp only [CollatzResearch.WordTrace]
  refine ⟨3114064430686579165642867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4152085907582105554190489 3114064430686579165642867)
  ·
    refine ⟨4671096646029868748464301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3114064430686579165642867 4671096646029868748464301)
    ·
      refine ⟨1751661242261200780674113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4671096646029868748464301 1751661242261200780674113)
      ·
        refine ⟨1313745931695900585505585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1751661242261200780674113 1313745931695900585505585)
        ·
          refine ⟨985309448771925439129189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1313745931695900585505585 985309448771925439129189)
          ·
            refine ⟨184745521644736019836723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 985309448771925439129189 184745521644736019836723)
            ·
              refine ⟨277118282467104029755085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184745521644736019836723 277118282467104029755085)
              ·
                refine ⟨103919355925164011158157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 277118282467104029755085 103919355925164011158157)
                ·
                  refine ⟨38969758471936504184309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103919355925164011158157 38969758471936504184309)
                  ·
                    rfl

theorem cell21_170760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 3, 3].length) (baseStart_170760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_170760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_170760 prefixEnd_170760 := by exact prefixLift 170760
  have htrace : WordTrace (prefixWord ++ tailWord_170760) baseStart_170760 baseEnd_170760 := by
    simpa [prefixWord, tailWord_170760, baseEnd_170760] using wordTrace_append hprefix tailTrace_170760
  have hstable : (prefixWord ++ tailWord_170760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170760).length < 2 ^ (prefixWord ++ tailWord_170760).sum := by decide
  have hdescent : baseEnd_170760 < baseStart_170760 := by decide
  rcases family_descends (prefixWord ++ tailWord_170760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170788 : List Nat := [2, 3, 1, 3, 3, 1, 2, 6]
def baseStart_170788 : Nat := 118140960795 + 170788 * 2 ^ 59
def prefixEnd_170788 : Nat := 4983230072969 + 3 ^ 40 * 170788 * 2
def baseEnd_170788 : Nat := 12992049484471559239195

theorem tailTrace_170788 : CollatzResearch.WordTrace tailWord_170788 prefixEnd_170788 12992049484471559239195 := by
  unfold tailWord_170788
  simp only [CollatzResearch.WordTrace]
  refine ⟨3114575052635859556652509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4152766736847812742203345 3114575052635859556652509)
  ·
    refine ⟨1167965644738447333744691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3114575052635859556652509 1167965644738447333744691)
    ·
      refine ⟨1751948467107671000617037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1167965644738447333744691 1751948467107671000617037)
      ·
        refine ⟨656980675165376625231389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1751948467107671000617037 656980675165376625231389)
        ·
          refine ⟨246367753187016234461771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 656980675165376625231389 246367753187016234461771)
          ·
            refine ⟨369551629780524351692657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246367753187016234461771 369551629780524351692657)
            ·
              refine ⟨277163722335393263769493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 369551629780524351692657 277163722335393263769493)
              ·
                refine ⟨12992049484471559239195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 277163722335393263769493 12992049484471559239195)
                ·
                  rfl

theorem cell21_170788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 6].length) (baseStart_170788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_170788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_170788 prefixEnd_170788 := by exact prefixLift 170788
  have htrace : WordTrace (prefixWord ++ tailWord_170788) baseStart_170788 baseEnd_170788 := by
    simpa [prefixWord, tailWord_170788, baseEnd_170788] using wordTrace_append hprefix tailTrace_170788
  have hstable : (prefixWord ++ tailWord_170788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170788).length < 2 ^ (prefixWord ++ tailWord_170788).sum := by decide
  have hdescent : baseEnd_170788 < baseStart_170788 := by decide
  rcases family_descends (prefixWord ++ tailWord_170788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170836 : List Nat := [2, 4, 1, 1, 4, 1, 1, 4, 3]
def baseStart_170836 : Nat := 118140960795 + 170836 * 2 ^ 59
def prefixEnd_170836 : Nat := 4983230072969 + 3 ^ 40 * 170836 * 2
def baseEnd_170836 : Nat := 38987102707377260917487

theorem tailTrace_170836 : CollatzResearch.WordTrace tailWord_170836 prefixEnd_170836 38987102707377260917487 := by
  unfold tailWord_170836
  simp only [CollatzResearch.WordTrace]
  refine ⟨3115450404548911655526181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4153933872731882207368241 3115450404548911655526181)
  ·
    refine ⟨584146950852920935411159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3115450404548911655526181 584146950852920935411159)
    ·
      refine ⟨876220426279381403116739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 584146950852920935411159 876220426279381403116739)
      ·
        refine ⟨1314330639419072104675109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 876220426279381403116739 1314330639419072104675109)
        ·
          refine ⟨246436994891076019626583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1314330639419072104675109 246436994891076019626583)
          ·
            refine ⟨369655492336614029439875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246436994891076019626583 369655492336614029439875)
            ·
              refine ⟨554483238504921044159813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369655492336614029439875 554483238504921044159813)
              ·
                refine ⟨103965607219672695779965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 554483238504921044159813 103965607219672695779965)
                ·
                  refine ⟨38987102707377260917487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103965607219672695779965 38987102707377260917487)
                  ·
                    rfl

theorem cell21_170836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_170836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_170836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_170836 prefixEnd_170836 := by exact prefixLift 170836
  have htrace : WordTrace (prefixWord ++ tailWord_170836) baseStart_170836 baseEnd_170836 := by
    simpa [prefixWord, tailWord_170836, baseEnd_170836] using wordTrace_append hprefix tailTrace_170836
  have hstable : (prefixWord ++ tailWord_170836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170836).length < 2 ^ (prefixWord ++ tailWord_170836).sum := by decide
  have hdescent : baseEnd_170836 < baseStart_170836 := by decide
  rcases family_descends (prefixWord ++ tailWord_170836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170929 : List Nat := [1, 2, 2, 4, 4, 1, 1, 3, 3]
def baseStart_170929 : Nat := 118140960795 + 170929 * 2 ^ 59
def prefixEnd_170929 : Nat := 4983230072969 + 3 ^ 40 * 170929 * 2
def baseEnd_170929 : Nat := 39008326574429765867297

theorem tailTrace_170929 : CollatzResearch.WordTrace tailWord_170929 prefixEnd_170929 39008326574429765867297 := by
  unfold tailWord_170929
  simp only [CollatzResearch.WordTrace]
  refine ⟨6234292797760900194187841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4156195198507266796125227 6234292797760900194187841)
  ·
    refine ⟨4675719598320675145640881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6234292797760900194187841 4675719598320675145640881)
    ·
      refine ⟨3506789698740506359230661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4675719598320675145640881 3506789698740506359230661)
      ·
        refine ⟨657523068513844942355749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3506789698740506359230661 657523068513844942355749)
        ·
          refine ⟨123285575346345926691703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 657523068513844942355749 123285575346345926691703)
          ·
            refine ⟨184928363019518890037555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123285575346345926691703 184928363019518890037555)
            ·
              refine ⟨277392544529278335056333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184928363019518890037555 277392544529278335056333)
              ·
                refine ⟨104022204198479375646125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 277392544529278335056333 104022204198479375646125)
                ·
                  refine ⟨39008326574429765867297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104022204198479375646125 39008326574429765867297)
                  ·
                    rfl

theorem cell21_170929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 3, 3].length) (baseStart_170929 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_170929 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_170929 prefixEnd_170929 := by exact prefixLift 170929
  have htrace : WordTrace (prefixWord ++ tailWord_170929) baseStart_170929 baseEnd_170929 := by
    simpa [prefixWord, tailWord_170929, baseEnd_170929] using wordTrace_append hprefix tailTrace_170929
  have hstable : (prefixWord ++ tailWord_170929).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170929).length < 2 ^ (prefixWord ++ tailWord_170929).sum := by decide
  have hdescent : baseEnd_170929 < baseStart_170929 := by decide
  rcases family_descends (prefixWord ++ tailWord_170929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171013 : List Nat := [1, 3, 1, 1, 2, 3, 2, 3, 5]
def baseStart_171013 : Nat := 118140960795 + 171013 * 2 ^ 59
def prefixEnd_171013 : Nat := 4983230072969 + 3 ^ 40 * 171013 * 2
def baseEnd_171013 : Nat := 39027496518864286467125

theorem tailTrace_171013 : CollatzResearch.WordTrace tailWord_171013 prefixEnd_171013 39027496518864286467125 := by
  unfold tailWord_171013
  simp only [CollatzResearch.WordTrace]
  refine ⟨6237356529456582540245693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4158237686304388360163795 6237356529456582540245693)
  ·
    refine ⟨2339008698546218452592135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6237356529456582540245693 2339008698546218452592135)
    ·
      refine ⟨3508513047819327678888203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2339008698546218452592135 3508513047819327678888203)
      ·
        refine ⟨5262769571728991518332305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3508513047819327678888203 5262769571728991518332305)
        ·
          refine ⟨3947077178796743638749229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5262769571728991518332305 3947077178796743638749229)
          ·
            refine ⟨1480153942048778864530961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3947077178796743638749229 1480153942048778864530961)
            ·
              refine ⟨1110115456536584148398221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1480153942048778864530961 1110115456536584148398221)
              ·
                refine ⟨416293296201219055649333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1110115456536584148398221 416293296201219055649333)
                ·
                  refine ⟨39027496518864286467125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 416293296201219055649333 39027496518864286467125)
                  ·
                    rfl

theorem cell21_171013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_171013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_171013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_171013 prefixEnd_171013 := by exact prefixLift 171013
  have htrace : WordTrace (prefixWord ++ tailWord_171013) baseStart_171013 baseEnd_171013 := by
    simpa [prefixWord, tailWord_171013, baseEnd_171013] using wordTrace_append hprefix tailTrace_171013
  have hstable : (prefixWord ++ tailWord_171013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171013).length < 2 ^ (prefixWord ++ tailWord_171013).sum := by decide
  have hdescent : baseEnd_171013 < baseStart_171013 := by decide
  rcases family_descends (prefixWord ++ tailWord_171013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171027 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 8]
def baseStart_171027 : Nat := 118140960795 + 171027 * 2 ^ 59
def prefixEnd_171027 : Nat := 4983230072969 + 3 ^ 40 * 171027 * 2
def baseEnd_171027 : Nat := 39030691509603373233763

theorem tailTrace_171027 : CollatzResearch.WordTrace tailWord_171027 prefixEnd_171027 39030691509603373233763 := by
  unfold tailWord_171027
  simp only [CollatzResearch.WordTrace]
  refine ⟨6237867151405862931255335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4158578100937241954170223 6237867151405862931255335)
  ·
    refine ⟨9356800727108794396883003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6237867151405862931255335 9356800727108794396883003)
    ·
      refine ⟨14035201090663191595324505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9356800727108794396883003 14035201090663191595324505)
      ·
        refine ⟨10526400817997393696493379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14035201090663191595324505 10526400817997393696493379)
        ·
          refine ⟨15789601226996090544740069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10526400817997393696493379 15789601226996090544740069)
          ·
            refine ⟨2960550230061766977138763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15789601226996090544740069 2960550230061766977138763)
            ·
              refine ⟨4440825345092650465708145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2960550230061766977138763 4440825345092650465708145)
              ·
                refine ⟨3330619008819487849281109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4440825345092650465708145 3330619008819487849281109)
                ·
                  refine ⟨39030691509603373233763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3330619008819487849281109 39030691509603373233763)
                  ·
                    rfl

theorem cell21_171027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 8].length) (baseStart_171027 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_171027 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_171027 prefixEnd_171027 := by exact prefixLift 171027
  have htrace : WordTrace (prefixWord ++ tailWord_171027) baseStart_171027 baseEnd_171027 := by
    simpa [prefixWord, tailWord_171027, baseEnd_171027] using wordTrace_append hprefix tailTrace_171027
  have hstable : (prefixWord ++ tailWord_171027).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171027).length < 2 ^ (prefixWord ++ tailWord_171027).sum := by decide
  have hdescent : baseEnd_171027 < baseStart_171027 := by decide
  rcases family_descends (prefixWord ++ tailWord_171027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171058 : List Nat := [3, 2, 1, 1, 2, 2, 10]
def baseStart_171058 : Nat := 118140960795 + 171058 * 2 ^ 59
def prefixEnd_171058 : Nat := 4983230072969 + 3 ^ 40 * 171058 * 2
def baseEnd_171058 : Nat := 4337529570217134246337

theorem tailTrace_171058 : CollatzResearch.WordTrace tailWord_171058 prefixEnd_171058 4337529570217134246337 := by
  unfold tailWord_171058
  simp only [CollatzResearch.WordTrace]
  refine ⟨1559749453573388806408457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4159331876195703483755885 1559749453573388806408457)
  ·
    refine ⟨1169812090180041604806343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1559749453573388806408457 1169812090180041604806343)
    ·
      refine ⟨1754718135270062407209515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1169812090180041604806343 1754718135270062407209515)
      ·
        refine ⟨2632077202905093610814273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1754718135270062407209515 2632077202905093610814273)
        ·
          refine ⟨1974057902178820208110705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2632077202905093610814273 1974057902178820208110705)
          ·
            refine ⟨1480543426634115156083029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1974057902178820208110705 1480543426634115156083029)
            ·
              refine ⟨4337529570217134246337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1480543426634115156083029 4337529570217134246337)
              ·
                rfl

theorem cell21_171058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 10].length) (baseStart_171058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_171058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_171058 prefixEnd_171058 := by exact prefixLift 171058
  have htrace : WordTrace (prefixWord ++ tailWord_171058) baseStart_171058 baseEnd_171058 := by
    simpa [prefixWord, tailWord_171058, baseEnd_171058] using wordTrace_append hprefix tailTrace_171058
  have hstable : (prefixWord ++ tailWord_171058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171058).length < 2 ^ (prefixWord ++ tailWord_171058).sum := by decide
  have hdescent : baseEnd_171058 < baseStart_171058 := by decide
  rcases family_descends (prefixWord ++ tailWord_171058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171089 : List Nat := [1, 2, 2, 1, 3, 1, 4, 2, 5]
def baseStart_171089 : Nat := 118140960795 + 171089 * 2 ^ 59
def prefixEnd_171089 : Nat := 4983230072969 + 3 ^ 40 * 171089 * 2
def baseEnd_171089 : Nat := 39044840754305043200303

theorem tailTrace_171089 : CollatzResearch.WordTrace tailWord_171089 prefixEnd_171089 39044840754305043200303 := by
  unfold tailWord_171089
  simp only [CollatzResearch.WordTrace]
  refine ⟨6240128477181247520012321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4160085651454165013341547 6240128477181247520012321)
  ·
    refine ⟨4680096357885935640009241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6240128477181247520012321 4680096357885935640009241)
    ·
      refine ⟨3510072268414451730006931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4680096357885935640009241 3510072268414451730006931)
      ·
        refine ⟨5265108402621677595010397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3510072268414451730006931 5265108402621677595010397)
        ·
          refine ⟨1974415650983129098128899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5265108402621677595010397 1974415650983129098128899)
          ·
            refine ⟨2961623476474693647193349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1974415650983129098128899 2961623476474693647193349)
            ·
              refine ⟨555304401839005058848753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2961623476474693647193349 555304401839005058848753)
              ·
                refine ⟨416478301379253794136565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 555304401839005058848753 416478301379253794136565)
                ·
                  refine ⟨39044840754305043200303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 416478301379253794136565 39044840754305043200303)
                  ·
                    rfl

theorem cell21_171089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 5].length) (baseStart_171089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_171089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_171089 prefixEnd_171089 := by exact prefixLift 171089
  have htrace : WordTrace (prefixWord ++ tailWord_171089) baseStart_171089 baseEnd_171089 := by
    simpa [prefixWord, tailWord_171089, baseEnd_171089] using wordTrace_append hprefix tailTrace_171089
  have hstable : (prefixWord ++ tailWord_171089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171089).length < 2 ^ (prefixWord ++ tailWord_171089).sum := by decide
  have hdescent : baseEnd_171089 < baseStart_171089 := by decide
  rcases family_descends (prefixWord ++ tailWord_171089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171103 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 8]
def baseStart_171103 : Nat := 118140960795 + 171103 * 2 ^ 59
def prefixEnd_171103 : Nat := 4983230072969 + 3 ^ 40 * 171103 * 2
def baseEnd_171103 : Nat := 39048035745044129966941

theorem tailTrace_171103 : CollatzResearch.WordTrace tailWord_171103 prefixEnd_171103 39048035745044129966941 := by
  unfold tailWord_171103
  simp only [CollatzResearch.WordTrace]
  refine ⟨6240639099130527911021963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4160426066087018607347975 6240639099130527911021963)
  ·
    refine ⟨9360958648695791866532945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6240639099130527911021963 9360958648695791866532945)
    ·
      refine ⟨7020718986521843899899709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9360958648695791866532945 7020718986521843899899709)
      ·
        refine ⟨2632769619945691462462391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7020718986521843899899709 2632769619945691462462391)
        ·
          refine ⟨3949154429918537193693587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2632769619945691462462391 3949154429918537193693587)
          ·
            refine ⟨5923731644877805790540381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3949154429918537193693587 5923731644877805790540381)
            ·
              refine ⟨2221399366829177171452643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5923731644877805790540381 2221399366829177171452643)
              ·
                refine ⟨3332099050243765757178965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2221399366829177171452643 3332099050243765757178965)
                ·
                  refine ⟨39048035745044129966941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3332099050243765757178965 39048035745044129966941)
                  ·
                    rfl

theorem cell21_171103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 8].length) (baseStart_171103 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_171103 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_171103 prefixEnd_171103 := by exact prefixLift 171103
  have htrace : WordTrace (prefixWord ++ tailWord_171103) baseStart_171103 baseEnd_171103 := by
    simpa [prefixWord, tailWord_171103, baseEnd_171103] using wordTrace_append hprefix tailTrace_171103
  have hstable : (prefixWord ++ tailWord_171103).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171103).length < 2 ^ (prefixWord ++ tailWord_171103).sum := by decide
  have hdescent : baseEnd_171103 < baseStart_171103 := by decide
  rcases family_descends (prefixWord ++ tailWord_171103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171120 : List Nat := [2, 1, 1, 1, 5, 1, 2, 4, 4]
def baseStart_171120 : Nat := 118140960795 + 171120 * 2 ^ 59
def prefixEnd_171120 : Nat := 4983230072969 + 3 ^ 40 * 171120 * 2
def baseEnd_171120 : Nat := 39051915376655878183573

theorem tailTrace_171120 : CollatzResearch.WordTrace tailWord_171120 prefixEnd_171120 39051915376655878183573 := by
  unfold tailWord_171120
  simp only [CollatzResearch.WordTrace]
  refine ⟨3120629570034469907195407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4160839426712626542927209 3120629570034469907195407)
  ·
    refine ⟨4680944355051704860793111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3120629570034469907195407 4680944355051704860793111)
    ·
      refine ⟨7021416532577557291189667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4680944355051704860793111 7021416532577557291189667)
      ·
        refine ⟨10532124798866335936784501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7021416532577557291189667 10532124798866335936784501)
        ·
          refine ⟨987386699893718994073547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10532124798866335936784501 987386699893718994073547)
          ·
            refine ⟨1481080049840578491110321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 987386699893718994073547 1481080049840578491110321)
            ·
              refine ⟨1110810037380433868332741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1481080049840578491110321 1110810037380433868332741)
              ·
                refine ⟨208276882008831350312389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1110810037380433868332741 208276882008831350312389)
                ·
                  refine ⟨39051915376655878183573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 208276882008831350312389 39051915376655878183573)
                  ·
                    rfl

theorem cell21_171120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 4, 4].length) (baseStart_171120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_171120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_171120 prefixEnd_171120 := by exact prefixLift 171120
  have htrace : WordTrace (prefixWord ++ tailWord_171120) baseStart_171120 baseEnd_171120 := by
    simpa [prefixWord, tailWord_171120, baseEnd_171120] using wordTrace_append hprefix tailTrace_171120
  have hstable : (prefixWord ++ tailWord_171120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171120).length < 2 ^ (prefixWord ++ tailWord_171120).sum := by decide
  have hdescent : baseEnd_171120 < baseStart_171120 := by decide
  rcases family_descends (prefixWord ++ tailWord_171120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171137 : List Nat := [1, 2, 4, 2, 2, 2, 1, 3, 4]
def baseStart_171137 : Nat := 118140960795 + 171137 * 2 ^ 59
def prefixEnd_171137 : Nat := 4983230072969 + 3 ^ 40 * 171137 * 2
def baseEnd_171137 : Nat := 39055795008267626400205

theorem tailTrace_171137 : CollatzResearch.WordTrace tailWord_171137 prefixEnd_171137 39055795008267626400205 := by
  unfold tailWord_171137
  simp only [CollatzResearch.WordTrace]
  refine ⟨6241879181007351717759665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4161252787338234478506443 6241879181007351717759665)
  ·
    refine ⟨4681409385755513788319749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6241879181007351717759665 4681409385755513788319749)
    ·
      refine ⟨877764259829158835309953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4681409385755513788319749 877764259829158835309953)
      ·
        refine ⟨658323194871869126482465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 877764259829158835309953 658323194871869126482465)
        ·
          refine ⟨493742396153901844861849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 658323194871869126482465 493742396153901844861849)
          ·
            refine ⟨370306797115426383646387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 493742396153901844861849 370306797115426383646387)
            ·
              refine ⟨555460195673139575469581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 370306797115426383646387 555460195673139575469581)
              ·
                refine ⟨208297573377427340801093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 555460195673139575469581 208297573377427340801093)
                ·
                  refine ⟨39055795008267626400205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 208297573377427340801093 39055795008267626400205)
                  ·
                    rfl

theorem cell21_171137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 3, 4].length) (baseStart_171137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_171137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_171137 prefixEnd_171137 := by exact prefixLift 171137
  have htrace : WordTrace (prefixWord ++ tailWord_171137) baseStart_171137 baseEnd_171137 := by
    simpa [prefixWord, tailWord_171137, baseEnd_171137] using wordTrace_append hprefix tailTrace_171137
  have hstable : (prefixWord ++ tailWord_171137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171137).length < 2 ^ (prefixWord ++ tailWord_171137).sum := by decide
  have hdescent : baseEnd_171137 < baseStart_171137 := by decide
  rcases family_descends (prefixWord ++ tailWord_171137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171202 : List Nat := [3, 5, 1, 1, 2, 1, 3, 5]
def baseStart_171202 : Nat := 118140960795 + 171202 * 2 ^ 59
def prefixEnd_171202 : Nat := 4983230072969 + 3 ^ 40 * 171202 * 2
def baseEnd_171202 : Nat := 13023542964613985938913

theorem tailTrace_171202 : CollatzResearch.WordTrace tailWord_171202 prefixEnd_171202 13023542964613985938913 := by
  unfold tailWord_171202
  simp only [CollatzResearch.WordTrace]
  refine ⟨1561062481442966954718965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4162833283847911879250573 1561062481442966954718965)
  ·
    refine ⟨146349607635278152004903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1561062481442966954718965 146349607635278152004903)
    ·
      refine ⟨219524411452917228007355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146349607635278152004903 219524411452917228007355)
      ·
        refine ⟨329286617179375842011033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219524411452917228007355 329286617179375842011033)
        ·
          refine ⟨246964962884531881508275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 329286617179375842011033 246964962884531881508275)
          ·
            refine ⟨370447444326797822262413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246964962884531881508275 370447444326797822262413)
            ·
              refine ⟨138917791622549183348405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 370447444326797822262413 138917791622549183348405)
              ·
                refine ⟨13023542964613985938913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 138917791622549183348405 13023542964613985938913)
                ·
                  rfl

theorem cell21_171202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 5].length) (baseStart_171202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_171202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_171202 prefixEnd_171202 := by exact prefixLift 171202
  have htrace : WordTrace (prefixWord ++ tailWord_171202) baseStart_171202 baseEnd_171202 := by
    simpa [prefixWord, tailWord_171202, baseEnd_171202] using wordTrace_append hprefix tailTrace_171202
  have hstable : (prefixWord ++ tailWord_171202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171202).length < 2 ^ (prefixWord ++ tailWord_171202).sum := by decide
  have hdescent : baseEnd_171202 < baseStart_171202 := by decide
  rcases family_descends (prefixWord ++ tailWord_171202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171275 : List Nat := [1, 1, 1, 1, 5, 5, 1, 3, 3]
def baseStart_171275 : Nat := 118140960795 + 171275 * 2 ^ 59
def prefixEnd_171275 : Nat := 4983230072969 + 3 ^ 40 * 171275 * 2
def baseEnd_171275 : Nat := 39087288488410053099923

theorem tailTrace_171275 : CollatzResearch.WordTrace tailWord_171275 prefixEnd_171275 39087288488410053099923 := by
  unfold tailWord_171275
  simp only [CollatzResearch.WordTrace]
  refine ⟨6246912454507401286283279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4164608303004934190855519 6246912454507401286283279)
  ·
    refine ⟨9370368681761101929424919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6246912454507401286283279 9370368681761101929424919)
    ·
      refine ⟨14055553022641652894137379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9370368681761101929424919 14055553022641652894137379)
      ·
        refine ⟨21083329533962479341206069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14055553022641652894137379 21083329533962479341206069)
        ·
          refine ⟨1976562143808982438238069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21083329533962479341206069 1976562143808982438238069)
          ·
            refine ⟨185302700982092103584819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1976562143808982438238069 185302700982092103584819)
            ·
              refine ⟨277954051473138155377229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185302700982092103584819 277954051473138155377229)
              ·
                refine ⟨104232769302426808266461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 277954051473138155377229 104232769302426808266461)
                ·
                  refine ⟨39087288488410053099923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104232769302426808266461 39087288488410053099923)
                  ·
                    rfl

theorem cell21_171275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 3, 3].length) (baseStart_171275 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_171275 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_171275 prefixEnd_171275 := by exact prefixLift 171275
  have htrace : WordTrace (prefixWord ++ tailWord_171275) baseStart_171275 baseEnd_171275 := by
    simpa [prefixWord, tailWord_171275, baseEnd_171275] using wordTrace_append hprefix tailTrace_171275
  have hstable : (prefixWord ++ tailWord_171275).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171275).length < 2 ^ (prefixWord ++ tailWord_171275).sum := by decide
  have hdescent : baseEnd_171275 < baseStart_171275 := by decide
  rcases family_descends (prefixWord ++ tailWord_171275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171306 : List Nat := [3, 1, 4, 2, 1, 1, 4, 1, 4]
def baseStart_171306 : Nat := 118140960795 + 171306 * 2 ^ 59
def prefixEnd_171306 : Nat := 4983230072969 + 3 ^ 40 * 171306 * 2
def baseEnd_171306 : Nat := 39094363110760888083193

theorem tailTrace_171306 : CollatzResearch.WordTrace tailWord_171306 prefixEnd_171306 39094363110760888083193 := by
  unfold tailWord_171306
  simp only [CollatzResearch.WordTrace]
  refine ⟨1562010779348773395165443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4165362078263395720441181 1562010779348773395165443)
  ·
    refine ⟨2343016169023160092748165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1562010779348773395165443 2343016169023160092748165)
    ·
      refine ⟨439315531691842517390281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2343016169023160092748165 439315531691842517390281)
      ·
        refine ⟨329486648768881888042711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 439315531691842517390281 329486648768881888042711)
        ·
          refine ⟨494229973153322832064067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329486648768881888042711 494229973153322832064067)
          ·
            refine ⟨741344959729984248096101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 494229973153322832064067 741344959729984248096101)
            ·
              refine ⟨139002179949372046518019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 741344959729984248096101 139002179949372046518019)
              ·
                refine ⟨208503269924058069777029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139002179949372046518019 208503269924058069777029)
                ·
                  refine ⟨39094363110760888083193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 208503269924058069777029 39094363110760888083193)
                  ·
                    rfl

theorem cell21_171306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 1, 4].length) (baseStart_171306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_171306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_171306 prefixEnd_171306 := by exact prefixLift 171306
  have htrace : WordTrace (prefixWord ++ tailWord_171306) baseStart_171306 baseEnd_171306 := by
    simpa [prefixWord, tailWord_171306, baseEnd_171306] using wordTrace_append hprefix tailTrace_171306
  have hstable : (prefixWord ++ tailWord_171306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171306).length < 2 ^ (prefixWord ++ tailWord_171306).sum := by decide
  have hdescent : baseEnd_171306 < baseStart_171306 := by decide
  rcases family_descends (prefixWord ++ tailWord_171306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171351 : List Nat := [1, 1, 3, 2, 3, 2, 4, 2, 3]
def baseStart_171351 : Nat := 118140960795 + 171351 * 2 ^ 59
def prefixEnd_171351 : Nat := 4983230072969 + 3 ^ 40 * 171351 * 2
def baseEnd_171351 : Nat := 39104632723850809833101

theorem tailTrace_171351 : CollatzResearch.WordTrace tailWord_171351 prefixEnd_171351 39104632723850809833101 := by
  unfold tailWord_171351
  simp only [CollatzResearch.WordTrace]
  refine ⟨6249684402232066266049907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4166456268154710844033271 6249684402232066266049907)
  ·
    refine ⟨9374526603348099399074861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6249684402232066266049907 9374526603348099399074861)
    ·
      refine ⟨3515447476255537274653073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9374526603348099399074861 3515447476255537274653073)
      ·
        refine ⟨2636585607191652955989805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3515447476255537274653073 2636585607191652955989805)
        ·
          refine ⟨988719602696869858496177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2636585607191652955989805 988719602696869858496177)
          ·
            refine ⟨741539702022652393872133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 988719602696869858496177 741539702022652393872133)
            ·
              refine ⟨139038694129247323851025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 741539702022652393872133 139038694129247323851025)
              ·
                refine ⟨104279020596935492888269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139038694129247323851025 104279020596935492888269)
                ·
                  refine ⟨39104632723850809833101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104279020596935492888269 39104632723850809833101)
                  ·
                    rfl

theorem cell21_171351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 2, 3].length) (baseStart_171351 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_171351 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_171351 prefixEnd_171351 := by exact prefixLift 171351
  have htrace : WordTrace (prefixWord ++ tailWord_171351) baseStart_171351 baseEnd_171351 := by
    simpa [prefixWord, tailWord_171351, baseEnd_171351] using wordTrace_append hprefix tailTrace_171351
  have hstable : (prefixWord ++ tailWord_171351).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171351).length < 2 ^ (prefixWord ++ tailWord_171351).sum := by decide
  have hdescent : baseEnd_171351 < baseStart_171351 := by decide
  rcases family_descends (prefixWord ++ tailWord_171351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171531 : List Nat := [1, 1, 1, 1, 8, 2, 1, 6]
def baseStart_171531 : Nat := 118140960795 + 171531 * 2 ^ 59
def prefixEnd_171531 : Nat := 4983230072969 + 3 ^ 40 * 171531 * 2
def baseEnd_171531 : Nat := 13048570392070165610911

theorem tailTrace_171531 : CollatzResearch.WordTrace tailWord_171531 prefixEnd_171531 13048570392070165610911 := by
  unfold tailWord_171531
  simp only [CollatzResearch.WordTrace]
  refine ⟨6256249541579957007602447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4170833027719971338401631 6256249541579957007602447)
  ·
    refine ⟨9384374312369935511403671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6256249541579957007602447 9384374312369935511403671)
    ·
      refine ⟨14076561468554903267105507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9384374312369935511403671 14076561468554903267105507)
      ·
        refine ⟨21114842202832354900658261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14076561468554903267105507 21114842202832354900658261)
        ·
          refine ⟨247439557064441658992089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 21114842202832354900658261 247439557064441658992089)
          ·
            refine ⟨185579667798331244244067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247439557064441658992089 185579667798331244244067)
            ·
              refine ⟨278369501697496866366101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185579667798331244244067 278369501697496866366101)
              ·
                refine ⟨13048570392070165610911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 278369501697496866366101 13048570392070165610911)
                ·
                  rfl

theorem cell21_171531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 6].length) (baseStart_171531 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_171531 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_171531 prefixEnd_171531 := by exact prefixLift 171531
  have htrace : WordTrace (prefixWord ++ tailWord_171531) baseStart_171531 baseEnd_171531 := by
    simpa [prefixWord, tailWord_171531, baseEnd_171531] using wordTrace_append hprefix tailTrace_171531
  have hstable : (prefixWord ++ tailWord_171531).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171531).length < 2 ^ (prefixWord ++ tailWord_171531).sum := by decide
  have hdescent : baseEnd_171531 < baseStart_171531 := by decide
  rcases family_descends (prefixWord ++ tailWord_171531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171576 : List Nat := [2, 1, 2, 1, 4, 2, 3, 2, 4]
def baseStart_171576 : Nat := 118140960795 + 171576 * 2 ^ 59
def prefixEnd_171576 : Nat := 4983230072969 + 3 ^ 40 * 171576 * 2
def baseEnd_171576 : Nat := 39155980789300418582641

theorem tailTrace_171576 : CollatzResearch.WordTrace tailWord_171576 prefixEnd_171576 39155980789300418582641 := by
  unfold tailWord_171576
  simp only [CollatzResearch.WordTrace]
  refine ⟨3128945413208464846495291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4171927217611286461993721 3128945413208464846495291)
  ·
    refine ⟨4693418119812697269742937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3128945413208464846495291 4693418119812697269742937)
    ·
      refine ⟨3520063589859522952307203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4693418119812697269742937 3520063589859522952307203)
      ·
        refine ⟨5280095384789284428460805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3520063589859522952307203 5280095384789284428460805)
        ·
          refine ⟨990017884647990830336401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5280095384789284428460805 990017884647990830336401)
          ·
            refine ⟨742513413485993122752301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 990017884647990830336401 742513413485993122752301)
            ·
              refine ⟨278442530057247421032113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 742513413485993122752301 278442530057247421032113)
              ·
                refine ⟨208831897542935565774085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 278442530057247421032113 208831897542935565774085)
                ·
                  refine ⟨39155980789300418582641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 208831897542935565774085 39155980789300418582641)
                  ·
                    rfl

theorem cell21_171576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 2, 4].length) (baseStart_171576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_171576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_171576 prefixEnd_171576 := by exact prefixLift 171576
  have htrace : WordTrace (prefixWord ++ tailWord_171576) baseStart_171576 baseEnd_171576 := by
    simpa [prefixWord, tailWord_171576, baseEnd_171576] using wordTrace_append hprefix tailTrace_171576
  have hstable : (prefixWord ++ tailWord_171576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171576).length < 2 ^ (prefixWord ++ tailWord_171576).sum := by decide
  have hdescent : baseEnd_171576 < baseStart_171576 := by decide
  rcases family_descends (prefixWord ++ tailWord_171576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171607 : List Nat := [1, 1, 3, 2, 2, 5, 2, 5]
def baseStart_171607 : Nat := 118140960795 + 171607 * 2 ^ 59
def prefixEnd_171607 : Nat := 4983230072969 + 3 ^ 40 * 171607 * 2
def baseEnd_171607 : Nat := 13054351803883751188637

theorem tailTrace_171607 : CollatzResearch.WordTrace tailWord_171607 prefixEnd_171607 13054351803883751188637 := by
  unfold tailWord_171607
  simp only [CollatzResearch.WordTrace]
  refine ⟨6259021489304621987369075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4172680992869747991579383 6259021489304621987369075)
  ·
    refine ⟨9388532233956932981053613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6259021489304621987369075 9388532233956932981053613)
    ·
      refine ⟨3520699587733849867895105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9388532233956932981053613 3520699587733849867895105)
      ·
        refine ⟨2640524690800387400921329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3520699587733849867895105 2640524690800387400921329)
        ·
          refine ⟨1980393518100290550690997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2640524690800387400921329 1980393518100290550690997)
          ·
            refine ⟨185661892321902239127281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1980393518100290550690997 185661892321902239127281)
            ·
              refine ⟨139246419241426679345461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185661892321902239127281 139246419241426679345461)
              ·
                refine ⟨13054351803883751188637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 139246419241426679345461 13054351803883751188637)
                ·
                  rfl

theorem cell21_171607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 5].length) (baseStart_171607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_171607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_171607 prefixEnd_171607 := by exact prefixLift 171607
  have htrace : WordTrace (prefixWord ++ tailWord_171607) baseStart_171607 baseEnd_171607 := by
    simpa [prefixWord, tailWord_171607, baseEnd_171607] using wordTrace_append hprefix tailTrace_171607
  have hstable : (prefixWord ++ tailWord_171607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171607).length < 2 ^ (prefixWord ++ tailWord_171607).sum := by decide
  have hdescent : baseEnd_171607 < baseStart_171607 := by decide
  rcases family_descends (prefixWord ++ tailWord_171607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171613 : List Nat := [1, 4, 4, 2, 1, 2, 1, 3, 3]
def baseStart_171613 : Nat := 118140960795 + 171613 * 2 ^ 59
def prefixEnd_171613 : Nat := 4983230072969 + 3 ^ 40 * 171613 * 2
def baseEnd_171613 : Nat := 39164424693396576465899

theorem tailTrace_171613 : CollatzResearch.WordTrace tailWord_171613 prefixEnd_171613 39164424693396576465899 := by
  unfold tailWord_171613
  simp only [CollatzResearch.WordTrace]
  refine ⟨6259240327282885012087493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4172826884855256674724995 6259240327282885012087493)
  ·
    refine ⟨1173607561365540939766405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6259240327282885012087493 1173607561365540939766405)
    ·
      refine ⟨220051417756038926206201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1173607561365540939766405 220051417756038926206201)
      ·
        refine ⟨165038563317029194654651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220051417756038926206201 165038563317029194654651)
        ·
          refine ⟨247557844975543791981977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165038563317029194654651 247557844975543791981977)
          ·
            refine ⟨185668383731657843986483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247557844975543791981977 185668383731657843986483)
            ·
              refine ⟨278502575597486765979725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185668383731657843986483 278502575597486765979725)
              ·
                refine ⟨104438465849057537242397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 278502575597486765979725 104438465849057537242397)
                ·
                  refine ⟨39164424693396576465899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104438465849057537242397 39164424693396576465899)
                  ·
                    rfl

theorem cell21_171613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 3, 3].length) (baseStart_171613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_171613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_171613 prefixEnd_171613 := by exact prefixLift 171613
  have htrace : WordTrace (prefixWord ++ tailWord_171613) baseStart_171613 baseEnd_171613 := by
    simpa [prefixWord, tailWord_171613, baseEnd_171613] using wordTrace_append hprefix tailTrace_171613
  have hstable : (prefixWord ++ tailWord_171613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171613).length < 2 ^ (prefixWord ++ tailWord_171613).sum := by decide
  have hdescent : baseEnd_171613 < baseStart_171613 := by decide
  rcases family_descends (prefixWord ++ tailWord_171613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171638 : List Nat := [5, 1, 1, 2, 2, 1, 3, 1, 5]
def baseStart_171638 : Nat := 118140960795 + 171638 * 2 ^ 59
def prefixEnd_171638 : Nat := 4983230072969 + 3 ^ 40 * 171638 * 2
def baseEnd_171638 : Nat := 39170130034002088549181

theorem tailTrace_171638 : CollatzResearch.WordTrace tailWord_171638 prefixEnd_171638 39170130034002088549181 := by
  unfold tailWord_171638
  simp only [CollatzResearch.WordTrace]
  refine ⟨391259509512019642609223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4173434768128209521165045 391259509512019642609223)
  ·
    refine ⟨586889264268029463913835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 391259509512019642609223 586889264268029463913835)
    ·
      refine ⟨880333896402044195870753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 586889264268029463913835 880333896402044195870753)
      ·
        refine ⟨660250422301533146903065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 880333896402044195870753 660250422301533146903065)
        ·
          refine ⟨495187816726149860177299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 660250422301533146903065 495187816726149860177299)
          ·
            refine ⟨742781725089224790265949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 495187816726149860177299 742781725089224790265949)
            ·
              refine ⟨278543146908459296349731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 742781725089224790265949 278543146908459296349731)
              ·
                refine ⟨417814720362688944524597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 278543146908459296349731 417814720362688944524597)
                ·
                  refine ⟨39170130034002088549181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 417814720362688944524597 39170130034002088549181)
                  ·
                    rfl

theorem cell21_171638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_171638 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_171638 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_171638 prefixEnd_171638 := by exact prefixLift 171638
  have htrace : WordTrace (prefixWord ++ tailWord_171638) baseStart_171638 baseEnd_171638 := by
    simpa [prefixWord, tailWord_171638, baseEnd_171638] using wordTrace_append hprefix tailTrace_171638
  have hstable : (prefixWord ++ tailWord_171638).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171638).length < 2 ^ (prefixWord ++ tailWord_171638).sum := by decide
  have hdescent : baseEnd_171638 < baseStart_171638 := by decide
  rcases family_descends (prefixWord ++ tailWord_171638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171711 : List Nat := [1, 1, 2, 2, 2, 3, 1, 5, 4]
def baseStart_171711 : Nat := 118140960795 + 171711 * 2 ^ 59
def prefixEnd_171711 : Nat := 4983230072969 + 3 ^ 40 * 171711 * 2
def baseEnd_171711 : Nat := 39186789628570183832365

theorem tailTrace_171711 : CollatzResearch.WordTrace tailWord_171711 prefixEnd_171711 39186789628570183832365 := by
  unfold tailWord_171711
  simp only [CollatzResearch.WordTrace]
  refine ⟨6262814680927847749154987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4175209787285231832769991 6262814680927847749154987)
  ·
    refine ⟨9394222021391771623732481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6262814680927847749154987 9394222021391771623732481)
    ·
      refine ⟨7045666516043828717799361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9394222021391771623732481 7045666516043828717799361)
      ·
        refine ⟨5284249887032871538349521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7045666516043828717799361 5284249887032871538349521)
        ·
          refine ⟨3963187415274653653762141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5284249887032871538349521 3963187415274653653762141)
          ·
            refine ⟨1486195280727995120160803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3963187415274653653762141 1486195280727995120160803)
            ·
              refine ⟨2229292921091992680241205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1486195280727995120160803 2229292921091992680241205)
              ·
                refine ⟨208996211352374313772613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2229292921091992680241205 208996211352374313772613)
                ·
                  refine ⟨39186789628570183832365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 208996211352374313772613 39186789628570183832365)
                  ·
                    rfl

theorem cell21_171711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 5, 4].length) (baseStart_171711 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_171711 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_171711 prefixEnd_171711 := by exact prefixLift 171711
  have htrace : WordTrace (prefixWord ++ tailWord_171711) baseStart_171711 baseEnd_171711 := by
    simpa [prefixWord, tailWord_171711, baseEnd_171711] using wordTrace_append hprefix tailTrace_171711
  have hstable : (prefixWord ++ tailWord_171711).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171711).length < 2 ^ (prefixWord ++ tailWord_171711).sum := by decide
  have hdescent : baseEnd_171711 < baseStart_171711 := by decide
  rcases family_descends (prefixWord ++ tailWord_171711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171745 : List Nat := [1, 2, 3, 1, 5, 2, 1, 2, 4]
def baseStart_171745 : Nat := 118140960795 + 171745 * 2 ^ 59
def prefixEnd_171745 : Nat := 4983230072969 + 3 ^ 40 * 171745 * 2
def baseEnd_171745 : Nat := 39194548891793680265629

theorem tailTrace_171745 : CollatzResearch.WordTrace tailWord_171745 prefixEnd_171745 39194548891793680265629 := by
  unfold tailWord_171745
  simp only [CollatzResearch.WordTrace]
  refine ⟨6264054762804671555892689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4176036508536447703928459 6264054762804671555892689)
  ·
    refine ⟨4698041072103503666919517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6264054762804671555892689 4698041072103503666919517)
    ·
      refine ⟨1761765402038813875094819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4698041072103503666919517 1761765402038813875094819)
      ·
        refine ⟨2642648103058220812642229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1761765402038813875094819 2642648103058220812642229)
        ·
          refine ⟨247748259661708201185209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2642648103058220812642229 247748259661708201185209)
          ·
            refine ⟨185811194746281150888907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247748259661708201185209 185811194746281150888907)
            ·
              refine ⟨278716792119421726333361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185811194746281150888907 278716792119421726333361)
              ·
                refine ⟨209037594089566294750021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 278716792119421726333361 209037594089566294750021)
                ·
                  refine ⟨39194548891793680265629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 209037594089566294750021 39194548891793680265629)
                  ·
                    rfl

theorem cell21_171745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 2, 4].length) (baseStart_171745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_171745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_171745 prefixEnd_171745 := by exact prefixLift 171745
  have htrace : WordTrace (prefixWord ++ tailWord_171745) baseStart_171745 baseEnd_171745 := by
    simpa [prefixWord, tailWord_171745, baseEnd_171745] using wordTrace_append hprefix tailTrace_171745
  have hstable : (prefixWord ++ tailWord_171745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171745).length < 2 ^ (prefixWord ++ tailWord_171745).sum := by decide
  have hdescent : baseEnd_171745 < baseStart_171745 := by decide
  rcases family_descends (prefixWord ++ tailWord_171745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171756 : List Nat := [2, 2, 1, 1, 2, 2, 3, 3, 5]
def baseStart_171756 : Nat := 118140960795 + 171756 * 2 ^ 59
def prefixEnd_171756 : Nat := 4983230072969 + 3 ^ 40 * 171756 * 2
def baseEnd_171756 : Nat := 39197059241660105582273

theorem tailTrace_171756 : CollatzResearch.WordTrace tailWord_171756 prefixEnd_171756 39197059241660105582273 := by
  unfold tailWord_171756
  simp only [CollatzResearch.WordTrace]
  refine ⟨3132227982882410217271561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4176303977176546956362081 3132227982882410217271561)
  ·
    refine ⟨2349170987161807662953671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3132227982882410217271561 2349170987161807662953671)
    ·
      refine ⟨3523756480742711494430507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2349170987161807662953671 3523756480742711494430507)
      ·
        refine ⟨5285634721114067241645761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3523756480742711494430507 5285634721114067241645761)
        ·
          refine ⟨3964226040835550431234321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5285634721114067241645761 3964226040835550431234321)
          ·
            refine ⟨2973169530626662823425741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3964226040835550431234321 2973169530626662823425741)
            ·
              refine ⟨1114938573984998558784653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2973169530626662823425741 1114938573984998558784653)
              ·
                refine ⟨418101965244374459544245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1114938573984998558784653 418101965244374459544245)
                ·
                  refine ⟨39197059241660105582273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 418101965244374459544245 39197059241660105582273)
                  ·
                    rfl

theorem cell21_171756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_171756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_171756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_171756 prefixEnd_171756 := by exact prefixLift 171756
  have htrace : WordTrace (prefixWord ++ tailWord_171756) baseStart_171756 baseEnd_171756 := by
    simpa [prefixWord, tailWord_171756, baseEnd_171756] using wordTrace_append hprefix tailTrace_171756
  have hstable : (prefixWord ++ tailWord_171756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171756).length < 2 ^ (prefixWord ++ tailWord_171756).sum := by decide
  have hdescent : baseEnd_171756 < baseStart_171756 := by decide
  rcases family_descends (prefixWord ++ tailWord_171756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171790 : List Nat := [4, 1, 1, 2, 1, 1, 5, 3, 3]
def baseStart_171790 : Nat := 118140960795 + 171790 * 2 ^ 59
def prefixEnd_171790 : Nat := 4983230072969 + 3 ^ 40 * 171790 * 2
def baseEnd_171790 : Nat := 39204818504883602015537

theorem tailTrace_171790 : CollatzResearch.WordTrace tailWord_171790 prefixEnd_171790 39204818504883602015537 := by
  unfold tailWord_171790
  simp only [CollatzResearch.WordTrace]
  refine ⟨783212005955205530160103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4177130698427762827520549 783212005955205530160103)
  ·
    refine ⟨1174818008932808295240155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 783212005955205530160103 1174818008932808295240155)
    ·
      refine ⟨1762227013399212442860233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1174818008932808295240155 1762227013399212442860233)
      ·
        refine ⟨1321670260049409332145175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1762227013399212442860233 1321670260049409332145175)
        ·
          refine ⟨1982505390074113998217763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1321670260049409332145175 1982505390074113998217763)
          ·
            refine ⟨2973758085111170997326645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1982505390074113998217763 2973758085111170997326645)
            ·
              refine ⟨278789820479172280999373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2973758085111170997326645 278789820479172280999373)
              ·
                refine ⟨104546182679689605374765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 278789820479172280999373 104546182679689605374765)
                ·
                  refine ⟨39204818504883602015537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104546182679689605374765 39204818504883602015537)
                  ·
                    rfl

theorem cell21_171790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 3, 3].length) (baseStart_171790 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_171790 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_171790 prefixEnd_171790 := by exact prefixLift 171790
  have htrace : WordTrace (prefixWord ++ tailWord_171790) baseStart_171790 baseEnd_171790 := by
    simpa [prefixWord, tailWord_171790, baseEnd_171790] using wordTrace_append hprefix tailTrace_171790
  have hstable : (prefixWord ++ tailWord_171790).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171790).length < 2 ^ (prefixWord ++ tailWord_171790).sum := by decide
  have hdescent : baseEnd_171790 < baseStart_171790 := by decide
  rcases family_descends (prefixWord ++ tailWord_171790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171849 : List Nat := [1, 2, 1, 1, 2, 4, 2, 5, 3]
def baseStart_171849 : Nat := 118140960795 + 171849 * 2 ^ 59
def prefixEnd_171849 : Nat := 4983230072969 + 3 ^ 40 * 171849 * 2
def baseEnd_171849 : Nat := 39218283108712610532083

theorem tailTrace_171849 : CollatzResearch.WordTrace tailWord_171849 prefixEnd_171849 39218283108712610532083 := by
  unfold tailWord_171849
  simp only [CollatzResearch.WordTrace]
  refine ⟨6267847954427897317678601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4178565302951931545119067 6267847954427897317678601)
  ·
    refine ⟨4700885965820922988258951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6267847954427897317678601 4700885965820922988258951)
    ·
      refine ⟨7051328948731384482388427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4700885965820922988258951 7051328948731384482388427)
      ·
        refine ⟨10576993423097076723582641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7051328948731384482388427 10576993423097076723582641)
        ·
          refine ⟨7932745067322807542686981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10576993423097076723582641 7932745067322807542686981)
          ·
            refine ⟨1487389700123026414253809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7932745067322807542686981 1487389700123026414253809)
            ·
              refine ⟨1115542275092269810690357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1487389700123026414253809 1115542275092269810690357)
              ·
                refine ⟨104582088289900294752221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1115542275092269810690357 104582088289900294752221)
                ·
                  refine ⟨39218283108712610532083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104582088289900294752221 39218283108712610532083)
                  ·
                    rfl

theorem cell21_171849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 5, 3].length) (baseStart_171849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_171849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_171849 prefixEnd_171849 := by exact prefixLift 171849
  have htrace : WordTrace (prefixWord ++ tailWord_171849) baseStart_171849 baseEnd_171849 := by
    simpa [prefixWord, tailWord_171849, baseEnd_171849] using wordTrace_append hprefix tailTrace_171849
  have hstable : (prefixWord ++ tailWord_171849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171849).length < 2 ^ (prefixWord ++ tailWord_171849).sum := by decide
  have hdescent : baseEnd_171849 < baseStart_171849 := by decide
  rcases family_descends (prefixWord ++ tailWord_171849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171914 : List Nat := [3, 1, 2, 4, 3, 1, 1, 2, 4]
def baseStart_171914 : Nat := 118140960795 + 171914 * 2 ^ 59
def prefixEnd_171914 : Nat := 4983230072969 + 3 ^ 40 * 171914 * 2
def baseEnd_171914 : Nat := 39233116994286941948617

theorem tailTrace_171914 : CollatzResearch.WordTrace tailWord_171914 prefixEnd_171914 39233116994286941948617 := by
  unfold tailWord_171914
  simp only [CollatzResearch.WordTrace]
  refine ⟨1567554674798103354698699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4180145799461608945863197 1567554674798103354698699)
  ·
    refine ⟨2351332012197155032048049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1567554674798103354698699 2351332012197155032048049)
    ·
      refine ⟨1763499009147866274036037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2351332012197155032048049 1763499009147866274036037)
      ·
        refine ⟨330656064215224926381757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1763499009147866274036037 330656064215224926381757)
        ·
          refine ⟨123996024080709347393159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 330656064215224926381757 123996024080709347393159)
          ·
            refine ⟨185994036121064021089739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123996024080709347393159 185994036121064021089739)
            ·
              refine ⟨278991054181596031634609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185994036121064021089739 278991054181596031634609)
              ·
                refine ⟨209243290636197023725957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 278991054181596031634609 209243290636197023725957)
                ·
                  refine ⟨39233116994286941948617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 209243290636197023725957 39233116994286941948617)
                  ·
                    rfl

theorem cell21_171914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 2, 4].length) (baseStart_171914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_171914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_171914 prefixEnd_171914 := by exact prefixLift 171914
  have htrace : WordTrace (prefixWord ++ tailWord_171914) baseStart_171914 baseEnd_171914 := by
    simpa [prefixWord, tailWord_171914, baseEnd_171914] using wordTrace_append hprefix tailTrace_171914
  have hstable : (prefixWord ++ tailWord_171914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171914).length < 2 ^ (prefixWord ++ tailWord_171914).sum := by decide
  have hdescent : baseEnd_171914 < baseStart_171914 := by decide
  rcases family_descends (prefixWord ++ tailWord_171914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171925 : List Nat := [1, 3, 2, 1, 1, 3, 1, 6, 3]
def baseStart_171925 : Nat := 118140960795 + 171925 * 2 ^ 59
def prefixEnd_171925 : Nat := 4983230072969 + 3 ^ 40 * 171925 * 2
def baseEnd_171925 : Nat := 39235627344153367265261

theorem tailTrace_171925 : CollatzResearch.WordTrace tailWord_171925 prefixEnd_171925 39235627344153367265261 := by
  unfold tailWord_171925
  simp only [CollatzResearch.WordTrace]
  refine ⟨6270619902152562297445229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4180413268101708198296819 6270619902152562297445229)
  ·
    refine ⟨2351482463307210861541961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6270619902152562297445229 2351482463307210861541961)
    ·
      refine ⟨1763611847480408146156471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2351482463307210861541961 1763611847480408146156471)
      ·
        refine ⟨2645417771220612219234707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1763611847480408146156471 2645417771220612219234707)
        ·
          refine ⟨3968126656830918328852061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2645417771220612219234707 3968126656830918328852061)
          ·
            refine ⟨1488047496311594373319523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3968126656830918328852061 1488047496311594373319523)
            ·
              refine ⟨2232071244467391559979285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1488047496311594373319523 2232071244467391559979285)
              ·
                refine ⟨104628339584408979374029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2232071244467391559979285 104628339584408979374029)
                ·
                  refine ⟨39235627344153367265261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104628339584408979374029 39235627344153367265261)
                  ·
                    rfl

theorem cell21_171925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 6, 3].length) (baseStart_171925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_171925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_171925 prefixEnd_171925 := by exact prefixLift 171925
  have htrace : WordTrace (prefixWord ++ tailWord_171925) baseStart_171925 baseEnd_171925 := by
    simpa [prefixWord, tailWord_171925, baseEnd_171925] using wordTrace_append hprefix tailTrace_171925
  have hstable : (prefixWord ++ tailWord_171925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171925).length < 2 ^ (prefixWord ++ tailWord_171925).sum := by decide
  have hdescent : baseEnd_171925 < baseStart_171925 := by decide
  rcases family_descends (prefixWord ++ tailWord_171925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171984 : List Nat := [2, 1, 1, 1, 1, 2, 7, 1, 5]
def baseStart_171984 : Nat := 118140960795 + 171984 * 2 ^ 59
def prefixEnd_171984 : Nat := 4983230072969 + 3 ^ 40 * 171984 * 2
def baseEnd_171984 : Nat := 39249091947982375781807

theorem tailTrace_171984 : CollatzResearch.WordTrace tailWord_171984 prefixEnd_171984 39249091947982375781807 := by
  unfold tailWord_171984
  simp only [CollatzResearch.WordTrace]
  refine ⟨3136385904469407686921503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4181847872625876915895337 3136385904469407686921503)
  ·
    refine ⟨4704578856704111530382255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3136385904469407686921503 4704578856704111530382255)
    ·
      refine ⟨7056868285056167295573383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4704578856704111530382255 7056868285056167295573383)
      ·
        refine ⟨10585302427584250943360075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7056868285056167295573383 10585302427584250943360075)
        ·
          refine ⟨15877953641376376415040113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10585302427584250943360075 15877953641376376415040113)
          ·
            refine ⟨11908465231032282311280085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15877953641376376415040113 11908465231032282311280085)
            ·
              refine ⟨279104653852319116670627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 11908465231032282311280085 279104653852319116670627)
              ·
                refine ⟨418656980778478675005941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 279104653852319116670627 418656980778478675005941)
                ·
                  refine ⟨39249091947982375781807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 418656980778478675005941 39249091947982375781807)
                  ·
                    rfl

theorem cell21_171984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 5].length) (baseStart_171984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_171984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_171984 prefixEnd_171984 := by exact prefixLift 171984
  have htrace : WordTrace (prefixWord ++ tailWord_171984) baseStart_171984 baseEnd_171984 := by
    simpa [prefixWord, tailWord_171984, baseEnd_171984] using wordTrace_append hprefix tailTrace_171984
  have hstable : (prefixWord ++ tailWord_171984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171984).length < 2 ^ (prefixWord ++ tailWord_171984).sum := by decide
  have hdescent : baseEnd_171984 < baseStart_171984 := by decide
  rcases family_descends (prefixWord ++ tailWord_171984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172038 : List Nat := [6, 2, 1, 2, 1, 2, 1, 6]
def baseStart_172038 : Nat := 118140960795 + 172038 * 2 ^ 59
def prefixEnd_172038 : Nat := 4983230072969 + 3 ^ 40 * 172038 * 2
def baseEnd_172038 : Nat := 13087138494563427293899

theorem tailTrace_172038 : CollatzResearch.WordTrace tailWord_172038 prefixEnd_172038 13087138494563427293899 := by
  unfold tailWord_172038
  simp only [CollatzResearch.WordTrace]
  refine ⟨196085667210724456134649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4183160900495455064205845 196085667210724456134649)
  ·
    refine ⟨147064250408043342100987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196085667210724456134649 147064250408043342100987)
    ·
      refine ⟨220596375612065013151481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147064250408043342100987 220596375612065013151481)
      ·
        refine ⟨165447281709048759863611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220596375612065013151481 165447281709048759863611)
        ·
          refine ⟨248170922563573139795417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165447281709048759863611 248170922563573139795417)
          ·
            refine ⟨186128191922679854846563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248170922563573139795417 186128191922679854846563)
            ·
              refine ⟨279192287884019782269845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186128191922679854846563 279192287884019782269845)
              ·
                refine ⟨13087138494563427293899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 279192287884019782269845 13087138494563427293899)
                ·
                  rfl

theorem cell21_172038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_172038 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_172038 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_172038 prefixEnd_172038 := by exact prefixLift 172038
  have htrace : WordTrace (prefixWord ++ tailWord_172038) baseStart_172038 baseEnd_172038 := by
    simpa [prefixWord, tailWord_172038, baseEnd_172038] using wordTrace_append hprefix tailTrace_172038
  have hstable : (prefixWord ++ tailWord_172038).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172038).length < 2 ^ (prefixWord ++ tailWord_172038).sum := by decide
  have hdescent : baseEnd_172038 < baseStart_172038 := by decide
  rcases family_descends (prefixWord ++ tailWord_172038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172060 : List Nat := [2, 2, 3, 1, 3, 1, 1, 1, 7]
def baseStart_172060 : Nat := 118140960795 + 172060 * 2 ^ 59
def prefixEnd_172060 : Nat := 4983230072969 + 3 ^ 40 * 172060 * 2
def baseEnd_172060 : Nat := 39266436183423132514985

theorem tailTrace_172060 : CollatzResearch.WordTrace tailWord_172060 prefixEnd_172060 39266436183423132514985 := by
  unfold tailWord_172060
  simp only [CollatzResearch.WordTrace]
  refine ⟨3137771878331740176804817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4183695837775653569073089 3137771878331740176804817)
  ·
    refine ⟨2353328908748805132603613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3137771878331740176804817 2353328908748805132603613)
    ·
      refine ⟨882498340780801924726355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2353328908748805132603613 882498340780801924726355)
      ·
        refine ⟨1323747511171202887089533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 882498340780801924726355 1323747511171202887089533)
        ·
          refine ⟨496405316689201082658575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1323747511171202887089533 496405316689201082658575)
          ·
            refine ⟨744607975033801623987863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496405316689201082658575 744607975033801623987863)
            ·
              refine ⟨1116911962550702435981795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 744607975033801623987863 1116911962550702435981795)
              ·
                refine ⟨1675367943826053653972693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1116911962550702435981795 1675367943826053653972693)
                ·
                  refine ⟨39266436183423132514985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1675367943826053653972693 39266436183423132514985)
                  ·
                    rfl

theorem cell21_172060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_172060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_172060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_172060 prefixEnd_172060 := by exact prefixLift 172060
  have htrace : WordTrace (prefixWord ++ tailWord_172060) baseStart_172060 baseEnd_172060 := by
    simpa [prefixWord, tailWord_172060, baseEnd_172060] using wordTrace_append hprefix tailTrace_172060
  have hstable : (prefixWord ++ tailWord_172060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172060).length < 2 ^ (prefixWord ++ tailWord_172060).sum := by decide
  have hdescent : baseEnd_172060 < baseStart_172060 := by decide
  rcases family_descends (prefixWord ++ tailWord_172060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172094 : List Nat := [4, 2, 1, 3, 2, 1, 2, 1, 5]
def baseStart_172094 : Nat := 118140960795 + 172094 * 2 ^ 59
def prefixEnd_172094 : Nat := 4983230072969 + 3 ^ 40 * 172094 * 2
def baseEnd_172094 : Nat := 39274195446646628948249

theorem tailTrace_172094 : CollatzResearch.WordTrace tailWord_172094 prefixEnd_172094 39274195446646628948249 := by
  unfold tailWord_172094
  simp only [CollatzResearch.WordTrace]
  refine ⟨784597979817538020043417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4184522559026869440231557 784597979817538020043417)
  ·
    refine ⟨588448484863153515032563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 784597979817538020043417 588448484863153515032563)
    ·
      refine ⟨882672727294730272548845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 588448484863153515032563 882672727294730272548845)
      ·
        refine ⟨331002272735523852205817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 882672727294730272548845 331002272735523852205817)
        ·
          refine ⟨248251704551642889154363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 331002272735523852205817 248251704551642889154363)
          ·
            refine ⟨372377556827464333731545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248251704551642889154363 372377556827464333731545)
            ·
              refine ⟨279283167620598250298659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 372377556827464333731545 279283167620598250298659)
              ·
                refine ⟨418924751430897375447989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 279283167620598250298659 418924751430897375447989)
                ·
                  refine ⟨39274195446646628948249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 418924751430897375447989 39274195446646628948249)
                  ·
                    rfl

theorem cell21_172094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_172094 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_172094 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_172094 prefixEnd_172094 := by exact prefixLift 172094
  have htrace : WordTrace (prefixWord ++ tailWord_172094) baseStart_172094 baseEnd_172094 := by
    simpa [prefixWord, tailWord_172094, baseEnd_172094] using wordTrace_append hprefix tailTrace_172094
  have hstable : (prefixWord ++ tailWord_172094).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172094).length < 2 ^ (prefixWord ++ tailWord_172094).sum := by decide
  have hdescent : baseEnd_172094 < baseStart_172094 := by decide
  rcases family_descends (prefixWord ++ tailWord_172094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172153 : List Nat := [1, 2, 1, 3, 4, 3, 1, 1, 5]
def baseStart_172153 : Nat := 118140960795 + 172153 * 2 ^ 59
def prefixEnd_172153 : Nat := 4983230072969 + 3 ^ 40 * 172153 * 2
def baseEnd_172153 : Nat := 39287660050475637464795

theorem tailTrace_172153 : CollatzResearch.WordTrace tailWord_172153 prefixEnd_172153 39287660050475637464795 := by
  unfold tailWord_172153
  simp only [CollatzResearch.WordTrace]
  refine ⟨6278935745326557236745113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4185957163551038157830075 6278935745326557236745113)
  ·
    refine ⟨4709201808994917927558835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6278935745326557236745113 4709201808994917927558835)
    ·
      refine ⟨7063802713492376891338253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4709201808994917927558835 7063802713492376891338253)
      ·
        refine ⟨2648926017559641334251845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7063802713492376891338253 2648926017559641334251845)
        ·
          refine ⟨496673628292432750172221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2648926017559641334251845 496673628292432750172221)
          ·
            refine ⟨186252610609662281314583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 496673628292432750172221 186252610609662281314583)
            ·
              refine ⟨279378915914493421971875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186252610609662281314583 279378915914493421971875)
              ·
                refine ⟨419068373871740132957813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 279378915914493421971875 419068373871740132957813)
                ·
                  refine ⟨39287660050475637464795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 419068373871740132957813 39287660050475637464795)
                  ·
                    rfl

theorem cell21_172153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 5].length) (baseStart_172153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_172153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_172153 prefixEnd_172153 := by exact prefixLift 172153
  have htrace : WordTrace (prefixWord ++ tailWord_172153) baseStart_172153 baseEnd_172153 := by
    simpa [prefixWord, tailWord_172153, baseEnd_172153] using wordTrace_append hprefix tailTrace_172153
  have hstable : (prefixWord ++ tailWord_172153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172153).length < 2 ^ (prefixWord ++ tailWord_172153).sum := by decide
  have hdescent : baseEnd_172153 < baseStart_172153 := by decide
  rcases family_descends (prefixWord ++ tailWord_172153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172302 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 8]
def baseStart_172302 : Nat := 118140960795 + 172302 * 2 ^ 59
def prefixEnd_172302 : Nat := 4983230072969 + 3 ^ 40 * 172302 * 2
def baseEnd_172302 : Nat := 39321663880484489481157

theorem tailTrace_172302 : CollatzResearch.WordTrace tailWord_172302 prefixEnd_172302 39321663880484489481157 := by
  unfold tailWord_172302
  simp only [CollatzResearch.WordTrace]
  refine ⟨785546277723344460489895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4189580147857837122612773 785546277723344460489895)
  ·
    refine ⟨1178319416585016690734843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 785546277723344460489895 1178319416585016690734843)
    ·
      refine ⟨1767479124877525036102265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1178319416585016690734843 1767479124877525036102265)
      ·
        refine ⟨1325609343658143777076699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1767479124877525036102265 1325609343658143777076699)
        ·
          refine ⟨1988414015487215665615049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1325609343658143777076699 1988414015487215665615049)
          ·
            refine ⟨1491310511615411749211287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1988414015487215665615049 1491310511615411749211287)
            ·
              refine ⟨2236965767423117623816931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1491310511615411749211287 2236965767423117623816931)
              ·
                refine ⟨3355448651134676435725397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2236965767423117623816931 3355448651134676435725397)
                ·
                  refine ⟨39321663880484489481157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3355448651134676435725397 39321663880484489481157)
                  ·
                    rfl

theorem cell21_172302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_172302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_172302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_172302 prefixEnd_172302 := by exact prefixLift 172302
  have htrace : WordTrace (prefixWord ++ tailWord_172302) baseStart_172302 baseEnd_172302 := by
    simpa [prefixWord, tailWord_172302, baseEnd_172302] using wordTrace_append hprefix tailTrace_172302
  have hstable : (prefixWord ++ tailWord_172302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172302).length < 2 ^ (prefixWord ++ tailWord_172302).sum := by decide
  have hdescent : baseEnd_172302 < baseStart_172302 := by decide
  rcases family_descends (prefixWord ++ tailWord_172302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172305 : List Nat := [1, 2, 2, 1, 1, 5, 3, 3, 3]
def baseStart_172305 : Nat := 118140960795 + 172305 * 2 ^ 59
def prefixEnd_172305 : Nat := 4983230072969 + 3 ^ 40 * 172305 * 2
def baseEnd_172305 : Nat := 39322348521357150931151

theorem tailTrace_172305 : CollatzResearch.WordTrace tailWord_172305 prefixEnd_172305 39322348521357150931151 := by
  unfold tailWord_172305
  simp only [CollatzResearch.WordTrace]
  refine ⟨6284479640775887196278369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4189653093850591464185579 6284479640775887196278369)
  ·
    refine ⟨4713359730581915397208777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6284479640775887196278369 4713359730581915397208777)
    ·
      refine ⟨3535019797936436547906583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4713359730581915397208777 3535019797936436547906583)
      ·
        refine ⟨5302529696904654821859875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3535019797936436547906583 5302529696904654821859875)
        ·
          refine ⟨7953794545356982232789813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5302529696904654821859875 7953794545356982232789813)
          ·
            refine ⟨745668238627217084324045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7953794545356982232789813 745668238627217084324045)
            ·
              refine ⟨279625589485206406621517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 745668238627217084324045 279625589485206406621517)
              ·
                refine ⟨104859596056952402483069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 279625589485206406621517 104859596056952402483069)
                ·
                  refine ⟨39322348521357150931151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104859596056952402483069 39322348521357150931151)
                  ·
                    rfl

theorem cell21_172305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 3, 3].length) (baseStart_172305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_172305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_172305 prefixEnd_172305 := by exact prefixLift 172305
  have htrace : WordTrace (prefixWord ++ tailWord_172305) baseStart_172305 baseEnd_172305 := by
    simpa [prefixWord, tailWord_172305, baseEnd_172305] using wordTrace_append hprefix tailTrace_172305
  have hstable : (prefixWord ++ tailWord_172305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172305).length < 2 ^ (prefixWord ++ tailWord_172305).sum := by decide
  have hdescent : baseEnd_172305 < baseStart_172305 := by decide
  rcases family_descends (prefixWord ++ tailWord_172305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172423 : List Nat := [1, 1, 4, 2, 2, 1, 1, 2, 7]
def baseStart_172423 : Nat := 118140960795 + 172423 * 2 ^ 59
def prefixEnd_172423 : Nat := 4983230072969 + 3 ^ 40 * 172423 * 2
def baseEnd_172423 : Nat := 39349277729015167964243

theorem tailTrace_172423 : CollatzResearch.WordTrace tailWord_172423 prefixEnd_172423 39349277729015167964243 := by
  unfold tailWord_172423
  simp only [CollatzResearch.WordTrace]
  refine ⟨6288783454348393349073923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4192522302898928899382615 6288783454348393349073923)
  ·
    refine ⟨9433175181522590023610885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6288783454348393349073923 9433175181522590023610885)
    ·
      refine ⟨1768720346535485629427041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9433175181522590023610885 1768720346535485629427041)
      ·
        refine ⟨1326540259901614222070281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1768720346535485629427041 1326540259901614222070281)
        ·
          refine ⟨994905194926210666552711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1326540259901614222070281 994905194926210666552711)
          ·
            refine ⟨1492357792389315999829067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 994905194926210666552711 1492357792389315999829067)
            ·
              refine ⟨2238536688583973999743601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1492357792389315999829067 2238536688583973999743601)
              ·
                refine ⟨1678902516437980499807701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2238536688583973999743601 1678902516437980499807701)
                ·
                  refine ⟨39349277729015167964243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1678902516437980499807701 39349277729015167964243)
                  ·
                    rfl

theorem cell21_172423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 7].length) (baseStart_172423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_172423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_172423 prefixEnd_172423 := by exact prefixLift 172423
  have htrace : WordTrace (prefixWord ++ tailWord_172423) baseStart_172423 baseEnd_172423 := by
    simpa [prefixWord, tailWord_172423, baseEnd_172423] using wordTrace_append hprefix tailTrace_172423
  have hstable : (prefixWord ++ tailWord_172423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172423).length < 2 ^ (prefixWord ++ tailWord_172423).sum := by decide
  have hdescent : baseEnd_172423 < baseStart_172423 := by decide
  rcases family_descends (prefixWord ++ tailWord_172423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172426 : List Nat := [3, 1, 2, 5, 1, 1, 8]
def baseStart_172426 : Nat := 118140960795 + 172426 * 2 ^ 59
def prefixEnd_172426 : Nat := 4983230072969 + 3 ^ 40 * 172426 * 2
def baseEnd_172426 : Nat := 4372218041098647712693

theorem tailTrace_172426 : CollatzResearch.WordTrace tailWord_172426 prefixEnd_172426 4372218041098647712693 := by
  unfold tailWord_172426
  simp only [CollatzResearch.WordTrace]
  refine ⟨1572223218334381215358283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4192595248891683240955421 1572223218334381215358283)
  ·
    refine ⟨2358334827501571823037425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1572223218334381215358283 2358334827501571823037425)
    ·
      refine ⟨1768751120626178867278069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2358334827501571823037425 1768751120626178867278069)
      ·
        refine ⟨165820417558704268807319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1768751120626178867278069 165820417558704268807319)
        ·
          refine ⟨248730626338056403210979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165820417558704268807319 248730626338056403210979)
          ·
            refine ⟨373095939507084604816469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248730626338056403210979 373095939507084604816469)
            ·
              refine ⟨4372218041098647712693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 373095939507084604816469 4372218041098647712693)
              ·
                rfl

theorem cell21_172426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 8].length) (baseStart_172426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_172426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_172426 prefixEnd_172426 := by exact prefixLift 172426
  have htrace : WordTrace (prefixWord ++ tailWord_172426) baseStart_172426 baseEnd_172426 := by
    simpa [prefixWord, tailWord_172426, baseEnd_172426] using wordTrace_append hprefix tailTrace_172426
  have hstable : (prefixWord ++ tailWord_172426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172426).length < 2 ^ (prefixWord ++ tailWord_172426).sum := by decide
  have hdescent : baseEnd_172426 < baseStart_172426 := by decide
  rcases family_descends (prefixWord ++ tailWord_172426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172440 : List Nat := [2, 1, 2, 5, 1, 1, 1, 3, 5]
def baseStart_172440 : Nat := 118140960795 + 172440 * 2 ^ 59
def prefixEnd_172440 : Nat := 4983230072969 + 3 ^ 40 * 172440 * 2
def baseEnd_172440 : Nat := 39353157360626916180875

theorem tailTrace_172440 : CollatzResearch.WordTrace tailWord_172440 prefixEnd_172440 39353157360626916180875 := by
  unfold tailWord_172440
  simp only [CollatzResearch.WordTrace]
  refine ⟨3144701747643402626221387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4192935663524536834961849 3144701747643402626221387)
  ·
    refine ⟨4717052621465103939332081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3144701747643402626221387 4717052621465103939332081)
    ·
      refine ⟨3537789466098827954499061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4717052621465103939332081 3537789466098827954499061)
      ·
        refine ⟨331667762446765120734287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3537789466098827954499061 331667762446765120734287)
        ·
          refine ⟨497501643670147681101431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331667762446765120734287 497501643670147681101431)
          ·
            refine ⟨746252465505221521652147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 497501643670147681101431 746252465505221521652147)
            ·
              refine ⟨1119378698257832282478221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 746252465505221521652147 1119378698257832282478221)
              ·
                refine ⟨419767011846687105929333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1119378698257832282478221 419767011846687105929333)
                ·
                  refine ⟨39353157360626916180875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 419767011846687105929333 39353157360626916180875)
                  ·
                    rfl

theorem cell21_172440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 5].length) (baseStart_172440 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_172440 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_172440 prefixEnd_172440 := by exact prefixLift 172440
  have htrace : WordTrace (prefixWord ++ tailWord_172440) baseStart_172440 baseEnd_172440 := by
    simpa [prefixWord, tailWord_172440, baseEnd_172440] using wordTrace_append hprefix tailTrace_172440
  have hstable : (prefixWord ++ tailWord_172440).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172440).length < 2 ^ (prefixWord ++ tailWord_172440).sum := by decide
  have hdescent : baseEnd_172440 < baseStart_172440 := by decide
  rcases family_descends (prefixWord ++ tailWord_172440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172502 : List Nat := [5, 2, 1, 1, 1, 1, 4, 6]
def baseStart_172502 : Nat := 118140960795 + 172502 * 2 ^ 59
def prefixEnd_172502 : Nat := 4983230072969 + 3 ^ 40 * 172502 * 2
def baseEnd_172502 : Nat := 13122435535109528715805

theorem tailTrace_172502 : CollatzResearch.WordTrace tailWord_172502 prefixEnd_172502 13122435535109528715805 := by
  unfold tailWord_172502
  simp only [CollatzResearch.WordTrace]
  refine ⟨393229051316386865074985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4194443214041459894133173 393229051316386865074985)
  ·
    refine ⟨294921788487290148806239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 393229051316386865074985 294921788487290148806239)
    ·
      refine ⟨442382682730935223209359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294921788487290148806239 442382682730935223209359)
      ·
        refine ⟨663574024096402834814039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 442382682730935223209359 663574024096402834814039)
        ·
          refine ⟨995361036144604252221059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 663574024096402834814039 995361036144604252221059)
          ·
            refine ⟨1493041554216906378331589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 995361036144604252221059 1493041554216906378331589)
            ·
              refine ⟨279945291415669945937173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1493041554216906378331589 279945291415669945937173)
              ·
                refine ⟨13122435535109528715805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 279945291415669945937173 13122435535109528715805)
                ·
                  rfl

theorem cell21_172502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_172502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_172502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_172502 prefixEnd_172502 := by exact prefixLift 172502
  have htrace : WordTrace (prefixWord ++ tailWord_172502) baseStart_172502 baseEnd_172502 := by
    simpa [prefixWord, tailWord_172502, baseEnd_172502] using wordTrace_append hprefix tailTrace_172502
  have hstable : (prefixWord ++ tailWord_172502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172502).length < 2 ^ (prefixWord ++ tailWord_172502).sum := by decide
  have hdescent : baseEnd_172502 < baseStart_172502 := by decide
  rcases family_descends (prefixWord ++ tailWord_172502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172564 : List Nat := [2, 4, 3, 1, 1, 1, 2, 3, 4]
def baseStart_172564 : Nat := 118140960795 + 172564 * 2 ^ 59
def prefixEnd_172564 : Nat := 4983230072969 + 3 ^ 40 * 172564 * 2
def baseEnd_172564 : Nat := 39381455850030256113955

theorem tailTrace_172564 : CollatzResearch.WordTrace tailWord_172564 prefixEnd_172564 39381455850030256113955 := by
  unfold tailWord_172564
  simp only [CollatzResearch.WordTrace]
  refine ⟨3146963073418787214978373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4195950764558382953304497 3146963073418787214978373)
  ·
    refine ⟨590055576266022602808445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3146963073418787214978373 590055576266022602808445)
    ·
      refine ⟨221270841099758476053167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 590055576266022602808445 221270841099758476053167)
      ·
        refine ⟨331906261649637714079751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221270841099758476053167 331906261649637714079751)
        ·
          refine ⟨497859392474456571119627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331906261649637714079751 497859392474456571119627)
          ·
            refine ⟨746789088711684856679441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 497859392474456571119627 746789088711684856679441)
            ·
              refine ⟨560091816533763642509581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 746789088711684856679441 560091816533763642509581)
              ·
                refine ⟨210034431200161365941093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 560091816533763642509581 210034431200161365941093)
                ·
                  refine ⟨39381455850030256113955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 210034431200161365941093 39381455850030256113955)
                  ·
                    rfl

theorem cell21_172564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_172564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_172564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_172564 prefixEnd_172564 := by exact prefixLift 172564
  have htrace : WordTrace (prefixWord ++ tailWord_172564) baseStart_172564 baseEnd_172564 := by
    simpa [prefixWord, tailWord_172564, baseEnd_172564] using wordTrace_append hprefix tailTrace_172564
  have hstable : (prefixWord ++ tailWord_172564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172564).length < 2 ^ (prefixWord ++ tailWord_172564).sum := by decide
  have hdescent : baseEnd_172564 < baseStart_172564 := by decide
  rcases family_descends (prefixWord ++ tailWord_172564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172592 : List Nat := [2, 1, 1, 1, 2, 3, 3, 5, 3]
def baseStart_172592 : Nat := 118140960795 + 172592 * 2 ^ 59
def prefixEnd_172592 : Nat := 4983230072969 + 3 ^ 40 * 172592 * 2
def baseEnd_172592 : Nat := 39387845831508429647231

theorem tailTrace_172592 : CollatzResearch.WordTrace tailWord_172592 prefixEnd_172592 39387845831508429647231 := by
  unfold tailWord_172592
  simp only [CollatzResearch.WordTrace]
  refine ⟨3147473695368067605988015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4196631593824090141317353 3147473695368067605988015)
  ·
    refine ⟨4721210543052101408982023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3147473695368067605988015 4721210543052101408982023)
    ·
      refine ⟨7081815814578152113473035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4721210543052101408982023 7081815814578152113473035)
      ·
        refine ⟨10622723721867228170209553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7081815814578152113473035 10622723721867228170209553)
        ·
          refine ⟨7967042791400421127657165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10622723721867228170209553 7967042791400421127657165)
          ·
            refine ⟨2987641046775157922871437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7967042791400421127657165 2987641046775157922871437)
            ·
              refine ⟨1120365392540684221076789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2987641046775157922871437 1120365392540684221076789)
              ·
                refine ⟨105034255550689145725949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1120365392540684221076789 105034255550689145725949)
                ·
                  refine ⟨39387845831508429647231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105034255550689145725949 39387845831508429647231)
                  ·
                    rfl

theorem cell21_172592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 5, 3].length) (baseStart_172592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_172592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_172592 prefixEnd_172592 := by exact prefixLift 172592
  have htrace : WordTrace (prefixWord ++ tailWord_172592) baseStart_172592 baseEnd_172592 := by
    simpa [prefixWord, tailWord_172592, baseEnd_172592] using wordTrace_append hprefix tailTrace_172592
  have hstable : (prefixWord ++ tailWord_172592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172592).length < 2 ^ (prefixWord ++ tailWord_172592).sum := by decide
  have hdescent : baseEnd_172592 < baseStart_172592 := by decide
  rcases family_descends (prefixWord ++ tailWord_172592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172609 : List Nat := [1, 2, 5, 1, 1, 2, 2, 4, 3]
def baseStart_172609 : Nat := 118140960795 + 172609 * 2 ^ 59
def prefixEnd_172609 : Nat := 4983230072969 + 3 ^ 40 * 172609 * 2
def baseEnd_172609 : Nat := 39391725463120177863863

theorem tailTrace_172609 : CollatzResearch.WordTrace tailWord_172609 prefixEnd_172609 39391725463120177863863 := by
  unfold tailWord_172609
  simp only [CollatzResearch.WordTrace]
  refine ⟨6295567431674547115344881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4197044954449698076896587 6295567431674547115344881)
  ·
    refine ⟨4721675573755910336508661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6295567431674547115344881 4721675573755910336508661)
    ·
      refine ⟨442657085039616594047687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4721675573755910336508661 442657085039616594047687)
      ·
        refine ⟨663985627559424891071531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 442657085039616594047687 663985627559424891071531)
        ·
          refine ⟨995978441339137336607297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 663985627559424891071531 995978441339137336607297)
          ·
            refine ⟨746983831004353002455473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 995978441339137336607297 746983831004353002455473)
            ·
              refine ⟨560237873253264751841605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 746983831004353002455473 560237873253264751841605)
              ·
                refine ⟨105044601234987140970301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 560237873253264751841605 105044601234987140970301)
                ·
                  refine ⟨39391725463120177863863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105044601234987140970301 39391725463120177863863)
                  ·
                    rfl

theorem cell21_172609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 4, 3].length) (baseStart_172609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_172609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_172609 prefixEnd_172609 := by exact prefixLift 172609
  have htrace : WordTrace (prefixWord ++ tailWord_172609) baseStart_172609 baseEnd_172609 := by
    simpa [prefixWord, tailWord_172609, baseEnd_172609] using wordTrace_append hprefix tailTrace_172609
  have hstable : (prefixWord ++ tailWord_172609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172609).length < 2 ^ (prefixWord ++ tailWord_172609).sum := by decide
  have hdescent : baseEnd_172609 < baseStart_172609 := by decide
  rcases family_descends (prefixWord ++ tailWord_172609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172620 : List Nat := [2, 2, 1, 3, 1, 2, 2, 8]
def baseStart_172620 : Nat := 118140960795 + 172620 * 2 ^ 59
def prefixEnd_172620 : Nat := 4983230072969 + 3 ^ 40 * 172620 * 2
def baseEnd_172620 : Nat := 13131411937662201060169

theorem tailTrace_172620 : CollatzResearch.WordTrace tailWord_172620 prefixEnd_172620 13131411937662201060169 := by
  unfold tailWord_172620
  simp only [CollatzResearch.WordTrace]
  refine ⟨3147984317317347996997657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4197312423089797329330209 3147984317317347996997657)
  ·
    refine ⟨2360988237988010997748243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3147984317317347996997657 2360988237988010997748243)
    ·
      refine ⟨3541482356982016496622365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2360988237988010997748243 3541482356982016496622365)
      ·
        refine ⟨1328055883868256186233387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3541482356982016496622365 1328055883868256186233387)
        ·
          refine ⟨1992083825802384279350081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1328055883868256186233387 1992083825802384279350081)
          ·
            refine ⟨1494062869351788209512561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1992083825802384279350081 1494062869351788209512561)
            ·
              refine ⟨1120547152013841157134421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1494062869351788209512561 1120547152013841157134421)
              ·
                refine ⟨13131411937662201060169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1120547152013841157134421 13131411937662201060169)
                ·
                  rfl

theorem cell21_172620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 8].length) (baseStart_172620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_172620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_172620 prefixEnd_172620 := by exact prefixLift 172620
  have htrace : WordTrace (prefixWord ++ tailWord_172620) baseStart_172620 baseEnd_172620 := by
    simpa [prefixWord, tailWord_172620, baseEnd_172620] using wordTrace_append hprefix tailTrace_172620
  have hstable : (prefixWord ++ tailWord_172620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172620).length < 2 ^ (prefixWord ++ tailWord_172620).sum := by decide
  have hdescent : baseEnd_172620 < baseStart_172620 := by decide
  rcases family_descends (prefixWord ++ tailWord_172620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172668 : List Nat := [2, 2, 2, 1, 1, 2, 2, 6, 3]
def baseStart_172668 : Nat := 118140960795 + 172668 * 2 ^ 59
def prefixEnd_172668 : Nat := 4983230072969 + 3 ^ 40 * 172668 * 2
def baseEnd_172668 : Nat := 39405190066949186380409

theorem tailTrace_172668 : CollatzResearch.WordTrace tailWord_172668 prefixEnd_172668 39405190066949186380409 := by
  unfold tailWord_172668
  simp only [CollatzResearch.WordTrace]
  refine ⟨3148859669230400095871329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4198479558973866794495105 3148859669230400095871329)
  ·
    refine ⟨2361644751922800071903497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3148859669230400095871329 2361644751922800071903497)
    ·
      refine ⟨1771233563942100053927623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2361644751922800071903497 1771233563942100053927623)
      ·
        refine ⟨2656850345913150080891435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1771233563942100053927623 2656850345913150080891435)
        ·
          refine ⟨3985275518869725121337153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2656850345913150080891435 3985275518869725121337153)
          ·
            refine ⟨2988956639152293841002865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3985275518869725121337153 2988956639152293841002865)
            ·
              refine ⟨2241717479364220380752149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2988956639152293841002865 2241717479364220380752149)
              ·
                refine ⟨105080506845197830347757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2241717479364220380752149 105080506845197830347757)
                ·
                  refine ⟨39405190066949186380409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105080506845197830347757 39405190066949186380409)
                  ·
                    rfl

theorem cell21_172668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 6, 3].length) (baseStart_172668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_172668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_172668 prefixEnd_172668 := by exact prefixLift 172668
  have htrace : WordTrace (prefixWord ++ tailWord_172668) baseStart_172668 baseEnd_172668 := by
    simpa [prefixWord, tailWord_172668, baseEnd_172668] using wordTrace_append hprefix tailTrace_172668
  have hstable : (prefixWord ++ tailWord_172668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172668).length < 2 ^ (prefixWord ++ tailWord_172668).sum := by decide
  have hdescent : baseEnd_172668 < baseStart_172668 := by decide
  rcases family_descends (prefixWord ++ tailWord_172668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172674 : List Nat := [3, 4, 3, 1, 1, 1, 1, 3, 4]
def baseStart_172674 : Nat := 118140960795 + 172674 * 2 ^ 59
def prefixEnd_172674 : Nat := 4983230072969 + 3 ^ 40 * 172674 * 2
def baseEnd_172674 : Nat := 39406559348694509280397

theorem tailTrace_172674 : CollatzResearch.WordTrace tailWord_172674 prefixEnd_172674 39406559348694509280397 := by
  unfold tailWord_172674
  simp only [CollatzResearch.WordTrace]
  refine ⟨1574484544109765804115269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4198625450959375477640717 1574484544109765804115269)
  ·
    refine ⟨295215852020581088271613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1574484544109765804115269 295215852020581088271613)
    ·
      refine ⟨110705944507717908101855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 295215852020581088271613 110705944507717908101855)
      ·
        refine ⟨166058916761576862152783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110705944507717908101855 166058916761576862152783)
        ·
          refine ⟨249088375142365293229175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166058916761576862152783 249088375142365293229175)
          ·
            refine ⟨373632562713547939843763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249088375142365293229175 373632562713547939843763)
            ·
              refine ⟨560448844070321909765645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 373632562713547939843763 560448844070321909765645)
              ·
                refine ⟨210168316526370716162117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 560448844070321909765645 210168316526370716162117)
                ·
                  refine ⟨39406559348694509280397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 210168316526370716162117 39406559348694509280397)
                  ·
                    rfl

theorem cell21_172674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_172674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_172674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_172674 prefixEnd_172674 := by exact prefixLift 172674
  have htrace : WordTrace (prefixWord ++ tailWord_172674) baseStart_172674 baseEnd_172674 := by
    simpa [prefixWord, tailWord_172674, baseEnd_172674] using wordTrace_append hprefix tailTrace_172674
  have hstable : (prefixWord ++ tailWord_172674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172674).length < 2 ^ (prefixWord ++ tailWord_172674).sum := by decide
  have hdescent : baseEnd_172674 < baseStart_172674 := by decide
  rcases family_descends (prefixWord ++ tailWord_172674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172696 : List Nat := [2, 1, 2, 4, 1, 1, 1, 9]
def baseStart_172696 : Nat := 118140960795 + 172696 * 2 ^ 59
def prefixEnd_172696 : Nat := 4983230072969 + 3 ^ 40 * 172696 * 2
def baseEnd_172696 : Nat := 13137193349475786637895

theorem tailTrace_172696 : CollatzResearch.WordTrace tailWord_172696 prefixEnd_172696 13137193349475786637895 := by
  unfold tailWord_172696
  simp only [CollatzResearch.WordTrace]
  refine ⟨3149370291179680486880971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4199160388239573982507961 3149370291179680486880971)
  ·
    refine ⟨4724055436769520730321457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3149370291179680486880971 4724055436769520730321457)
    ·
      refine ⟨3543041577577140547741093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4724055436769520730321457 3543041577577140547741093)
      ·
        refine ⟨664320295795713852701455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3543041577577140547741093 664320295795713852701455)
        ·
          refine ⟨996480443693570779052183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 664320295795713852701455 996480443693570779052183)
          ·
            refine ⟨1494720665540356168578275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 996480443693570779052183 1494720665540356168578275)
            ·
              refine ⟨2242080998310534252867413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1494720665540356168578275 2242080998310534252867413)
              ·
                refine ⟨13137193349475786637895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2242080998310534252867413 13137193349475786637895)
                ·
                  rfl

theorem cell21_172696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 9].length) (baseStart_172696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_172696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_172696 prefixEnd_172696 := by exact prefixLift 172696
  have htrace : WordTrace (prefixWord ++ tailWord_172696) baseStart_172696 baseEnd_172696 := by
    simpa [prefixWord, tailWord_172696, baseEnd_172696] using wordTrace_append hprefix tailTrace_172696
  have hstable : (prefixWord ++ tailWord_172696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172696).length < 2 ^ (prefixWord ++ tailWord_172696).sum := by decide
  have hdescent : baseEnd_172696 < baseStart_172696 := by decide
  rcases family_descends (prefixWord ++ tailWord_172696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172772 : List Nat := [2, 3, 1, 1, 1, 5, 8]
def baseStart_172772 : Nat := 118140960795 + 172772 * 2 ^ 59
def prefixEnd_172772 : Nat := 4983230072969 + 3 ^ 40 * 172772 * 2
def baseEnd_172772 : Nat := 4380991587096457405207

theorem tailTrace_172772 : CollatzResearch.WordTrace tailWord_172772 prefixEnd_172772 4380991587096457405207 := by
  unfold tailWord_172772
  simp only [CollatzResearch.WordTrace]
  refine ⟨3150756265042012976764285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4201008353389350635685713 3150756265042012976764285)
  ·
    refine ⟨1181533599390754866286607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3150756265042012976764285 1181533599390754866286607)
    ·
      refine ⟨1772300399086132299429911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1181533599390754866286607 1772300399086132299429911)
      ·
        refine ⟨2658450598629198449144867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1772300399086132299429911 2658450598629198449144867)
        ·
          refine ⟨3987675897943797673717301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2658450598629198449144867 3987675897943797673717301)
          ·
            refine ⟨373844615432231031910997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3987675897943797673717301 373844615432231031910997)
            ·
              refine ⟨4380991587096457405207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 373844615432231031910997 4380991587096457405207)
              ·
                rfl

theorem cell21_172772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 8].length) (baseStart_172772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_172772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_172772 prefixEnd_172772 := by exact prefixLift 172772
  have htrace : WordTrace (prefixWord ++ tailWord_172772) baseStart_172772 baseEnd_172772 := by
    simpa [prefixWord, tailWord_172772, baseEnd_172772] using wordTrace_append hprefix tailTrace_172772
  have hstable : (prefixWord ++ tailWord_172772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172772).length < 2 ^ (prefixWord ++ tailWord_172772).sum := by decide
  have hdescent : baseEnd_172772 < baseStart_172772 := by decide
  rcases family_descends (prefixWord ++ tailWord_172772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172817 : List Nat := [1, 2, 2, 1, 1, 3, 3, 2, 6]
def baseStart_172817 : Nat := 118140960795 + 172817 * 2 ^ 59
def prefixEnd_172817 : Nat := 4983230072969 + 3 ^ 40 * 172817 * 2
def baseEnd_172817 : Nat := 39439193896958038396771

theorem tailTrace_172817 : CollatzResearch.WordTrace tailWord_172817 prefixEnd_172817 39439193896958038396771 := by
  unfold tailWord_172817
  simp only [CollatzResearch.WordTrace]
  refine ⟨6303153814920998638916705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4202102543280665759277803 6303153814920998638916705)
  ·
    refine ⟨4727365361190748979187529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6303153814920998638916705 4727365361190748979187529)
    ·
      refine ⟨3545524020893061734390647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4727365361190748979187529 3545524020893061734390647)
      ·
        refine ⟨5318286031339592601585971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3545524020893061734390647 5318286031339592601585971)
        ·
          refine ⟨7977429047009388902378957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5318286031339592601585971 7977429047009388902378957)
          ·
            refine ⟨2991535892628520838392109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7977429047009388902378957 2991535892628520838392109)
            ·
              refine ⟨1121825959735695314397041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2991535892628520838392109 1121825959735695314397041)
              ·
                refine ⟨841369469801771485797781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1121825959735695314397041 841369469801771485797781)
                ·
                  refine ⟨39439193896958038396771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 841369469801771485797781 39439193896958038396771)
                  ·
                    rfl

theorem cell21_172817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 6].length) (baseStart_172817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_172817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_172817 prefixEnd_172817 := by exact prefixLift 172817
  have htrace : WordTrace (prefixWord ++ tailWord_172817) baseStart_172817 baseEnd_172817 := by
    simpa [prefixWord, tailWord_172817, baseEnd_172817] using wordTrace_append hprefix tailTrace_172817
  have hstable : (prefixWord ++ tailWord_172817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172817).length < 2 ^ (prefixWord ++ tailWord_172817).sum := by decide
  have hdescent : baseEnd_172817 < baseStart_172817 := by decide
  rcases family_descends (prefixWord ++ tailWord_172817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172834 : List Nat := [3, 3, 1, 1, 2, 2, 2, 1, 6]
def baseStart_172834 : Nat := 118140960795 + 172834 * 2 ^ 59
def prefixEnd_172834 : Nat := 4983230072969 + 3 ^ 40 * 172834 * 2
def baseEnd_172834 : Nat := 39443073528569786613403

theorem tailTrace_172834 : CollatzResearch.WordTrace tailWord_172834 prefixEnd_172834 39443073528569786613403 := by
  unfold tailWord_172834
  simp only [CollatzResearch.WordTrace]
  refine ⟨1575943463964852635571389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4202515903906273694857037 1575943463964852635571389)
  ·
    refine ⟨590978798986819738339271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1575943463964852635571389 590978798986819738339271)
    ·
      refine ⟨886468198480229607508907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 590978798986819738339271 886468198480229607508907)
      ·
        refine ⟨1329702297720344411263361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 886468198480229607508907 1329702297720344411263361)
        ·
          refine ⟨997276723290258308447521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1329702297720344411263361 997276723290258308447521)
          ·
            refine ⟨747957542467693731335641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 997276723290258308447521 747957542467693731335641)
            ·
              refine ⟨560968156850770298501731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 747957542467693731335641 560968156850770298501731)
              ·
                refine ⟨841452235276155447752597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 560968156850770298501731 841452235276155447752597)
                ·
                  refine ⟨39443073528569786613403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 841452235276155447752597 39443073528569786613403)
                  ·
                    rfl

theorem cell21_172834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_172834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_172834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_172834 prefixEnd_172834 := by exact prefixLift 172834
  have htrace : WordTrace (prefixWord ++ tailWord_172834) baseStart_172834 baseEnd_172834 := by
    simpa [prefixWord, tailWord_172834, baseEnd_172834] using wordTrace_append hprefix tailTrace_172834
  have hstable : (prefixWord ++ tailWord_172834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172834).length < 2 ^ (prefixWord ++ tailWord_172834).sum := by decide
  have hdescent : baseEnd_172834 < baseStart_172834 := by decide
  rcases family_descends (prefixWord ++ tailWord_172834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172837 : List Nat := [1, 3, 1, 2, 3, 1, 5, 2, 3]
def baseStart_172837 : Nat := 118140960795 + 172837 * 2 ^ 59
def prefixEnd_172837 : Nat := 4983230072969 + 3 ^ 40 * 172837 * 2
def baseEnd_172837 : Nat := 39443758169442448063397

theorem tailTrace_172837 : CollatzResearch.WordTrace tailWord_172837 prefixEnd_172837 39443758169442448063397 := by
  unfold tailWord_172837
  simp only [CollatzResearch.WordTrace]
  refine ⟨6303883274848542054644765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4202588849899028036429843 6303883274848542054644765)
  ·
    refine ⟨2363956228068203270491787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6303883274848542054644765 2363956228068203270491787)
    ·
      refine ⟨3545934342102304905737681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2363956228068203270491787 3545934342102304905737681)
      ·
        refine ⟨2659450756576728679303261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3545934342102304905737681 2659450756576728679303261)
        ·
          refine ⟨997294033716273254738723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2659450756576728679303261 997294033716273254738723)
          ·
            refine ⟨1495941050574409882108085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 997294033716273254738723 1495941050574409882108085)
            ·
              refine ⟨140244473491350926447633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1495941050574409882108085 140244473491350926447633)
              ·
                refine ⟨105183355118513194835725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140244473491350926447633 105183355118513194835725)
                ·
                  refine ⟨39443758169442448063397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105183355118513194835725 39443758169442448063397)
                  ·
                    rfl

theorem cell21_172837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 2, 3].length) (baseStart_172837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_172837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_172837 prefixEnd_172837 := by exact prefixLift 172837
  have htrace : WordTrace (prefixWord ++ tailWord_172837) baseStart_172837 baseEnd_172837 := by
    simpa [prefixWord, tailWord_172837, baseEnd_172837] using wordTrace_append hprefix tailTrace_172837
  have hstable : (prefixWord ++ tailWord_172837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172837).length < 2 ^ (prefixWord ++ tailWord_172837).sum := by decide
  have hdescent : baseEnd_172837 < baseStart_172837 := by decide
  rcases family_descends (prefixWord ++ tailWord_172837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172851 : List Nat := [1, 1, 1, 2, 6, 1, 4, 1, 4]
def baseStart_172851 : Nat := 118140960795 + 172851 * 2 ^ 59
def prefixEnd_172851 : Nat := 4983230072969 + 3 ^ 40 * 172851 * 2
def baseEnd_172851 : Nat := 39446953160181534830035

theorem tailTrace_172851 : CollatzResearch.WordTrace tailWord_172851 prefixEnd_172851 39446953160181534830035 := by
  unfold tailWord_172851
  simp only [CollatzResearch.WordTrace]
  refine ⟨6304393896797822445654407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4202929264531881630436271 6304393896797822445654407)
  ·
    refine ⟨9456590845196733668481611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6304393896797822445654407 9456590845196733668481611)
    ·
      refine ⟨14184886267795100502722417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9456590845196733668481611 14184886267795100502722417)
      ·
        refine ⟨10638664700846325377041813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14184886267795100502722417 10638664700846325377041813)
        ·
          refine ⟨498687407852171502048835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10638664700846325377041813 498687407852171502048835)
          ·
            refine ⟨748031111778257253073253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498687407852171502048835 748031111778257253073253)
            ·
              refine ⟨140255833458423234951235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 748031111778257253073253 140255833458423234951235)
              ·
                refine ⟨210383750187634852426853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140255833458423234951235 210383750187634852426853)
                ·
                  refine ⟨39446953160181534830035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 210383750187634852426853 39446953160181534830035)
                  ·
                    rfl

theorem cell21_172851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 1, 4].length) (baseStart_172851 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_172851 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_172851 prefixEnd_172851 := by exact prefixLift 172851
  have htrace : WordTrace (prefixWord ++ tailWord_172851) baseStart_172851 baseEnd_172851 := by
    simpa [prefixWord, tailWord_172851, baseEnd_172851] using wordTrace_append hprefix tailTrace_172851
  have hstable : (prefixWord ++ tailWord_172851).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172851).length < 2 ^ (prefixWord ++ tailWord_172851).sum := by decide
  have hdescent : baseEnd_172851 < baseStart_172851 := by decide
  rcases family_descends (prefixWord ++ tailWord_172851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172896 : List Nat := [2, 1, 1, 3, 3, 1, 3, 4, 3]
def baseStart_172896 : Nat := 118140960795 + 172896 * 2 ^ 59
def prefixEnd_172896 : Nat := 4983230072969 + 3 ^ 40 * 172896 * 2
def baseEnd_172896 : Nat := 39457222773271456579943

theorem tailTrace_172896 : CollatzResearch.WordTrace tailWord_172896 prefixEnd_172896 39457222773271456579943 := by
  unfold tailWord_172896
  simp only [CollatzResearch.WordTrace]
  refine ⟨3153017590817397565521271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4204023454423196754028361 3153017590817397565521271)
  ·
    refine ⟨4729526386226096348281907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3153017590817397565521271 4729526386226096348281907)
    ·
      refine ⟨7094289579339144522422861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4729526386226096348281907 7094289579339144522422861)
      ·
        refine ⟨2660358592252179195908573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7094289579339144522422861 2660358592252179195908573)
        ·
          refine ⟨997634472094567198465715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2660358592252179195908573 997634472094567198465715)
          ·
            refine ⟨1496451708141850797698573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 997634472094567198465715 1496451708141850797698573)
            ·
              refine ⟨561169390553194049136965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1496451708141850797698573 561169390553194049136965)
              ·
                refine ⟨105219260728723884213181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 561169390553194049136965 105219260728723884213181)
                ·
                  refine ⟨39457222773271456579943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105219260728723884213181 39457222773271456579943)
                  ·
                    rfl

theorem cell21_172896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 4, 3].length) (baseStart_172896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_172896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_172896 prefixEnd_172896 := by exact prefixLift 172896
  have htrace : WordTrace (prefixWord ++ tailWord_172896) baseStart_172896 baseEnd_172896 := by
    simpa [prefixWord, tailWord_172896, baseEnd_172896] using wordTrace_append hprefix tailTrace_172896
  have hstable : (prefixWord ++ tailWord_172896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172896).length < 2 ^ (prefixWord ++ tailWord_172896).sum := by decide
  have hdescent : baseEnd_172896 < baseStart_172896 := by decide
  rcases family_descends (prefixWord ++ tailWord_172896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173242 : List Nat := [3, 1, 1, 1, 2, 2, 1, 5, 5]
def baseStart_173242 : Nat := 118140960795 + 173242 * 2 ^ 59
def prefixEnd_173242 : Nat := 4983230072969 + 3 ^ 40 * 173242 * 2
def baseEnd_173242 : Nat := 39536184687251743812569

theorem tailTrace_173242 : CollatzResearch.WordTrace tailWord_173242 prefixEnd_173242 39536184687251743812569 := by
  unfold tailWord_173242
  simp only [CollatzResearch.WordTrace]
  refine ⟨1579663709595324055784495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4212436558920864148758653 1579663709595324055784495)
  ·
    refine ⟨2369495564392986083676743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1579663709595324055784495 2369495564392986083676743)
    ·
      refine ⟨3554243346589479125515115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2369495564392986083676743 3554243346589479125515115)
      ·
        refine ⟨5331365019884218688272673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3554243346589479125515115 5331365019884218688272673)
        ·
          refine ⟨3998523764913164016204505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5331365019884218688272673 3998523764913164016204505)
          ·
            refine ⟨2998892823684873012153379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3998523764913164016204505 2998892823684873012153379)
            ·
              refine ⟨4498339235527309518230069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2998892823684873012153379 4498339235527309518230069)
              ·
                refine ⟨421719303330685267334069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4498339235527309518230069 421719303330685267334069)
                ·
                  refine ⟨39536184687251743812569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 421719303330685267334069 39536184687251743812569)
                  ·
                    rfl

theorem cell21_173242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_173242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_173242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_173242 prefixEnd_173242 := by exact prefixLift 173242
  have htrace : WordTrace (prefixWord ++ tailWord_173242) baseStart_173242 baseEnd_173242 := by
    simpa [prefixWord, tailWord_173242, baseEnd_173242] using wordTrace_append hprefix tailTrace_173242
  have hstable : (prefixWord ++ tailWord_173242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173242).length < 2 ^ (prefixWord ++ tailWord_173242).sum := by decide
  have hdescent : baseEnd_173242 < baseStart_173242 := by decide
  rcases family_descends (prefixWord ++ tailWord_173242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173290 : List Nat := [3, 1, 3, 1, 1, 3, 3, 2, 4]
def baseStart_173290 : Nat := 118140960795 + 173290 * 2 ^ 59
def prefixEnd_173290 : Nat := 4983230072969 + 3 ^ 40 * 173290 * 2
def baseEnd_173290 : Nat := 39547138941214327012471

theorem tailTrace_173290 : CollatzResearch.WordTrace tailWord_173290 prefixEnd_173290 39547138941214327012471 := by
  unfold tailWord_173290
  simp only [CollatzResearch.WordTrace]
  refine ⟨1580101385551850105221331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4213603694804933613923549 1580101385551850105221331)
  ·
    refine ⟨2370152078327775157831997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1580101385551850105221331 2370152078327775157831997)
    ·
      refine ⟨888807029372915684186999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2370152078327775157831997 888807029372915684186999)
      ·
        refine ⟨1333210544059373526280499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 888807029372915684186999 1333210544059373526280499)
        ·
          refine ⟨1999815816089060289420749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1333210544059373526280499 1999815816089060289420749)
          ·
            refine ⟨749930931033397608532781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1999815816089060289420749 749930931033397608532781)
            ·
              refine ⟨281224099137524103199793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 749930931033397608532781 281224099137524103199793)
              ·
                refine ⟨210918074353143077399845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 281224099137524103199793 210918074353143077399845)
                ·
                  refine ⟨39547138941214327012471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 210918074353143077399845 39547138941214327012471)
                  ·
                    rfl

theorem cell21_173290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 2, 4].length) (baseStart_173290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_173290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_173290 prefixEnd_173290 := by exact prefixLift 173290
  have htrace : WordTrace (prefixWord ++ tailWord_173290) baseStart_173290 baseEnd_173290 := by
    simpa [prefixWord, tailWord_173290, baseEnd_173290] using wordTrace_append hprefix tailTrace_173290
  have hstable : (prefixWord ++ tailWord_173290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173290).length < 2 ^ (prefixWord ++ tailWord_173290).sum := by decide
  have hdescent : baseEnd_173290 < baseStart_173290 := by decide
  rcases family_descends (prefixWord ++ tailWord_173290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173349 : List Nat := [1, 3, 1, 2, 4, 1, 2, 1, 6]
def baseStart_173349 : Nat := 118140960795 + 173349 * 2 ^ 59
def prefixEnd_173349 : Nat := 4983230072969 + 3 ^ 40 * 173349 * 2
def baseEnd_173349 : Nat := 39560603545043335529017

theorem tailTrace_173349 : CollatzResearch.WordTrace tailWord_173349 prefixEnd_173349 39560603545043335529017 := by
  unfold tailWord_173349
  simp only [CollatzResearch.WordTrace]
  refine ⟨6322557448993653497283101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4215038299329102331522067 6322557448993653497283101)
  ·
    refine ⟨2370959043372620061481163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6322557448993653497283101 2370959043372620061481163)
    ·
      refine ⟨3556438565058930092221745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2370959043372620061481163 3556438565058930092221745)
      ·
        refine ⟨2667328923794197569166309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3556438565058930092221745 2667328923794197569166309)
        ·
          refine ⟨500124173211412044218683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2667328923794197569166309 500124173211412044218683)
          ·
            refine ⟨750186259817118066328025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 500124173211412044218683 750186259817118066328025)
            ·
              refine ⟨562639694862838549746019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 750186259817118066328025 562639694862838549746019)
              ·
                refine ⟨843959542294257824619029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 562639694862838549746019 843959542294257824619029)
                ·
                  refine ⟨39560603545043335529017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 843959542294257824619029 39560603545043335529017)
                  ·
                    rfl

theorem cell21_173349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_173349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_173349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_173349 prefixEnd_173349 := by exact prefixLift 173349
  have htrace : WordTrace (prefixWord ++ tailWord_173349) baseStart_173349 baseEnd_173349 := by
    simpa [prefixWord, tailWord_173349, baseEnd_173349] using wordTrace_append hprefix tailTrace_173349
  have hstable : (prefixWord ++ tailWord_173349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173349).length < 2 ^ (prefixWord ++ tailWord_173349).sum := by decide
  have hdescent : baseEnd_173349 < baseStart_173349 := by decide
  rcases family_descends (prefixWord ++ tailWord_173349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173352 : List Nat := [2, 1, 5, 1, 2, 3, 1, 1, 5]
def baseStart_173352 : Nat := 118140960795 + 173352 * 2 ^ 59
def prefixEnd_173352 : Nat := 4983230072969 + 3 ^ 40 * 173352 * 2
def baseEnd_173352 : Nat := 39561288185915996979011

theorem tailTrace_173352 : CollatzResearch.WordTrace tailWord_173352 prefixEnd_173352 39561288185915996979011 := by
  unfold tailWord_173352
  simp only [CollatzResearch.WordTrace]
  refine ⟨3161333433991392504821155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4215111245321856673094873 3161333433991392504821155)
  ·
    refine ⟨4742000150987088757231733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3161333433991392504821155 4742000150987088757231733)
    ·
      refine ⟨444562514155039570990475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4742000150987088757231733 444562514155039570990475)
      ·
        refine ⟨666843771232559356485713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444562514155039570990475 666843771232559356485713)
        ·
          refine ⟨500132828424419517364285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 666843771232559356485713 500132828424419517364285)
          ·
            refine ⟨187549810659157319011607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 500132828424419517364285 187549810659157319011607)
            ·
              refine ⟨281324715988735978517411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187549810659157319011607 281324715988735978517411)
              ·
                refine ⟨421987073983103967776117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 281324715988735978517411 421987073983103967776117)
                ·
                  refine ⟨39561288185915996979011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 421987073983103967776117 39561288185915996979011)
                  ·
                    rfl

theorem cell21_173352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 5].length) (baseStart_173352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_173352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_173352 prefixEnd_173352 := by exact prefixLift 173352
  have htrace : WordTrace (prefixWord ++ tailWord_173352) baseStart_173352 baseEnd_173352 := by
    simpa [prefixWord, tailWord_173352, baseEnd_173352] using wordTrace_append hprefix tailTrace_173352
  have hstable : (prefixWord ++ tailWord_173352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173352).length < 2 ^ (prefixWord ++ tailWord_173352).sum := by decide
  have hdescent : baseEnd_173352 < baseStart_173352 := by decide
  rcases family_descends (prefixWord ++ tailWord_173352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173363 : List Nat := [1, 1, 1, 2, 5, 2, 1, 8]
def baseStart_173363 : Nat := 118140960795 + 173363 * 2 ^ 59
def prefixEnd_173363 : Nat := 4983230072969 + 3 ^ 40 * 173363 * 2
def baseEnd_173363 : Nat := 13187932845260807431885

theorem tailTrace_173363 : CollatzResearch.WordTrace tailWord_173363 prefixEnd_173363 13187932845260807431885 := by
  unfold tailWord_173363
  simp only [CollatzResearch.WordTrace]
  refine ⟨6323068070942933888292743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4215378713961955925528495 6323068070942933888292743)
  ·
    refine ⟨9484602106414400832439115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6323068070942933888292743 9484602106414400832439115)
    ·
      refine ⟨14226903159621601248658673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9484602106414400832439115 14226903159621601248658673)
      ·
        refine ⟨10670177369716200936494005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14226903159621601248658673 10670177369716200936494005)
        ·
          refine ⟨1000329128410893837796313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10670177369716200936494005 1000329128410893837796313)
          ·
            refine ⟨750246846308170378347235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1000329128410893837796313 750246846308170378347235)
            ·
              refine ⟨1125370269462255567520853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 750246846308170378347235 1125370269462255567520853)
              ·
                refine ⟨13187932845260807431885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1125370269462255567520853 13187932845260807431885)
                ·
                  rfl

theorem cell21_173363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 8].length) (baseStart_173363 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_173363 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_173363 prefixEnd_173363 := by exact prefixLift 173363
  have htrace : WordTrace (prefixWord ++ tailWord_173363) baseStart_173363 baseEnd_173363 := by
    simpa [prefixWord, tailWord_173363, baseEnd_173363] using wordTrace_append hprefix tailTrace_173363
  have hstable : (prefixWord ++ tailWord_173363).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173363).length < 2 ^ (prefixWord ++ tailWord_173363).sum := by decide
  have hdescent : baseEnd_173363 < baseStart_173363 := by decide
  rcases family_descends (prefixWord ++ tailWord_173363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173425 : List Nat := [1, 2, 2, 2, 1, 2, 4, 3, 4]
def baseStart_173425 : Nat := 118140960795 + 173425 * 2 ^ 59
def prefixEnd_173425 : Nat := 4983230072969 + 3 ^ 40 * 173425 * 2
def baseEnd_173425 : Nat := 39577947780484092262195

theorem tailTrace_173425 : CollatzResearch.WordTrace tailWord_173425 prefixEnd_173425 39577947780484092262195 := by
  unfold tailWord_173425
  simp only [CollatzResearch.WordTrace]
  refine ⟨6325329396718318477049729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4216886264478878984699819 6325329396718318477049729)
  ·
    refine ⟨4743997047538738857787297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6325329396718318477049729 4743997047538738857787297)
    ·
      refine ⟨3557997785654054143340473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4743997047538738857787297 3557997785654054143340473)
      ·
        refine ⟨2668498339240540607505355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3557997785654054143340473 2668498339240540607505355)
        ·
          refine ⟨4002747508860810911258033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2668498339240540607505355 4002747508860810911258033)
          ·
            refine ⟨3002060631645608183443525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4002747508860810911258033 3002060631645608183443525)
            ·
              refine ⟨562886368433551534395661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3002060631645608183443525 562886368433551534395661)
              ·
                refine ⟨211082388162581825398373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 562886368433551534395661 211082388162581825398373)
                ·
                  refine ⟨39577947780484092262195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 211082388162581825398373 39577947780484092262195)
                  ·
                    rfl

theorem cell21_173425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 3, 4].length) (baseStart_173425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_173425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_173425 prefixEnd_173425 := by exact prefixLift 173425
  have htrace : WordTrace (prefixWord ++ tailWord_173425) baseStart_173425 baseEnd_173425 := by
    simpa [prefixWord, tailWord_173425, baseEnd_173425] using wordTrace_append hprefix tailTrace_173425
  have hstable : (prefixWord ++ tailWord_173425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173425).length < 2 ^ (prefixWord ++ tailWord_173425).sum := by decide
  have hdescent : baseEnd_173425 < baseStart_173425 := by decide
  rcases family_descends (prefixWord ++ tailWord_173425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173577 : List Nat := [1, 2, 1, 1, 3, 1, 6, 2, 4]
def baseStart_173577 : Nat := 118140960795 + 173577 * 2 ^ 59
def prefixEnd_173577 : Nat := 4983230072969 + 3 ^ 40 * 173577 * 2
def baseEnd_173577 : Nat := 39612636251365605728551

theorem tailTrace_173577 : CollatzResearch.WordTrace tailWord_173577 prefixEnd_173577 39612636251365605728551 := by
  unfold tailWord_173577
  simp only [CollatzResearch.WordTrace]
  refine ⟨6330873292167648436582985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4220582194778432291055323 6330873292167648436582985)
  ·
    refine ⟨4748154969125736327437239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6330873292167648436582985 4748154969125736327437239)
    ·
      refine ⟨7122232453688604491155859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4748154969125736327437239 7122232453688604491155859)
      ·
        refine ⟨10683348680532906736733789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7122232453688604491155859 10683348680532906736733789)
        ·
          refine ⟨4006255755199840026275171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10683348680532906736733789 4006255755199840026275171)
          ·
            refine ⟨6009383632799760039412757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4006255755199840026275171 6009383632799760039412757)
            ·
              refine ⟨281689857787488751847473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6009383632799760039412757 281689857787488751847473)
              ·
                refine ⟨211267393340616563885605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 281689857787488751847473 211267393340616563885605)
                ·
                  refine ⟨39612636251365605728551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 211267393340616563885605 39612636251365605728551)
                  ·
                    rfl

theorem cell21_173577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 2, 4].length) (baseStart_173577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_173577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_173577 prefixEnd_173577 := by exact prefixLift 173577
  have htrace : WordTrace (prefixWord ++ tailWord_173577) baseStart_173577 baseEnd_173577 := by
    simpa [prefixWord, tailWord_173577, baseEnd_173577] using wordTrace_append hprefix tailTrace_173577
  have hstable : (prefixWord ++ tailWord_173577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173577).length < 2 ^ (prefixWord ++ tailWord_173577).sum := by decide
  have hdescent : baseEnd_173577 < baseStart_173577 := by decide
  rcases family_descends (prefixWord ++ tailWord_173577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173580 : List Nat := [2, 2, 1, 2, 5, 1, 1, 4, 3]
def baseStart_173580 : Nat := 118140960795 + 173580 * 2 ^ 59
def prefixEnd_173580 : Nat := 4983230072969 + 3 ^ 40 * 173580 * 2
def baseEnd_173580 : Nat := 39613320892238267178545

theorem tailTrace_173580 : CollatzResearch.WordTrace tailWord_173580 prefixEnd_173580 39613320892238267178545 := by
  unfold tailWord_173580
  simp only [CollatzResearch.WordTrace]
  refine ⟨3165491355578389974471097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4220655140771186632628129 3165491355578389974471097)
  ·
    refine ⟨2374118516683792480853323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3165491355578389974471097 2374118516683792480853323)
    ·
      refine ⟨3561177775025688721279985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2374118516683792480853323 3561177775025688721279985)
      ·
        refine ⟨2670883331269266540959989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3561177775025688721279985 2670883331269266540959989)
        ·
          refine ⟨250395312306493738214999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2670883331269266540959989 250395312306493738214999)
          ·
            refine ⟨375592968459740607322499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250395312306493738214999 375592968459740607322499)
            ·
              refine ⟨563389452689610910983749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 375592968459740607322499 563389452689610910983749)
              ·
                refine ⟨105635522379302045809453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 563389452689610910983749 105635522379302045809453)
                ·
                  refine ⟨39613320892238267178545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105635522379302045809453 39613320892238267178545)
                  ·
                    rfl

theorem cell21_173580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 4, 3].length) (baseStart_173580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_173580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_173580 prefixEnd_173580 := by exact prefixLift 173580
  have htrace : WordTrace (prefixWord ++ tailWord_173580) baseStart_173580 baseEnd_173580 := by
    simpa [prefixWord, tailWord_173580, baseEnd_173580] using wordTrace_append hprefix tailTrace_173580
  have hstable : (prefixWord ++ tailWord_173580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173580).length < 2 ^ (prefixWord ++ tailWord_173580).sum := by decide
  have hdescent : baseEnd_173580 < baseStart_173580 := by decide
  rcases family_descends (prefixWord ++ tailWord_173580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173639 : List Nat := [1, 1, 4, 1, 5, 1, 2, 1, 5]
def baseStart_173639 : Nat := 118140960795 + 173639 * 2 ^ 59
def prefixEnd_173639 : Nat := 4983230072969 + 3 ^ 40 * 173639 * 2
def baseEnd_173639 : Nat := 39626785496067275695091

theorem tailTrace_173639 : CollatzResearch.WordTrace tailWord_173639 prefixEnd_173639 39626785496067275695091 := by
  unfold tailWord_173639
  simp only [CollatzResearch.WordTrace]
  refine ⟨6333134617943033025339971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4222089745295355350226647 6333134617943033025339971)
  ·
    refine ⟨9499701926914549538009957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6333134617943033025339971 9499701926914549538009957)
    ·
      refine ⟨1781194111296478038376867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9499701926914549538009957 1781194111296478038376867)
      ·
        refine ⟨2671791166944717057565301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1781194111296478038376867 2671791166944717057565301)
        ·
          refine ⟨250480421901067224146747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2671791166944717057565301 250480421901067224146747)
          ·
            refine ⟨375720632851600836220121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250480421901067224146747 375720632851600836220121)
            ·
              refine ⟨281790474638700627165091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 375720632851600836220121 281790474638700627165091)
              ·
                refine ⟨422685711958050940747637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 281790474638700627165091 422685711958050940747637)
                ·
                  refine ⟨39626785496067275695091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 422685711958050940747637 39626785496067275695091)
                  ·
                    rfl

theorem cell21_173639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 5].length) (baseStart_173639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_173639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_173639 prefixEnd_173639 := by exact prefixLift 173639
  have htrace : WordTrace (prefixWord ++ tailWord_173639) baseStart_173639 baseEnd_173639 := by
    simpa [prefixWord, tailWord_173639, baseEnd_173639] using wordTrace_append hprefix tailTrace_173639
  have hstable : (prefixWord ++ tailWord_173639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173639).length < 2 ^ (prefixWord ++ tailWord_173639).sum := by decide
  have hdescent : baseEnd_173639 < baseStart_173639 := by decide
  rcases family_descends (prefixWord ++ tailWord_173639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173667 : List Nat := [1, 1, 1, 5, 1, 4, 1, 7]
def baseStart_173667 : Nat := 118140960795 + 173667 * 2 ^ 59
def prefixEnd_173667 : Nat := 4983230072969 + 3 ^ 40 * 173667 * 2
def baseEnd_173667 : Nat := 13211058492515149742789

theorem tailTrace_173667 : CollatzResearch.WordTrace tailWord_173667 prefixEnd_173667 13211058492515149742789 := by
  unfold tailWord_173667
  simp only [CollatzResearch.WordTrace]
  refine ⟨6334155861841593807359255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4222770574561062538239503 6334155861841593807359255)
  ·
    refine ⟨9501233792762390711038883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6334155861841593807359255 9501233792762390711038883)
    ·
      refine ⟨14251850689143586066558325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9501233792762390711038883 14251850689143586066558325)
      ·
        refine ⟨1336111002107211193739843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14251850689143586066558325 1336111002107211193739843)
        ·
          refine ⟨2004166503160816790609765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1336111002107211193739843 2004166503160816790609765)
          ·
            refine ⟨375781219342653148239331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2004166503160816790609765 375781219342653148239331)
            ·
              refine ⟨563671829013979722358997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 375781219342653148239331 563671829013979722358997)
              ·
                refine ⟨13211058492515149742789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 563671829013979722358997 13211058492515149742789)
                ·
                  rfl

theorem cell21_173667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 7].length) (baseStart_173667 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_173667 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_173667 prefixEnd_173667 := by exact prefixLift 173667
  have htrace : WordTrace (prefixWord ++ tailWord_173667) baseStart_173667 baseEnd_173667 := by
    simpa [prefixWord, tailWord_173667, baseEnd_173667] using wordTrace_append hprefix tailTrace_173667
  have hstable : (prefixWord ++ tailWord_173667).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173667).length < 2 ^ (prefixWord ++ tailWord_173667).sum := by decide
  have hdescent : baseEnd_173667 < baseStart_173667 := by decide
  rcases family_descends (prefixWord ++ tailWord_173667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173681 : List Nat := [1, 2, 2, 2, 1, 1, 1, 4, 7]
def baseStart_173681 : Nat := 118140960795 + 173681 * 2 ^ 59
def prefixEnd_173681 : Nat := 4983230072969 + 3 ^ 40 * 173681 * 2
def baseEnd_173681 : Nat := 39636370468284535995005

theorem tailTrace_173681 : CollatzResearch.WordTrace tailWord_173681 prefixEnd_173681 39636370468284535995005 := by
  unfold tailWord_173681
  simp only [CollatzResearch.WordTrace]
  refine ⟨6334666483790874198368897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4223110989193916132245931 6334666483790874198368897)
  ·
    refine ⟨4750999862843155648776673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6334666483790874198368897 4750999862843155648776673)
    ·
      refine ⟨3563249897132366736582505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4750999862843155648776673 3563249897132366736582505)
      ·
        refine ⟨2672437422849275052436879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3563249897132366736582505 2672437422849275052436879)
        ·
          refine ⟨4008656134273912578655319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2672437422849275052436879 4008656134273912578655319)
          ·
            refine ⟨6012984201410868867982979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4008656134273912578655319 6012984201410868867982979)
            ·
              refine ⟨9019476302116303301974469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6012984201410868867982979 9019476302116303301974469)
              ·
                refine ⟨1691151806646806869120213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9019476302116303301974469 1691151806646806869120213)
                ·
                  refine ⟨39636370468284535995005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1691151806646806869120213 39636370468284535995005)
                  ·
                    rfl

theorem cell21_173681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 7].length) (baseStart_173681 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_173681 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_173681 prefixEnd_173681 := by exact prefixLift 173681
  have htrace : WordTrace (prefixWord ++ tailWord_173681) baseStart_173681 baseEnd_173681 := by
    simpa [prefixWord, tailWord_173681, baseEnd_173681] using wordTrace_append hprefix tailTrace_173681
  have hstable : (prefixWord ++ tailWord_173681).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173681).length < 2 ^ (prefixWord ++ tailWord_173681).sum := by decide
  have hdescent : baseEnd_173681 < baseStart_173681 := by decide
  rcases family_descends (prefixWord ++ tailWord_173681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173704 : List Nat := [2, 1, 3, 5, 1, 2, 2, 1, 4]
def baseStart_173704 : Nat := 118140960795 + 173704 * 2 ^ 59
def prefixEnd_173704 : Nat := 4983230072969 + 3 ^ 40 * 173704 * 2
def baseEnd_173704 : Nat := 39641619381641607111625

theorem tailTrace_173704 : CollatzResearch.WordTrace tailWord_173704 prefixEnd_173704 39641619381641607111625 := by
  unfold tailWord_173704
  simp only [CollatzResearch.WordTrace]
  refine ⟨3167752681353774563228083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4223670241805032750970777 3167752681353774563228083)
  ·
    refine ⟨4751629022030661844842125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3167752681353774563228083 4751629022030661844842125)
    ·
      refine ⟨1781860883261498191815797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4751629022030661844842125 1781860883261498191815797)
      ·
        refine ⟨167049457805765455482731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1781860883261498191815797 167049457805765455482731)
        ·
          refine ⟨250574186708648183224097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167049457805765455482731 250574186708648183224097)
          ·
            refine ⟨187930640031486137418073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250574186708648183224097 187930640031486137418073)
            ·
              refine ⟨140947980023614603063555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187930640031486137418073 140947980023614603063555)
              ·
                refine ⟨211421970035421904595333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140947980023614603063555 211421970035421904595333)
                ·
                  refine ⟨39641619381641607111625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 211421970035421904595333 39641619381641607111625)
                  ·
                    rfl

theorem cell21_173704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 1, 4].length) (baseStart_173704 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_173704 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_173704 prefixEnd_173704 := by exact prefixLift 173704
  have htrace : WordTrace (prefixWord ++ tailWord_173704) baseStart_173704 baseEnd_173704 := by
    simpa [prefixWord, tailWord_173704, baseEnd_173704] using wordTrace_append hprefix tailTrace_173704
  have hstable : (prefixWord ++ tailWord_173704).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173704).length < 2 ^ (prefixWord ++ tailWord_173704).sum := by decide
  have hdescent : baseEnd_173704 < baseStart_173704 := by decide
  rcases family_descends (prefixWord ++ tailWord_173704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173774 : List Nat := [4, 1, 1, 1, 3, 1, 3, 2, 5]
def baseStart_173774 : Nat := 118140960795 + 173774 * 2 ^ 59
def prefixEnd_173774 : Nat := 4983230072969 + 3 ^ 40 * 173774 * 2
def baseEnd_173774 : Nat := 39657594335337040944815

theorem tailTrace_173774 : CollatzResearch.WordTrace tailWord_173774 prefixEnd_173774 39657594335337040944815 := by
  unfold tailWord_173774
  simp only [CollatzResearch.WordTrace]
  refine ⟨792257309056743885188047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4225372314969300721002917 792257309056743885188047)
  ·
    refine ⟨1188385963585115827782071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 792257309056743885188047 1188385963585115827782071)
    ·
      refine ⟨1782578945377673741673107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1188385963585115827782071 1782578945377673741673107)
      ·
        refine ⟨2673868418066510612509661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1782578945377673741673107 2673868418066510612509661)
        ·
          refine ⟨1002700656774941479691123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2673868418066510612509661 1002700656774941479691123)
          ·
            refine ⟨1504050985162412219536685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1002700656774941479691123 1504050985162412219536685)
            ·
              refine ⟨564019119435904582326257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1504050985162412219536685 564019119435904582326257)
              ·
                refine ⟨423014339576928436744693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 564019119435904582326257 423014339576928436744693)
                ·
                  refine ⟨39657594335337040944815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 423014339576928436744693 39657594335337040944815)
                  ·
                    rfl

theorem cell21_173774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_173774 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_173774 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_173774 prefixEnd_173774 := by exact prefixLift 173774
  have htrace : WordTrace (prefixWord ++ tailWord_173774) baseStart_173774 baseEnd_173774 := by
    simpa [prefixWord, tailWord_173774, baseEnd_173774] using wordTrace_append hprefix tailTrace_173774
  have hstable : (prefixWord ++ tailWord_173774).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173774).length < 2 ^ (prefixWord ++ tailWord_173774).sum := by decide
  have hdescent : baseEnd_173774 < baseStart_173774 := by decide
  rcases family_descends (prefixWord ++ tailWord_173774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173791 : List Nat := [1, 1, 2, 3, 2, 2, 4, 3, 3]
def baseStart_173791 : Nat := 118140960795 + 173791 * 2 ^ 59
def prefixEnd_173791 : Nat := 4983230072969 + 3 ^ 40 * 173791 * 2
def baseEnd_173791 : Nat := 39661473966948789161447

theorem tailTrace_173791 : CollatzResearch.WordTrace tailWord_173791 prefixEnd_173791 39661473966948789161447 := by
  unfold tailWord_173791
  simp only [CollatzResearch.WordTrace]
  refine ⟨6338678513392362984873227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4225785675594908656582151 6338678513392362984873227)
  ·
    refine ⟨9508017770088544477309841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6338678513392362984873227 9508017770088544477309841)
    ·
      refine ⟨7131013327566408357982381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9508017770088544477309841 7131013327566408357982381)
      ·
        refine ⟨2674129997837403134243393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7131013327566408357982381 2674129997837403134243393)
        ·
          refine ⟨2005597498378052350682545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2674129997837403134243393 2005597498378052350682545)
          ·
            refine ⟨1504198123783539263011909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2005597498378052350682545 1504198123783539263011909)
            ·
              refine ⟨282037148209413611814733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1504198123783539263011909 282037148209413611814733)
              ·
                refine ⟨105763930578530104430525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 282037148209413611814733 105763930578530104430525)
                ·
                  refine ⟨39661473966948789161447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105763930578530104430525 39661473966948789161447)
                  ·
                    rfl

theorem cell21_173791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 3, 3].length) (baseStart_173791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_173791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_173791 prefixEnd_173791 := by exact prefixLift 173791
  have htrace : WordTrace (prefixWord ++ tailWord_173791) baseStart_173791 baseEnd_173791 := by
    simpa [prefixWord, tailWord_173791, baseEnd_173791] using wordTrace_append hprefix tailTrace_173791
  have hstable : (prefixWord ++ tailWord_173791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173791).length < 2 ^ (prefixWord ++ tailWord_173791).sum := by decide
  have hdescent : baseEnd_173791 < baseStart_173791 := by decide
  rcases family_descends (prefixWord ++ tailWord_173791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173805 : List Nat := [1, 5, 1, 2, 1, 3, 1, 1, 6]
def baseStart_173805 : Nat := 118140960795 + 173805 * 2 ^ 59
def prefixEnd_173805 : Nat := 4983230072969 + 3 ^ 40 * 173805 * 2
def baseEnd_173805 : Nat := 39664668957687875928085

theorem tailTrace_173805 : CollatzResearch.WordTrace tailWord_173805 prefixEnd_173805 39664668957687875928085 := by
  unfold tailWord_173805
  simp only [CollatzResearch.WordTrace]
  refine ⟨6339189135341643375882869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4226126090227762250588579 6339189135341643375882869)
  ·
    refine ⟨594298981438279066489019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6339189135341643375882869 594298981438279066489019)
    ·
      refine ⟨891448472157418599733529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 594298981438279066489019 891448472157418599733529)
      ·
        refine ⟨668586354118063949800147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 891448472157418599733529 668586354118063949800147)
        ·
          refine ⟨1002879531177095924700221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 668586354118063949800147 1002879531177095924700221)
          ·
            refine ⟨376079824191410971762583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1002879531177095924700221 376079824191410971762583)
            ·
              refine ⟨564119736287116457643875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 376079824191410971762583 564119736287116457643875)
              ·
                refine ⟨846179604430674686465813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 564119736287116457643875 846179604430674686465813)
                ·
                  refine ⟨39664668957687875928085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 846179604430674686465813 39664668957687875928085)
                  ·
                    rfl

theorem cell21_173805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_173805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_173805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_173805 prefixEnd_173805 := by exact prefixLift 173805
  have htrace : WordTrace (prefixWord ++ tailWord_173805) baseStart_173805 baseEnd_173805 := by
    simpa [prefixWord, tailWord_173805, baseEnd_173805] using wordTrace_append hprefix tailTrace_173805
  have hstable : (prefixWord ++ tailWord_173805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173805).length < 2 ^ (prefixWord ++ tailWord_173805).sum := by decide
  have hdescent : baseEnd_173805 < baseStart_173805 := by decide
  rcases family_descends (prefixWord ++ tailWord_173805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173960 : List Nat := [2, 1, 3, 3, 3, 1, 2, 3, 3]
def baseStart_173960 : Nat := 118140960795 + 173960 * 2 ^ 59
def prefixEnd_173960 : Nat := 4983230072969 + 3 ^ 40 * 173960 * 2
def baseEnd_173960 : Nat := 39700042069442050844435

theorem tailTrace_173960 : CollatzResearch.WordTrace tailWord_173960 prefixEnd_173960 39700042069442050844435 := by
  unfold tailWord_173960
  simp only [CollatzResearch.WordTrace]
  refine ⟨3172421224890052423887667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4229894966520069898516889 3172421224890052423887667)
  ·
    refine ⟨4758631837335078635831501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3172421224890052423887667 4758631837335078635831501)
    ·
      refine ⟨1784486939000654488436813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4758631837335078635831501 1784486939000654488436813)
      ·
        refine ⟨669182602125245433163805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1784486939000654488436813 669182602125245433163805)
        ·
          refine ⟨250943475796967037436427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 669182602125245433163805 250943475796967037436427)
          ·
            refine ⟨376415213695450556154641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250943475796967037436427 376415213695450556154641)
            ·
              refine ⟨282311410271587917115981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 376415213695450556154641 282311410271587917115981)
              ·
                refine ⟨105866778851845468918493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 282311410271587917115981 105866778851845468918493)
                ·
                  refine ⟨39700042069442050844435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105866778851845468918493 39700042069442050844435)
                  ·
                    rfl

theorem cell21_173960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 3, 3].length) (baseStart_173960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_173960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_173960 prefixEnd_173960 := by exact prefixLift 173960
  have htrace : WordTrace (prefixWord ++ tailWord_173960) baseStart_173960 baseEnd_173960 := by
    simpa [prefixWord, tailWord_173960, baseEnd_173960] using wordTrace_append hprefix tailTrace_173960
  have hstable : (prefixWord ++ tailWord_173960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173960).length < 2 ^ (prefixWord ++ tailWord_173960).sum := by decide
  have hdescent : baseEnd_173960 < baseStart_173960 := by decide
  rcases family_descends (prefixWord ++ tailWord_173960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174036 : List Nat := [2, 4, 1, 2, 1, 1, 5, 2, 3]
def baseStart_174036 : Nat := 118140960795 + 174036 * 2 ^ 59
def prefixEnd_174036 : Nat := 4983230072969 + 3 ^ 40 * 174036 * 2
def baseEnd_174036 : Nat := 39717386304882807577613

theorem tailTrace_174036 : CollatzResearch.WordTrace tailWord_174036 prefixEnd_174036 39717386304882807577613 := by
  unfold tailWord_174036
  simp only [CollatzResearch.WordTrace]
  refine ⟨3173807198752384913770981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4231742931669846551694641 3173807198752384913770981)
  ·
    refine ⟨595088849766072171332059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3173807198752384913770981 595088849766072171332059)
    ·
      refine ⟨892633274649108256998089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 595088849766072171332059 892633274649108256998089)
      ·
        refine ⟨669474955986831192748567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 892633274649108256998089 669474955986831192748567)
        ·
          refine ⟨1004212433980246789122851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 669474955986831192748567 1004212433980246789122851)
          ·
            refine ⟨1506318650970370183684277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1004212433980246789122851 1506318650970370183684277)
            ·
              refine ⟨141217373528472204720401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1506318650970370183684277 141217373528472204720401)
              ·
                refine ⟨105913030146354153540301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141217373528472204720401 105913030146354153540301)
                ·
                  refine ⟨39717386304882807577613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105913030146354153540301 39717386304882807577613)
                  ·
                    rfl

theorem cell21_174036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_174036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_174036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_174036 prefixEnd_174036 := by exact prefixLift 174036
  have htrace : WordTrace (prefixWord ++ tailWord_174036) baseStart_174036 baseEnd_174036 := by
    simpa [prefixWord, tailWord_174036, baseEnd_174036] using wordTrace_append hprefix tailTrace_174036
  have hstable : (prefixWord ++ tailWord_174036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174036).length < 2 ^ (prefixWord ++ tailWord_174036).sum := by decide
  have hdescent : baseEnd_174036 < baseStart_174036 := by decide
  rcases family_descends (prefixWord ++ tailWord_174036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174047 : List Nat := [1, 1, 2, 3, 4, 2, 2, 6]
def baseStart_174047 : Nat := 118140960795 + 174047 * 2 ^ 59
def prefixEnd_174047 : Nat := 4983230072969 + 3 ^ 40 * 174047 * 2
def baseEnd_174047 : Nat := 13239965551583077631419

theorem tailTrace_174047 : CollatzResearch.WordTrace tailWord_174047 prefixEnd_174047 13239965551583077631419 := by
  unfold tailWord_174047
  simp only [CollatzResearch.WordTrace]
  refine ⟨6348015600464918706192395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4232010400309945804128263 6348015600464918706192395)
  ·
    refine ⟨9522023400697378059288593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6348015600464918706192395 9522023400697378059288593)
    ·
      refine ⟨7141517550523033544466445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9522023400697378059288593 7141517550523033544466445)
      ·
        refine ⟨2678069081446137579174917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7141517550523033544466445 2678069081446137579174917)
        ·
          refine ⟨502137952771150796095297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2678069081446137579174917 502137952771150796095297)
          ·
            refine ⟨376603464578363097071473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 502137952771150796095297 376603464578363097071473)
            ·
              refine ⟨282452598433772322803605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 376603464578363097071473 282452598433772322803605)
              ·
                refine ⟨13239965551583077631419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 282452598433772322803605 13239965551583077631419)
                ·
                  rfl

theorem cell21_174047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 6].length) (baseStart_174047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_174047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_174047 prefixEnd_174047 := by exact prefixLift 174047
  have htrace : WordTrace (prefixWord ++ tailWord_174047) baseStart_174047 baseEnd_174047 := by
    simpa [prefixWord, tailWord_174047, baseEnd_174047] using wordTrace_append hprefix tailTrace_174047
  have hstable : (prefixWord ++ tailWord_174047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174047).length < 2 ^ (prefixWord ++ tailWord_174047).sum := by decide
  have hdescent : baseEnd_174047 < baseStart_174047 := by decide
  rcases family_descends (prefixWord ++ tailWord_174047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174075 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 8]
def baseStart_174075 : Nat := 118140960795 + 174075 * 2 ^ 59
def prefixEnd_174075 : Nat := 4983230072969 + 3 ^ 40 * 174075 * 2
def baseEnd_174075 : Nat := 39726286636227406427533

theorem tailTrace_174075 : CollatzResearch.WordTrace tailWord_174075 prefixEnd_174075 39726286636227406427533 := by
  unfold tailWord_174075
  simp only [CollatzResearch.WordTrace]
  refine ⟨6349036844363479488211679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4232691229575652992141119 6349036844363479488211679)
  ·
    refine ⟨9523555266545219232317519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6349036844363479488211679 9523555266545219232317519)
    ·
      refine ⟨14285332899817828848476279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9523555266545219232317519 14285332899817828848476279)
      ·
        refine ⟨21427999349726743272714419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14285332899817828848476279 21427999349726743272714419)
        ·
          refine ⟨32141999024590114909071629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21427999349726743272714419 32141999024590114909071629)
          ·
            refine ⟨12053249634221293090901861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32141999024590114909071629 12053249634221293090901861)
            ·
              refine ⟨2259984306416492454544099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12053249634221293090901861 2259984306416492454544099)
              ·
                refine ⟨3389976459624738681816149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2259984306416492454544099 3389976459624738681816149)
                ·
                  refine ⟨39726286636227406427533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3389976459624738681816149 39726286636227406427533)
                  ·
                    rfl

theorem cell21_174075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 8].length) (baseStart_174075 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_174075 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_174075 prefixEnd_174075 := by exact prefixLift 174075
  have htrace : WordTrace (prefixWord ++ tailWord_174075) baseStart_174075 baseEnd_174075 := by
    simpa [prefixWord, tailWord_174075, baseEnd_174075] using wordTrace_append hprefix tailTrace_174075
  have hstable : (prefixWord ++ tailWord_174075).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174075).length < 2 ^ (prefixWord ++ tailWord_174075).sum := by decide
  have hdescent : baseEnd_174075 < baseStart_174075 := by decide
  rcases family_descends (prefixWord ++ tailWord_174075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174109 : List Nat := [1, 4, 2, 2, 2, 1, 2, 3, 4]
def baseStart_174109 : Nat := 118140960795 + 174109 * 2 ^ 59
def prefixEnd_174109 : Nat := 4983230072969 + 3 ^ 40 * 174109 * 2
def baseEnd_174109 : Nat := 39734045899450902860797

theorem tailTrace_174109 : CollatzResearch.WordTrace tailWord_174109 prefixEnd_174109 39734045899450902860797 := by
  unfold tailWord_174109
  simp only [CollatzResearch.WordTrace]
  refine ⟨6350276926240303294949381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4233517950826868863299587 6350276926240303294949381)
  ·
    refine ⟨1190676923670056867803009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6350276926240303294949381 1190676923670056867803009)
    ·
      refine ⟨893007692752542650852257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1190676923670056867803009 893007692752542650852257)
      ·
        refine ⟨669755769564406988139193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 893007692752542650852257 669755769564406988139193)
        ·
          refine ⟨502316827173305241104395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 669755769564406988139193 502316827173305241104395)
          ·
            refine ⟨753475240759957861656593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502316827173305241104395 753475240759957861656593)
            ·
              refine ⟨565106430569968396242445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 753475240759957861656593 565106430569968396242445)
              ·
                refine ⟨211914911463738148590917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 565106430569968396242445 211914911463738148590917)
                ·
                  refine ⟨39734045899450902860797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 211914911463738148590917 39734045899450902860797)
                  ·
                    rfl

theorem cell21_174109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_174109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_174109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_174109 prefixEnd_174109 := by exact prefixLift 174109
  have htrace : WordTrace (prefixWord ++ tailWord_174109) baseStart_174109 baseEnd_174109 := by
    simpa [prefixWord, tailWord_174109, baseEnd_174109] using wordTrace_append hprefix tailTrace_174109
  have hstable : (prefixWord ++ tailWord_174109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174109).length < 2 ^ (prefixWord ++ tailWord_174109).sum := by decide
  have hdescent : baseEnd_174109 < baseStart_174109 := by decide
  rcases family_descends (prefixWord ++ tailWord_174109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174303 : List Nat := [1, 1, 2, 3, 2, 1, 1, 4, 6]
def baseStart_174303 : Nat := 118140960795 + 174303 * 2 ^ 59
def prefixEnd_174303 : Nat := 4983230072969 + 3 ^ 40 * 174303 * 2
def baseEnd_174303 : Nat := 39778319342549676627067

theorem tailTrace_174303 : CollatzResearch.WordTrace tailWord_174303 prefixEnd_174303 39778319342549676627067 := by
  unfold tailWord_174303
  simp only [CollatzResearch.WordTrace]
  refine ⟨6357352687537474427511563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4238235125024982951674375 6357352687537474427511563)
  ·
    refine ⟨9536029031306211641267345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6357352687537474427511563 9536029031306211641267345)
    ·
      refine ⟨7152021773479658730950509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9536029031306211641267345 7152021773479658730950509)
      ·
        refine ⟨2682008165054872024106441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7152021773479658730950509 2682008165054872024106441)
        ·
          refine ⟨2011506123791154018079831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2682008165054872024106441 2011506123791154018079831)
          ·
            refine ⟨3017259185686731027119747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2011506123791154018079831 3017259185686731027119747)
            ·
              refine ⟨4525888778530096540679621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3017259185686731027119747 4525888778530096540679621)
              ·
                refine ⟨848604145974393101377429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4525888778530096540679621 848604145974393101377429)
                ·
                  refine ⟨39778319342549676627067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 848604145974393101377429 39778319342549676627067)
                  ·
                    rfl

theorem cell21_174303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 6].length) (baseStart_174303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_174303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_174303 prefixEnd_174303 := by exact prefixLift 174303
  have htrace : WordTrace (prefixWord ++ tailWord_174303) baseStart_174303 baseEnd_174303 := by
    simpa [prefixWord, tailWord_174303, baseEnd_174303] using wordTrace_append hprefix tailTrace_174303
  have hstable : (prefixWord ++ tailWord_174303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174303).length < 2 ^ (prefixWord ++ tailWord_174303).sum := by decide
  have hdescent : baseEnd_174303 < baseStart_174303 := by decide
  rcases family_descends (prefixWord ++ tailWord_174303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174337 : List Nat := [1, 2, 4, 1, 1, 2, 5, 1, 4]
def baseStart_174337 : Nat := 118140960795 + 174337 * 2 ^ 59
def prefixEnd_174337 : Nat := 4983230072969 + 3 ^ 40 * 174337 * 2
def baseEnd_174337 : Nat := 39786078605773173060331

theorem tailTrace_174337 : CollatzResearch.WordTrace tailWord_174337 prefixEnd_174337 39786078605773173060331 := by
  unfold tailWord_174337
  simp only [CollatzResearch.WordTrace]
  refine ⟨6358592769414298234249265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4239061846276198822832843 6358592769414298234249265)
  ·
    refine ⟨4768944577060723675686949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6358592769414298234249265 4768944577060723675686949)
    ·
      refine ⟨894177108198885689191303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4768944577060723675686949 894177108198885689191303)
      ·
        refine ⟨1341265662298328533786955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 894177108198885689191303 1341265662298328533786955)
        ·
          refine ⟨2011898493447492800680433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1341265662298328533786955 2011898493447492800680433)
          ·
            refine ⟨1508923870085619600510325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2011898493447492800680433 1508923870085619600510325)
            ·
              refine ⟨141461612820526837547843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1508923870085619600510325 141461612820526837547843)
              ·
                refine ⟨212192419230790256321765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141461612820526837547843 212192419230790256321765)
                ·
                  refine ⟨39786078605773173060331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 212192419230790256321765 39786078605773173060331)
                  ·
                    rfl

theorem cell21_174337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 1, 4].length) (baseStart_174337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_174337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_174337 prefixEnd_174337 := by exact prefixLift 174337
  have htrace : WordTrace (prefixWord ++ tailWord_174337) baseStart_174337 baseEnd_174337 := by
    simpa [prefixWord, tailWord_174337, baseEnd_174337] using wordTrace_append hprefix tailTrace_174337
  have hstable : (prefixWord ++ tailWord_174337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174337).length < 2 ^ (prefixWord ++ tailWord_174337).sum := by decide
  have hdescent : baseEnd_174337 < baseStart_174337 := by decide
  rcases family_descends (prefixWord ++ tailWord_174337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174396 : List Nat := [2, 2, 2, 2, 1, 2, 3, 3, 4]
def baseStart_174396 : Nat := 118140960795 + 174396 * 2 ^ 59
def prefixEnd_174396 : Nat := 4983230072969 + 3 ^ 40 * 174396 * 2
def baseEnd_174396 : Nat := 39799543209602181576877

theorem tailTrace_174396 : CollatzResearch.WordTrace tailWord_174396 prefixEnd_174396 39799543209602181576877 := by
  unfold tailWord_174396
  simp only [CollatzResearch.WordTrace]
  refine ⟨3180372338100275655323521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4240496450800367540431361 3180372338100275655323521)
  ·
    refine ⟨2385279253575206741492641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3180372338100275655323521 2385279253575206741492641)
    ·
      refine ⟨1788959440181405056119481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2385279253575206741492641 1788959440181405056119481)
      ·
        refine ⟨1341719580136053792089611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1788959440181405056119481 1341719580136053792089611)
        ·
          refine ⟨2012579370204080688134417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1341719580136053792089611 2012579370204080688134417)
          ·
            refine ⟨1509434527653060516100813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2012579370204080688134417 1509434527653060516100813)
            ·
              refine ⟨566037947869897693537805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1509434527653060516100813 566037947869897693537805)
              ·
                refine ⟨212264230451211635076677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 566037947869897693537805 212264230451211635076677)
                ·
                  refine ⟨39799543209602181576877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 212264230451211635076677 39799543209602181576877)
                  ·
                    rfl

theorem cell21_174396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 3, 4].length) (baseStart_174396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_174396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_174396 prefixEnd_174396 := by exact prefixLift 174396
  have htrace : WordTrace (prefixWord ++ tailWord_174396) baseStart_174396 baseEnd_174396 := by
    simpa [prefixWord, tailWord_174396, baseEnd_174396] using wordTrace_append hprefix tailTrace_174396
  have hstable : (prefixWord ++ tailWord_174396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174396).length < 2 ^ (prefixWord ++ tailWord_174396).sum := by decide
  have hdescent : baseEnd_174396 < baseStart_174396 := by decide
  rcases family_descends (prefixWord ++ tailWord_174396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174424 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 9]
def baseStart_174424 : Nat := 118140960795 + 174424 * 2 ^ 59
def prefixEnd_174424 : Nat := 4983230072969 + 3 ^ 40 * 174424 * 2
def baseEnd_174424 : Nat := 39805933191080355110153

theorem tailTrace_174424 : CollatzResearch.WordTrace tailWord_174424 prefixEnd_174424 39805933191080355110153 := by
  unfold tailWord_174424
  simp only [CollatzResearch.WordTrace]
  refine ⟨3180882960049556046333163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4241177280066074728444217 3180882960049556046333163)
  ·
    refine ⟨4771324440074334069499745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3180882960049556046333163 4771324440074334069499745)
    ·
      refine ⟨3578493330055750552124809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4771324440074334069499745 3578493330055750552124809)
      ·
        refine ⟨2683869997541812914093607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3578493330055750552124809 2683869997541812914093607)
        ·
          refine ⟨4025804996312719371140411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2683869997541812914093607 4025804996312719371140411)
          ·
            refine ⟨6038707494469079056710617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4025804996312719371140411 6038707494469079056710617)
            ·
              refine ⟨4529030620851809292532963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6038707494469079056710617 4529030620851809292532963)
              ·
                refine ⟨6793545931277713938799445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4529030620851809292532963 6793545931277713938799445)
                ·
                  refine ⟨39805933191080355110153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 6793545931277713938799445 39805933191080355110153)
                  ·
                    rfl

theorem cell21_174424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 9].length) (baseStart_174424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_174424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_174424 prefixEnd_174424 := by exact prefixLift 174424
  have htrace : WordTrace (prefixWord ++ tailWord_174424) baseStart_174424 baseEnd_174424 := by
    simpa [prefixWord, tailWord_174424, baseEnd_174424] using wordTrace_append hprefix tailTrace_174424
  have hstable : (prefixWord ++ tailWord_174424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174424).length < 2 ^ (prefixWord ++ tailWord_174424).sum := by decide
  have hdescent : baseEnd_174424 < baseStart_174424 := by decide
  rcases family_descends (prefixWord ++ tailWord_174424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174444 : List Nat := [2, 2, 1, 1, 7, 1, 1, 6]
def baseStart_174444 : Nat := 118140960795 + 174444 * 2 ^ 59
def prefixEnd_174444 : Nat := 4983230072969 + 3 ^ 40 * 174444 * 2
def baseEnd_174444 : Nat := 13270165821188254925593

theorem tailTrace_174444 : CollatzResearch.WordTrace tailWord_174444 prefixEnd_174444 13270165821188254925593 := by
  unfold tailWord_174444
  simp only [CollatzResearch.WordTrace]
  refine ⟨3181247690013327754197193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4241663586684437005596257 3181247690013327754197193)
  ·
    refine ⟨2385935767509995815647895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3181247690013327754197193 2385935767509995815647895)
    ·
      refine ⟨3578903651264993723471843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2385935767509995815647895 3578903651264993723471843)
      ·
        refine ⟨5368355476897490585207765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3578903651264993723471843 5368355476897490585207765)
        ·
          refine ⟨125820831489784935590807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 5368355476897490585207765 125820831489784935590807)
          ·
            refine ⟨188731247234677403386211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125820831489784935590807 188731247234677403386211)
            ·
              refine ⟨283096870852016105079317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188731247234677403386211 283096870852016105079317)
              ·
                refine ⟨13270165821188254925593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 283096870852016105079317 13270165821188254925593)
                ·
                  rfl

theorem cell21_174444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 6].length) (baseStart_174444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_174444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_174444 prefixEnd_174444 := by exact prefixLift 174444
  have htrace : WordTrace (prefixWord ++ tailWord_174444) baseStart_174444 baseEnd_174444 := by
    simpa [prefixWord, tailWord_174444, baseEnd_174444] using wordTrace_append hprefix tailTrace_174444
  have hstable : (prefixWord ++ tailWord_174444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174444).length < 2 ^ (prefixWord ++ tailWord_174444).sum := by decide
  have hdescent : baseEnd_174444 < baseStart_174444 := by decide
  rcases family_descends (prefixWord ++ tailWord_174444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174548 : List Nat := [2, 4, 1, 2, 2, 1, 2, 1, 6]
def baseStart_174548 : Nat := 118140960795 + 174548 * 2 ^ 59
def prefixEnd_174548 : Nat := 4983230072969 + 3 ^ 40 * 174548 * 2
def baseEnd_174548 : Nat := 39834231680483695043233

theorem tailTrace_174548 : CollatzResearch.WordTrace tailWord_174548 prefixEnd_174548 39834231680483695043233 := by
  unfold tailWord_174548
  simp only [CollatzResearch.WordTrace]
  refine ⟨3183144285824940635090149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4244192381099920846786865 3183144285824940635090149)
  ·
    refine ⟨596839553592176369079403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3183144285824940635090149 596839553592176369079403)
    ·
      refine ⟨895259330388264553619105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 596839553592176369079403 895259330388264553619105)
      ·
        refine ⟨671444497791198415214329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 895259330388264553619105 671444497791198415214329)
        ·
          refine ⟨503583373343398811410747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 671444497791198415214329 503583373343398811410747)
          ·
            refine ⟨755375060015098217116121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 503583373343398811410747 755375060015098217116121)
            ·
              refine ⟨566531295011323662837091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 755375060015098217116121 566531295011323662837091)
              ·
                refine ⟨849796942516985494255637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 566531295011323662837091 849796942516985494255637)
                ·
                  refine ⟨39834231680483695043233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 849796942516985494255637 39834231680483695043233)
                  ·
                    rfl

theorem cell21_174548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_174548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_174548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_174548 prefixEnd_174548 := by exact prefixLift 174548
  have htrace : WordTrace (prefixWord ++ tailWord_174548) baseStart_174548 baseEnd_174548 := by
    simpa [prefixWord, tailWord_174548, baseEnd_174548] using wordTrace_append hprefix tailTrace_174548
  have hstable : (prefixWord ++ tailWord_174548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174548).length < 2 ^ (prefixWord ++ tailWord_174548).sum := by decide
  have hdescent : baseEnd_174548 < baseStart_174548 := by decide
  rcases family_descends (prefixWord ++ tailWord_174548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174565 : List Nat := [1, 3, 1, 5, 2, 1, 1, 3, 4]
def baseStart_174565 : Nat := 118140960795 + 174565 * 2 ^ 59
def prefixEnd_174565 : Nat := 4983230072969 + 3 ^ 40 * 174565 * 2
def baseEnd_174565 : Nat := 39838111312095443259865

theorem tailTrace_174565 : CollatzResearch.WordTrace tailWord_174565 prefixEnd_174565 39838111312095443259865 := by
  unfold tailWord_174565
  simp only [CollatzResearch.WordTrace]
  refine ⟨6366908612588293173549149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4244605741725528782366099 6366908612588293173549149)
  ·
    refine ⟨2387590729720609940080931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6366908612588293173549149 2387590729720609940080931)
    ·
      refine ⟨3581386094580914910121397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2387590729720609940080931 3581386094580914910121397)
      ·
        refine ⟨335754946366960772823881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3581386094580914910121397 335754946366960772823881)
        ·
          refine ⟨251816209775220579617911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 335754946366960772823881 251816209775220579617911)
          ·
            refine ⟨377724314662830869426867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251816209775220579617911 377724314662830869426867)
            ·
              refine ⟨566586471994246304140301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 377724314662830869426867 566586471994246304140301)
              ·
                refine ⟨212469926997842364052613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 566586471994246304140301 212469926997842364052613)
                ·
                  refine ⟨39838111312095443259865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 212469926997842364052613 39838111312095443259865)
                  ·
                    rfl

theorem cell21_174565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 3, 4].length) (baseStart_174565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_174565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_174565 prefixEnd_174565 := by exact prefixLift 174565
  have htrace : WordTrace (prefixWord ++ tailWord_174565) baseStart_174565 baseEnd_174565 := by
    simpa [prefixWord, tailWord_174565, baseEnd_174565] using wordTrace_append hprefix tailTrace_174565
  have hstable : (prefixWord ++ tailWord_174565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174565).length < 2 ^ (prefixWord ++ tailWord_174565).sum := by decide
  have hdescent : baseEnd_174565 < baseStart_174565 := by decide
  rcases family_descends (prefixWord ++ tailWord_174565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174576 : List Nat := [2, 1, 1, 1, 3, 3, 2, 1, 7]
def baseStart_174576 : Nat := 118140960795 + 174576 * 2 ^ 59
def prefixEnd_174576 : Nat := 4983230072969 + 3 ^ 40 * 174576 * 2
def baseEnd_174576 : Nat := 39840621661961868576509

theorem tailTrace_174576 : CollatzResearch.WordTrace tailWord_174576 prefixEnd_174576 39840621661961868576509 := by
  unfold tailWord_174576
  simp only [CollatzResearch.WordTrace]
  refine ⟨3183654907774221026099791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4244873210365628034799721 3183654907774221026099791)
  ·
    refine ⟨4775482361661331539149687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3183654907774221026099791 4775482361661331539149687)
    ·
      refine ⟨7163223542491997308724531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4775482361661331539149687 7163223542491997308724531)
      ·
        refine ⟨10744835313737995963086797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7163223542491997308724531 10744835313737995963086797)
        ·
          refine ⟨4029313242651748486157549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10744835313737995963086797 4029313242651748486157549)
          ·
            refine ⟨1510992465994405682309081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4029313242651748486157549 1510992465994405682309081)
            ·
              refine ⟨1133244349495804261731811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1510992465994405682309081 1133244349495804261731811)
              ·
                refine ⟨1699866524243706392597717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1133244349495804261731811 1699866524243706392597717)
                ·
                  refine ⟨39840621661961868576509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1699866524243706392597717 39840621661961868576509)
                  ·
                    rfl

theorem cell21_174576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 7].length) (baseStart_174576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_174576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_174576 prefixEnd_174576 := by exact prefixLift 174576
  have htrace : WordTrace (prefixWord ++ tailWord_174576) baseStart_174576 baseEnd_174576 := by
    simpa [prefixWord, tailWord_174576, baseEnd_174576] using wordTrace_append hprefix tailTrace_174576
  have hstable : (prefixWord ++ tailWord_174576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174576).length < 2 ^ (prefixWord ++ tailWord_174576).sum := by decide
  have hdescent : baseEnd_174576 < baseStart_174576 := by decide
  rcases family_descends (prefixWord ++ tailWord_174576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174607 : List Nat := [1, 1, 2, 1, 1, 1, 2, 8, 4]
def baseStart_174607 : Nat := 118140960795 + 174607 * 2 ^ 59
def prefixEnd_174607 : Nat := 4983230072969 + 3 ^ 40 * 174607 * 2
def baseEnd_174607 : Nat := 39847696284312703559779

theorem tailTrace_174607 : CollatzResearch.WordTrace tailWord_174607 prefixEnd_174607 39847696284312703559779 := by
  unfold tailWord_174607
  simp only [CollatzResearch.WordTrace]
  refine ⟨6368440478436134346578075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4245626985624089564385383 6368440478436134346578075)
  ·
    refine ⟨9552660717654201519867113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6368440478436134346578075 9552660717654201519867113)
    ·
      refine ⟨7164495538240651139900335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9552660717654201519867113 7164495538240651139900335)
      ·
        refine ⟨10746743307360976709850503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7164495538240651139900335 10746743307360976709850503)
        ·
          refine ⟨16120114961041465064775755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10746743307360976709850503 16120114961041465064775755)
          ·
            refine ⟨24180172441562197597163633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16120114961041465064775755 24180172441562197597163633)
            ·
              refine ⟨18135129331171648197872725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24180172441562197597163633 18135129331171648197872725)
              ·
                refine ⟨212521046849667752318821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 18135129331171648197872725 212521046849667752318821)
                ·
                  refine ⟨39847696284312703559779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 212521046849667752318821 39847696284312703559779)
                  ·
                    rfl

theorem cell21_174607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 8, 4].length) (baseStart_174607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_174607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_174607 prefixEnd_174607 := by exact prefixLift 174607
  have htrace : WordTrace (prefixWord ++ tailWord_174607) baseStart_174607 baseEnd_174607 := by
    simpa [prefixWord, tailWord_174607, baseEnd_174607] using wordTrace_append hprefix tailTrace_174607
  have hstable : (prefixWord ++ tailWord_174607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174607).length < 2 ^ (prefixWord ++ tailWord_174607).sum := by decide
  have hdescent : baseEnd_174607 < baseStart_174607 := by decide
  rcases family_descends (prefixWord ++ tailWord_174607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174838 : List Nat := [5, 1, 1, 1, 1, 2, 1, 6, 3]
def baseStart_174838 : Nat := 118140960795 + 174838 * 2 ^ 59
def prefixEnd_174838 : Nat := 4983230072969 + 3 ^ 40 * 174838 * 2
def baseEnd_174838 : Nat := 39900413631507635209307

theorem tailTrace_174838 : CollatzResearch.WordTrace tailWord_174838 prefixEnd_174838 39900413631507635209307 := by
  unfold tailWord_174838
  simp only [CollatzResearch.WordTrace]
  refine ⟨398554108787453799889823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4251243827066173865491445 398554108787453799889823)
  ·
    refine ⟨597831163181180699834735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 398554108787453799889823 597831163181180699834735)
    ·
      refine ⟨896746744771771049752103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 597831163181180699834735 896746744771771049752103)
      ·
        refine ⟨1345120117157656574628155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 896746744771771049752103 1345120117157656574628155)
        ·
          refine ⟨2017680175736484861942233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1345120117157656574628155 2017680175736484861942233)
          ·
            refine ⟨1513260131802363646456675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2017680175736484861942233 1513260131802363646456675)
            ·
              refine ⟨2269890197703545469685013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1513260131802363646456675 2269890197703545469685013)
              ·
                refine ⟨106401103017353693891485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2269890197703545469685013 106401103017353693891485)
                ·
                  refine ⟨39900413631507635209307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106401103017353693891485 39900413631507635209307)
                  ·
                    rfl

theorem cell21_174838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_174838 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_174838 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_174838 prefixEnd_174838 := by exact prefixLift 174838
  have htrace : WordTrace (prefixWord ++ tailWord_174838) baseStart_174838 baseEnd_174838 := by
    simpa [prefixWord, tailWord_174838, baseEnd_174838] using wordTrace_append hprefix tailTrace_174838
  have hstable : (prefixWord ++ tailWord_174838).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174838).length < 2 ^ (prefixWord ++ tailWord_174838).sum := by decide
  have hdescent : baseEnd_174838 < baseStart_174838 := by decide
  rcases family_descends (prefixWord ++ tailWord_174838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174849 : List Nat := [1, 2, 4, 1, 1, 1, 1, 10]
def baseStart_174849 : Nat := 118140960795 + 174849 * 2 ^ 59
def prefixEnd_174849 : Nat := 4983230072969 + 3 ^ 40 * 174849 * 2
def baseEnd_174849 : Nat := 13300974660458020175317

theorem tailTrace_174849 : CollatzResearch.WordTrace tailWord_174849 prefixEnd_174849 13300974660458020175317 := by
  unfold tailWord_174849
  simp only [CollatzResearch.WordTrace]
  refine ⟨6377266943559409676887601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4251511295706273117925067 6377266943559409676887601)
  ·
    refine ⟨4782950207669557257665701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6377266943559409676887601 4782950207669557257665701)
    ·
      refine ⟨896803163938041985812319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4782950207669557257665701 896803163938041985812319)
      ·
        refine ⟨1345204745907062978718479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 896803163938041985812319 1345204745907062978718479)
        ·
          refine ⟨2017807118860594468077719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1345204745907062978718479 2017807118860594468077719)
          ·
            refine ⟨3026710678290891702116579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2017807118860594468077719 3026710678290891702116579)
            ·
              refine ⟨4540066017436337553174869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3026710678290891702116579 4540066017436337553174869)
              ·
                refine ⟨13300974660458020175317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 4540066017436337553174869 13300974660458020175317)
                ·
                  rfl

theorem cell21_174849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 10].length) (baseStart_174849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_174849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_174849 prefixEnd_174849 := by exact prefixLift 174849
  have htrace : WordTrace (prefixWord ++ tailWord_174849) baseStart_174849 baseEnd_174849 := by
    simpa [prefixWord, tailWord_174849, baseEnd_174849] using wordTrace_append hprefix tailTrace_174849
  have hstable : (prefixWord ++ tailWord_174849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174849).length < 2 ^ (prefixWord ++ tailWord_174849).sum := by decide
  have hdescent : baseEnd_174849 < baseStart_174849 := by decide
  rcases family_descends (prefixWord ++ tailWord_174849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174956 : List Nat := [2, 2, 1, 1, 4, 1, 2, 3, 5]
def baseStart_174956 : Nat := 118140960795 + 174956 * 2 ^ 59
def prefixEnd_174956 : Nat := 4983230072969 + 3 ^ 40 * 174956 * 2
def baseEnd_174956 : Nat := 39927342839165652242399

theorem tailTrace_174956 : CollatzResearch.WordTrace tailWord_174956 prefixEnd_174956 39927342839165652242399 := by
  unfold tailWord_174956
  simp only [CollatzResearch.WordTrace]
  refine ⟨3190584777085883475516361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4254113036114511300688481 3190584777085883475516361)
  ·
    refine ⟨2392938582814412606637271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3190584777085883475516361 2392938582814412606637271)
    ·
      refine ⟨3589407874221618909955907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2392938582814412606637271 3589407874221618909955907)
      ·
        refine ⟨5384111811332428364933861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3589407874221618909955907 5384111811332428364933861)
        ·
          refine ⟨1009520964624830318425099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5384111811332428364933861 1009520964624830318425099)
          ·
            refine ⟨1514281446937245477637649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1009520964624830318425099 1514281446937245477637649)
            ·
              refine ⟨1135711085202934108228237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1514281446937245477637649 1135711085202934108228237)
              ·
                refine ⟨425891656951100290585589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1135711085202934108228237 425891656951100290585589)
                ·
                  refine ⟨39927342839165652242399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 425891656951100290585589 39927342839165652242399)
                  ·
                    rfl

theorem cell21_174956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_174956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_174956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_174956 prefixEnd_174956 := by exact prefixLift 174956
  have htrace : WordTrace (prefixWord ++ tailWord_174956) baseStart_174956 baseEnd_174956 := by
    simpa [prefixWord, tailWord_174956, baseEnd_174956] using wordTrace_append hprefix tailTrace_174956
  have hstable : (prefixWord ++ tailWord_174956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174956).length < 2 ^ (prefixWord ++ tailWord_174956).sum := by decide
  have hdescent : baseEnd_174956 < baseStart_174956 := by decide
  rcases family_descends (prefixWord ++ tailWord_174956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174970 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 8]
def baseStart_174970 : Nat := 118140960795 + 174970 * 2 ^ 59
def prefixEnd_174970 : Nat := 4983230072969 + 3 ^ 40 * 174970 * 2
def baseEnd_174970 : Nat := 39930537829904739009037

theorem tailTrace_174970 : CollatzResearch.WordTrace tailWord_174970 prefixEnd_174970 39930537829904739009037 := by
  unfold tailWord_174970
  simp only [CollatzResearch.WordTrace]
  refine ⟨1595420044030261835510591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4254453450747364894694909 1595420044030261835510591)
  ·
    refine ⟨2393130066045392753265887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1595420044030261835510591 2393130066045392753265887)
    ·
      refine ⟨3589695099068089129898831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2393130066045392753265887 3589695099068089129898831)
      ·
        refine ⟨5384542648602133694848247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3589695099068089129898831 5384542648602133694848247)
        ·
          refine ⟨8076813972903200542272371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5384542648602133694848247 8076813972903200542272371)
          ·
            refine ⟨12115220959354800813408557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8076813972903200542272371 12115220959354800813408557)
            ·
              refine ⟨4543207859758050305028209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12115220959354800813408557 4543207859758050305028209)
              ·
                refine ⟨3407405894818537728771157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4543207859758050305028209 3407405894818537728771157)
                ·
                  refine ⟨39930537829904739009037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3407405894818537728771157 39930537829904739009037)
                  ·
                    rfl

theorem cell21_174970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_174970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_174970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_174970 prefixEnd_174970 := by exact prefixLift 174970
  have htrace : WordTrace (prefixWord ++ tailWord_174970) baseStart_174970 baseEnd_174970 := by
    simpa [prefixWord, tailWord_174970, baseEnd_174970] using wordTrace_append hprefix tailTrace_174970
  have hstable : (prefixWord ++ tailWord_174970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174970).length < 2 ^ (prefixWord ++ tailWord_174970).sum := by decide
  have hdescent : baseEnd_174970 < baseStart_174970 := by decide
  rcases family_descends (prefixWord ++ tailWord_174970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175004 : List Nat := [2, 2, 3, 3, 2, 1, 1, 1, 6]
def baseStart_175004 : Nat := 118140960795 + 175004 * 2 ^ 59
def prefixEnd_175004 : Nat := 4983230072969 + 3 ^ 40 * 175004 * 2
def baseEnd_175004 : Nat := 39938297093128235442301

theorem tailTrace_175004 : CollatzResearch.WordTrace tailWord_175004 prefixEnd_175004 39938297093128235442301 := by
  unfold tailWord_175004
  simp only [CollatzResearch.WordTrace]
  refine ⟨3191460128998935574390033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4255280171998580765853377 3191460128998935574390033)
  ·
    refine ⟨2393595096749201680792525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3191460128998935574390033 2393595096749201680792525)
    ·
      refine ⟨897598161280950630297197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2393595096749201680792525 897598161280950630297197)
      ·
        refine ⟨336599310480356486361449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 897598161280950630297197 336599310480356486361449)
        ·
          refine ⟨252449482860267364771087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 336599310480356486361449 252449482860267364771087)
          ·
            refine ⟨378674224290401047156631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252449482860267364771087 378674224290401047156631)
            ·
              refine ⟨568011336435601570734947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 378674224290401047156631 568011336435601570734947)
              ·
                refine ⟨852017004653402356102421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 568011336435601570734947 852017004653402356102421)
                ·
                  refine ⟨39938297093128235442301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 852017004653402356102421 39938297093128235442301)
                  ·
                    rfl

theorem cell21_175004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 6].length) (baseStart_175004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_175004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_175004 prefixEnd_175004 := by exact prefixLift 175004
  have htrace : WordTrace (prefixWord ++ tailWord_175004) baseStart_175004 baseEnd_175004 := by
    simpa [prefixWord, tailWord_175004, baseEnd_175004] using wordTrace_append hprefix tailTrace_175004
  have hstable : (prefixWord ++ tailWord_175004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175004).length < 2 ^ (prefixWord ++ tailWord_175004).sum := by decide
  have hdescent : baseEnd_175004 < baseStart_175004 := by decide
  rcases family_descends (prefixWord ++ tailWord_175004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175032 : List Nat := [2, 1, 2, 1, 2, 4, 2, 2, 5]
def baseStart_175032 : Nat := 118140960795 + 175032 * 2 ^ 59
def prefixEnd_175032 : Nat := 4983230072969 + 3 ^ 40 * 175032 * 2
def baseEnd_175032 : Nat := 39944687074606408975577

theorem tailTrace_175032 : CollatzResearch.WordTrace tailWord_175032 prefixEnd_175032 39944687074606408975577 := by
  unfold tailWord_175032
  simp only [CollatzResearch.WordTrace]
  refine ⟨3191970750948215965399675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4255961001264287953866233 3191970750948215965399675)
  ·
    refine ⟨4787956126422323948099513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3191970750948215965399675 4787956126422323948099513)
    ·
      refine ⟨3590967094816742961074635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4787956126422323948099513 3590967094816742961074635)
      ·
        refine ⟨5386450642225114441611953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3590967094816742961074635 5386450642225114441611953)
        ·
          refine ⟨4039837981668835831208965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5386450642225114441611953 4039837981668835831208965)
          ·
            refine ⟨757469621562906718351681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4039837981668835831208965 757469621562906718351681)
            ·
              refine ⟨568102216172180038763761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 757469621562906718351681 568102216172180038763761)
              ·
                refine ⟨426076662129135029072821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 568102216172180038763761 426076662129135029072821)
                ·
                  refine ⟨39944687074606408975577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 426076662129135029072821 39944687074606408975577)
                  ·
                    rfl

theorem cell21_175032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 5].length) (baseStart_175032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_175032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_175032 prefixEnd_175032 := by exact prefixLift 175032
  have htrace : WordTrace (prefixWord ++ tailWord_175032) baseStart_175032 baseEnd_175032 := by
    simpa [prefixWord, tailWord_175032, baseEnd_175032] using wordTrace_append hprefix tailTrace_175032
  have hstable : (prefixWord ++ tailWord_175032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175032).length < 2 ^ (prefixWord ++ tailWord_175032).sum := by decide
  have hdescent : baseEnd_175032 < baseStart_175032 := by decide
  rcases family_descends (prefixWord ++ tailWord_175032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175080 : List Nat := [2, 1, 4, 1, 1, 1, 6, 1, 4]
def baseStart_175080 : Nat := 118140960795 + 175080 * 2 ^ 59
def prefixEnd_175080 : Nat := 4983230072969 + 3 ^ 40 * 175080 * 2
def baseEnd_175080 : Nat := 39955641328568992175479

theorem tailTrace_175080 : CollatzResearch.WordTrace tailWord_175080 prefixEnd_175080 39955641328568992175479 := by
  unfold tailWord_175080
  simp only [CollatzResearch.WordTrace]
  refine ⟨3192846102861268064273347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4257128137148357419031129 3192846102861268064273347)
  ·
    refine ⟨4789269154291902096410021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3192846102861268064273347 4789269154291902096410021)
    ·
      refine ⟨897987966429731643076879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4789269154291902096410021 897987966429731643076879)
      ·
        refine ⟨1346981949644597464615319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 897987966429731643076879 1346981949644597464615319)
        ·
          refine ⟨2020472924466896196922979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1346981949644597464615319 2020472924466896196922979)
          ·
            refine ⟨3030709386700344295384469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2020472924466896196922979 3030709386700344295384469)
            ·
              refine ⟨142064502501578638846147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3030709386700344295384469 142064502501578638846147)
              ·
                refine ⟨213096753752367958269221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142064502501578638846147 213096753752367958269221)
                ·
                  refine ⟨39955641328568992175479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 213096753752367958269221 39955641328568992175479)
                  ·
                    rfl

theorem cell21_175080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 1, 4].length) (baseStart_175080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_175080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_175080 prefixEnd_175080 := by exact prefixLift 175080
  have htrace : WordTrace (prefixWord ++ tailWord_175080) baseStart_175080 baseEnd_175080 := by
    simpa [prefixWord, tailWord_175080, baseEnd_175080] using wordTrace_append hprefix tailTrace_175080
  have hstable : (prefixWord ++ tailWord_175080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175080).length < 2 ^ (prefixWord ++ tailWord_175080).sum := by decide
  have hdescent : baseEnd_175080 < baseStart_175080 := by decide
  rcases family_descends (prefixWord ++ tailWord_175080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175094 : List Nat := [5, 1, 1, 1, 3, 1, 2, 7]
def baseStart_175094 : Nat := 118140960795 + 175094 * 2 ^ 59
def prefixEnd_175094 : Nat := 4983230072969 + 3 ^ 40 * 175094 * 2
def baseEnd_175094 : Nat := 13319612106436026314039

theorem tailTrace_175094 : CollatzResearch.WordTrace tailWord_175094 prefixEnd_175094 13319612106436026314039 := by
  unfold tailWord_175094
  simp only [CollatzResearch.WordTrace]
  refine ⟨399137676729488532472271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4257468551781211013037557 399137676729488532472271)
  ·
    refine ⟨598706515094232798708407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 399137676729488532472271 598706515094232798708407)
    ·
      refine ⟨898059772641349198062611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 598706515094232798708407 898059772641349198062611)
      ·
        refine ⟨1347089658962023797093917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 898059772641349198062611 1347089658962023797093917)
        ·
          refine ⟨505158622110758923910219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1347089658962023797093917 505158622110758923910219)
          ·
            refine ⟨757737933166138385865329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 505158622110758923910219 757737933166138385865329)
            ·
              refine ⟨568303449874603789398997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 757737933166138385865329 568303449874603789398997)
              ·
                refine ⟨13319612106436026314039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 568303449874603789398997 13319612106436026314039)
                ·
                  rfl

theorem cell21_175094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_175094 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_175094 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_175094 prefixEnd_175094 := by exact prefixLift 175094
  have htrace : WordTrace (prefixWord ++ tailWord_175094) baseStart_175094 baseEnd_175094 := by
    simpa [prefixWord, tailWord_175094, baseEnd_175094] using wordTrace_append hprefix tailTrace_175094
  have hstable : (prefixWord ++ tailWord_175094).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175094).length < 2 ^ (prefixWord ++ tailWord_175094).sum := by decide
  have hdescent : baseEnd_175094 < baseStart_175094 := by decide
  rcases family_descends (prefixWord ++ tailWord_175094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175139 : List Nat := [1, 1, 1, 4, 3, 2, 2, 3, 4]
def baseStart_175139 : Nat := 118140960795 + 175139 * 2 ^ 59
def prefixEnd_175139 : Nat := 4983230072969 + 3 ^ 40 * 175139 * 2
def baseEnd_175139 : Nat := 39969105932398000692025

theorem tailTrace_175139 : CollatzResearch.WordTrace tailWord_175139 prefixEnd_175139 39969105932398000692025 := by
  unfold tailWord_175139
  simp only [CollatzResearch.WordTrace]
  refine ⟨6387844112508789204944471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4258562741672526136629647 6387844112508789204944471)
  ·
    refine ⟨9581766168763183807416707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6387844112508789204944471 9581766168763183807416707)
    ·
      refine ⟨14372649253144775711125061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9581766168763183807416707 14372649253144775711125061)
      ·
        refine ⟨2694871734964645445835949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14372649253144775711125061 2694871734964645445835949)
        ·
          refine ⟨1010576900611742042188481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2694871734964645445835949 1010576900611742042188481)
          ·
            refine ⟨757932675458806531641361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1010576900611742042188481 757932675458806531641361)
            ·
              refine ⟨568449506594104898731021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 757932675458806531641361 568449506594104898731021)
              ·
                refine ⟨213168564972789337024133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 568449506594104898731021 213168564972789337024133)
                ·
                  refine ⟨39969105932398000692025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 213168564972789337024133 39969105932398000692025)
                  ·
                    rfl

theorem cell21_175139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 3, 4].length) (baseStart_175139 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_175139 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_175139 prefixEnd_175139 := by exact prefixLift 175139
  have htrace : WordTrace (prefixWord ++ tailWord_175139) baseStart_175139 baseEnd_175139 := by
    simpa [prefixWord, tailWord_175139, baseEnd_175139] using wordTrace_append hprefix tailTrace_175139
  have hstable : (prefixWord ++ tailWord_175139).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175139).length < 2 ^ (prefixWord ++ tailWord_175139).sum := by decide
  have hdescent : baseEnd_175139 < baseStart_175139 := by decide
  rcases family_descends (prefixWord ++ tailWord_175139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175167 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 9]
def baseStart_175167 : Nat := 118140960795 + 175167 * 2 ^ 59
def prefixEnd_175167 : Nat := 4983230072969 + 3 ^ 40 * 175167 * 2
def baseEnd_175167 : Nat := 39975495913876174225301

theorem tailTrace_175167 : CollatzResearch.WordTrace tailWord_175167 prefixEnd_175167 39975495913876174225301 := by
  unfold tailWord_175167
  simp only [CollatzResearch.WordTrace]
  refine ⟨6388865356407349986963755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4259243570938233324642503 6388865356407349986963755)
  ·
    refine ⟨9583298034611024980445633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6388865356407349986963755 9583298034611024980445633)
    ·
      refine ⟨7187473525958268735334225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9583298034611024980445633 7187473525958268735334225)
      ·
        refine ⟨5390605144468701551500669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7187473525958268735334225 5390605144468701551500669)
        ·
          refine ⟨2021476929175763081812751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5390605144468701551500669 2021476929175763081812751)
          ·
            refine ⟨3032215393763644622719127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2021476929175763081812751 3032215393763644622719127)
            ·
              refine ⟨4548323090645466934078691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3032215393763644622719127 4548323090645466934078691)
              ·
                refine ⟨6822484635968200401118037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4548323090645466934078691 6822484635968200401118037)
                ·
                  refine ⟨39975495913876174225301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 6822484635968200401118037 39975495913876174225301)
                  ·
                    rfl

theorem cell21_175167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 9].length) (baseStart_175167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_175167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_175167 prefixEnd_175167 := by exact prefixLift 175167
  have htrace : WordTrace (prefixWord ++ tailWord_175167) baseStart_175167 baseEnd_175167 := by
    simpa [prefixWord, tailWord_175167, baseEnd_175167] using wordTrace_append hprefix tailTrace_175167
  have hstable : (prefixWord ++ tailWord_175167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175167).length < 2 ^ (prefixWord ++ tailWord_175167).sum := by decide
  have hdescent : baseEnd_175167 < baseStart_175167 := by decide
  rcases family_descends (prefixWord ++ tailWord_175167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175246 : List Nat := [4, 1, 1, 3, 2, 2, 2, 6]
def baseStart_175246 : Nat := 118140960795 + 175246 * 2 ^ 59
def prefixEnd_175246 : Nat := 4983230072969 + 3 ^ 40 * 175246 * 2
def baseEnd_175246 : Nat := 13331174930063197469491

theorem tailTrace_175246 : CollatzResearch.WordTrace tailWord_175246 prefixEnd_175246 13331174930063197469491 := by
  unfold tailWord_175246
  simp only [CollatzResearch.WordTrace]
  refine ⟨798968340390143309886199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4261164482080764319393061 798968340390143309886199)
  ·
    refine ⟨1198452510585214964829299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 798968340390143309886199 1198452510585214964829299)
    ·
      refine ⟨1797678765877822447243949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1198452510585214964829299 1797678765877822447243949)
      ·
        refine ⟨674129537204183417716481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1797678765877822447243949 674129537204183417716481)
        ·
          refine ⟨505597152903137563287361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 674129537204183417716481 505597152903137563287361)
          ·
            refine ⟨379197864677353172465521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 505597152903137563287361 379197864677353172465521)
            ·
              refine ⟨284398398508014879349141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 379197864677353172465521 284398398508014879349141)
              ·
                refine ⟨13331174930063197469491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 284398398508014879349141 13331174930063197469491)
                ·
                  rfl

theorem cell21_175246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_175246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_175246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_175246 prefixEnd_175246 := by exact prefixLift 175246
  have htrace : WordTrace (prefixWord ++ tailWord_175246) baseStart_175246 baseEnd_175246 := by
    simpa [prefixWord, tailWord_175246, baseEnd_175246] using wordTrace_append hprefix tailTrace_175246
  have hstable : (prefixWord ++ tailWord_175246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175246).length < 2 ^ (prefixWord ++ tailWord_175246).sum := by decide
  have hdescent : baseEnd_175246 < baseStart_175246 := by decide
  rcases family_descends (prefixWord ++ tailWord_175246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175286 : List Nat := [5, 1, 3, 2, 2, 1, 2, 2, 3]
def baseStart_175286 : Nat := 118140960795 + 175286 * 2 ^ 59
def prefixEnd_175286 : Nat := 4983230072969 + 3 ^ 40 * 175286 * 2
def baseEnd_175286 : Nat := 40002653335158411741725

theorem tailTrace_175286 : CollatzResearch.WordTrace tailWord_175286 prefixEnd_175286 40002653335158411741725 := by
  unfold tailWord_175286
  simp only [CollatzResearch.WordTrace]
  refine ⟨399575352686014581909107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4262137095317488873697141 399575352686014581909107)
  ·
    refine ⟨599363029029021872863661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 399575352686014581909107 599363029029021872863661)
    ·
      refine ⟨224761135885883202323873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 599363029029021872863661 224761135885883202323873)
      ·
        refine ⟨168570851914412401742905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224761135885883202323873 168570851914412401742905)
        ·
          refine ⟨126428138935809301307179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168570851914412401742905 126428138935809301307179)
          ·
            refine ⟨189642208403713951960769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126428138935809301307179 189642208403713951960769)
            ·
              refine ⟨142231656302785463970577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189642208403713951960769 142231656302785463970577)
              ·
                refine ⟨106673742227089097977933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142231656302785463970577 106673742227089097977933)
                ·
                  refine ⟨40002653335158411741725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106673742227089097977933 40002653335158411741725)
                  ·
                    rfl

theorem cell21_175286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_175286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_175286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_175286 prefixEnd_175286 := by exact prefixLift 175286
  have htrace : WordTrace (prefixWord ++ tailWord_175286) baseStart_175286 baseEnd_175286 := by
    simpa [prefixWord, tailWord_175286, baseEnd_175286] using wordTrace_append hprefix tailTrace_175286
  have hstable : (prefixWord ++ tailWord_175286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175286).length < 2 ^ (prefixWord ++ tailWord_175286).sum := by decide
  have hdescent : baseEnd_175286 < baseStart_175286 := by decide
  rcases family_descends (prefixWord ++ tailWord_175286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175294 : List Nat := [4, 2, 1, 1, 3, 2, 1, 4, 3]
def baseStart_175294 : Nat := 118140960795 + 175294 * 2 ^ 59
def prefixEnd_175294 : Nat := 4983230072969 + 3 ^ 40 * 175294 * 2
def baseEnd_175294 : Nat := 40004479044152175608375

theorem tailTrace_175294 : CollatzResearch.WordTrace tailWord_175294 prefixEnd_175294 40004479044152175608375 := by
  unfold tailWord_175294
  simp only [CollatzResearch.WordTrace]
  refine ⟨799187178368406334604617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4262331617964833784557957 799187178368406334604617)
  ·
    refine ⟨599390383776304750953463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 799187178368406334604617 599390383776304750953463)
    ·
      refine ⟨899085575664457126430195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 599390383776304750953463 899085575664457126430195)
      ·
        refine ⟨1348628363496685689645293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 899085575664457126430195 1348628363496685689645293)
        ·
          refine ⟨505735636311257133616985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1348628363496685689645293 505735636311257133616985)
          ·
            refine ⟨379301727233442850212739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 505735636311257133616985 379301727233442850212739)
            ·
              refine ⟨568952590850164275319109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 379301727233442850212739 568952590850164275319109)
              ·
                refine ⟨106678610784405801622333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 568952590850164275319109 106678610784405801622333)
                ·
                  refine ⟨40004479044152175608375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106678610784405801622333 40004479044152175608375)
                  ·
                    rfl

theorem cell21_175294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_175294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_175294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_175294 prefixEnd_175294 := by exact prefixLift 175294
  have htrace : WordTrace (prefixWord ++ tailWord_175294) baseStart_175294 baseEnd_175294 := by
    simpa [prefixWord, tailWord_175294, baseEnd_175294] using wordTrace_append hprefix tailTrace_175294
  have hstable : (prefixWord ++ tailWord_175294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175294).length < 2 ^ (prefixWord ++ tailWord_175294).sum := by decide
  have hdescent : baseEnd_175294 < baseStart_175294 := by decide
  rcases family_descends (prefixWord ++ tailWord_175294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175319 : List Nat := [1, 1, 3, 2, 1, 2, 3, 1, 7]
def baseStart_175319 : Nat := 118140960795 + 175319 * 2 ^ 59
def prefixEnd_175319 : Nat := 4983230072969 + 3 ^ 40 * 175319 * 2
def baseEnd_175319 : Nat := 40010184384757687691657

theorem tailTrace_175319 : CollatzResearch.WordTrace tailWord_175319 prefixEnd_175319 40010184384757687691657 := by
  unfold tailWord_175319
  simp only [CollatzResearch.WordTrace]
  refine ⟨6394409251856679946497011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4262939501237786630998007 6394409251856679946497011)
  ·
    refine ⟨9591613877785019919745517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6394409251856679946497011 9591613877785019919745517)
    ·
      refine ⟨3596855204169382469904569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9591613877785019919745517 3596855204169382469904569)
      ·
        refine ⟨2697641403127036852428427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3596855204169382469904569 2697641403127036852428427)
        ·
          refine ⟨4046462104690555278642641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2697641403127036852428427 4046462104690555278642641)
          ·
            refine ⟨3034846578517916458981981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4046462104690555278642641 3034846578517916458981981)
            ·
              refine ⟨1138067466944218672118243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3034846578517916458981981 1138067466944218672118243)
              ·
                refine ⟨1707101200416328008177365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1138067466944218672118243 1707101200416328008177365)
                ·
                  refine ⟨40010184384757687691657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1707101200416328008177365 40010184384757687691657)
                  ·
                    rfl

theorem cell21_175319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 7].length) (baseStart_175319 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_175319 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_175319 prefixEnd_175319 := by exact prefixLift 175319
  have htrace : WordTrace (prefixWord ++ tailWord_175319) baseStart_175319 baseEnd_175319 := by
    simpa [prefixWord, tailWord_175319, baseEnd_175319] using wordTrace_append hprefix tailTrace_175319
  have hstable : (prefixWord ++ tailWord_175319).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175319).length < 2 ^ (prefixWord ++ tailWord_175319).sum := by decide
  have hdescent : baseEnd_175319 < baseStart_175319 := by decide
  rcases family_descends (prefixWord ++ tailWord_175319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175440 : List Nat := [2, 1, 1, 1, 1, 5, 1, 9]
def baseStart_175440 : Nat := 118140960795 + 175440 * 2 ^ 59
def prefixEnd_175440 : Nat := 4983230072969 + 3 ^ 40 * 175440 * 2
def baseEnd_175440 : Nat := 13345932744429455391581

theorem tailTrace_175440 : CollatzResearch.WordTrace tailWord_175440 prefixEnd_175440 13345932744429455391581 := by
  unfold tailWord_175440
  simp only [CollatzResearch.WordTrace]
  refine ⟨3199411242209158805825887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4265881656278878407767849 3199411242209158805825887)
  ·
    refine ⟨4799116863313738208738831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3199411242209158805825887 4799116863313738208738831)
    ·
      refine ⟨7198675294970607313108247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4799116863313738208738831 7198675294970607313108247)
      ·
        refine ⟨10798012942455910969662371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7198675294970607313108247 10798012942455910969662371)
        ·
          refine ⟨16197019413683866454493557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10798012942455910969662371 16197019413683866454493557)
          ·
            refine ⟨1518470570032862480108771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16197019413683866454493557 1518470570032862480108771)
            ·
              refine ⟨2277705855049293720163157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1518470570032862480108771 2277705855049293720163157)
              ·
                refine ⟨13345932744429455391581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2277705855049293720163157 13345932744429455391581)
                ·
                  rfl

theorem cell21_175440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 9].length) (baseStart_175440 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_175440 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_175440 prefixEnd_175440 := by exact prefixLift 175440
  have htrace : WordTrace (prefixWord ++ tailWord_175440) baseStart_175440 baseEnd_175440 := by
    simpa [prefixWord, tailWord_175440, baseEnd_175440] using wordTrace_append hprefix tailTrace_175440
  have hstable : (prefixWord ++ tailWord_175440).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175440).length < 2 ^ (prefixWord ++ tailWord_175440).sum := by decide
  have hdescent : baseEnd_175440 < baseStart_175440 := by decide
  rcases family_descends (prefixWord ++ tailWord_175440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175463 : List Nat := [1, 1, 5, 1, 4, 2, 2, 2, 3]
def baseStart_175463 : Nat := 118140960795 + 175463 * 2 ^ 59
def prefixEnd_175463 : Nat := 4983230072969 + 3 ^ 40 * 175463 * 2
def baseEnd_175463 : Nat := 40043047146645437291363

theorem tailTrace_175463 : CollatzResearch.WordTrace tailWord_175463 prefixEnd_175463 40043047146645437291363 := by
  unfold tailWord_175463
  simp only [CollatzResearch.WordTrace]
  refine ⟨6399661363334992539739043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4266440908889995026492695 6399661363334992539739043)
  ·
    refine ⟨9599492045002488809608565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6399661363334992539739043 9599492045002488809608565)
    ·
      refine ⟨899952379218983325900803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9599492045002488809608565 899952379218983325900803)
      ·
        refine ⟨1349928568828474988851205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 899952379218983325900803 1349928568828474988851205)
        ·
          refine ⟨253111606655339060409601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1349928568828474988851205 253111606655339060409601)
          ·
            refine ⟨189833704991504295307201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253111606655339060409601 189833704991504295307201)
            ·
              refine ⟨142375278743628221480401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189833704991504295307201 142375278743628221480401)
              ·
                refine ⟨106781459057721166110301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142375278743628221480401 106781459057721166110301)
                ·
                  refine ⟨40043047146645437291363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106781459057721166110301 40043047146645437291363)
                  ·
                    rfl

theorem cell21_175463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 2, 3].length) (baseStart_175463 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_175463 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_175463 prefixEnd_175463 := by exact prefixLift 175463
  have htrace : WordTrace (prefixWord ++ tailWord_175463) baseStart_175463 baseEnd_175463 := by
    simpa [prefixWord, tailWord_175463, baseEnd_175463] using wordTrace_append hprefix tailTrace_175463
  have hstable : (prefixWord ++ tailWord_175463).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175463).length < 2 ^ (prefixWord ++ tailWord_175463).sum := by decide
  have hdescent : baseEnd_175463 < baseStart_175463 := by decide
  rcases family_descends (prefixWord ++ tailWord_175463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175471 : List Nat := [1, 1, 2, 1, 3, 1, 4, 3, 5]
def baseStart_175471 : Nat := 118140960795 + 175471 * 2 ^ 59
def prefixEnd_175471 : Nat := 4983230072969 + 3 ^ 40 * 175471 * 2
def baseEnd_175471 : Nat := 40044872855639201158013

theorem tailTrace_175471 : CollatzResearch.WordTrace tailWord_175471 prefixEnd_175471 40044872855639201158013 := by
  unfold tailWord_175471
  simp only [CollatzResearch.WordTrace]
  refine ⟨6399953147306009906030267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4266635431537339937353511 6399953147306009906030267)
  ·
    refine ⟨9599929720959014859045401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6399953147306009906030267 9599929720959014859045401)
    ·
      refine ⟨7199947290719261144284051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9599929720959014859045401 7199947290719261144284051)
      ·
        refine ⟨10799920936078891716426077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7199947290719261144284051 10799920936078891716426077)
        ·
          refine ⟨4049970351029584393659779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10799920936078891716426077 4049970351029584393659779)
          ·
            refine ⟨6074955526544376590489669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4049970351029584393659779 6074955526544376590489669)
            ·
              refine ⟨1139054161227070610716813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6074955526544376590489669 1139054161227070610716813)
              ·
                refine ⟨427145310460151479018805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1139054161227070610716813 427145310460151479018805)
                ·
                  refine ⟨40044872855639201158013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 427145310460151479018805 40044872855639201158013)
                  ·
                    rfl

theorem cell21_175471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 5].length) (baseStart_175471 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_175471 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_175471 prefixEnd_175471 := by exact prefixLift 175471
  have htrace : WordTrace (prefixWord ++ tailWord_175471) baseStart_175471 baseEnd_175471 := by
    simpa [prefixWord, tailWord_175471, baseEnd_175471] using wordTrace_append hprefix tailTrace_175471
  have hstable : (prefixWord ++ tailWord_175471).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175471).length < 2 ^ (prefixWord ++ tailWord_175471).sum := by decide
  have hdescent : baseEnd_175471 < baseStart_175471 := by decide
  rcases family_descends (prefixWord ++ tailWord_175471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175519 : List Nat := [1, 1, 2, 5, 1, 2, 3, 2, 4]
def baseStart_175519 : Nat := 118140960795 + 175519 * 2 ^ 59
def prefixEnd_175519 : Nat := 4983230072969 + 3 ^ 40 * 175519 * 2
def baseEnd_175519 : Nat := 40055827109601784357915

theorem tailTrace_175519 : CollatzResearch.WordTrace tailWord_175519 prefixEnd_175519 40055827109601784357915 := by
  unfold tailWord_175519
  simp only [CollatzResearch.WordTrace]
  refine ⟨6401703851132114103777611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4267802567421409402518407 6401703851132114103777611)
  ·
    refine ⟨9602555776698171155666417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6401703851132114103777611 9602555776698171155666417)
    ·
      refine ⟨7201916832523628366749813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9602555776698171155666417 7201916832523628366749813)
      ·
        refine ⟨675179703049090159382795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7201916832523628366749813 675179703049090159382795)
        ·
          refine ⟨1012769554573635239074193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 675179703049090159382795 1012769554573635239074193)
          ·
            refine ⟨759577165930226429305645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1012769554573635239074193 759577165930226429305645)
            ·
              refine ⟨284841437223834910989617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 759577165930226429305645 284841437223834910989617)
              ·
                refine ⟨213631077917876183242213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 284841437223834910989617 213631077917876183242213)
                ·
                  refine ⟨40055827109601784357915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 213631077917876183242213 40055827109601784357915)
                  ·
                    rfl

theorem cell21_175519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 2, 4].length) (baseStart_175519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_175519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_175519 prefixEnd_175519 := by exact prefixLift 175519
  have htrace : WordTrace (prefixWord ++ tailWord_175519) baseStart_175519 baseEnd_175519 := by
    simpa [prefixWord, tailWord_175519, baseEnd_175519] using wordTrace_append hprefix tailTrace_175519
  have hstable : (prefixWord ++ tailWord_175519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175519).length < 2 ^ (prefixWord ++ tailWord_175519).sum := by decide
  have hdescent : baseEnd_175519 < baseStart_175519 := by decide
  rcases family_descends (prefixWord ++ tailWord_175519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175578 : List Nat := [3, 1, 1, 2, 3, 2, 2, 1, 6]
def baseStart_175578 : Nat := 118140960795 + 175578 * 2 ^ 59
def prefixEnd_175578 : Nat := 4983230072969 + 3 ^ 40 * 175578 * 2
def baseEnd_175578 : Nat := 40069291713430792874461

theorem tailTrace_175578 : CollatzResearch.WordTrace tailWord_175578 prefixEnd_175578 40069291713430792874461 := by
  unfold tailWord_175578
  simp only [CollatzResearch.WordTrace]
  refine ⟨1600963939479591795043847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4269237171945578120116925 1600963939479591795043847)
  ·
    refine ⟨2401445909219387692565771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1600963939479591795043847 2401445909219387692565771)
    ·
      refine ⟨3602168863829081538848657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2401445909219387692565771 3602168863829081538848657)
      ·
        refine ⟨2701626647871811154136493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3602168863829081538848657 2701626647871811154136493)
        ·
          refine ⟨1013109992951929182801185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2701626647871811154136493 1013109992951929182801185)
          ·
            refine ⟨759832494713946887100889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1013109992951929182801185 759832494713946887100889)
            ·
              refine ⟨569874371035460165325667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 759832494713946887100889 569874371035460165325667)
              ·
                refine ⟨854811556553190247988501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 569874371035460165325667 854811556553190247988501)
                ·
                  refine ⟨40069291713430792874461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 854811556553190247988501 40069291713430792874461)
                  ·
                    rfl

theorem cell21_175578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_175578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_175578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_175578 prefixEnd_175578 := by exact prefixLift 175578
  have htrace : WordTrace (prefixWord ++ tailWord_175578) baseStart_175578 baseEnd_175578 := by
    simpa [prefixWord, tailWord_175578, baseEnd_175578] using wordTrace_append hprefix tailTrace_175578
  have hstable : (prefixWord ++ tailWord_175578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175578).length < 2 ^ (prefixWord ++ tailWord_175578).sum := by decide
  have hdescent : baseEnd_175578 < baseStart_175578 := by decide
  rcases family_descends (prefixWord ++ tailWord_175578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175581 : List Nat := [1, 4, 3, 1, 1, 4, 1, 1, 5]
def baseStart_175581 : Nat := 118140960795 + 175581 * 2 ^ 59
def prefixEnd_175581 : Nat := 4983230072969 + 3 ^ 40 * 175581 * 2
def baseEnd_175581 : Nat := 40069976354303454324455

theorem tailTrace_175581 : CollatzResearch.WordTrace tailWord_175581 prefixEnd_175581 40069976354303454324455 := by
  unfold tailWord_175581
  simp only [CollatzResearch.WordTrace]
  refine ⟨6403965176907498692534597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4269310117938332461689731 6403965176907498692534597)
  ·
    refine ⟨1200743470670156004850237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6403965176907498692534597 1200743470670156004850237)
    ·
      refine ⟨450278801501308501818839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1200743470670156004850237 450278801501308501818839)
      ·
        refine ⟨675418202251962752728259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 450278801501308501818839 675418202251962752728259)
        ·
          refine ⟨1013127303377944129092389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 675418202251962752728259 1013127303377944129092389)
          ·
            refine ⟨189961369383364524204823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1013127303377944129092389 189961369383364524204823)
            ·
              refine ⟨284942054075046786307235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189961369383364524204823 284942054075046786307235)
              ·
                refine ⟨427413081112570179460853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 284942054075046786307235 427413081112570179460853)
                ·
                  refine ⟨40069976354303454324455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 427413081112570179460853 40069976354303454324455)
                  ·
                    rfl

theorem cell21_175581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_175581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_175581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_175581 prefixEnd_175581 := by exact prefixLift 175581
  have htrace : WordTrace (prefixWord ++ tailWord_175581) baseStart_175581 baseEnd_175581 := by
    simpa [prefixWord, tailWord_175581, baseEnd_175581] using wordTrace_append hprefix tailTrace_175581
  have hstable : (prefixWord ++ tailWord_175581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175581).length < 2 ^ (prefixWord ++ tailWord_175581).sum := by decide
  have hdescent : baseEnd_175581 < baseStart_175581 := by decide
  rcases family_descends (prefixWord ++ tailWord_175581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175730 : List Nat := [3, 2, 1, 2, 3, 1, 1, 2, 6]
def baseStart_175730 : Nat := 118140960795 + 175730 * 2 ^ 59
def prefixEnd_175730 : Nat := 4983230072969 + 3 ^ 40 * 175730 * 2
def baseEnd_175730 : Nat := 40103980184312306340817

theorem tailTrace_175730 : CollatzResearch.WordTrace tailWord_175730 prefixEnd_175730 40103980184312306340817 := by
  unfold tailWord_175730
  simp only [CollatzResearch.WordTrace]
  refine ⟨1602349913341924284927161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4272933102245131426472429 1602349913341924284927161)
  ·
    refine ⟨1201762435006443213695371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1602349913341924284927161 1201762435006443213695371)
    ·
      refine ⟨1802643652509664820543057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1201762435006443213695371 1802643652509664820543057)
      ·
        refine ⟨1351982739382248615407293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1802643652509664820543057 1351982739382248615407293)
        ·
          refine ⟨506993527268343230777735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1351982739382248615407293 506993527268343230777735)
          ·
            refine ⟨760490290902514846166603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 506993527268343230777735 760490290902514846166603)
            ·
              refine ⟨1140735436353772269249905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 760490290902514846166603 1140735436353772269249905)
              ·
                refine ⟨855551577265329201937429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1140735436353772269249905 855551577265329201937429)
                ·
                  refine ⟨40103980184312306340817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 855551577265329201937429 40103980184312306340817)
                  ·
                    rfl

theorem cell21_175730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_175730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_175730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_175730 prefixEnd_175730 := by exact prefixLift 175730
  have htrace : WordTrace (prefixWord ++ tailWord_175730) baseStart_175730 baseEnd_175730 := by
    simpa [prefixWord, tailWord_175730, baseEnd_175730] using wordTrace_append hprefix tailTrace_175730
  have hstable : (prefixWord ++ tailWord_175730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175730).length < 2 ^ (prefixWord ++ tailWord_175730).sum := by decide
  have hdescent : baseEnd_175730 < baseStart_175730 := by decide
  rcases family_descends (prefixWord ++ tailWord_175730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175764 : List Nat := [2, 4, 2, 2, 2, 1, 1, 3, 4]
def baseStart_175764 : Nat := 118140960795 + 175764 * 2 ^ 59
def prefixEnd_175764 : Nat := 4983230072969 + 3 ^ 40 * 175764 * 2
def baseEnd_175764 : Nat := 40111739447535802774081

theorem tailTrace_175764 : CollatzResearch.WordTrace tailWord_175764 prefixEnd_175764 40111739447535802774081 := by
  unfold tailWord_175764
  simp only [CollatzResearch.WordTrace]
  refine ⟨3205319867622260473223173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4273759823496347297630897 3205319867622260473223173)
  ·
    refine ⟨600997475179173838729345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3205319867622260473223173 600997475179173838729345)
    ·
      refine ⟨450748106384380379047009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 600997475179173838729345 450748106384380379047009)
      ·
        refine ⟨338061079788285284285257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 450748106384380379047009 338061079788285284285257)
        ·
          refine ⟨253545809841213963213943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 338061079788285284285257 253545809841213963213943)
          ·
            refine ⟨380318714761820944820915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253545809841213963213943 380318714761820944820915)
            ·
              refine ⟨570478072142731417231373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 380318714761820944820915 570478072142731417231373)
              ·
                refine ⟨213929277053524281461765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 570478072142731417231373 213929277053524281461765)
                ·
                  refine ⟨40111739447535802774081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 213929277053524281461765 40111739447535802774081)
                  ·
                    rfl

theorem cell21_175764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_175764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_175764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_175764 prefixEnd_175764 := by exact prefixLift 175764
  have htrace : WordTrace (prefixWord ++ tailWord_175764) baseStart_175764 baseEnd_175764 := by
    simpa [prefixWord, tailWord_175764, baseEnd_175764] using wordTrace_append hprefix tailTrace_175764
  have hstable : (prefixWord ++ tailWord_175764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175764).length < 2 ^ (prefixWord ++ tailWord_175764).sum := by decide
  have hdescent : baseEnd_175764 < baseStart_175764 := by decide
  rcases family_descends (prefixWord ++ tailWord_175764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175868 : List Nat := [2, 2, 2, 1, 3, 1, 1, 6, 3]
def baseStart_175868 : Nat := 118140960795 + 175868 * 2 ^ 59
def prefixEnd_175868 : Nat := 4983230072969 + 3 ^ 40 * 175868 * 2
def baseEnd_175868 : Nat := 40135473664454733040535

theorem tailTrace_175868 : CollatzResearch.WordTrace tailWord_175868 prefixEnd_175868 40135473664454733040535 := by
  unfold tailWord_175868
  simp only [CollatzResearch.WordTrace]
  refine ⟨3207216463433873354116129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4276288617911831138821505 3207216463433873354116129)
  ·
    refine ⟨2405412347575405015587097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3207216463433873354116129 2405412347575405015587097)
    ·
      refine ⟨1804059260681553761690323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2405412347575405015587097 1804059260681553761690323)
      ·
        refine ⟨2706088891022330642535485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1804059260681553761690323 2706088891022330642535485)
        ·
          refine ⟨1014783334133373990950807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2706088891022330642535485 1014783334133373990950807)
          ·
            refine ⟨1522175001200060986426211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1014783334133373990950807 1522175001200060986426211)
            ·
              refine ⟨2283262501800091479639317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1522175001200060986426211 2283262501800091479639317)
              ·
                refine ⟨107027929771879288108093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2283262501800091479639317 107027929771879288108093)
                ·
                  refine ⟨40135473664454733040535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107027929771879288108093 40135473664454733040535)
                  ·
                    rfl

theorem cell21_175868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 6, 3].length) (baseStart_175868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_175868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_175868 prefixEnd_175868 := by exact prefixLift 175868
  have htrace : WordTrace (prefixWord ++ tailWord_175868) baseStart_175868 baseEnd_175868 := by
    simpa [prefixWord, tailWord_175868, baseEnd_175868] using wordTrace_append hprefix tailTrace_175868
  have hstable : (prefixWord ++ tailWord_175868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175868).length < 2 ^ (prefixWord ++ tailWord_175868).sum := by decide
  have hdescent : baseEnd_175868 < baseStart_175868 := by decide
  rcases family_descends (prefixWord ++ tailWord_175868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175972 : List Nat := [2, 3, 1, 1, 5, 9]
def baseStart_175972 : Nat := 118140960795 + 175972 * 2 ^ 59
def prefixEnd_175972 : Nat := 4983230072969 + 3 ^ 40 * 175972 * 2
def baseEnd_175972 : Nat := 1487378069680506048407

theorem tailTrace_175972 : CollatzResearch.WordTrace tailWord_175972 prefixEnd_175972 1487378069680506048407 := by
  unfold tailWord_175972
  simp only [CollatzResearch.WordTrace]
  refine ⟨3209113059245486235009085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4278817412327314980012113 3209113059245486235009085)
  ·
    refine ⟨1203417397217057338128407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3209113059245486235009085 1203417397217057338128407)
    ·
      refine ⟨1805126095825586007192611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1203417397217057338128407 1805126095825586007192611)
      ·
        refine ⟨2707689143738379010788917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1805126095825586007192611 2707689143738379010788917)
        ·
          refine ⟨253845857225473032261461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2707689143738379010788917 253845857225473032261461)
          ·
            refine ⟨1487378069680506048407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 253845857225473032261461 1487378069680506048407)
            ·
              rfl

theorem cell21_175972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 9].length) (baseStart_175972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_175972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_175972 prefixEnd_175972 := by exact prefixLift 175972
  have htrace : WordTrace (prefixWord ++ tailWord_175972) baseStart_175972 baseEnd_175972 := by
    simpa [prefixWord, tailWord_175972, baseEnd_175972] using wordTrace_append hprefix tailTrace_175972
  have hstable : (prefixWord ++ tailWord_175972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175972).length < 2 ^ (prefixWord ++ tailWord_175972).sum := by decide
  have hdescent : baseEnd_175972 < baseStart_175972 := by decide
  rcases family_descends (prefixWord ++ tailWord_175972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175978 : List Nat := [3, 1, 3, 4, 1, 1, 1, 4, 3]
def baseStart_175978 : Nat := 118140960795 + 175978 * 2 ^ 59
def prefixEnd_175978 : Nat := 4983230072969 + 3 ^ 40 * 175978 * 2
def baseEnd_175978 : Nat := 40160577163118986206977

theorem tailTrace_175978 : CollatzResearch.WordTrace tailWord_175978 prefixEnd_175978 40160577163118986206977 := by
  unfold tailWord_175978
  simp only [CollatzResearch.WordTrace]
  refine ⟨1604611239117308873684147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4278963304312823663157725 1604611239117308873684147)
  ·
    refine ⟨2406916858675963310526221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1604611239117308873684147 2406916858675963310526221)
    ·
      refine ⟨902593822003486241447333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2406916858675963310526221 902593822003486241447333)
      ·
        refine ⟨169236341625653670271375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 902593822003486241447333 169236341625653670271375)
        ·
          refine ⟨253854512438480505407063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169236341625653670271375 253854512438480505407063)
          ·
            refine ⟨380781768657720758110595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253854512438480505407063 380781768657720758110595)
            ·
              refine ⟨571172652986581137165893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 380781768657720758110595 571172652986581137165893)
              ·
                refine ⟨107094872434983963218605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 571172652986581137165893 107094872434983963218605)
                ·
                  refine ⟨40160577163118986206977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107094872434983963218605 40160577163118986206977)
                  ·
                    rfl

theorem cell21_175978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 4, 3].length) (baseStart_175978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_175978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_175978 prefixEnd_175978 := by exact prefixLift 175978
  have htrace : WordTrace (prefixWord ++ tailWord_175978) baseStart_175978 baseEnd_175978 := by
    simpa [prefixWord, tailWord_175978, baseEnd_175978] using wordTrace_append hprefix tailTrace_175978
  have hstable : (prefixWord ++ tailWord_175978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175978).length < 2 ^ (prefixWord ++ tailWord_175978).sum := by decide
  have hdescent : baseEnd_175978 < baseStart_175978 := by decide
  rcases family_descends (prefixWord ++ tailWord_175978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176003 : List Nat := [1, 1, 1, 3, 4, 3, 1, 2, 5]
def baseStart_176003 : Nat := 118140960795 + 176003 * 2 ^ 59
def prefixEnd_176003 : Nat := 4983230072969 + 3 ^ 40 * 176003 * 2
def baseEnd_176003 : Nat := 40166282503724498290259

theorem tailTrace_176003 : CollatzResearch.WordTrace tailWord_176003 prefixEnd_176003 40166282503724498290259 := by
  unfold tailWord_176003
  simp only [CollatzResearch.WordTrace]
  refine ⟨6419356781378664764396663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4279571187585776509597775 6419356781378664764396663)
  ·
    refine ⟨9629035172067997146594995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6419356781378664764396663 9629035172067997146594995)
    ·
      refine ⟨14443552758101995719892493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9629035172067997146594995 14443552758101995719892493)
      ·
        refine ⟨5416332284288248394959685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14443552758101995719892493 5416332284288248394959685)
        ·
          refine ⟨1015562303304046574054941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5416332284288248394959685 1015562303304046574054941)
          ·
            refine ⟨380835863739017465270603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1015562303304046574054941 380835863739017465270603)
            ·
              refine ⟨571253795608526197905905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 380835863739017465270603 571253795608526197905905)
              ·
                refine ⟨428440346706394648429429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 571253795608526197905905 428440346706394648429429)
                ·
                  refine ⟨40166282503724498290259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 428440346706394648429429 40166282503724498290259)
                  ·
                    rfl

theorem cell21_176003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 5].length) (baseStart_176003 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_176003 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_176003 prefixEnd_176003 := by exact prefixLift 176003
  have htrace : WordTrace (prefixWord ++ tailWord_176003) baseStart_176003 baseEnd_176003 := by
    simpa [prefixWord, tailWord_176003, baseEnd_176003] using wordTrace_append hprefix tailTrace_176003
  have hstable : (prefixWord ++ tailWord_176003).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176003).length < 2 ^ (prefixWord ++ tailWord_176003).sum := by decide
  have hdescent : baseEnd_176003 < baseStart_176003 := by decide
  rcases family_descends (prefixWord ++ tailWord_176003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176082 : List Nat := [3, 2, 2, 3, 3, 1, 7]
def baseStart_176082 : Nat := 118140960795 + 176082 * 2 ^ 59
def prefixEnd_176082 : Nat := 4983230072969 + 3 ^ 40 * 176082 * 2
def baseEnd_176082 : Nat := 4464923486670879608159

theorem tailTrace_176082 : CollatzResearch.WordTrace tailWord_176082 prefixEnd_176082 4464923486670879608159 := by
  unfold tailWord_176082
  simp only [CollatzResearch.WordTrace]
  refine ⟨1605559537023115314130625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4281492098728307504348333 1605559537023115314130625)
  ·
    refine ⟨1204169652767336485597969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1605559537023115314130625 1204169652767336485597969)
    ·
      refine ⟨903127239575502364198477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1204169652767336485597969 903127239575502364198477)
      ·
        refine ⟨338672714840813386574429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 903127239575502364198477 338672714840813386574429)
        ·
          refine ⟨127002268065305019965411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 338672714840813386574429 127002268065305019965411)
          ·
            refine ⟨190503402097957529948117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127002268065305019965411 190503402097957529948117)
            ·
              refine ⟨4464923486670879608159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 190503402097957529948117 4464923486670879608159)
              ·
                rfl

theorem cell21_176082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 7].length) (baseStart_176082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_176082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_176082 prefixEnd_176082 := by exact prefixLift 176082
  have htrace : WordTrace (prefixWord ++ tailWord_176082) baseStart_176082 baseEnd_176082 := by
    simpa [prefixWord, tailWord_176082, baseEnd_176082] using wordTrace_append hprefix tailTrace_176082
  have hstable : (prefixWord ++ tailWord_176082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176082).length < 2 ^ (prefixWord ++ tailWord_176082).sum := by decide
  have hdescent : baseEnd_176082 < baseStart_176082 := by decide
  rcases family_descends (prefixWord ++ tailWord_176082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176183 : List Nat := [1, 1, 3, 1, 2, 2, 2, 9]
def baseStart_176183 : Nat := 118140960795 + 176183 * 2 ^ 59
def prefixEnd_176183 : Nat := 4983230072969 + 3 ^ 40 * 176183 * 2
def baseEnd_176183 : Nat := 13402453652028061763297

theorem tailTrace_176183 : CollatzResearch.WordTrace tailWord_176183 prefixEnd_176183 13402453652028061763297 := by
  unfold tailWord_176183
  simp only [CollatzResearch.WordTrace]
  refine ⟨6425921920726555505949203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4283947947151037003966135 6425921920726555505949203)
  ·
    refine ⟨9638882881089833258923805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6425921920726555505949203 9638882881089833258923805)
    ·
      refine ⟨3614581080408687472096427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9638882881089833258923805 3614581080408687472096427)
      ·
        refine ⟨5421871620613031208144641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3614581080408687472096427 5421871620613031208144641)
        ·
          refine ⟨4066403715459773406108481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5421871620613031208144641 4066403715459773406108481)
          ·
            refine ⟨3049802786594830054581361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4066403715459773406108481 3049802786594830054581361)
            ·
              refine ⟨2287352089946122540936021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3049802786594830054581361 2287352089946122540936021)
              ·
                refine ⟨13402453652028061763297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2287352089946122540936021 13402453652028061763297)
                ·
                  rfl

theorem cell21_176183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 9].length) (baseStart_176183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_176183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_176183 prefixEnd_176183 := by exact prefixLift 176183
  have htrace : WordTrace (prefixWord ++ tailWord_176183) baseStart_176183 baseEnd_176183 := by
    simpa [prefixWord, tailWord_176183, baseEnd_176183] using wordTrace_append hprefix tailTrace_176183
  have hstable : (prefixWord ++ tailWord_176183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176183).length < 2 ^ (prefixWord ++ tailWord_176183).sum := by decide
  have hdescent : baseEnd_176183 < baseStart_176183 := by decide
  rcases family_descends (prefixWord ++ tailWord_176183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176234 : List Nat := [3, 1, 3, 2, 3, 2, 2, 5]
def baseStart_176234 : Nat := 118140960795 + 176234 * 2 ^ 59
def prefixEnd_176234 : Nat := 4983230072969 + 3 ^ 40 * 176234 * 2
def baseEnd_176234 : Nat := 13406333283639809979929

theorem tailTrace_176234 : CollatzResearch.WordTrace tailWord_176234 prefixEnd_176234 13406333283639809979929 := by
  unfold tailWord_176234
  simp only [CollatzResearch.WordTrace]
  refine ⟨1606945510885447804013939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4285188029027860810703837 1606945510885447804013939)
  ·
    refine ⟨2410418266328171706020909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1606945510885447804013939 2410418266328171706020909)
    ·
      refine ⟨903906849873064389757841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2410418266328171706020909 903906849873064389757841)
      ·
        refine ⟨677930137404798292318381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 903906849873064389757841 677930137404798292318381)
        ·
          refine ⟨254223801526799359619393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 677930137404798292318381 254223801526799359619393)
          ·
            refine ⟨190667851145099519714545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 254223801526799359619393 190667851145099519714545)
            ·
              refine ⟨143000888358824639785909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190667851145099519714545 143000888358824639785909)
              ·
                refine ⟨13406333283639809979929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 143000888358824639785909 13406333283639809979929)
                ·
                  rfl

theorem cell21_176234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 5].length) (baseStart_176234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_176234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_176234 prefixEnd_176234 := by exact prefixLift 176234
  have htrace : WordTrace (prefixWord ++ tailWord_176234) baseStart_176234 baseEnd_176234 := by
    simpa [prefixWord, tailWord_176234, baseEnd_176234] using wordTrace_append hprefix tailTrace_176234
  have hstable : (prefixWord ++ tailWord_176234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176234).length < 2 ^ (prefixWord ++ tailWord_176234).sum := by decide
  have hdescent : baseEnd_176234 < baseStart_176234 := by decide
  rcases family_descends (prefixWord ++ tailWord_176234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176259 : List Nat := [1, 1, 1, 3, 3, 3, 9]
def baseStart_176259 : Nat := 118140960795 + 176259 * 2 ^ 59
def prefixEnd_176259 : Nat := 4983230072969 + 3 ^ 40 * 176259 * 2
def baseEnd_176259 : Nat := 4469411687947215780341

theorem tailTrace_176259 : CollatzResearch.WordTrace tailWord_176259 prefixEnd_176259 4469411687947215780341 := by
  unfold tailWord_176259
  simp only [CollatzResearch.WordTrace]
  refine ⟨6428693868451220485715831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4285795912300813657143887 6428693868451220485715831)
  ·
    refine ⟨9643040802676830728573747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6428693868451220485715831 9643040802676830728573747)
    ·
      refine ⟨14464561204015246092860621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9643040802676830728573747 14464561204015246092860621)
      ·
        refine ⟨5424210451505717284822733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14464561204015246092860621 5424210451505717284822733)
        ·
          refine ⟨2034078919314643981808525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5424210451505717284822733 2034078919314643981808525)
          ·
            refine ⟨762779594742991493178197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2034078919314643981808525 762779594742991493178197)
            ·
              refine ⟨4469411687947215780341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 762779594742991493178197 4469411687947215780341)
              ·
                rfl

theorem cell21_176259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 9].length) (baseStart_176259 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_176259 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_176259 prefixEnd_176259 := by exact prefixLift 176259
  have htrace : WordTrace (prefixWord ++ tailWord_176259) baseStart_176259 baseEnd_176259 := by
    simpa [prefixWord, tailWord_176259, baseEnd_176259] using wordTrace_append hprefix tailTrace_176259
  have hstable : (prefixWord ++ tailWord_176259).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176259).length < 2 ^ (prefixWord ++ tailWord_176259).sum := by decide
  have hdescent : baseEnd_176259 < baseStart_176259 := by decide
  rcases family_descends (prefixWord ++ tailWord_176259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176307 : List Nat := [1, 1, 1, 2, 3, 2, 1, 7, 3]
def baseStart_176307 : Nat := 118140960795 + 176307 * 2 ^ 59
def prefixEnd_176307 : Nat := 4983230072969 + 3 ^ 40 * 176307 * 2
def baseEnd_176307 : Nat := 40235659445487525222971

theorem tailTrace_176307 : CollatzResearch.WordTrace tailWord_176307 prefixEnd_176307 40235659445487525222971 := by
  unfold tailWord_176307
  simp only [CollatzResearch.WordTrace]
  refine ⟨6430444572277324683463175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4286963048184883122308783 6430444572277324683463175)
  ·
    refine ⟨9645666858415987025194763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6430444572277324683463175 9645666858415987025194763)
    ·
      refine ⟨14468500287623980537792145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9645666858415987025194763 14468500287623980537792145)
      ·
        refine ⟨10851375215717985403344109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14468500287623980537792145 10851375215717985403344109)
        ·
          refine ⟨4069265705894244526254041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10851375215717985403344109 4069265705894244526254041)
          ·
            refine ⟨3051949279420683394690531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4069265705894244526254041 3051949279420683394690531)
            ·
              refine ⟨4577923919131025092035797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3051949279420683394690531 4577923919131025092035797)
              ·
                refine ⟨107295091854633400594589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4577923919131025092035797 107295091854633400594589)
                ·
                  refine ⟨40235659445487525222971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107295091854633400594589 40235659445487525222971)
                  ·
                    rfl

theorem cell21_176307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 7, 3].length) (baseStart_176307 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_176307 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_176307 prefixEnd_176307 := by exact prefixLift 176307
  have htrace : WordTrace (prefixWord ++ tailWord_176307) baseStart_176307 baseEnd_176307 := by
    simpa [prefixWord, tailWord_176307, baseEnd_176307] using wordTrace_append hprefix tailTrace_176307
  have hstable : (prefixWord ++ tailWord_176307).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176307).length < 2 ^ (prefixWord ++ tailWord_176307).sum := by decide
  have hdescent : baseEnd_176307 < baseStart_176307 := by decide
  rcases family_descends (prefixWord ++ tailWord_176307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176338 : List Nat := [3, 2, 2, 2, 1, 2, 2, 3, 4]
def baseStart_176338 : Nat := 118140960795 + 176338 * 2 ^ 59
def prefixEnd_176338 : Nat := 4983230072969 + 3 ^ 40 * 176338 * 2
def baseEnd_176338 : Nat := 40242734067838360206241

theorem tailTrace_176338 : CollatzResearch.WordTrace tailWord_176338 prefixEnd_176338 40242734067838360206241 := by
  unfold tailWord_176338
  simp only [CollatzResearch.WordTrace]
  refine ⟨1607893808791254244460417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4287716823443344651894445 1607893808791254244460417)
  ·
    refine ⟨1205920356593440683345313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1607893808791254244460417 1205920356593440683345313)
    ·
      refine ⟨904440267445080512508985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1205920356593440683345313 904440267445080512508985)
      ·
        refine ⟨678330200583810384381739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 904440267445080512508985 678330200583810384381739)
        ·
          refine ⟨1017495300875715576572609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 678330200583810384381739 1017495300875715576572609)
          ·
            refine ⟨763121475656786682429457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1017495300875715576572609 763121475656786682429457)
            ·
              refine ⟨572341106742590011822093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 763121475656786682429457 572341106742590011822093)
              ·
                refine ⟨214627915028471254433285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 572341106742590011822093 214627915028471254433285)
                ·
                  refine ⟨40242734067838360206241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 214627915028471254433285 40242734067838360206241)
                  ·
                    rfl

theorem cell21_176338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_176338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_176338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_176338 prefixEnd_176338 := by exact prefixLift 176338
  have htrace : WordTrace (prefixWord ++ tailWord_176338) baseStart_176338 baseEnd_176338 := by
    simpa [prefixWord, tailWord_176338, baseEnd_176338] using wordTrace_append hprefix tailTrace_176338
  have hstable : (prefixWord ++ tailWord_176338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176338).length < 2 ^ (prefixWord ++ tailWord_176338).sum := by decide
  have hdescent : baseEnd_176338 < baseStart_176338 := by decide
  rcases family_descends (prefixWord ++ tailWord_176338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176352 : List Nat := [2, 1, 1, 3, 1, 3, 5, 5]
def baseStart_176352 : Nat := 118140960795 + 176352 * 2 ^ 59
def prefixEnd_176352 : Nat := 4983230072969 + 3 ^ 40 * 176352 * 2
def baseEnd_176352 : Nat := 13415309686192482324293

theorem tailTrace_176352 : CollatzResearch.WordTrace tailWord_176352 prefixEnd_176352 13415309686192482324293 := by
  unfold tailWord_176352
  simp only [CollatzResearch.WordTrace]
  refine ⟨3216042928557148684425655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4288057238076198245900873 3216042928557148684425655)
  ·
    refine ⟨4824064392835723026638483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3216042928557148684425655 4824064392835723026638483)
    ·
      refine ⟨7236096589253584539957725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4824064392835723026638483 7236096589253584539957725)
      ·
        refine ⟨2713536220970094202484147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7236096589253584539957725 2713536220970094202484147)
        ·
          refine ⟨4070304331455141303726221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2713536220970094202484147 4070304331455141303726221)
          ·
            refine ⟨1526364124295677988897333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4070304331455141303726221 1526364124295677988897333)
            ·
              refine ⟨143096636652719811459125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1526364124295677988897333 143096636652719811459125)
              ·
                refine ⟨13415309686192482324293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 143096636652719811459125 13415309686192482324293)
                ·
                  rfl

theorem cell21_176352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 5].length) (baseStart_176352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_176352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_176352 prefixEnd_176352 := by exact prefixLift 176352
  have htrace : WordTrace (prefixWord ++ tailWord_176352) baseStart_176352 baseEnd_176352 := by
    simpa [prefixWord, tailWord_176352, baseEnd_176352] using wordTrace_append hprefix tailTrace_176352
  have hstable : (prefixWord ++ tailWord_176352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176352).length < 2 ^ (prefixWord ++ tailWord_176352).sum := by decide
  have hdescent : baseEnd_176352 < baseStart_176352 := by decide
  rcases family_descends (prefixWord ++ tailWord_176352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176366 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 9]
def baseStart_176366 : Nat := 118140960795 + 176366 * 2 ^ 59
def prefixEnd_176366 : Nat := 4983230072969 + 3 ^ 40 * 176366 * 2
def baseEnd_176366 : Nat := 40249124049316533739517

theorem tailTrace_176366 : CollatzResearch.WordTrace tailWord_176366 prefixEnd_176366 40249124049316533739517 := by
  unfold tailWord_176366
  simp only [CollatzResearch.WordTrace]
  refine ⟨804074559882947219982619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4288397652709051839907301 804074559882947219982619)
  ·
    refine ⟨1206111839824420829973929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 804074559882947219982619 1206111839824420829973929)
    ·
      refine ⟨904583879868315622480447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1206111839824420829973929 904583879868315622480447)
      ·
        refine ⟨1356875819802473433720671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 904583879868315622480447 1356875819802473433720671)
        ·
          refine ⟨2035313729703710150581007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1356875819802473433720671 2035313729703710150581007)
          ·
            refine ⟨3052970594555565225871511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2035313729703710150581007 3052970594555565225871511)
            ·
              refine ⟨4579455891833347838807267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3052970594555565225871511 4579455891833347838807267)
              ·
                refine ⟨6869183837750021758210901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4579455891833347838807267 6869183837750021758210901)
                ·
                  refine ⟨40249124049316533739517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 6869183837750021758210901 40249124049316533739517)
                  ·
                    rfl

theorem cell21_176366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_176366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_176366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_176366 prefixEnd_176366 := by exact prefixLift 176366
  have htrace : WordTrace (prefixWord ++ tailWord_176366) baseStart_176366 baseEnd_176366 := by
    simpa [prefixWord, tailWord_176366, baseEnd_176366] using wordTrace_append hprefix tailTrace_176366
  have hstable : (prefixWord ++ tailWord_176366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176366).length < 2 ^ (prefixWord ++ tailWord_176366).sum := by decide
  have hdescent : baseEnd_176366 < baseStart_176366 := by decide
  rcases family_descends (prefixWord ++ tailWord_176366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176383 : List Nat := [1, 1, 2, 2, 1, 4, 1, 6, 3]
def baseStart_176383 : Nat := 118140960795 + 176383 * 2 ^ 59
def prefixEnd_176383 : Nat := 4983230072969 + 3 ^ 40 * 176383 * 2
def baseEnd_176383 : Nat := 40253003680928281956149

theorem tailTrace_176383 : CollatzResearch.WordTrace tailWord_176383 prefixEnd_176383 40253003680928281956149 := by
  unfold tailWord_176383
  simp only [CollatzResearch.WordTrace]
  refine ⟨6433216520001989663229803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4288811013334659775486535 6433216520001989663229803)
  ·
    refine ⟨9649824780002984494844705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6433216520001989663229803 9649824780002984494844705)
    ·
      refine ⟨7237368585002238371133529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9649824780002984494844705 7237368585002238371133529)
      ·
        refine ⟨5428026438751678778350147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7237368585002238371133529 5428026438751678778350147)
        ·
          refine ⟨8142039658127518167525221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5428026438751678778350147 8142039658127518167525221)
          ·
            refine ⟨1526632435898909656410979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8142039658127518167525221 1526632435898909656410979)
            ·
              refine ⟨2289948653848364484616469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1526632435898909656410979 2289948653848364484616469)
              ·
                refine ⟨107341343149142085216397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2289948653848364484616469 107341343149142085216397)
                ·
                  refine ⟨40253003680928281956149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107341343149142085216397 40253003680928281956149)
                  ·
                    rfl

theorem cell21_176383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 6, 3].length) (baseStart_176383 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_176383 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_176383 prefixEnd_176383 := by exact prefixLift 176383
  have htrace : WordTrace (prefixWord ++ tailWord_176383) baseStart_176383 baseEnd_176383 := by
    simpa [prefixWord, tailWord_176383, baseEnd_176383] using wordTrace_append hprefix tailTrace_176383
  have hstable : (prefixWord ++ tailWord_176383).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176383).length < 2 ^ (prefixWord ++ tailWord_176383).sum := by decide
  have hdescent : baseEnd_176383 < baseStart_176383 := by decide
  rcases family_descends (prefixWord ++ tailWord_176383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176487 : List Nat := [1, 1, 5, 1, 3, 10]
def baseStart_176487 : Nat := 118140960795 + 176487 * 2 ^ 59
def prefixEnd_176487 : Nat := 4983230072969 + 3 ^ 40 * 176487 * 2
def baseEnd_176487 : Nat := 1491731033253600452689

theorem tailTrace_176487 : CollatzResearch.WordTrace tailWord_176487 prefixEnd_176487 1491731033253600452689 := by
  unfold tailWord_176487
  simp only [CollatzResearch.WordTrace]
  refine ⟨6437009711625215425015715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4291339807750143616677143 6437009711625215425015715)
  ·
    refine ⟨9655514567437823137523573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6437009711625215425015715 9655514567437823137523573)
    ·
      refine ⟨905204490697295919142835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9655514567437823137523573 905204490697295919142835)
      ·
        refine ⟨1357806736045943878714253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 905204490697295919142835 1357806736045943878714253)
        ·
          refine ⟨509177526017228954517845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1357806736045943878714253 509177526017228954517845)
          ·
            refine ⟨1491731033253600452689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 509177526017228954517845 1491731033253600452689)
            ·
              rfl

theorem cell21_176487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 10].length) (baseStart_176487 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_176487 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_176487 prefixEnd_176487 := by exact prefixLift 176487
  have htrace : WordTrace (prefixWord ++ tailWord_176487) baseStart_176487 baseEnd_176487 := by
    simpa [prefixWord, tailWord_176487, baseEnd_176487] using wordTrace_append hprefix tailTrace_176487
  have hstable : (prefixWord ++ tailWord_176487).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176487).length < 2 ^ (prefixWord ++ tailWord_176487).sum := by decide
  have hdescent : baseEnd_176487 < baseStart_176487 := by decide
  rcases family_descends (prefixWord ++ tailWord_176487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176490 : List Nat := [3, 1, 3, 3, 1, 1, 1, 4, 4]
def baseStart_176490 : Nat := 118140960795 + 176490 * 2 ^ 59
def prefixEnd_176490 : Nat := 4983230072969 + 3 ^ 40 * 176490 * 2
def baseEnd_176490 : Nat := 40277422538719873672597

theorem tailTrace_176490 : CollatzResearch.WordTrace tailWord_176490 prefixEnd_176490 40277422538719873672597 := by
  unfold tailWord_176490
  simp only [CollatzResearch.WordTrace]
  refine ⟨1609279782653586734343731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4291412753742897958249949 1609279782653586734343731)
  ·
    refine ⟨2413919673980380101515597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1609279782653586734343731 2413919673980380101515597)
    ·
      refine ⟨905219877742642538068349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2413919673980380101515597 905219877742642538068349)
      ·
        refine ⟨339457454153490951775631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 905219877742642538068349 339457454153490951775631)
        ·
          refine ⟨509186181230236427663447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339457454153490951775631 509186181230236427663447)
          ·
            refine ⟨763779271845354641495171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 509186181230236427663447 763779271845354641495171)
            ·
              refine ⟨1145668907768031962242757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 763779271845354641495171 1145668907768031962242757)
              ·
                refine ⟨214812920206505992920517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1145668907768031962242757 214812920206505992920517)
                ·
                  refine ⟨40277422538719873672597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 214812920206505992920517 40277422538719873672597)
                  ·
                    rfl

theorem cell21_176490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 4, 4].length) (baseStart_176490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_176490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_176490 prefixEnd_176490 := by exact prefixLift 176490
  have htrace : WordTrace (prefixWord ++ tailWord_176490) baseStart_176490 baseEnd_176490 := by
    simpa [prefixWord, tailWord_176490, baseEnd_176490] using wordTrace_append hprefix tailTrace_176490
  have hstable : (prefixWord ++ tailWord_176490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176490).length < 2 ^ (prefixWord ++ tailWord_176490).sum := by decide
  have hdescent : baseEnd_176490 < baseStart_176490 := by decide
  rcases family_descends (prefixWord ++ tailWord_176490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176535 : List Nat := [1, 1, 3, 3, 1, 1, 3, 5, 3]
def baseStart_176535 : Nat := 118140960795 + 176535 * 2 ^ 59
def prefixEnd_176535 : Nat := 4983230072969 + 3 ^ 40 * 176535 * 2
def baseEnd_176535 : Nat := 40287692151809795422505

theorem tailTrace_176535 : CollatzResearch.WordTrace tailWord_176535 prefixEnd_176535 40287692151809795422505 := by
  unfold tailWord_176535
  simp only [CollatzResearch.WordTrace]
  refine ⟨6438760415451319622763059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4292506943634213081842039 6438760415451319622763059)
  ·
    refine ⟨9658140623176979434144589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6438760415451319622763059 9658140623176979434144589)
    ·
      refine ⟨3621802733691367287804221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9658140623176979434144589 3621802733691367287804221)
      ·
        refine ⟨1358176025134262732926583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3621802733691367287804221 1358176025134262732926583)
        ·
          refine ⟨2037264037701394099389875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1358176025134262732926583 2037264037701394099389875)
          ·
            refine ⟨3055896056552091149084813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2037264037701394099389875 3055896056552091149084813)
            ·
              refine ⟨1145961021207034180906805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3055896056552091149084813 1145961021207034180906805)
              ·
                refine ⟨107433845738159454460013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1145961021207034180906805 107433845738159454460013)
                ·
                  refine ⟨40287692151809795422505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107433845738159454460013 40287692151809795422505)
                  ·
                    rfl

theorem cell21_176535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 5, 3].length) (baseStart_176535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_176535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_176535 prefixEnd_176535 := by exact prefixLift 176535
  have htrace : WordTrace (prefixWord ++ tailWord_176535) baseStart_176535 baseEnd_176535 := by
    simpa [prefixWord, tailWord_176535, baseEnd_176535] using wordTrace_append hprefix tailTrace_176535
  have hstable : (prefixWord ++ tailWord_176535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176535).length < 2 ^ (prefixWord ++ tailWord_176535).sum := by decide
  have hdescent : baseEnd_176535 < baseStart_176535 := by decide
  rcases family_descends (prefixWord ++ tailWord_176535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176552 : List Nat := [2, 1, 6, 1, 1, 2, 2, 1, 5]
def baseStart_176552 : Nat := 118140960795 + 176552 * 2 ^ 59
def prefixEnd_176552 : Nat := 4983230072969 + 3 ^ 40 * 176552 * 2
def baseEnd_176552 : Nat := 40291571783421543639137

theorem tailTrace_176552 : CollatzResearch.WordTrace tailWord_176552 prefixEnd_176552 40291571783421543639137 := by
  unfold tailWord_176552
  simp only [CollatzResearch.WordTrace]
  refine ⟨3219690228194865763065955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4292920304259821017421273 3219690228194865763065955)
  ·
    refine ⟨4829535342292298644598933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3219690228194865763065955 4829535342292298644598933)
    ·
      refine ⟨226384469169951498965575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4829535342292298644598933 226384469169951498965575)
      ·
        refine ⟨339576703754927248448363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226384469169951498965575 339576703754927248448363)
        ·
          refine ⟨509365055632390872672545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339576703754927248448363 509365055632390872672545)
          ·
            refine ⟨382023791724293154504409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 509365055632390872672545 382023791724293154504409)
            ·
              refine ⟨286517843793219865878307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 382023791724293154504409 286517843793219865878307)
              ·
                refine ⟨429776765689829798817461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 286517843793219865878307 429776765689829798817461)
                ·
                  refine ⟨40291571783421543639137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 429776765689829798817461 40291571783421543639137)
                  ·
                    rfl

theorem cell21_176552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 5].length) (baseStart_176552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_176552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_176552 prefixEnd_176552 := by exact prefixLift 176552
  have htrace : WordTrace (prefixWord ++ tailWord_176552) baseStart_176552 baseEnd_176552 := by
    simpa [prefixWord, tailWord_176552, baseEnd_176552] using wordTrace_append hprefix tailTrace_176552
  have hstable : (prefixWord ++ tailWord_176552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176552).length < 2 ^ (prefixWord ++ tailWord_176552).sum := by decide
  have hdescent : baseEnd_176552 < baseStart_176552 := by decide
  rcases family_descends (prefixWord ++ tailWord_176552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176608 : List Nat := [2, 1, 1, 3, 1, 1, 3, 3, 6]
def baseStart_176608 : Nat := 118140960795 + 176608 * 2 ^ 59
def prefixEnd_176608 : Nat := 4983230072969 + 3 ^ 40 * 176608 * 2
def baseEnd_176608 : Nat := 40304351746377890705689

theorem tailTrace_176608 : CollatzResearch.WordTrace tailWord_176608 prefixEnd_176608 40304351746377890705689 := by
  unfold tailWord_176608
  simp only [CollatzResearch.WordTrace]
  refine ⟨3220711472093426545085239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4294281962791235393446985 3220711472093426545085239)
  ·
    refine ⟨4831067208140139817627859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3220711472093426545085239 4831067208140139817627859)
    ·
      refine ⟨7246600812210209726441789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4831067208140139817627859 7246600812210209726441789)
      ·
        refine ⟨2717475304578828647415671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7246600812210209726441789 2717475304578828647415671)
        ·
          refine ⟨4076212956868242971123507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2717475304578828647415671 4076212956868242971123507)
          ·
            refine ⟨6114319435302364456685261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4076212956868242971123507 6114319435302364456685261)
            ·
              refine ⟨2292869788238386671256973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6114319435302364456685261 2292869788238386671256973)
              ·
                refine ⟨859826170589395001721365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2292869788238386671256973 859826170589395001721365)
                ·
                  refine ⟨40304351746377890705689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 859826170589395001721365 40304351746377890705689)
                  ·
                    rfl

theorem cell21_176608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 6].length) (baseStart_176608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_176608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_176608 prefixEnd_176608 := by exact prefixLift 176608
  have htrace : WordTrace (prefixWord ++ tailWord_176608) baseStart_176608 baseEnd_176608 := by
    simpa [prefixWord, tailWord_176608, baseEnd_176608] using wordTrace_append hprefix tailTrace_176608
  have hstable : (prefixWord ++ tailWord_176608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176608).length < 2 ^ (prefixWord ++ tailWord_176608).sum := by decide
  have hdescent : baseEnd_176608 < baseStart_176608 := by decide
  rcases family_descends (prefixWord ++ tailWord_176608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176625 : List Nat := [1, 2, 2, 2, 3, 1, 3, 3, 4]
def baseStart_176625 : Nat := 118140960795 + 176625 * 2 ^ 59
def prefixEnd_176625 : Nat := 4983230072969 + 3 ^ 40 * 176625 * 2
def baseEnd_176625 : Nat := 40308231377989638922321

theorem tailTrace_176625 : CollatzResearch.WordTrace tailWord_176625 prefixEnd_176625 40308231377989638922321 := by
  unfold tailWord_176625
  simp only [CollatzResearch.WordTrace]
  refine ⟨6442042985125264993539329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4294695323416843329026219 6442042985125264993539329)
  ·
    refine ⟨4831532238843948745154497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6442042985125264993539329 4831532238843948745154497)
    ·
      refine ⟨3623649179132961558865873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4831532238843948745154497 3623649179132961558865873)
      ·
        refine ⟨2717736884349721169149405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3623649179132961558865873 2717736884349721169149405)
        ·
          refine ⟨1019151331631145438431027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2717736884349721169149405 1019151331631145438431027)
          ·
            refine ⟨1528726997446718157646541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1019151331631145438431027 1528726997446718157646541)
            ·
              refine ⟨573272624042519309117453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1528726997446718157646541 573272624042519309117453)
              ·
                refine ⟨214977234015944740919045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 573272624042519309117453 214977234015944740919045)
                ·
                  refine ⟨40308231377989638922321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 214977234015944740919045 40308231377989638922321)
                  ·
                    rfl

theorem cell21_176625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 3, 4].length) (baseStart_176625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_176625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_176625 prefixEnd_176625 := by exact prefixLift 176625
  have htrace : WordTrace (prefixWord ++ tailWord_176625) baseStart_176625 baseEnd_176625 := by
    simpa [prefixWord, tailWord_176625, baseEnd_176625] using wordTrace_append hprefix tailTrace_176625
  have hstable : (prefixWord ++ tailWord_176625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176625).length < 2 ^ (prefixWord ++ tailWord_176625).sum := by decide
  have hdescent : baseEnd_176625 < baseStart_176625 := by decide
  rcases family_descends (prefixWord ++ tailWord_176625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176746 : List Nat := [3, 1, 3, 2, 1, 1, 1, 4, 5]
def baseStart_176746 : Nat := 118140960795 + 176746 * 2 ^ 59
def prefixEnd_176746 : Nat := 4983230072969 + 3 ^ 40 * 176746 * 2
def baseEnd_176746 : Nat := 40335845226520317405407

theorem tailTrace_176746 : CollatzResearch.WordTrace tailWord_176746 prefixEnd_176746 40335845226520317405407 := by
  unfold tailWord_176746
  simp only [CollatzResearch.WordTrace]
  refine ⟨1611614054421725664673523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4297637478457935105796061 1611614054421725664673523)
  ·
    refine ⟨2417421081632588497010285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1611614054421725664673523 2417421081632588497010285)
    ·
      refine ⟨906532905612220686378857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2417421081632588497010285 906532905612220686378857)
      ·
        refine ⟨679899679209165514784143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 906532905612220686378857 679899679209165514784143)
        ·
          refine ⟨1019849518813748272176215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 679899679209165514784143 1019849518813748272176215)
          ·
            refine ⟨1529774278220622408264323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1019849518813748272176215 1529774278220622408264323)
            ·
              refine ⟨2294661417330933612396485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1529774278220622408264323 2294661417330933612396485)
              ·
                refine ⟨430249015749550052324341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2294661417330933612396485 430249015749550052324341)
                ·
                  refine ⟨40335845226520317405407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 430249015749550052324341 40335845226520317405407)
                  ·
                    rfl

theorem cell21_176746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_176746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_176746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_176746 prefixEnd_176746 := by exact prefixLift 176746
  have htrace : WordTrace (prefixWord ++ tailWord_176746) baseStart_176746 baseEnd_176746 := by
    simpa [prefixWord, tailWord_176746, baseEnd_176746] using wordTrace_append hprefix tailTrace_176746
  have hstable : (prefixWord ++ tailWord_176746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176746).length < 2 ^ (prefixWord ++ tailWord_176746).sum := by decide
  have hdescent : baseEnd_176746 < baseStart_176746 := by decide
  rcases family_descends (prefixWord ++ tailWord_176746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176749 : List Nat := [1, 5, 1, 1, 3, 3, 2, 5]
def baseStart_176749 : Nat := 118140960795 + 176749 * 2 ^ 59
def prefixEnd_176749 : Nat := 4983230072969 + 3 ^ 40 * 176749 * 2
def baseEnd_176749 : Nat := 13445509955797659618467

theorem tailTrace_176749 : CollatzResearch.WordTrace tailWord_176749 prefixEnd_176749 13445509955797659618467 := by
  unfold tailWord_176749
  simp only [CollatzResearch.WordTrace]
  refine ⟨6446565636676034171053301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4297710424450689447368867 6446565636676034171053301)
  ·
    refine ⟨604365528438378203536247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6446565636676034171053301 604365528438378203536247)
    ·
      refine ⟨906548292657567305304371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 604365528438378203536247 906548292657567305304371)
      ·
        refine ⟨1359822438986350957956557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 906548292657567305304371 1359822438986350957956557)
        ·
          refine ⟨509933414619881609233709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1359822438986350957956557 509933414619881609233709)
          ·
            refine ⟨191225030482455603462641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 509933414619881609233709 191225030482455603462641)
            ·
              refine ⟨143418772861841702596981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191225030482455603462641 143418772861841702596981)
              ·
                refine ⟨13445509955797659618467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 143418772861841702596981 13445509955797659618467)
                ·
                  rfl

theorem cell21_176749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 5].length) (baseStart_176749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_176749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_176749 prefixEnd_176749 := by exact prefixLift 176749
  have htrace : WordTrace (prefixWord ++ tailWord_176749) baseStart_176749 baseEnd_176749 := by
    simpa [prefixWord, tailWord_176749, baseEnd_176749] using wordTrace_append hprefix tailTrace_176749
  have hstable : (prefixWord ++ tailWord_176749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176749).length < 2 ^ (prefixWord ++ tailWord_176749).sum := by decide
  have hdescent : baseEnd_176749 < baseStart_176749 := by decide
  rcases family_descends (prefixWord ++ tailWord_176749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176791 : List Nat := [1, 1, 3, 3, 2, 1, 4, 6]
def baseStart_176791 : Nat := 118140960795 + 176791 * 2 ^ 59
def prefixEnd_176791 : Nat := 4983230072969 + 3 ^ 40 * 176791 * 2
def baseEnd_176791 : Nat := 13448704946536746385105

theorem tailTrace_176791 : CollatzResearch.WordTrace tailWord_176791 prefixEnd_176791 13448704946536746385105 := by
  unfold tailWord_176791
  simp only [CollatzResearch.WordTrace]
  refine ⟨6448097502523875344082227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4298731668349250229388151 6448097502523875344082227)
  ·
    refine ⟨9672146253785813016123341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6448097502523875344082227 9672146253785813016123341)
    ·
      refine ⟨3627054845169679881046253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9672146253785813016123341 3627054845169679881046253)
      ·
        refine ⟨1360145566938629955392345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3627054845169679881046253 1360145566938629955392345)
        ·
          refine ⟨1020109175203972466544259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1360145566938629955392345 1020109175203972466544259)
          ·
            refine ⟨1530163762805958699816389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1020109175203972466544259 1530163762805958699816389)
            ·
              refine ⟨286905705526117256215573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1530163762805958699816389 286905705526117256215573)
              ·
                refine ⟨13448704946536746385105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 286905705526117256215573 13448704946536746385105)
                ·
                  rfl

theorem cell21_176791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 6].length) (baseStart_176791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_176791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_176791 prefixEnd_176791 := by exact prefixLift 176791
  have htrace : WordTrace (prefixWord ++ tailWord_176791) baseStart_176791 baseEnd_176791 := by
    simpa [prefixWord, tailWord_176791, baseEnd_176791] using wordTrace_append hprefix tailTrace_176791
  have hstable : (prefixWord ++ tailWord_176791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176791).length < 2 ^ (prefixWord ++ tailWord_176791).sum := by decide
  have hdescent : baseEnd_176791 < baseStart_176791 := by decide
  rcases family_descends (prefixWord ++ tailWord_176791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176805 : List Nat := [1, 3, 1, 2, 1, 2, 1, 3, 7]
def baseStart_176805 : Nat := 118140960795 + 176805 * 2 ^ 59
def prefixEnd_176805 : Nat := 4983230072969 + 3 ^ 40 * 176805 * 2
def baseEnd_176805 : Nat := 40349309830349325921953

theorem tailTrace_176805 : CollatzResearch.WordTrace tailWord_176805 prefixEnd_176805 40349309830349325921953 := by
  unfold tailWord_176805
  simp only [CollatzResearch.WordTrace]
  refine ⟨6448608124473155735091869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4299072082982103823394579 6448608124473155735091869)
  ·
    refine ⟨2418228046677433400659451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6448608124473155735091869 2418228046677433400659451)
    ·
      refine ⟨3627342070016150100989177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2418228046677433400659451 3627342070016150100989177)
      ·
        refine ⟨2720506552512112575741883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3627342070016150100989177 2720506552512112575741883)
        ·
          refine ⟨4080759828768168863612825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2720506552512112575741883 4080759828768168863612825)
          ·
            refine ⟨3060569871576126647709619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4080759828768168863612825 3060569871576126647709619)
            ·
              refine ⟨4590854807364189971564429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3060569871576126647709619 4590854807364189971564429)
              ·
                refine ⟨1721570552761571239336661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4590854807364189971564429 1721570552761571239336661)
                ·
                  refine ⟨40349309830349325921953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1721570552761571239336661 40349309830349325921953)
                  ·
                    rfl

theorem cell21_176805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_176805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_176805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_176805 prefixEnd_176805 := by exact prefixLift 176805
  have htrace : WordTrace (prefixWord ++ tailWord_176805) baseStart_176805 baseEnd_176805 := by
    simpa [prefixWord, tailWord_176805, baseEnd_176805] using wordTrace_append hprefix tailTrace_176805
  have hstable : (prefixWord ++ tailWord_176805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176805).length < 2 ^ (prefixWord ++ tailWord_176805).sum := by decide
  have hdescent : baseEnd_176805 < baseStart_176805 := by decide
  rcases family_descends (prefixWord ++ tailWord_176805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176881 : List Nat := [1, 2, 2, 2, 2, 2, 1, 2, 7]
def baseStart_176881 : Nat := 118140960795 + 176881 * 2 ^ 59
def prefixEnd_176881 : Nat := 4983230072969 + 3 ^ 40 * 176881 * 2
def baseEnd_176881 : Nat := 40366654065790082655131

theorem tailTrace_176881 : CollatzResearch.WordTrace tailWord_176881 prefixEnd_176881 40366654065790082655131 := by
  unfold tailWord_176881
  simp only [CollatzResearch.WordTrace]
  refine ⟨6451380072197820714858497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4300920048131880476572331 6451380072197820714858497)
  ·
    refine ⟨4838535054148365536143873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6451380072197820714858497 4838535054148365536143873)
    ·
      refine ⟨3628901290611274152107905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4838535054148365536143873 3628901290611274152107905)
      ·
        refine ⟨2721675967958455614080929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3628901290611274152107905 2721675967958455614080929)
        ·
          refine ⟨2041256975968841710560697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2721675967958455614080929 2041256975968841710560697)
          ·
            refine ⟨1530942731976631282920523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2041256975968841710560697 1530942731976631282920523)
            ·
              refine ⟨2296414097964946924380785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1530942731976631282920523 2296414097964946924380785)
              ·
                refine ⟨1722310573473710193285589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2296414097964946924380785 1722310573473710193285589)
                ·
                  refine ⟨40366654065790082655131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1722310573473710193285589 40366654065790082655131)
                  ·
                    rfl

theorem cell21_176881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 7].length) (baseStart_176881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_176881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_176881 prefixEnd_176881 := by exact prefixLift 176881
  have htrace : WordTrace (prefixWord ++ tailWord_176881) baseStart_176881 baseEnd_176881 := by
    simpa [prefixWord, tailWord_176881, baseEnd_176881] using wordTrace_append hprefix tailTrace_176881
  have hstable : (prefixWord ++ tailWord_176881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176881).length < 2 ^ (prefixWord ++ tailWord_176881).sum := by decide
  have hdescent : baseEnd_176881 < baseStart_176881 := by decide
  rcases family_descends (prefixWord ++ tailWord_176881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177002 : List Nat := [3, 1, 3, 14]
def baseStart_177002 : Nat := 118140960795 + 177002 * 2 ^ 59
def prefixEnd_177002 : Nat := 4983230072969 + 3 ^ 40 * 177002 * 2
def baseEnd_177002 : Nat := 166231555202966095219

theorem tailTrace_177002 : CollatzResearch.WordTrace tailWord_177002 prefixEnd_177002 166231555202966095219 := by
  unfold tailWord_177002
  simp only [CollatzResearch.WordTrace]
  refine ⟨1613948326189864595003315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4303862203172972253342173 1613948326189864595003315)
  ·
    refine ⟨2420922489284796892504973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1613948326189864595003315 2420922489284796892504973)
    ·
      refine ⟨907845933481798834689365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2420922489284796892504973 907845933481798834689365)
      ·
        refine ⟨166231555202966095219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 907845933481798834689365 166231555202966095219)
        ·
          rfl

theorem cell21_177002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 14].length) (baseStart_177002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_177002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_177002 prefixEnd_177002 := by exact prefixLift 177002
  have htrace : WordTrace (prefixWord ++ tailWord_177002) baseStart_177002 baseEnd_177002 := by
    simpa [prefixWord, tailWord_177002, baseEnd_177002] using wordTrace_append hprefix tailTrace_177002
  have hstable : (prefixWord ++ tailWord_177002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177002).length < 2 ^ (prefixWord ++ tailWord_177002).sum := by decide
  have hdescent : baseEnd_177002 < baseStart_177002 := by decide
  rcases family_descends (prefixWord ++ tailWord_177002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177033 : List Nat := [1, 2, 1, 1, 5, 2, 1, 1, 7]
def baseStart_177033 : Nat := 118140960795 + 177033 * 2 ^ 59
def prefixEnd_177033 : Nat := 4983230072969 + 3 ^ 40 * 177033 * 2
def baseEnd_177033 : Nat := 40401342536671596121487

theorem tailTrace_177033 : CollatzResearch.WordTrace tailWord_177033 prefixEnd_177033 40401342536671596121487 := by
  unfold tailWord_177033
  simp only [CollatzResearch.WordTrace]
  refine ⟨6456923967647150674391753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4304615978431433782927835 6456923967647150674391753)
  ·
    refine ⟨4842692975735363005793815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6456923967647150674391753 4842692975735363005793815)
    ·
      refine ⟨7264039463603044508690723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4842692975735363005793815 7264039463603044508690723)
      ·
        refine ⟨10896059195404566763036085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7264039463603044508690723 10896059195404566763036085)
        ·
          refine ⟨1021505549569178134034633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10896059195404566763036085 1021505549569178134034633)
          ·
            refine ⟨766129162176883600525975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1021505549569178134034633 766129162176883600525975)
            ·
              refine ⟨1149193743265325400788963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 766129162176883600525975 1149193743265325400788963)
              ·
                refine ⟨1723790614897988101183445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1149193743265325400788963 1723790614897988101183445)
                ·
                  refine ⟨40401342536671596121487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1723790614897988101183445 40401342536671596121487)
                  ·
                    rfl

theorem cell21_177033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 7].length) (baseStart_177033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_177033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_177033 prefixEnd_177033 := by exact prefixLift 177033
  have htrace : WordTrace (prefixWord ++ tailWord_177033) baseStart_177033 baseEnd_177033 := by
    simpa [prefixWord, tailWord_177033, baseEnd_177033] using wordTrace_append hprefix tailTrace_177033
  have hstable : (prefixWord ++ tailWord_177033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177033).length < 2 ^ (prefixWord ++ tailWord_177033).sum := by decide
  have hdescent : baseEnd_177033 < baseStart_177033 := by decide
  rcases family_descends (prefixWord ++ tailWord_177033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177095 : List Nat := [1, 1, 4, 1, 1, 2, 6, 5]
def baseStart_177095 : Nat := 118140960795 + 177095 * 2 ^ 59
def prefixEnd_177095 : Nat := 4983230072969 + 3 ^ 40 * 177095 * 2
def baseEnd_177095 : Nat := 13471830593791088696009

theorem tailTrace_177095 : CollatzResearch.WordTrace tailWord_177095 prefixEnd_177095 13471830593791088696009 := by
  unfold tailWord_177095
  simp only [CollatzResearch.WordTrace]
  refine ⟨6459185293422535263148739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4306123528948356842099159 6459185293422535263148739)
  ·
    refine ⟨9688777940133802894723109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6459185293422535263148739 9688777940133802894723109)
    ·
      refine ⟨1816645863775088042760583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9688777940133802894723109 1816645863775088042760583)
      ·
        refine ⟨2724968795662632064140875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1816645863775088042760583 2724968795662632064140875)
        ·
          refine ⟨4087453193493948096211313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2724968795662632064140875 4087453193493948096211313)
          ·
            refine ⟨3065589895120461072158485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4087453193493948096211313 3065589895120461072158485)
            ·
              refine ⟨143699526333771612757429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3065589895120461072158485 143699526333771612757429)
              ·
                refine ⟨13471830593791088696009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 143699526333771612757429 13471830593791088696009)
                ·
                  rfl

theorem cell21_177095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 5].length) (baseStart_177095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_177095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_177095 prefixEnd_177095 := by exact prefixLift 177095
  have htrace : WordTrace (prefixWord ++ tailWord_177095) baseStart_177095 baseEnd_177095 := by
    simpa [prefixWord, tailWord_177095, baseEnd_177095] using wordTrace_append hprefix tailTrace_177095
  have hstable : (prefixWord ++ tailWord_177095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177095).length < 2 ^ (prefixWord ++ tailWord_177095).sum := by decide
  have hdescent : baseEnd_177095 < baseStart_177095 := by decide
  rcases family_descends (prefixWord ++ tailWord_177095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177188 : List Nat := [2, 3, 1, 4, 1, 3, 1, 6]
def baseStart_177188 : Nat := 118140960795 + 177188 * 2 ^ 59
def prefixEnd_177188 : Nat := 4983230072969 + 3 ^ 40 * 177188 * 2
def baseEnd_177188 : Nat := 13478905216141923679279

theorem tailTrace_177188 : CollatzResearch.WordTrace tailWord_177188 prefixEnd_177188 13478905216141923679279 := by
  unfold tailWord_177188
  simp only [CollatzResearch.WordTrace]
  refine ⟨3231288641042806073142109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4308384854723741430856145 3231288641042806073142109)
  ·
    refine ⟨1211733240391052277428291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3231288641042806073142109 1211733240391052277428291)
    ·
      refine ⟨1817599860586578416142437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1211733240391052277428291 1817599860586578416142437)
      ·
        refine ⟨340799973859983453026707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1817599860586578416142437 340799973859983453026707)
        ·
          refine ⟨511199960789975179540061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340799973859983453026707 511199960789975179540061)
          ·
            refine ⟨191699985296240692327523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 511199960789975179540061 191699985296240692327523)
            ·
              refine ⟨287549977944361038491285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191699985296240692327523 287549977944361038491285)
              ·
                refine ⟨13478905216141923679279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 287549977944361038491285 13478905216141923679279)
                ·
                  rfl

theorem cell21_177188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 6].length) (baseStart_177188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_177188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_177188 prefixEnd_177188 := by exact prefixLift 177188
  have htrace : WordTrace (prefixWord ++ tailWord_177188) baseStart_177188 baseEnd_177188 := by
    simpa [prefixWord, tailWord_177188, baseEnd_177188] using wordTrace_append hprefix tailTrace_177188
  have hstable : (prefixWord ++ tailWord_177188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177188).length < 2 ^ (prefixWord ++ tailWord_177188).sum := by decide
  have hdescent : baseEnd_177188 < baseStart_177188 := by decide
  rcases family_descends (prefixWord ++ tailWord_177188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177230 : List Nat := [4, 1, 1, 1, 1, 3, 10]
def baseStart_177230 : Nat := 118140960795 + 177230 * 2 ^ 59
def prefixEnd_177230 : Nat := 4983230072969 + 3 ^ 40 * 177230 * 2
def baseEnd_177230 : Nat := 4494033402293670148639

theorem tailTrace_177230 : CollatzResearch.WordTrace tailWord_177230 prefixEnd_177230 4494033402293670148639 := by
  unfold tailWord_177230
  simp only [CollatzResearch.WordTrace]
  refine ⟨808013643491681664914143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4309406098622302212875429 808013643491681664914143)
  ·
    refine ⟨1212020465237522497371215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 808013643491681664914143 1212020465237522497371215)
    ·
      refine ⟨1818030697856283746056823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1212020465237522497371215 1818030697856283746056823)
      ·
        refine ⟨2727046046784425619085235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1818030697856283746056823 2727046046784425619085235)
        ·
          refine ⟨4090569070176638428627853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2727046046784425619085235 4090569070176638428627853)
          ·
            refine ⟨1533963401316239410735445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4090569070176638428627853 1533963401316239410735445)
            ·
              refine ⟨4494033402293670148639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1533963401316239410735445 4494033402293670148639)
              ·
                rfl

theorem cell21_177230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 10].length) (baseStart_177230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_177230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_177230 prefixEnd_177230 := by exact prefixLift 177230
  have htrace : WordTrace (prefixWord ++ tailWord_177230) baseStart_177230 baseEnd_177230 := by
    simpa [prefixWord, tailWord_177230, baseEnd_177230] using wordTrace_append hprefix tailTrace_177230
  have hstable : (prefixWord ++ tailWord_177230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177230).length < 2 ^ (prefixWord ++ tailWord_177230).sum := by decide
  have hdescent : baseEnd_177230 < baseStart_177230 := by decide
  rcases family_descends (prefixWord ++ tailWord_177230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177351 : List Nat := [1, 1, 4, 1, 1, 1, 1, 5, 6]
def baseStart_177351 : Nat := 118140960795 + 177351 * 2 ^ 59
def prefixEnd_177351 : Nat := 4983230072969 + 3 ^ 40 * 177351 * 2
def baseEnd_177351 : Nat := 40473914469173709820837

theorem tailTrace_177351 : CollatzResearch.WordTrace tailWord_177351 prefixEnd_177351 40473914469173709820837 := by
  unfold tailWord_177351
  simp only [CollatzResearch.WordTrace]
  refine ⟨6468522380495090984467907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4312348253663393989645271 6468522380495090984467907)
  ·
    refine ⟨9702783570742636476701861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6468522380495090984467907 9702783570742636476701861)
    ·
      refine ⟨1819271919514244339381599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9702783570742636476701861 1819271919514244339381599)
      ·
        refine ⟨2728907879271366509072399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1819271919514244339381599 2728907879271366509072399)
        ·
          refine ⟨4093361818907049763608599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2728907879271366509072399 4093361818907049763608599)
          ·
            refine ⟨6140042728360574645412899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4093361818907049763608599 6140042728360574645412899)
            ·
              refine ⟨9210064092540861968119349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6140042728360574645412899 9210064092540861968119349)
              ·
                refine ⟨863443508675705809511189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9210064092540861968119349 863443508675705809511189)
                ·
                  refine ⟨40473914469173709820837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 863443508675705809511189 40473914469173709820837)
                  ·
                    rfl

theorem cell21_177351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 6].length) (baseStart_177351 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_177351 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_177351 prefixEnd_177351 := by exact prefixLift 177351
  have htrace : WordTrace (prefixWord ++ tailWord_177351) baseStart_177351 baseEnd_177351 := by
    simpa [prefixWord, tailWord_177351, baseEnd_177351] using wordTrace_append hprefix tailTrace_177351
  have hstable : (prefixWord ++ tailWord_177351).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177351).length < 2 ^ (prefixWord ++ tailWord_177351).sum := by decide
  have hdescent : baseEnd_177351 < baseStart_177351 := by decide
  rcases family_descends (prefixWord ++ tailWord_177351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177413 : List Nat := [1, 3, 1, 1, 2, 1, 6, 1, 5]
def baseStart_177413 : Nat := 118140960795 + 177413 * 2 ^ 59
def prefixEnd_177413 : Nat := 4983230072969 + 3 ^ 40 * 177413 * 2
def baseEnd_177413 : Nat := 40488063713875379787377

theorem tailTrace_177413 : CollatzResearch.WordTrace tailWord_177413 prefixEnd_177413 40488063713875379787377 := by
  unfold tailWord_177413
  simp only [CollatzResearch.WordTrace]
  refine ⟨6470783706270475573224893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4313855804180317048816595 6470783706270475573224893)
  ·
    refine ⟨2426543889851428339959335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6470783706270475573224893 2426543889851428339959335)
    ·
      refine ⟨3639815834777142509939003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2426543889851428339959335 3639815834777142509939003)
      ·
        refine ⟨5459723752165713764908505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3639815834777142509939003 5459723752165713764908505)
        ·
          refine ⟨4094792814124285323681379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5459723752165713764908505 4094792814124285323681379)
          ·
            refine ⟨6142189221186427985522069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4094792814124285323681379 6142189221186427985522069)
            ·
              refine ⟨287915119743113811821347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6142189221186427985522069 287915119743113811821347)
              ·
                refine ⟨431872679614670717732021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 287915119743113811821347 431872679614670717732021)
                ·
                  refine ⟨40488063713875379787377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 431872679614670717732021 40488063713875379787377)
                  ·
                    rfl

theorem cell21_177413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 5].length) (baseStart_177413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_177413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_177413 prefixEnd_177413 := by exact prefixLift 177413
  have htrace : WordTrace (prefixWord ++ tailWord_177413) baseStart_177413 baseEnd_177413 := by
    simpa [prefixWord, tailWord_177413, baseEnd_177413] using wordTrace_append hprefix tailTrace_177413
  have hstable : (prefixWord ++ tailWord_177413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177413).length < 2 ^ (prefixWord ++ tailWord_177413).sum := by decide
  have hdescent : baseEnd_177413 < baseStart_177413 := by decide
  rcases family_descends (prefixWord ++ tailWord_177413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177458 : List Nat := [3, 2, 1, 1, 4, 1, 9]
def baseStart_177458 : Nat := 118140960795 + 177458 * 2 ^ 59
def prefixEnd_177458 : Nat := 4983230072969 + 3 ^ 40 * 177458 * 2
def baseEnd_177458 : Nat := 4499814814107255726365

theorem tailTrace_177458 : CollatzResearch.WordTrace tailWord_177458 prefixEnd_177458 4499814814107255726365 := by
  unfold tailWord_177458
  simp only [CollatzResearch.WordTrace]
  refine ⟨1618106247776862064653257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4314949994071632172408685 1618106247776862064653257)
  ·
    refine ⟨1213579685832646548489943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1618106247776862064653257 1213579685832646548489943)
    ·
      refine ⟨1820369528748969822734915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1213579685832646548489943 1820369528748969822734915)
      ·
        refine ⟨2730554293123454734102373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1820369528748969822734915 2730554293123454734102373)
        ·
          refine ⟨511978929960647762644195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2730554293123454734102373 511978929960647762644195)
          ·
            refine ⟨767968394940971643966293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 511978929960647762644195 767968394940971643966293)
            ·
              refine ⟨4499814814107255726365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 767968394940971643966293 4499814814107255726365)
              ·
                rfl

theorem cell21_177458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 9].length) (baseStart_177458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_177458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_177458 prefixEnd_177458 := by exact prefixLift 177458
  have htrace : WordTrace (prefixWord ++ tailWord_177458) baseStart_177458 baseEnd_177458 := by
    simpa [prefixWord, tailWord_177458, baseEnd_177458] using wordTrace_append hprefix tailTrace_177458
  have hstable : (prefixWord ++ tailWord_177458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177458).length < 2 ^ (prefixWord ++ tailWord_177458).sum := by decide
  have hdescent : baseEnd_177458 < baseStart_177458 := by decide
  rcases family_descends (prefixWord ++ tailWord_177458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177520 : List Nat := [2, 1, 1, 1, 4, 2, 4, 2, 4]
def baseStart_177520 : Nat := 118140960795 + 177520 * 2 ^ 59
def prefixEnd_177520 : Nat := 4983230072969 + 3 ^ 40 * 177520 * 2
def baseEnd_177520 : Nat := 40512482571666971503825

theorem tailTrace_177520 : CollatzResearch.WordTrace tailWord_177520 prefixEnd_177520 40512482571666971503825 := by
  unfold tailWord_177520
  simp only [CollatzResearch.WordTrace]
  refine ⟨3237343158441416423685007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4316457544588555231580009 3237343158441416423685007)
  ·
    refine ⟨4856014737662124635527511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3237343158441416423685007 4856014737662124635527511)
    ·
      refine ⟨7284022106493186953291267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4856014737662124635527511 7284022106493186953291267)
      ·
        refine ⟨10926033159739780429936901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7284022106493186953291267 10926033159739780429936901)
        ·
          refine ⟨2048631217451208830613169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10926033159739780429936901 2048631217451208830613169)
          ·
            refine ⟨1536473413088406622959877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2048631217451208830613169 1536473413088406622959877)
            ·
              refine ⟨288088764954076241804977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1536473413088406622959877 288088764954076241804977)
              ·
                refine ⟨216066573715557181353733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 288088764954076241804977 216066573715557181353733)
                ·
                  refine ⟨40512482571666971503825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 216066573715557181353733 40512482571666971503825)
                  ·
                    rfl

theorem cell21_177520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 2, 4].length) (baseStart_177520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_177520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_177520 prefixEnd_177520 := by exact prefixLift 177520
  have htrace : WordTrace (prefixWord ++ tailWord_177520) baseStart_177520 baseEnd_177520 := by
    simpa [prefixWord, tailWord_177520, baseEnd_177520] using wordTrace_append hprefix tailTrace_177520
  have hstable : (prefixWord ++ tailWord_177520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177520).length < 2 ^ (prefixWord ++ tailWord_177520).sum := by decide
  have hdescent : baseEnd_177520 < baseStart_177520 := by decide
  rcases family_descends (prefixWord ++ tailWord_177520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177602 : List Nat := [3, 5, 2, 1, 1, 1, 1, 7]
def baseStart_177602 : Nat := 118140960795 + 177602 * 2 ^ 59
def prefixEnd_177602 : Nat := 4983230072969 + 3 ^ 40 * 177602 * 2
def baseEnd_177602 : Nat := 13510398696284350378997

theorem tailTrace_177602 : CollatzResearch.WordTrace tailWord_177602 prefixEnd_177602 13510398696284350378997 := by
  unfold tailWord_177602
  simp only [CollatzResearch.WordTrace]
  refine ⟨1619419275646440212963765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4318451401723840567903373 1619419275646440212963765)
  ·
    refine ⟨151820557091853769965353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1619419275646440212963765 151820557091853769965353)
    ·
      refine ⟨113865417818890327474015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151820557091853769965353 113865417818890327474015)
      ·
        refine ⟨170798126728335491211023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113865417818890327474015 170798126728335491211023)
        ·
          refine ⟨256197190092503236816535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170798126728335491211023 256197190092503236816535)
          ·
            refine ⟨384295785138754855224803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256197190092503236816535 384295785138754855224803)
            ·
              refine ⟨576443677708132282837205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 384295785138754855224803 576443677708132282837205)
              ·
                refine ⟨13510398696284350378997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 576443677708132282837205 13510398696284350378997)
                ·
                  rfl

theorem cell21_177602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 7].length) (baseStart_177602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_177602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_177602 prefixEnd_177602 := by exact prefixLift 177602
  have htrace : WordTrace (prefixWord ++ tailWord_177602) baseStart_177602 baseEnd_177602 := by
    simpa [prefixWord, tailWord_177602, baseEnd_177602] using wordTrace_append hprefix tailTrace_177602
  have hstable : (prefixWord ++ tailWord_177602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177602).length < 2 ^ (prefixWord ++ tailWord_177602).sum := by decide
  have hdescent : baseEnd_177602 < baseStart_177602 := by decide
  rcases family_descends (prefixWord ++ tailWord_177602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177610 : List Nat := [3, 1, 2, 1, 2, 4, 1, 7]
def baseStart_177610 : Nat := 118140960795 + 177610 * 2 ^ 59
def prefixEnd_177610 : Nat := 4983230072969 + 3 ^ 40 * 177610 * 2
def baseEnd_177610 : Nat := 13511007265948938334547

theorem tailTrace_177610 : CollatzResearch.WordTrace tailWord_177610 prefixEnd_177610 13511007265948938334547 := by
  unfold tailWord_177610
  simp only [CollatzResearch.WordTrace]
  refine ⟨1619492221639194554536571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4318645924371185478764189 1619492221639194554536571)
  ·
    refine ⟨2429238332458791831804857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1619492221639194554536571 2429238332458791831804857)
    ·
      refine ⟨1821928749344093873853643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2429238332458791831804857 1821928749344093873853643)
      ·
        refine ⟨2732893124016140810780465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1821928749344093873853643 2732893124016140810780465)
        ·
          refine ⟨2049669843012105608085349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2732893124016140810780465 2049669843012105608085349)
          ·
            refine ⟨384313095564769801516003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2049669843012105608085349 384313095564769801516003)
            ·
              refine ⟨576469643347154702274005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 384313095564769801516003 576469643347154702274005)
              ·
                refine ⟨13511007265948938334547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 576469643347154702274005 13511007265948938334547)
                ·
                  rfl

theorem cell21_177610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 7].length) (baseStart_177610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_177610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_177610 prefixEnd_177610 := by exact prefixLift 177610
  have htrace : WordTrace (prefixWord ++ tailWord_177610) baseStart_177610 baseEnd_177610 := by
    simpa [prefixWord, tailWord_177610, baseEnd_177610] using wordTrace_append hprefix tailTrace_177610
  have hstable : (prefixWord ++ tailWord_177610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177610).length < 2 ^ (prefixWord ++ tailWord_177610).sum := by decide
  have hdescent : baseEnd_177610 < baseStart_177610 := by decide
  rcases family_descends (prefixWord ++ tailWord_177610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177624 : List Nat := [2, 1, 2, 2, 2, 1, 2, 2, 7]
def baseStart_177624 : Nat := 118140960795 + 177624 * 2 ^ 59
def prefixEnd_177624 : Nat := 4983230072969 + 3 ^ 40 * 177624 * 2
def baseEnd_177624 : Nat := 40536216788585901770279

theorem tailTrace_177624 : CollatzResearch.WordTrace tailWord_177624 prefixEnd_177624 40536216788585901770279 := by
  unfold tailWord_177624
  simp only [CollatzResearch.WordTrace]
  refine ⟨3239239754253029304577963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4318986339004039072770617 3239239754253029304577963)
  ·
    refine ⟨4858859631379543956866945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3239239754253029304577963 4858859631379543956866945)
    ·
      refine ⟨3644144723534657967650209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4858859631379543956866945 3644144723534657967650209)
      ·
        refine ⟨2733108542650993475737657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3644144723534657967650209 2733108542650993475737657)
        ·
          refine ⟨2049831406988245106803243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2733108542650993475737657 2049831406988245106803243)
          ·
            refine ⟨3074747110482367660204865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2049831406988245106803243 3074747110482367660204865)
            ·
              refine ⟨2306060332861775745153649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3074747110482367660204865 2306060332861775745153649)
              ·
                refine ⟨1729545249646331808865237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2306060332861775745153649 1729545249646331808865237)
                ·
                  refine ⟨40536216788585901770279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1729545249646331808865237 40536216788585901770279)
                  ·
                    rfl

theorem cell21_177624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 7].length) (baseStart_177624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_177624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_177624 prefixEnd_177624 := by exact prefixLift 177624
  have htrace : WordTrace (prefixWord ++ tailWord_177624) baseStart_177624 baseEnd_177624 := by
    simpa [prefixWord, tailWord_177624, baseEnd_177624] using wordTrace_append hprefix tailTrace_177624
  have hstable : (prefixWord ++ tailWord_177624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177624).length < 2 ^ (prefixWord ++ tailWord_177624).sum := by decide
  have hdescent : baseEnd_177624 < baseStart_177624 := by decide
  rcases family_descends (prefixWord ++ tailWord_177624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177717 : List Nat := [1, 3, 3, 1, 1, 4, 1, 2, 5]
def baseStart_177717 : Nat := 118140960795 + 177717 * 2 ^ 59
def prefixEnd_177717 : Nat := 4983230072969 + 3 ^ 40 * 177717 * 2
def baseEnd_177717 : Nat := 40557440655638406720089

theorem tailTrace_177717 : CollatzResearch.WordTrace tailWord_177717 prefixEnd_177717 40557440655638406720089 := by
  unfold tailWord_177717
  simp only [CollatzResearch.WordTrace]
  refine ⟨6481871497169135492291405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4321247664779423661527603 6481871497169135492291405)
  ·
    refine ⟨2430701811438425809609277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6481871497169135492291405 2430701811438425809609277)
    ·
      refine ⟨911513179289409678603479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2430701811438425809609277 911513179289409678603479)
      ·
        refine ⟨1367269768934114517905219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 911513179289409678603479 1367269768934114517905219)
        ·
          refine ⟨2050904653401171776857829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1367269768934114517905219 2050904653401171776857829)
          ·
            refine ⟨384544622512719708160843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2050904653401171776857829 384544622512719708160843)
            ·
              refine ⟨576816933769079562241265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 384544622512719708160843 576816933769079562241265)
              ·
                refine ⟨432612700326809671680949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 576816933769079562241265 432612700326809671680949)
                ·
                  refine ⟨40557440655638406720089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 432612700326809671680949 40557440655638406720089)
                  ·
                    rfl

theorem cell21_177717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 5].length) (baseStart_177717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_177717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_177717 prefixEnd_177717 := by exact prefixLift 177717
  have htrace : WordTrace (prefixWord ++ tailWord_177717) baseStart_177717 baseEnd_177717 := by
    simpa [prefixWord, tailWord_177717, baseEnd_177717] using wordTrace_append hprefix tailTrace_177717
  have hstable : (prefixWord ++ tailWord_177717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177717).length < 2 ^ (prefixWord ++ tailWord_177717).sum := by decide
  have hdescent : baseEnd_177717 < baseStart_177717 := by decide
  rcases family_descends (prefixWord ++ tailWord_177717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177745 : List Nat := [1, 2, 2, 1, 3, 2, 10]
def baseStart_177745 : Nat := 118140960795 + 177745 * 2 ^ 59
def prefixEnd_177745 : Nat := 4983230072969 + 3 ^ 40 * 177745 * 2
def baseEnd_177745 : Nat := 4507092293012953361485

theorem tailTrace_177745 : CollatzResearch.WordTrace tailWord_177745 prefixEnd_177745 4507092293012953361485 := by
  unfold tailWord_177745
  simp only [CollatzResearch.WordTrace]
  refine ⟨6482892741067696274310689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4321928494045130849540459 6482892741067696274310689)
  ·
    refine ⟨4862169555800772205733017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6482892741067696274310689 4862169555800772205733017)
    ·
      refine ⟨3646627166850579154299763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4862169555800772205733017 3646627166850579154299763)
      ·
        refine ⟨5469940750275868731449645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3646627166850579154299763 5469940750275868731449645)
        ·
          refine ⟨2051227781353450774293617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5469940750275868731449645 2051227781353450774293617)
          ·
            refine ⟨1538420836015088080720213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2051227781353450774293617 1538420836015088080720213)
            ·
              refine ⟨4507092293012953361485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1538420836015088080720213 4507092293012953361485)
              ·
                rfl

theorem cell21_177745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 10].length) (baseStart_177745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_177745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_177745 prefixEnd_177745 := by exact prefixLift 177745
  have htrace : WordTrace (prefixWord ++ tailWord_177745) baseStart_177745 baseEnd_177745 := by
    simpa [prefixWord, tailWord_177745, baseEnd_177745] using wordTrace_append hprefix tailTrace_177745
  have hstable : (prefixWord ++ tailWord_177745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177745).length < 2 ^ (prefixWord ++ tailWord_177745).sum := by decide
  have hdescent : baseEnd_177745 < baseStart_177745 := by decide
  rcases family_descends (prefixWord ++ tailWord_177745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177765 : List Nat := [1, 3, 1, 3, 3, 2, 3, 1, 4]
def baseStart_177765 : Nat := 118140960795 + 177765 * 2 ^ 59
def prefixEnd_177765 : Nat := 4983230072969 + 3 ^ 40 * 177765 * 2
def baseEnd_177765 : Nat := 40568394909600989919991

theorem tailTrace_177765 : CollatzResearch.WordTrace tailWord_177765 prefixEnd_177765 40568394909600989919991 := by
  unfold tailWord_177765
  simp only [CollatzResearch.WordTrace]
  refine ⟨6483622200995239690038749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4322414800663493126692499 6483622200995239690038749)
  ·
    refine ⟨2431358325373214883764531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6483622200995239690038749 2431358325373214883764531)
    ·
      refine ⟨3647037488059822325646797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2431358325373214883764531 3647037488059822325646797)
      ·
        refine ⟨1367639058022433372117549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3647037488059822325646797 1367639058022433372117549)
        ·
          refine ⟨512864646758412514544081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1367639058022433372117549 512864646758412514544081)
          ·
            refine ⟨384648485068809385908061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 512864646758412514544081 384648485068809385908061)
            ·
              refine ⟨144243181900803519715523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 384648485068809385908061 144243181900803519715523)
              ·
                refine ⟨216364772851205279573285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144243181900803519715523 216364772851205279573285)
                ·
                  refine ⟨40568394909600989919991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 216364772851205279573285 40568394909600989919991)
                  ·
                    rfl

theorem cell21_177765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 1, 4].length) (baseStart_177765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_177765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_177765 prefixEnd_177765 := by exact prefixLift 177765
  have htrace : WordTrace (prefixWord ++ tailWord_177765) baseStart_177765 baseEnd_177765 := by
    simpa [prefixWord, tailWord_177765, baseEnd_177765] using wordTrace_append hprefix tailTrace_177765
  have hstable : (prefixWord ++ tailWord_177765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177765).length < 2 ^ (prefixWord ++ tailWord_177765).sum := by decide
  have hdescent : baseEnd_177765 < baseStart_177765 := by decide
  rcases family_descends (prefixWord ++ tailWord_177765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177824 : List Nat := [2, 1, 1, 4, 3, 2, 1, 3, 4]
def baseStart_177824 : Nat := 118140960795 + 177824 * 2 ^ 59
def prefixEnd_177824 : Nat := 4983230072969 + 3 ^ 40 * 177824 * 2
def baseEnd_177824 : Nat := 40581859513429998436537

theorem tailTrace_177824 : CollatzResearch.WordTrace tailWord_177824 prefixEnd_177824 40581859513429998436537 := by
  unfold tailWord_177824
  simp only [CollatzResearch.WordTrace]
  refine ⟨3242887053890746383218263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4323849405187661844291017 3242887053890746383218263)
  ·
    refine ⟨4864330580836119574827395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3242887053890746383218263 4864330580836119574827395)
    ·
      refine ⟨7296495871254179362241093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4864330580836119574827395 7296495871254179362241093)
      ·
        refine ⟨1368092975860158630420205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7296495871254179362241093 1368092975860158630420205)
        ·
          refine ⟨513034865947559486407577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1368092975860158630420205 513034865947559486407577)
          ·
            refine ⟨384776149460669614805683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 513034865947559486407577 384776149460669614805683)
            ·
              refine ⟨577164224191004422208525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 384776149460669614805683 577164224191004422208525)
              ·
                refine ⟨216436584071626658328197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 577164224191004422208525 216436584071626658328197)
                ·
                  refine ⟨40581859513429998436537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 216436584071626658328197 40581859513429998436537)
                  ·
                    rfl

theorem cell21_177824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3, 4].length) (baseStart_177824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_177824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_177824 prefixEnd_177824 := by exact prefixLift 177824
  have htrace : WordTrace (prefixWord ++ tailWord_177824) baseStart_177824 baseEnd_177824 := by
    simpa [prefixWord, tailWord_177824, baseEnd_177824] using wordTrace_append hprefix tailTrace_177824
  have hstable : (prefixWord ++ tailWord_177824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177824).length < 2 ^ (prefixWord ++ tailWord_177824).sum := by decide
  have hdescent : baseEnd_177824 < baseStart_177824 := by decide
  rcases family_descends (prefixWord ++ tailWord_177824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178021 : List Nat := [1, 3, 1, 3, 1, 1, 1, 7, 3]
def baseStart_178021 : Nat := 118140960795 + 178021 * 2 ^ 59
def prefixEnd_178021 : Nat := 4983230072969 + 3 ^ 40 * 178021 * 2
def baseEnd_178021 : Nat := 40626817597401433652801

theorem tailTrace_178021 : CollatzResearch.WordTrace tailWord_178021 prefixEnd_178021 40626817597401433652801 := by
  unfold tailWord_178021
  simp only [CollatzResearch.WordTrace]
  refine ⟨6492959288067795411357917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4328639525378530274238611 6492959288067795411357917)
  ·
    refine ⟨2434859733025423279259219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6492959288067795411357917 2434859733025423279259219)
    ·
      refine ⟨3652289599538134918888829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2434859733025423279259219 3652289599538134918888829)
      ·
        refine ⟨1369608599826800594583311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3652289599538134918888829 1369608599826800594583311)
        ·
          refine ⟨2054412899740200891874967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1369608599826800594583311 2054412899740200891874967)
          ·
            refine ⟨3081619349610301337812451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2054412899740200891874967 3081619349610301337812451)
            ·
              refine ⟨4622429024415452006718677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3081619349610301337812451 4622429024415452006718677)
              ·
                refine ⟨108338180259737156407469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4622429024415452006718677 108338180259737156407469)
                ·
                  refine ⟨40626817597401433652801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108338180259737156407469 40626817597401433652801)
                  ·
                    rfl

theorem cell21_178021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 7, 3].length) (baseStart_178021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_178021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_178021 prefixEnd_178021 := by exact prefixLift 178021
  have htrace : WordTrace (prefixWord ++ tailWord_178021) baseStart_178021 baseEnd_178021 := by
    simpa [prefixWord, tailWord_178021, baseEnd_178021] using wordTrace_append hprefix tailTrace_178021
  have hstable : (prefixWord ++ tailWord_178021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178021).length < 2 ^ (prefixWord ++ tailWord_178021).sum := by decide
  have hdescent : baseEnd_178021 < baseStart_178021 := by decide
  rcases family_descends (prefixWord ++ tailWord_178021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178097 : List Nat := [1, 2, 2, 4, 2, 2, 2, 1, 5]
def baseStart_178097 : Nat := 118140960795 + 178097 * 2 ^ 59
def prefixEnd_178097 : Nat := 4983230072969 + 3 ^ 40 * 178097 * 2
def baseEnd_178097 : Nat := 40644161832842190385979

theorem tailTrace_178097 : CollatzResearch.WordTrace tailWord_178097 prefixEnd_178097 40644161832842190385979 := by
  unfold tailWord_178097
  simp only [CollatzResearch.WordTrace]
  refine ⟨6495731235792460391124545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4330487490528306927416363 6495731235792460391124545)
  ·
    refine ⟨4871798426844345293343409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6495731235792460391124545 4871798426844345293343409)
    ·
      refine ⟨3653848820133258970007557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4871798426844345293343409 3653848820133258970007557)
      ·
        refine ⟨685096653774986056876417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3653848820133258970007557 685096653774986056876417)
        ·
          refine ⟨513822490331239542657313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 685096653774986056876417 513822490331239542657313)
          ·
            refine ⟨385366867748429656992985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 513822490331239542657313 385366867748429656992985)
            ·
              refine ⟨289025150811322242744739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 385366867748429656992985 289025150811322242744739)
              ·
                refine ⟨433537726216983364117109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 289025150811322242744739 433537726216983364117109)
                ·
                  refine ⟨40644161832842190385979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 433537726216983364117109 40644161832842190385979)
                  ·
                    rfl

theorem cell21_178097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 5].length) (baseStart_178097 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_178097 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_178097 prefixEnd_178097 := by exact prefixLift 178097
  have htrace : WordTrace (prefixWord ++ tailWord_178097) baseStart_178097 baseEnd_178097 := by
    simpa [prefixWord, tailWord_178097, baseEnd_178097] using wordTrace_append hprefix tailTrace_178097
  have hstable : (prefixWord ++ tailWord_178097).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178097).length < 2 ^ (prefixWord ++ tailWord_178097).sum := by decide
  have hdescent : baseEnd_178097 < baseStart_178097 := by decide
  rcases family_descends (prefixWord ++ tailWord_178097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178204 : List Nat := [2, 2, 3, 1, 3, 2, 2, 2, 4]
def baseStart_178204 : Nat := 118140960795 + 178204 * 2 ^ 59
def prefixEnd_178204 : Nat := 4983230072969 + 3 ^ 40 * 178204 * 2
def baseEnd_178204 : Nat := 40668580690633782102427

theorem tailTrace_178204 : CollatzResearch.WordTrace tailWord_178204 prefixEnd_178204 40668580690633782102427 := by
  unfold tailWord_178204
  simp only [CollatzResearch.WordTrace]
  refine ⟨3249816923202408832634833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4333089230936545110179777 3249816923202408832634833)
  ·
    refine ⟨2437362692401806624476125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3249816923202408832634833 2437362692401806624476125)
    ·
      refine ⟨914011009650677484178547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2437362692401806624476125 914011009650677484178547)
      ·
        refine ⟨1371016514476016226267821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 914011009650677484178547 1371016514476016226267821)
        ·
          refine ⟨514131192928506084850433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1371016514476016226267821 514131192928506084850433)
          ·
            refine ⟨385598394696379563637825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 514131192928506084850433 385598394696379563637825)
            ·
              refine ⟨289198796022284672728369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 385598394696379563637825 289198796022284672728369)
              ·
                refine ⟨216899097016713504546277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 289198796022284672728369 216899097016713504546277)
                ·
                  refine ⟨40668580690633782102427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 216899097016713504546277 40668580690633782102427)
                  ·
                    rfl

theorem cell21_178204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 2, 4].length) (baseStart_178204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_178204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_178204 prefixEnd_178204 := by exact prefixLift 178204
  have htrace : WordTrace (prefixWord ++ tailWord_178204) baseStart_178204 baseEnd_178204 := by
    simpa [prefixWord, tailWord_178204, baseEnd_178204] using wordTrace_append hprefix tailTrace_178204
  have hstable : (prefixWord ++ tailWord_178204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178204).length < 2 ^ (prefixWord ++ tailWord_178204).sum := by decide
  have hdescent : baseEnd_178204 < baseStart_178204 := by decide
  rcases family_descends (prefixWord ++ tailWord_178204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178218 : List Nat := [3, 1, 4, 1, 2, 1, 3, 6]
def baseStart_178218 : Nat := 118140960795 + 178218 * 2 ^ 59
def prefixEnd_178218 : Nat := 4983230072969 + 3 ^ 40 * 178218 * 2
def baseEnd_178218 : Nat := 13557258560457622956355

theorem tailTrace_178218 : CollatzResearch.WordTrace tailWord_178218 prefixEnd_178218 13557258560457622956355 := by
  unfold tailWord_178218
  simp only [CollatzResearch.WordTrace]
  refine ⟨1625036117088524514069827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4333429645569398704186205 1625036117088524514069827)
  ·
    refine ⟨2437554175632786771104741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1625036117088524514069827 2437554175632786771104741)
    ·
      refine ⟨457041407931147519582139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2437554175632786771104741 457041407931147519582139)
      ·
        refine ⟨685562111896721279373209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457041407931147519582139 685562111896721279373209)
        ·
          refine ⟨514171583922540959529907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 685562111896721279373209 514171583922540959529907)
          ·
            refine ⟨771257375883811439294861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 514171583922540959529907 771257375883811439294861)
            ·
              refine ⟨289221515956429289735573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 771257375883811439294861 289221515956429289735573)
              ·
                refine ⟨13557258560457622956355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 289221515956429289735573 13557258560457622956355)
                ·
                  rfl

theorem cell21_178218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 6].length) (baseStart_178218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_178218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_178218 prefixEnd_178218 := by exact prefixLift 178218
  have htrace : WordTrace (prefixWord ++ tailWord_178218) baseStart_178218 baseEnd_178218 := by
    simpa [prefixWord, tailWord_178218, baseEnd_178218] using wordTrace_append hprefix tailTrace_178218
  have hstable : (prefixWord ++ tailWord_178218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178218).length < 2 ^ (prefixWord ++ tailWord_178218).sum := by decide
  have hdescent : baseEnd_178218 < baseStart_178218 := by decide
  rcases family_descends (prefixWord ++ tailWord_178218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178249 : List Nat := [1, 2, 1, 1, 2, 2, 6, 3, 3]
def baseStart_178249 : Nat := 118140960795 + 178249 * 2 ^ 59
def prefixEnd_178249 : Nat := 4983230072969 + 3 ^ 40 * 178249 * 2
def baseEnd_178249 : Nat := 40678850303723703852335

theorem tailTrace_178249 : CollatzResearch.WordTrace tailWord_178249 prefixEnd_178249 40678850303723703852335 := by
  unfold tailWord_178249
  simp only [CollatzResearch.WordTrace]
  refine ⟨6501275131241790350657801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4334183420827860233771867 6501275131241790350657801)
  ·
    refine ⟨4875956348431342762993351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6501275131241790350657801 4875956348431342762993351)
    ·
      refine ⟨7313934522647014144490027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4875956348431342762993351 7313934522647014144490027)
      ·
        refine ⟨10970901783970521216735041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7313934522647014144490027 10970901783970521216735041)
        ·
          refine ⟨8228176337977890912551281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10970901783970521216735041 8228176337977890912551281)
          ·
            refine ⟨6171132253483418184413461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8228176337977890912551281 6171132253483418184413461)
            ·
              refine ⟨289271824382035227394381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6171132253483418184413461 289271824382035227394381)
              ·
                refine ⟨108476934143263210272893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 289271824382035227394381 108476934143263210272893)
                ·
                  refine ⟨40678850303723703852335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108476934143263210272893 40678850303723703852335)
                  ·
                    rfl

theorem cell21_178249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 3, 3].length) (baseStart_178249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_178249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_178249 prefixEnd_178249 := by exact prefixLift 178249
  have htrace : WordTrace (prefixWord ++ tailWord_178249) baseStart_178249 baseEnd_178249 := by
    simpa [prefixWord, tailWord_178249, baseEnd_178249] using wordTrace_append hprefix tailTrace_178249
  have hstable : (prefixWord ++ tailWord_178249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178249).length < 2 ^ (prefixWord ++ tailWord_178249).sum := by decide
  have hdescent : baseEnd_178249 < baseStart_178249 := by decide
  rcases family_descends (prefixWord ++ tailWord_178249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178263 : List Nat := [1, 1, 3, 2, 2, 1, 5, 2, 4]
def baseStart_178263 : Nat := 118140960795 + 178263 * 2 ^ 59
def prefixEnd_178263 : Nat := 4983230072969 + 3 ^ 40 * 178263 * 2
def baseEnd_178263 : Nat := 40682045294462790618973

theorem tailTrace_178263 : CollatzResearch.WordTrace tailWord_178263 prefixEnd_178263 40682045294462790618973 := by
  unfold tailWord_178263
  simp only [CollatzResearch.WordTrace]
  refine ⟨6501785753191070741667443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4334523835460713827778295 6501785753191070741667443)
  ·
    refine ⟨9752678629786606112501165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6501785753191070741667443 9752678629786606112501165)
    ·
      refine ⟨3657254486169977292187937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9752678629786606112501165 3657254486169977292187937)
      ·
        refine ⟨2742940864627482969140953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3657254486169977292187937 2742940864627482969140953)
        ·
          refine ⟨2057205648470612226855715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2742940864627482969140953 2057205648470612226855715)
          ·
            refine ⟨3085808472705918340283573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2057205648470612226855715 3085808472705918340283573)
            ·
              refine ⟨289294544316179844401585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3085808472705918340283573 289294544316179844401585)
              ·
                refine ⟨216970908237134883301189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 289294544316179844401585 216970908237134883301189)
                ·
                  refine ⟨40682045294462790618973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 216970908237134883301189 40682045294462790618973)
                  ·
                    rfl

theorem cell21_178263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 2, 4].length) (baseStart_178263 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_178263 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_178263 prefixEnd_178263 := by exact prefixLift 178263
  have htrace : WordTrace (prefixWord ++ tailWord_178263) baseStart_178263 baseEnd_178263 := by
    simpa [prefixWord, tailWord_178263, baseEnd_178263] using wordTrace_append hprefix tailTrace_178263
  have hstable : (prefixWord ++ tailWord_178263).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178263).length < 2 ^ (prefixWord ++ tailWord_178263).sum := by decide
  have hdescent : baseEnd_178263 < baseStart_178263 := by decide
  rcases family_descends (prefixWord ++ tailWord_178263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178294 : List Nat := [5, 1, 1, 2, 1, 3, 1, 7]
def baseStart_178294 : Nat := 118140960795 + 178294 * 2 ^ 59
def prefixEnd_178294 : Nat := 4983230072969 + 3 ^ 40 * 178294 * 2
def baseEnd_178294 : Nat := 13563039972271208534081

theorem tailTrace_178294 : CollatzResearch.WordTrace tailWord_178294 prefixEnd_178294 13563039972271208534081 := by
  unfold tailWord_178294
  simp only [CollatzResearch.WordTrace]
  refine ⟨406432276004922689752871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4335277610719175357363957 406432276004922689752871)
  ·
    refine ⟨609648414007384034629307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 406432276004922689752871 609648414007384034629307)
    ·
      refine ⟨914472621011076051943961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 609648414007384034629307 914472621011076051943961)
      ·
        refine ⟨685854465758307038957971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 914472621011076051943961 685854465758307038957971)
        ·
          refine ⟨1028781698637460558436957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 685854465758307038957971 1028781698637460558436957)
          ·
            refine ⟨385793136989047709413859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1028781698637460558436957 385793136989047709413859)
            ·
              refine ⟨578689705483571564120789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385793136989047709413859 578689705483571564120789)
              ·
                refine ⟨13563039972271208534081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 578689705483571564120789 13563039972271208534081)
                ·
                  rfl

theorem cell21_178294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_178294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_178294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_178294 prefixEnd_178294 := by exact prefixLift 178294
  have htrace : WordTrace (prefixWord ++ tailWord_178294) baseStart_178294 baseEnd_178294 := by
    simpa [prefixWord, tailWord_178294, baseEnd_178294] using wordTrace_append hprefix tailTrace_178294
  have hstable : (prefixWord ++ tailWord_178294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178294).length < 2 ^ (prefixWord ++ tailWord_178294).sum := by decide
  have hdescent : baseEnd_178294 < baseStart_178294 := by decide
  rcases family_descends (prefixWord ++ tailWord_178294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178418 : List Nat := [3, 2, 1, 3, 2, 2, 2, 3, 3]
def baseStart_178418 : Nat := 118140960795 + 178418 * 2 ^ 59
def prefixEnd_178418 : Nat := 4983230072969 + 3 ^ 40 * 178418 * 2
def baseEnd_178418 : Nat := 40717418406216965535323

theorem tailTrace_178418 : CollatzResearch.WordTrace tailWord_178418 prefixEnd_178418 40717418406216965535323 := by
  unfold tailWord_178418
  simp only [CollatzResearch.WordTrace]
  refine ⟨1626859766907383053389977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4338292711753021475706605 1626859766907383053389977)
  ·
    refine ⟨1220144825180537290042483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1626859766907383053389977 1220144825180537290042483)
    ·
      refine ⟨1830217237770805935063725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1220144825180537290042483 1830217237770805935063725)
      ·
        refine ⟨686331464164052225648897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1830217237770805935063725 686331464164052225648897)
        ·
          refine ⟨514748598123039169236673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 686331464164052225648897 514748598123039169236673)
          ·
            refine ⟨386061448592279376927505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 514748598123039169236673 386061448592279376927505)
            ·
              refine ⟨289546086444209532695629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 386061448592279376927505 289546086444209532695629)
              ·
                refine ⟨108579782416578574760861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 289546086444209532695629 108579782416578574760861)
                ·
                  refine ⟨40717418406216965535323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108579782416578574760861 40717418406216965535323)
                  ·
                    rfl

theorem cell21_178418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 3, 3].length) (baseStart_178418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_178418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_178418 prefixEnd_178418 := by exact prefixLift 178418
  have htrace : WordTrace (prefixWord ++ tailWord_178418) baseStart_178418 baseEnd_178418 := by
    simpa [prefixWord, tailWord_178418, baseEnd_178418] using wordTrace_append hprefix tailTrace_178418
  have hstable : (prefixWord ++ tailWord_178418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178418).length < 2 ^ (prefixWord ++ tailWord_178418).sum := by decide
  have hdescent : baseEnd_178418 < baseStart_178418 := by decide
  rcases family_descends (prefixWord ++ tailWord_178418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178488 : List Nat := [2, 1, 2, 1, 3, 1, 11]
def baseStart_178488 : Nat := 118140960795 + 178488 * 2 ^ 59
def prefixEnd_178488 : Nat := 4983230072969 + 3 ^ 40 * 178488 * 2
def baseEnd_178488 : Nat := 4525932595545822152057

theorem tailTrace_178488 : CollatzResearch.WordTrace tailWord_178488 prefixEnd_178488 4525932595545822152057 := by
  unfold tailWord_178488
  simp only [CollatzResearch.WordTrace]
  refine ⟨3254996088687967084304059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4339994784917289445738745 3254996088687967084304059)
  ·
    refine ⟨4882494133031950626456089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3254996088687967084304059 4882494133031950626456089)
    ·
      refine ⟨3661870599773962969842067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4882494133031950626456089 3661870599773962969842067)
      ·
        refine ⟨5492805899660944454763101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3661870599773962969842067 5492805899660944454763101)
        ·
          refine ⟨2059802212372854170536163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5492805899660944454763101 2059802212372854170536163)
          ·
            refine ⟨3089703318559281255804245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2059802212372854170536163 3089703318559281255804245)
            ·
              refine ⟨4525932595545822152057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 3089703318559281255804245 4525932595545822152057)
              ·
                rfl

theorem cell21_178488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 11].length) (baseStart_178488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_178488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_178488 prefixEnd_178488 := by exact prefixLift 178488
  have htrace : WordTrace (prefixWord ++ tailWord_178488) baseStart_178488 baseEnd_178488 := by
    simpa [prefixWord, tailWord_178488, baseEnd_178488] using wordTrace_append hprefix tailTrace_178488
  have hstable : (prefixWord ++ tailWord_178488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178488).length < 2 ^ (prefixWord ++ tailWord_178488).sum := by decide
  have hdescent : baseEnd_178488 < baseStart_178488 := by decide
  rcases family_descends (prefixWord ++ tailWord_178488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178519 : List Nat := [1, 1, 3, 2, 3, 1, 2, 1, 7]
def baseStart_178519 : Nat := 118140960795 + 178519 * 2 ^ 59
def prefixEnd_178519 : Nat := 4983230072969 + 3 ^ 40 * 178519 * 2
def baseEnd_178519 : Nat := 40740467982263234351783

theorem tailTrace_178519 : CollatzResearch.WordTrace tailWord_178519 prefixEnd_178519 40740467982263234351783 := by
  unfold tailWord_178519
  simp only [CollatzResearch.WordTrace]
  refine ⟨6511122840263626462986611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4340748560175750975324407 6511122840263626462986611)
  ·
    refine ⟨9766684260395439694479917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6511122840263626462986611 9766684260395439694479917)
    ·
      refine ⟨3662506597648289885429969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9766684260395439694479917 3662506597648289885429969)
      ·
        refine ⟨2746879948236217414072477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3662506597648289885429969 2746879948236217414072477)
        ·
          refine ⟨1030079980588581530277179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2746879948236217414072477 1030079980588581530277179)
          ·
            refine ⟨1545119970882872295415769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1030079980588581530277179 1545119970882872295415769)
            ·
              refine ⟨1158839978162154221561827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1545119970882872295415769 1158839978162154221561827)
              ·
                refine ⟨1738259967243231332342741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1158839978162154221561827 1738259967243231332342741)
                ·
                  refine ⟨40740467982263234351783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1738259967243231332342741 40740467982263234351783)
                  ·
                    rfl

theorem cell21_178519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 7].length) (baseStart_178519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_178519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_178519 prefixEnd_178519 := by exact prefixLift 178519
  have htrace : WordTrace (prefixWord ++ tailWord_178519) baseStart_178519 baseEnd_178519 := by
    simpa [prefixWord, tailWord_178519, baseEnd_178519] using wordTrace_append hprefix tailTrace_178519
  have hstable : (prefixWord ++ tailWord_178519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178519).length < 2 ^ (prefixWord ++ tailWord_178519).sum := by decide
  have hdescent : baseEnd_178519 < baseStart_178519 := by decide
  rcases family_descends (prefixWord ++ tailWord_178519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178674 : List Nat := [3, 2, 1, 4, 2, 1, 2, 6]
def baseStart_178674 : Nat := 118140960795 + 178674 * 2 ^ 59
def prefixEnd_178674 : Nat := 4983230072969 + 3 ^ 40 * 178674 * 2
def baseEnd_178674 : Nat := 13591947031339136422711

theorem tailTrace_178674 : CollatzResearch.WordTrace tailWord_178674 prefixEnd_178674 13591947031339136422711 := by
  unfold tailWord_178674
  simp only [CollatzResearch.WordTrace]
  refine ⟨1629194038675521983719769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4344517436468058623252717 1629194038675521983719769)
  ·
    refine ⟨1221895529006641487789827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1629194038675521983719769 1221895529006641487789827)
    ·
      refine ⟨1832843293509962231684741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1221895529006641487789827 1832843293509962231684741)
      ·
        refine ⟨343658117533117918440889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1832843293509962231684741 343658117533117918440889)
        ·
          refine ⟨257743588149838438830667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 343658117533117918440889 257743588149838438830667)
          ·
            refine ⟨386615382224757658246001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257743588149838438830667 386615382224757658246001)
            ·
              refine ⟨289961536668568243684501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 386615382224757658246001 289961536668568243684501)
              ·
                refine ⟨13591947031339136422711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 289961536668568243684501 13591947031339136422711)
                ·
                  rfl

theorem cell21_178674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 6].length) (baseStart_178674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_178674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_178674 prefixEnd_178674 := by exact prefixLift 178674
  have htrace : WordTrace (prefixWord ++ tailWord_178674) baseStart_178674 baseEnd_178674 := by
    simpa [prefixWord, tailWord_178674, baseEnd_178674] using wordTrace_append hprefix tailTrace_178674
  have hstable : (prefixWord ++ tailWord_178674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178674).length < 2 ^ (prefixWord ++ tailWord_178674).sum := by decide
  have hdescent : baseEnd_178674 < baseStart_178674 := by decide
  rcases family_descends (prefixWord ++ tailWord_178674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178716 : List Nat := [2, 2, 3, 1, 2, 11]
def baseStart_178716 : Nat := 118140960795 + 178716 * 2 ^ 59
def prefixEnd_178716 : Nat := 4983230072969 + 3 ^ 40 * 178716 * 2
def baseEnd_178716 : Nat := 1510571335786469243261

theorem tailTrace_178716 : CollatzResearch.WordTrace tailWord_178716 prefixEnd_178716 1510571335786469243261 := by
  unfold tailWord_178716
  simp only [CollatzResearch.WordTrace]
  refine ⟨3259154010274964553954001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4345538680366619405272001 3259154010274964553954001)
  ·
    refine ⟨2444365507706223415465501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3259154010274964553954001 2444365507706223415465501)
    ·
      refine ⟨916637065389833780799563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2444365507706223415465501 916637065389833780799563)
      ·
        refine ⟨1374955598084750671199345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 916637065389833780799563 1374955598084750671199345)
        ·
          refine ⟨1031216698563563003399509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1374955598084750671199345 1031216698563563003399509)
          ·
            refine ⟨1510571335786469243261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1031216698563563003399509 1510571335786469243261)
            ·
              rfl

theorem cell21_178716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 11].length) (baseStart_178716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_178716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_178716 prefixEnd_178716 := by exact prefixLift 178716
  have htrace : WordTrace (prefixWord ++ tailWord_178716) baseStart_178716 baseEnd_178716 := by
    simpa [prefixWord, tailWord_178716, baseEnd_178716] using wordTrace_append hprefix tailTrace_178716
  have hstable : (prefixWord ++ tailWord_178716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178716).length < 2 ^ (prefixWord ++ tailWord_178716).sum := by decide
  have hdescent : baseEnd_178716 < baseStart_178716 := by decide
  rcases family_descends (prefixWord ++ tailWord_178716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178756 : List Nat := [2, 3, 5, 1, 1, 1, 2, 3, 3]
def baseStart_178756 : Nat := 118140960795 + 178756 * 2 ^ 59
def prefixEnd_178756 : Nat := 4983230072969 + 3 ^ 40 * 178756 * 2
def baseEnd_178756 : Nat := 40794554611203488901299

theorem tailTrace_178756 : CollatzResearch.WordTrace tailWord_178756 prefixEnd_178756 40794554611203488901299 := by
  unfold tailWord_178756
  simp only [CollatzResearch.WordTrace]
  refine ⟨3259883470202507969682061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4346511293603343959576081 3259883470202507969682061)
  ·
    refine ⟨1222456301325940488630773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3259883470202507969682061 1222456301325940488630773)
    ·
      refine ⟨114605278249306920809135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1222456301325940488630773 114605278249306920809135)
      ·
        refine ⟨171907917373960381213703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114605278249306920809135 171907917373960381213703)
        ·
          refine ⟨257861876060940571820555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171907917373960381213703 257861876060940571820555)
          ·
            refine ⟨386792814091410857730833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257861876060940571820555 386792814091410857730833)
            ·
              refine ⟨290094610568558143298125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 386792814091410857730833 290094610568558143298125)
              ·
                refine ⟨108785478963209303736797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 290094610568558143298125 108785478963209303736797)
                ·
                  refine ⟨40794554611203488901299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108785478963209303736797 40794554611203488901299)
                  ·
                    rfl

theorem cell21_178756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 3, 3].length) (baseStart_178756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_178756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_178756 prefixEnd_178756 := by exact prefixLift 178756
  have htrace : WordTrace (prefixWord ++ tailWord_178756) baseStart_178756 baseEnd_178756 := by
    simpa [prefixWord, tailWord_178756, baseEnd_178756] using wordTrace_append hprefix tailTrace_178756
  have hstable : (prefixWord ++ tailWord_178756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178756).length < 2 ^ (prefixWord ++ tailWord_178756).sum := by decide
  have hdescent : baseEnd_178756 < baseStart_178756 := by decide
  rcases family_descends (prefixWord ++ tailWord_178756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178809 : List Nat := [1, 2, 1, 3, 3, 2, 4, 5]
def baseStart_178809 : Nat := 118140960795 + 178809 * 2 ^ 59
def prefixEnd_178809 : Nat := 4983230072969 + 3 ^ 40 * 178809 * 2
def baseEnd_178809 : Nat := 13602216644429058172619

theorem tailTrace_178809 : CollatzResearch.WordTrace tailWord_178809 prefixEnd_178809 13602216644429058172619 := by
  unfold tailWord_178809
  simp only [CollatzResearch.WordTrace]
  refine ⟨6521700009213005991043481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4347800006142003994028987 6521700009213005991043481)
  ·
    refine ⟨4891275006909754493282611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6521700009213005991043481 4891275006909754493282611)
    ·
      refine ⟨7336912510364631739923917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4891275006909754493282611 7336912510364631739923917)
      ·
        refine ⟨2751342191386736902471469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7336912510364631739923917 2751342191386736902471469)
        ·
          refine ⟨1031753321770026338426801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2751342191386736902471469 1031753321770026338426801)
          ·
            refine ⟨773814991327519753820101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1031753321770026338426801 773814991327519753820101)
            ·
              refine ⟨145090310873909953841269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 773814991327519753820101 145090310873909953841269)
              ·
                refine ⟨13602216644429058172619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 145090310873909953841269 13602216644429058172619)
                ·
                  rfl

theorem cell21_178809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 5].length) (baseStart_178809 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_178809 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_178809 prefixEnd_178809 := by exact prefixLift 178809
  have htrace : WordTrace (prefixWord ++ tailWord_178809) baseStart_178809 baseEnd_178809 := by
    simpa [prefixWord, tailWord_178809, baseEnd_178809] using wordTrace_append hprefix tailTrace_178809
  have hstable : (prefixWord ++ tailWord_178809).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178809).length < 2 ^ (prefixWord ++ tailWord_178809).sum := by decide
  have hdescent : baseEnd_178809 < baseStart_178809 := by decide
  rcases family_descends (prefixWord ++ tailWord_178809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178826 : List Nat := [3, 1, 2, 3, 4, 1, 7]
def baseStart_178826 : Nat := 118140960795 + 178826 * 2 ^ 59
def prefixEnd_178826 : Nat := 4983230072969 + 3 ^ 40 * 178826 * 2
def baseEnd_178826 : Nat := 4534503284988769192721

theorem tailTrace_178826 : CollatzResearch.WordTrace tailWord_178826 prefixEnd_178826 4534503284988769192721 := by
  unfold tailWord_178826
  simp only [CollatzResearch.WordTrace]
  refine ⟨1630580012537854473603083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4348213366767611929608221 1630580012537854473603083)
  ·
    refine ⟨2445870018806781710404625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1630580012537854473603083 2445870018806781710404625)
    ·
      refine ⟨1834402514105086282803469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2445870018806781710404625 1834402514105086282803469)
      ·
        refine ⟨687900942789407356051301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1834402514105086282803469 687900942789407356051301)
        ·
          refine ⟨128981426773013879259619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 687900942789407356051301 128981426773013879259619)
          ·
            refine ⟨193472140159520818889429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128981426773013879259619 193472140159520818889429)
            ·
              refine ⟨4534503284988769192721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 193472140159520818889429 4534503284988769192721)
              ·
                rfl

theorem cell21_178826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 7].length) (baseStart_178826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_178826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_178826 prefixEnd_178826 := by exact prefixLift 178826
  have htrace : WordTrace (prefixWord ++ tailWord_178826) baseStart_178826 baseEnd_178826 := by
    simpa [prefixWord, tailWord_178826, baseEnd_178826] using wordTrace_append hprefix tailTrace_178826
  have hstable : (prefixWord ++ tailWord_178826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178826).length < 2 ^ (prefixWord ++ tailWord_178826).sum := by decide
  have hdescent : baseEnd_178826 < baseStart_178826 := by decide
  rcases family_descends (prefixWord ++ tailWord_178826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178975 : List Nat := [1, 1, 2, 4, 2, 2, 2, 2, 5]
def baseStart_178975 : Nat := 118140960795 + 178975 * 2 ^ 59
def prefixEnd_178975 : Nat := 4983230072969 + 3 ^ 40 * 178975 * 2
def baseEnd_178975 : Nat := 40844533394907774750851

theorem tailTrace_178975 : CollatzResearch.WordTrace tailWord_178975 prefixEnd_178975 40844533394907774750851 := by
  unfold tailWord_178975
  simp only [CollatzResearch.WordTrace]
  refine ⟨6527754526611616341586379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4351836351074410894390919 6527754526611616341586379)
  ·
    refine ⟨9791631789917424512379569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6527754526611616341586379 9791631789917424512379569)
    ·
      refine ⟨7343723842438068384284677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9791631789917424512379569 7343723842438068384284677)
      ·
        refine ⟨1376948220457137822053377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7343723842438068384284677 1376948220457137822053377)
        ·
          refine ⟨1032711165342853366540033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1376948220457137822053377 1032711165342853366540033)
          ·
            refine ⟨774533374007140024905025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1032711165342853366540033 774533374007140024905025)
            ·
              refine ⟨580900030505355018678769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 774533374007140024905025 580900030505355018678769)
              ·
                refine ⟨435675022879016264009077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 580900030505355018678769 435675022879016264009077)
                ·
                  refine ⟨40844533394907774750851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 435675022879016264009077 40844533394907774750851)
                  ·
                    rfl

theorem cell21_178975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 5].length) (baseStart_178975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_178975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_178975 prefixEnd_178975 := by exact prefixLift 178975
  have htrace : WordTrace (prefixWord ++ tailWord_178975) baseStart_178975 baseEnd_178975 := by
    simpa [prefixWord, tailWord_178975, baseEnd_178975] using wordTrace_append hprefix tailTrace_178975
  have hstable : (prefixWord ++ tailWord_178975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178975).length < 2 ^ (prefixWord ++ tailWord_178975).sum := by decide
  have hdescent : baseEnd_178975 < baseStart_178975 := by decide
  rcases family_descends (prefixWord ++ tailWord_178975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178978 : List Nat := [3, 3, 1, 1, 2, 4, 2, 5]
def baseStart_178978 : Nat := 118140960795 + 178978 * 2 ^ 59
def prefixEnd_178978 : Nat := 4983230072969 + 3 ^ 40 * 178978 * 2
def baseEnd_178978 : Nat := 13615072678593478733615

theorem tailTrace_178978 : CollatzResearch.WordTrace tailWord_178978 prefixEnd_178978 13615072678593478733615 := by
  unfold tailWord_178978
  simp only [CollatzResearch.WordTrace]
  refine ⟨1631965986400186963486397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4351909297067165235963725 1631965986400186963486397)
  ·
    refine ⟨611987244900070111307399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1631965986400186963486397 611987244900070111307399)
    ·
      refine ⟨917980867350105166961099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 611987244900070111307399 917980867350105166961099)
      ·
        refine ⟨1376971301025157750441649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 917980867350105166961099 1376971301025157750441649)
        ·
          refine ⟨1032728475768868312831237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1376971301025157750441649 1032728475768868312831237)
          ·
            refine ⟨193636589206662808655857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1032728475768868312831237 193636589206662808655857)
            ·
              refine ⟨145227441904997106491893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193636589206662808655857 145227441904997106491893)
              ·
                refine ⟨13615072678593478733615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 145227441904997106491893 13615072678593478733615)
                ·
                  rfl

theorem cell21_178978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 5].length) (baseStart_178978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_178978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_178978 prefixEnd_178978 := by exact prefixLift 178978
  have htrace : WordTrace (prefixWord ++ tailWord_178978) baseStart_178978 baseEnd_178978 := by
    simpa [prefixWord, tailWord_178978, baseEnd_178978] using wordTrace_append hprefix tailTrace_178978
  have hstable : (prefixWord ++ tailWord_178978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178978).length < 2 ^ (prefixWord ++ tailWord_178978).sum := by decide
  have hdescent : baseEnd_178978 < baseStart_178978 := by decide
  rcases family_descends (prefixWord ++ tailWord_178978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179020 : List Nat := [2, 2, 1, 3, 3, 1, 1, 8]
def baseStart_179020 : Nat := 118140960795 + 179020 * 2 ^ 59
def prefixEnd_179020 : Nat := 4983230072969 + 3 ^ 40 * 179020 * 2
def baseEnd_179020 : Nat := 13618267669332565500253

theorem tailTrace_179020 : CollatzResearch.WordTrace tailWord_179020 prefixEnd_179020 13618267669332565500253 := by
  unfold tailWord_179020
  simp only [CollatzResearch.WordTrace]
  refine ⟨3264697905724294513487257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4352930540965726017983009 3264697905724294513487257)
  ·
    refine ⟨2448523429293220885115443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3264697905724294513487257 2448523429293220885115443)
    ·
      refine ⟨3672785143939831327673165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2448523429293220885115443 3672785143939831327673165)
      ·
        refine ⟨1377294428977436747877437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3672785143939831327673165 1377294428977436747877437)
        ·
          refine ⟨516485410866538780454039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1377294428977436747877437 516485410866538780454039)
          ·
            refine ⟨774728116299808170681059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 516485410866538780454039 774728116299808170681059)
            ·
              refine ⟨1162092174449712256021589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 774728116299808170681059 1162092174449712256021589)
              ·
                refine ⟨13618267669332565500253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1162092174449712256021589 13618267669332565500253)
                ·
                  rfl

theorem cell21_179020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 8].length) (baseStart_179020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_179020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_179020 prefixEnd_179020 := by exact prefixLift 179020
  have htrace : WordTrace (prefixWord ++ tailWord_179020) baseStart_179020 baseEnd_179020 := by
    simpa [prefixWord, tailWord_179020, baseEnd_179020] using wordTrace_append hprefix tailTrace_179020
  have hstable : (prefixWord ++ tailWord_179020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179020).length < 2 ^ (prefixWord ++ tailWord_179020).sum := by decide
  have hdescent : baseEnd_179020 < baseStart_179020 := by decide
  rcases family_descends (prefixWord ++ tailWord_179020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179161 : List Nat := [1, 2, 1, 2, 5, 3, 1, 3, 3]
def baseStart_179161 : Nat := 118140960795 + 179161 * 2 ^ 59
def prefixEnd_179161 : Nat := 4983230072969 + 3 ^ 40 * 179161 * 2
def baseEnd_179161 : Nat := 40886981129012784650471

theorem tailTrace_179161 : CollatzResearch.WordTrace tailWord_179161 prefixEnd_179161 40886981129012784650471 := by
  unfold tailWord_179161
  simp only [CollatzResearch.WordTrace]
  refine ⟨6534538503937770107857337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4356359002625180071904891 6534538503937770107857337)
  ·
    refine ⟨4900903877953327580893003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6534538503937770107857337 4900903877953327580893003)
    ·
      refine ⟨7351355816929991371339505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4900903877953327580893003 7351355816929991371339505)
      ·
        refine ⟨5513516862697493528504629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7351355816929991371339505 5513516862697493528504629)
        ·
          refine ⟨516892205877890018297309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5513516862697493528504629 516892205877890018297309)
          ·
            refine ⟨193834577204208756861491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 516892205877890018297309 193834577204208756861491)
            ·
              refine ⟨290751865806313135292237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193834577204208756861491 290751865806313135292237)
              ·
                refine ⟨109031949677367425734589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 290751865806313135292237 109031949677367425734589)
                ·
                  refine ⟨40886981129012784650471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109031949677367425734589 40886981129012784650471)
                  ·
                    rfl

theorem cell21_179161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 3, 3].length) (baseStart_179161 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_179161 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_179161 prefixEnd_179161 := by exact prefixLift 179161
  have htrace : WordTrace (prefixWord ++ tailWord_179161) baseStart_179161 baseEnd_179161 := by
    simpa [prefixWord, tailWord_179161, baseEnd_179161] using wordTrace_append hprefix tailTrace_179161
  have hstable : (prefixWord ++ tailWord_179161).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179161).length < 2 ^ (prefixWord ++ tailWord_179161).sum := by decide
  have hdescent : baseEnd_179161 < baseStart_179161 := by decide
  rcases family_descends (prefixWord ++ tailWord_179161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179231 : List Nat := [1, 1, 2, 4, 1, 12]
def baseStart_179231 : Nat := 118140960795 + 179231 * 2 ^ 59
def prefixEnd_179231 : Nat := 4983230072969 + 3 ^ 40 * 179231 * 2
def baseEnd_179231 : Nat := 1514924299359563647543

theorem tailTrace_179231 : CollatzResearch.WordTrace tailWord_179231 prefixEnd_179231 1514924299359563647543 := by
  unfold tailWord_179231
  simp only [CollatzResearch.WordTrace]
  refine ⟨6537091613684172062905547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4358061075789448041937031 6537091613684172062905547)
  ·
    refine ⟨9805637420526258094358321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6537091613684172062905547 9805637420526258094358321)
    ·
      refine ⟨7354228065394693570768741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9805637420526258094358321 7354228065394693570768741)
      ·
        refine ⟨1378917762261505044519139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7354228065394693570768741 1378917762261505044519139)
        ·
          refine ⟨2068376643392257566778709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1378917762261505044519139 2068376643392257566778709)
          ·
            refine ⟨1514924299359563647543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 2068376643392257566778709 1514924299359563647543)
            ·
              rfl

theorem cell21_179231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 12].length) (baseStart_179231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_179231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_179231 prefixEnd_179231 := by exact prefixLift 179231
  have htrace : WordTrace (prefixWord ++ tailWord_179231) baseStart_179231 baseEnd_179231 := by
    simpa [prefixWord, tailWord_179231, baseEnd_179231] using wordTrace_append hprefix tailTrace_179231
  have hstable : (prefixWord ++ tailWord_179231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179231).length < 2 ^ (prefixWord ++ tailWord_179231).sum := by decide
  have hdescent : baseEnd_179231 < baseStart_179231 := by decide
  rcases family_descends (prefixWord ++ tailWord_179231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179234 : List Nat := [3, 3, 1, 1, 1, 3, 1, 4, 4]
def baseStart_179234 : Nat := 118140960795 + 179234 * 2 ^ 59
def prefixEnd_179234 : Nat := 4983230072969 + 3 ^ 40 * 179234 * 2
def baseEnd_179234 : Nat := 40903640723580879933655

theorem tailTrace_179234 : CollatzResearch.WordTrace tailWord_179234 prefixEnd_179234 40903640723580879933655 := by
  unfold tailWord_179234
  simp only [CollatzResearch.WordTrace]
  refine ⟨1634300258168325893816189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4358134021782202383509837 1634300258168325893816189)
  ·
    refine ⟨612862596813122210181071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1634300258168325893816189 612862596813122210181071)
    ·
      refine ⟨919293895219683315271607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 612862596813122210181071 919293895219683315271607)
      ·
        refine ⟨1378940842829524972907411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 919293895219683315271607 1378940842829524972907411)
        ·
          refine ⟨2068411264244287459361117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1378940842829524972907411 2068411264244287459361117)
          ·
            refine ⟨775654224091607797260419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2068411264244287459361117 775654224091607797260419)
            ·
              refine ⟨1163481336137411695890629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 775654224091607797260419 1163481336137411695890629)
              ·
                refine ⟨218152750525764692979493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1163481336137411695890629 218152750525764692979493)
                ·
                  refine ⟨40903640723580879933655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 218152750525764692979493 40903640723580879933655)
                  ·
                    rfl

theorem cell21_179234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_179234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_179234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_179234 prefixEnd_179234 := by exact prefixLift 179234
  have htrace : WordTrace (prefixWord ++ tailWord_179234) baseStart_179234 baseEnd_179234 := by
    simpa [prefixWord, tailWord_179234, baseEnd_179234] using wordTrace_append hprefix tailTrace_179234
  have hstable : (prefixWord ++ tailWord_179234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179234).length < 2 ^ (prefixWord ++ tailWord_179234).sum := by decide
  have hdescent : baseEnd_179234 < baseStart_179234 := by decide
  rcases family_descends (prefixWord ++ tailWord_179234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179383 : List Nat := [1, 1, 3, 1, 4, 1, 1, 9]
def baseStart_179383 : Nat := 118140960795 + 179383 * 2 ^ 59
def prefixEnd_179383 : Nat := 4983230072969 + 3 ^ 40 * 179383 * 2
def baseEnd_179383 : Nat := 13645881517863243983339

theorem tailTrace_179383 : CollatzResearch.WordTrace tailWord_179383 prefixEnd_179383 13645881517863243983339 := by
  unfold tailWord_179383
  simp only [CollatzResearch.WordTrace]
  refine ⟨6542635509133502022438803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4361757006089001348292535 6542635509133502022438803)
  ·
    refine ⟨9813953263700253033658205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6542635509133502022438803 9813953263700253033658205)
    ·
      refine ⟨3680232473887594887621827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9813953263700253033658205 3680232473887594887621827)
      ·
        refine ⟨5520348710831392331432741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3680232473887594887621827 5520348710831392331432741)
        ·
          refine ⟨1035065383280886062143639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5520348710831392331432741 1035065383280886062143639)
          ·
            refine ⟨1552598074921329093215459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1035065383280886062143639 1552598074921329093215459)
            ·
              refine ⟨2328897112381993639823189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1552598074921329093215459 2328897112381993639823189)
              ·
                refine ⟨13645881517863243983339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2328897112381993639823189 13645881517863243983339)
                ·
                  rfl

theorem cell21_179383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 9].length) (baseStart_179383 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_179383 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_179383 prefixEnd_179383 := by exact prefixLift 179383
  have htrace : WordTrace (prefixWord ++ tailWord_179383) baseStart_179383 baseEnd_179383 := by
    simpa [prefixWord, tailWord_179383, baseEnd_179383] using wordTrace_append hprefix tailTrace_179383
  have hstable : (prefixWord ++ tailWord_179383).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179383).length < 2 ^ (prefixWord ++ tailWord_179383).sum := by decide
  have hdescent : baseEnd_179383 < baseStart_179383 := by decide
  rcases family_descends (prefixWord ++ tailWord_179383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179406 : List Nat := [4, 1, 1, 1, 5, 2, 2, 2, 3]
def baseStart_179406 : Nat := 118140960795 + 179406 * 2 ^ 59
def prefixEnd_179406 : Nat := 4983230072969 + 3 ^ 40 * 179406 * 2
def baseEnd_179406 : Nat := 40942893466946803066637

theorem tailTrace_179406 : CollatzResearch.WordTrace tailWord_179406 prefixEnd_179406 40942893466946803066637 := by
  unfold tailWord_179406
  simp only [CollatzResearch.WordTrace]
  refine ⟨817934298506272118815759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4362316258700117967017381 817934298506272118815759)
  ·
    refine ⟨1226901447759408178223639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 817934298506272118815759 1226901447759408178223639)
    ·
      refine ⟨1840352171639112267335459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1226901447759408178223639 1840352171639112267335459)
      ·
        refine ⟨2760528257458668401003189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1840352171639112267335459 2760528257458668401003189)
        ·
          refine ⟨258799524136750162594049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2760528257458668401003189 258799524136750162594049)
          ·
            refine ⟨194099643102562621945537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258799524136750162594049 194099643102562621945537)
            ·
              refine ⟨145574732326921966459153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194099643102562621945537 145574732326921966459153)
              ·
                refine ⟨109181049245191474844365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145574732326921966459153 109181049245191474844365)
                ·
                  refine ⟨40942893466946803066637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109181049245191474844365 40942893466946803066637)
                  ·
                    rfl

theorem cell21_179406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 2, 3].length) (baseStart_179406 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_179406 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_179406 prefixEnd_179406 := by exact prefixLift 179406
  have htrace : WordTrace (prefixWord ++ tailWord_179406) baseStart_179406 baseEnd_179406 := by
    simpa [prefixWord, tailWord_179406, baseEnd_179406] using wordTrace_append hprefix tailTrace_179406
  have hstable : (prefixWord ++ tailWord_179406).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179406).length < 2 ^ (prefixWord ++ tailWord_179406).sum := by decide
  have hdescent : baseEnd_179406 < baseStart_179406 := by decide
  rcases family_descends (prefixWord ++ tailWord_179406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179459 : List Nat := [1, 1, 1, 3, 2, 5, 8]
def baseStart_179459 : Nat := 118140960795 + 179459 * 2 ^ 59
def prefixEnd_179459 : Nat := 4983230072969 + 3 ^ 40 * 179459 * 2
def baseEnd_179459 : Nat := 4550554309892276520355

theorem tailTrace_179459 : CollatzResearch.WordTrace tailWord_179459 prefixEnd_179459 4550554309892276520355 := by
  unfold tailWord_179459
  simp only [CollatzResearch.WordTrace]
  refine ⟨6545407456858167002205431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4363604971238778001470287 6545407456858167002205431)
  ·
    refine ⟨9818111185287250503308147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6545407456858167002205431 9818111185287250503308147)
    ·
      refine ⟨14727166777930875754962221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9818111185287250503308147 14727166777930875754962221)
      ·
        refine ⟨5522687541724078408110833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14727166777930875754962221 5522687541724078408110833)
        ·
          refine ⟨4142015656293058806083125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5522687541724078408110833 4142015656293058806083125)
          ·
            refine ⟨388313967777474263070293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4142015656293058806083125 388313967777474263070293)
            ·
              refine ⟨4550554309892276520355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 388313967777474263070293 4550554309892276520355)
              ·
                rfl

theorem cell21_179459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 8].length) (baseStart_179459 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_179459 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_179459 prefixEnd_179459 := by exact prefixLift 179459
  have htrace : WordTrace (prefixWord ++ tailWord_179459) baseStart_179459 baseEnd_179459 := by
    simpa [prefixWord, tailWord_179459, baseEnd_179459] using wordTrace_append hprefix tailTrace_179459
  have hstable : (prefixWord ++ tailWord_179459).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179459).length < 2 ^ (prefixWord ++ tailWord_179459).sum := by decide
  have hdescent : baseEnd_179459 < baseStart_179459 := by decide
  rcases family_descends (prefixWord ++ tailWord_179459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179493 : List Nat := [1, 3, 1, 2, 4, 3, 2, 5]
def baseStart_179493 : Nat := 118140960795 + 179493 * 2 ^ 59
def prefixEnd_179493 : Nat := 4983230072969 + 3 ^ 40 * 179493 * 2
def baseEnd_179493 : Nat := 13654249350751328372153

theorem tailTrace_179493 : CollatzResearch.WordTrace tailWord_179493 prefixEnd_179493 13654249350751328372153 := by
  unfold tailWord_179493
  simp only [CollatzResearch.WordTrace]
  refine ⟨6546647538734990808943133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4364431692489993872628755 6546647538734990808943133)
  ·
    refine ⟨2454992827025621553353675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6546647538734990808943133 2454992827025621553353675)
    ·
      refine ⟨3682489240538432330030513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2454992827025621553353675 3682489240538432330030513)
      ·
        refine ⟨2761866930403824247522885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3682489240538432330030513 2761866930403824247522885)
        ·
          refine ⟨517850049450717046410541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2761866930403824247522885 517850049450717046410541)
          ·
            refine ⟨194193768544018892403953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 517850049450717046410541 194193768544018892403953)
            ·
              refine ⟨145645326408014169302965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194193768544018892403953 145645326408014169302965)
              ·
                refine ⟨13654249350751328372153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 145645326408014169302965 13654249350751328372153)
                ·
                  rfl

theorem cell21_179493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 5].length) (baseStart_179493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_179493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_179493 prefixEnd_179493 := by exact prefixLift 179493
  have htrace : WordTrace (prefixWord ++ tailWord_179493) baseStart_179493 baseEnd_179493 := by
    simpa [prefixWord, tailWord_179493, baseEnd_179493] using wordTrace_append hprefix tailTrace_179493
  have hstable : (prefixWord ++ tailWord_179493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179493).length < 2 ^ (prefixWord ++ tailWord_179493).sum := by decide
  have hdescent : baseEnd_179493 < baseStart_179493 := by decide
  rcases family_descends (prefixWord ++ tailWord_179493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179504 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 8]
def baseStart_179504 : Nat := 118140960795 + 179504 * 2 ^ 59
def prefixEnd_179504 : Nat := 4983230072969 + 3 ^ 40 * 179504 * 2
def baseEnd_179504 : Nat := 40965258402120410433103

theorem tailTrace_179504 : CollatzResearch.WordTrace tailWord_179504 prefixEnd_179504 40965258402120410433103 := by
  unfold tailWord_179504
  simp only [CollatzResearch.WordTrace]
  refine ⟨3273524370847569843796783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4364699161130093125062377 3273524370847569843796783)
  ·
    refine ⟨4910286556271354765695175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3273524370847569843796783 4910286556271354765695175)
    ·
      refine ⟨7365429834407032148542763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4910286556271354765695175 7365429834407032148542763)
      ·
        refine ⟨11048144751610548222814145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7365429834407032148542763 11048144751610548222814145)
        ·
          refine ⟨8286108563707911167110609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11048144751610548222814145 8286108563707911167110609)
          ·
            refine ⟨6214581422780933375332957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8286108563707911167110609 6214581422780933375332957)
            ·
              refine ⟨2330468033542850015749859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6214581422780933375332957 2330468033542850015749859)
              ·
                refine ⟨3495702050314275023624789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2330468033542850015749859 3495702050314275023624789)
                ·
                  refine ⟨40965258402120410433103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3495702050314275023624789 40965258402120410433103)
                  ·
                    rfl

theorem cell21_179504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 8].length) (baseStart_179504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_179504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_179504 prefixEnd_179504 := by exact prefixLift 179504
  have htrace : WordTrace (prefixWord ++ tailWord_179504) baseStart_179504 baseEnd_179504 := by
    simpa [prefixWord, tailWord_179504, baseEnd_179504] using wordTrace_append hprefix tailTrace_179504
  have hstable : (prefixWord ++ tailWord_179504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179504).length < 2 ^ (prefixWord ++ tailWord_179504).sum := by decide
  have hdescent : baseEnd_179504 < baseStart_179504 := by decide
  rcases family_descends (prefixWord ++ tailWord_179504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179510 : List Nat := [5, 1, 2, 3, 1, 2, 7]
def baseStart_179510 : Nat := 118140960795 + 179510 * 2 ^ 59
def prefixEnd_179510 : Nat := 4983230072969 + 3 ^ 40 * 179510 * 2
def baseEnd_179510 : Nat := 4551847520429525925899

theorem tailTrace_179510 : CollatzResearch.WordTrace tailWord_179510 prefixEnd_179510 4551847520429525925899 := by
  unfold tailWord_179510
  simp only [CollatzResearch.WordTrace]
  refine ⟨409204223729587669519499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4364845053115601808207989 409204223729587669519499)
  ·
    refine ⟨613806335594381504279249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 409204223729587669519499 613806335594381504279249)
    ·
      refine ⟨460354751695786128209437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 613806335594381504279249 460354751695786128209437)
      ·
        refine ⟨172633031885919798078539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 460354751695786128209437 172633031885919798078539)
        ·
          refine ⟨258949547828879697117809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172633031885919798078539 258949547828879697117809)
          ·
            refine ⟨194212160871659772838357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258949547828879697117809 194212160871659772838357)
            ·
              refine ⟨4551847520429525925899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 194212160871659772838357 4551847520429525925899)
              ·
                rfl

theorem cell21_179510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 7].length) (baseStart_179510 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_179510 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_179510 prefixEnd_179510 := by exact prefixLift 179510
  have htrace : WordTrace (prefixWord ++ tailWord_179510) baseStart_179510 baseEnd_179510 := by
    simpa [prefixWord, tailWord_179510, baseEnd_179510] using wordTrace_append hprefix tailTrace_179510
  have hstable : (prefixWord ++ tailWord_179510).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179510).length < 2 ^ (prefixWord ++ tailWord_179510).sum := by decide
  have hdescent : baseEnd_179510 < baseStart_179510 := by decide
  rcases family_descends (prefixWord ++ tailWord_179510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179524 : List Nat := [2, 3, 4, 1, 1, 1, 3, 1, 5]
def baseStart_179524 : Nat := 118140960795 + 179524 * 2 ^ 59
def prefixEnd_179524 : Nat := 4983230072969 + 3 ^ 40 * 179524 * 2
def baseEnd_179524 : Nat := 40969822674604820099729

theorem tailTrace_179524 : CollatzResearch.WordTrace tailWord_179524 prefixEnd_179524 40969822674604820099729 := by
  unfold tailWord_179524
  simp only [CollatzResearch.WordTrace]
  refine ⟨3273889100811341551660813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4365185467748455402214417 3273889100811341551660813)
  ·
    refine ⟨1227708412804253081872805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3273889100811341551660813 1227708412804253081872805)
    ·
      refine ⟨230195327400797452851151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1227708412804253081872805 230195327400797452851151)
      ·
        refine ⟨345292991101196179276727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230195327400797452851151 345292991101196179276727)
        ·
          refine ⟨517939486651794268915091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345292991101196179276727 517939486651794268915091)
          ·
            refine ⟨776909229977691403372637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 517939486651794268915091 776909229977691403372637)
            ·
              refine ⟨291340961241634276264739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 776909229977691403372637 291340961241634276264739)
              ·
                refine ⟨437011441862451414397109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 291340961241634276264739 437011441862451414397109)
                ·
                  refine ⟨40969822674604820099729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 437011441862451414397109 40969822674604820099729)
                  ·
                    rfl

theorem cell21_179524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_179524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_179524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_179524 prefixEnd_179524 := by exact prefixLift 179524
  have htrace : WordTrace (prefixWord ++ tailWord_179524) baseStart_179524 baseEnd_179524 := by
    simpa [prefixWord, tailWord_179524, baseEnd_179524] using wordTrace_append hprefix tailTrace_179524
  have hstable : (prefixWord ++ tailWord_179524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179524).length < 2 ^ (prefixWord ++ tailWord_179524).sum := by decide
  have hdescent : baseEnd_179524 < baseStart_179524 := by decide
  rcases family_descends (prefixWord ++ tailWord_179524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179586 : List Nat := [3, 4, 2, 1, 1, 3, 1, 6]
def baseStart_179586 : Nat := 118140960795 + 179586 * 2 ^ 59
def prefixEnd_179586 : Nat := 4983230072969 + 3 ^ 40 * 179586 * 2
def baseEnd_179586 : Nat := 13661323973102163355423

theorem tailTrace_179586 : CollatzResearch.WordTrace tailWord_179586 prefixEnd_179586 13661323973102163355423 := by
  unfold tailWord_179586
  simp only [CollatzResearch.WordTrace]
  refine ⟨1637509881849516923019653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4366693018265378461385741 1637509881849516923019653)
  ·
    refine ⟨307033102846784423066185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1637509881849516923019653 307033102846784423066185)
    ·
      refine ⟨230274827135088317299639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307033102846784423066185 230274827135088317299639)
      ·
        refine ⟨345412240702632475949459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230274827135088317299639 345412240702632475949459)
        ·
          refine ⟨518118361053948713924189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345412240702632475949459 518118361053948713924189)
          ·
            refine ⟨194294385395230767721571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 518118361053948713924189 194294385395230767721571)
            ·
              refine ⟨291441578092846151582357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194294385395230767721571 291441578092846151582357)
              ·
                refine ⟨13661323973102163355423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 291441578092846151582357 13661323973102163355423)
                ·
                  rfl

theorem cell21_179586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 6].length) (baseStart_179586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_179586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_179586 prefixEnd_179586 := by exact prefixLift 179586
  have htrace : WordTrace (prefixWord ++ tailWord_179586) baseStart_179586 baseEnd_179586 := by
    simpa [prefixWord, tailWord_179586, baseEnd_179586] using wordTrace_append hprefix tailTrace_179586
  have hstable : (prefixWord ++ tailWord_179586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179586).length < 2 ^ (prefixWord ++ tailWord_179586).sum := by decide
  have hdescent : baseEnd_179586 < baseStart_179586 := by decide
  rcases family_descends (prefixWord ++ tailWord_179586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179687 : List Nat := [1, 1, 5, 2, 1, 2, 9]
def baseStart_179687 : Nat := 118140960795 + 179687 * 2 ^ 59
def prefixEnd_179687 : Nat := 4983230072969 + 3 ^ 40 * 179687 * 2
def baseEnd_179687 : Nat := 4556335721705862098081

theorem tailTrace_179687 : CollatzResearch.WordTrace tailWord_179687 prefixEnd_179687 4556335721705862098081 := by
  unfold tailWord_179687
  simp only [CollatzResearch.WordTrace]
  refine ⟨6553723300032161941505315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4369148866688107961003543 6553723300032161941505315)
  ·
    refine ⟨9830584950048242912257973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6553723300032161941505315 9830584950048242912257973)
    ·
      refine ⟨921617339067022773024185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9830584950048242912257973 921617339067022773024185)
      ·
        refine ⟨691213004300267079768139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 921617339067022773024185 691213004300267079768139)
        ·
          refine ⟨1036819506450400619652209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 691213004300267079768139 1036819506450400619652209)
          ·
            refine ⟨777614629837800464739157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1036819506450400619652209 777614629837800464739157)
            ·
              refine ⟨4556335721705862098081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 777614629837800464739157 4556335721705862098081)
              ·
                rfl

theorem cell21_179687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 9].length) (baseStart_179687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_179687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_179687 prefixEnd_179687 := by exact prefixLift 179687
  have htrace : WordTrace (prefixWord ++ tailWord_179687) baseStart_179687 baseEnd_179687 := by
    simpa [prefixWord, tailWord_179687, baseEnd_179687] using wordTrace_append hprefix tailTrace_179687
  have hstable : (prefixWord ++ tailWord_179687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179687).length < 2 ^ (prefixWord ++ tailWord_179687).sum := by decide
  have hdescent : baseEnd_179687 < baseStart_179687 := by decide
  rcases family_descends (prefixWord ++ tailWord_179687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179693 : List Nat := [1, 5, 1, 3, 3, 1, 1, 1, 5]
def baseStart_179693 : Nat := 118140960795 + 179693 * 2 ^ 59
def prefixEnd_179693 : Nat := 4983230072969 + 3 ^ 40 * 179693 * 2
def baseEnd_179693 : Nat := 41008390777098081782717

theorem tailTrace_179693 : CollatzResearch.WordTrace tailWord_179693 prefixEnd_179693 41008390777098081782717 := by
  unfold tailWord_179693
  simp only [CollatzResearch.WordTrace]
  refine ⟨6553942138010424966223733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4369294758673616644149155 6553942138010424966223733)
  ·
    refine ⟨614432075438477340583475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6553942138010424966223733 614432075438477340583475)
    ·
      refine ⟨921648113157716010875213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 614432075438477340583475 921648113157716010875213)
      ·
        refine ⟨345618042434143504078205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 921648113157716010875213 345618042434143504078205)
        ·
          refine ⟨129606765912803814029327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 345618042434143504078205 129606765912803814029327)
          ·
            refine ⟨194410148869205721043991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129606765912803814029327 194410148869205721043991)
            ·
              refine ⟨291615223303808581565987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194410148869205721043991 291615223303808581565987)
              ·
                refine ⟨437422834955712872348981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 291615223303808581565987 437422834955712872348981)
                ·
                  refine ⟨41008390777098081782717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 437422834955712872348981 41008390777098081782717)
                  ·
                    rfl

theorem cell21_179693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_179693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_179693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_179693 prefixEnd_179693 := by exact prefixLift 179693
  have htrace : WordTrace (prefixWord ++ tailWord_179693) baseStart_179693 baseEnd_179693 := by
    simpa [prefixWord, tailWord_179693, baseEnd_179693] using wordTrace_append hprefix tailTrace_179693
  have hstable : (prefixWord ++ tailWord_179693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179693).length < 2 ^ (prefixWord ++ tailWord_179693).sum := by decide
  have hdescent : baseEnd_179693 < baseStart_179693 := by decide
  rcases family_descends (prefixWord ++ tailWord_179693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179763 : List Nat := [1, 1, 1, 2, 4, 3, 3, 6]
def baseStart_179763 : Nat := 118140960795 + 179763 * 2 ^ 59
def prefixEnd_179763 : Nat := 4983230072969 + 3 ^ 40 * 179763 * 2
def baseEnd_179763 : Nat := 13674788576931171871969

theorem tailTrace_179763 : CollatzResearch.WordTrace tailWord_179763 prefixEnd_179763 13674788576931171871969 := by
  unfold tailWord_179763
  simp only [CollatzResearch.WordTrace]
  refine ⟨6556495247756826921271943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4370996831837884614181295 6556495247756826921271943)
  ·
    refine ⟨9834742871635240381907915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6556495247756826921271943 9834742871635240381907915)
    ·
      refine ⟨14752114307452860572861873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9834742871635240381907915 14752114307452860572861873)
      ·
        refine ⟨11064085730589645429646405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14752114307452860572861873 11064085730589645429646405)
        ·
          refine ⟨2074516074485558518058701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11064085730589645429646405 2074516074485558518058701)
          ·
            refine ⟨777943527932084444272013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2074516074485558518058701 777943527932084444272013)
            ·
              refine ⟨291728822974531666602005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 777943527932084444272013 291728822974531666602005)
              ·
                refine ⟨13674788576931171871969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 291728822974531666602005 13674788576931171871969)
                ·
                  rfl

theorem cell21_179763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 6].length) (baseStart_179763 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_179763 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_179763 prefixEnd_179763 := by exact prefixLift 179763
  have htrace : WordTrace (prefixWord ++ tailWord_179763) baseStart_179763 baseEnd_179763 := by
    simpa [prefixWord, tailWord_179763, baseEnd_179763] using wordTrace_append hprefix tailTrace_179763
  have hstable : (prefixWord ++ tailWord_179763).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179763).length < 2 ^ (prefixWord ++ tailWord_179763).sum := by decide
  have hdescent : baseEnd_179763 < baseStart_179763 := by decide
  rcases family_descends (prefixWord ++ tailWord_179763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179811 : List Nat := [1, 1, 1, 5, 1, 3, 2, 4, 3]
def baseStart_179811 : Nat := 118140960795 + 179811 * 2 ^ 59
def prefixEnd_179811 : Nat := 4983230072969 + 3 ^ 40 * 179811 * 2
def baseEnd_179811 : Nat := 41035319984756098815809

theorem tailTrace_179811 : CollatzResearch.WordTrace tailWord_179811 prefixEnd_179811 41035319984756098815809 := by
  unfold tailWord_179811
  simp only [CollatzResearch.WordTrace]
  refine ⟨6558245951582931119019287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4372163967721954079346191 6558245951582931119019287)
  ·
    refine ⟨9837368927374396678528931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6558245951582931119019287 9837368927374396678528931)
    ·
      refine ⟨14756053391061595017793397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9837368927374396678528931 14756053391061595017793397)
      ·
        refine ⟨1383380005412024532918131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14756053391061595017793397 1383380005412024532918131)
        ·
          refine ⟨2075070008118036799377197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1383380005412024532918131 2075070008118036799377197)
          ·
            refine ⟨778151253044263799766449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2075070008118036799377197 778151253044263799766449)
            ·
              refine ⟨583613439783197849824837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 778151253044263799766449 583613439783197849824837)
              ·
                refine ⟨109427519959349596842157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 583613439783197849824837 109427519959349596842157)
                ·
                  refine ⟨41035319984756098815809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109427519959349596842157 41035319984756098815809)
                  ·
                    rfl

theorem cell21_179811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 4, 3].length) (baseStart_179811 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_179811 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_179811 prefixEnd_179811 := by exact prefixLift 179811
  have htrace : WordTrace (prefixWord ++ tailWord_179811) baseStart_179811 baseEnd_179811 := by
    simpa [prefixWord, tailWord_179811, baseEnd_179811] using wordTrace_append hprefix tailTrace_179811
  have hstable : (prefixWord ++ tailWord_179811).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179811).length < 2 ^ (prefixWord ++ tailWord_179811).sum := by decide
  have hdescent : baseEnd_179811 < baseStart_179811 := by decide
  rcases family_descends (prefixWord ++ tailWord_179811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179994 : List Nat := [3, 1, 1, 3, 2, 3, 3, 1, 4]
def baseStart_179994 : Nat := 118140960795 + 179994 * 2 ^ 59
def prefixEnd_179994 : Nat := 4983230072969 + 3 ^ 40 * 179994 * 2
def baseEnd_179994 : Nat := 41077083077988447265435

theorem tailTrace_179994 : CollatzResearch.WordTrace tailWord_179994 prefixEnd_179994 41077083077988447265435 := by
  unfold tailWord_179994
  simp only [CollatzResearch.WordTrace]
  refine ⟨1641230127479988343232759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4376613673279968915287357 1641230127479988343232759)
  ·
    refine ⟨2461845191219982514849139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1641230127479988343232759 2461845191219982514849139)
    ·
      refine ⟨3692767786829973772273709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2461845191219982514849139 3692767786829973772273709)
      ·
        refine ⟨1384787920061240164602641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3692767786829973772273709 1384787920061240164602641)
        ·
          refine ⟨1038590940045930123451981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1384787920061240164602641 1038590940045930123451981)
          ·
            refine ⟨389471602517223796294493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1038590940045930123451981 389471602517223796294493)
            ·
              refine ⟨146051850943958923610435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 389471602517223796294493 146051850943958923610435)
              ·
                refine ⟨219077776415938385415653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146051850943958923610435 219077776415938385415653)
                ·
                  refine ⟨41077083077988447265435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 219077776415938385415653 41077083077988447265435)
                  ·
                    rfl

theorem cell21_179994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 1, 4].length) (baseStart_179994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_179994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_179994 prefixEnd_179994 := by exact prefixLift 179994
  have htrace : WordTrace (prefixWord ++ tailWord_179994) baseStart_179994 baseEnd_179994 := by
    simpa [prefixWord, tailWord_179994, baseEnd_179994] using wordTrace_append hprefix tailTrace_179994
  have hstable : (prefixWord ++ tailWord_179994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179994).length < 2 ^ (prefixWord ++ tailWord_179994).sum := by decide
  have hdescent : baseEnd_179994 < baseStart_179994 := by decide
  rcases family_descends (prefixWord ++ tailWord_179994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180008 : List Nat := [2, 1, 5, 1, 1, 2, 4, 5]
def baseStart_180008 : Nat := 118140960795 + 180008 * 2 ^ 59
def prefixEnd_180008 : Nat := 4983230072969 + 3 ^ 40 * 180008 * 2
def baseEnd_180008 : Nat := 13693426022909178010691

theorem tailTrace_180008 : CollatzResearch.WordTrace tailWord_180008 prefixEnd_180008 13693426022909178010691 := by
  unfold tailWord_180008
  simp only [CollatzResearch.WordTrace]
  refine ⟨3282715565934616881970339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4376954087912822509293785 3282715565934616881970339)
  ·
    refine ⟨4924073348901925322955509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3282715565934616881970339 4924073348901925322955509)
    ·
      refine ⟨461631876459555499027079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4924073348901925322955509 461631876459555499027079)
      ·
        refine ⟨692447814689333248540619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 461631876459555499027079 692447814689333248540619)
        ·
          refine ⟨1038671722033999872810929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 692447814689333248540619 1038671722033999872810929)
          ·
            refine ⟨779003791525499904608197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1038671722033999872810929 779003791525499904608197)
            ·
              refine ⟨146063210911031232114037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 779003791525499904608197 146063210911031232114037)
              ·
                refine ⟨13693426022909178010691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 146063210911031232114037 13693426022909178010691)
                ·
                  rfl

theorem cell21_180008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 5].length) (baseStart_180008 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_180008 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_180008 prefixEnd_180008 := by exact prefixLift 180008
  have htrace : WordTrace (prefixWord ++ tailWord_180008) baseStart_180008 baseEnd_180008 := by
    simpa [prefixWord, tailWord_180008, baseEnd_180008] using wordTrace_append hprefix tailTrace_180008
  have hstable : (prefixWord ++ tailWord_180008).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180008).length < 2 ^ (prefixWord ++ tailWord_180008).sum := by decide
  have hdescent : baseEnd_180008 < baseStart_180008 := by decide
  rcases family_descends (prefixWord ++ tailWord_180008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180014 : List Nat := [4, 1, 3, 2, 3, 1, 1, 3, 3]
def baseStart_180014 : Nat := 118140960795 + 180014 * 2 ^ 59
def prefixEnd_180014 : Nat := 4983230072969 + 3 ^ 40 * 180014 * 2
def baseEnd_180014 : Nat := 41081647350472856932061

theorem tailTrace_180014 : CollatzResearch.WordTrace tailWord_180014 prefixEnd_180014 41081647350472856932061 := by
  unfold tailWord_180014
  simp only [CollatzResearch.WordTrace]
  refine ⟨820706246230937098582387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4377099979898331192439397 820706246230937098582387)
  ·
    refine ⟨1231059369346405647873581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 820706246230937098582387 1231059369346405647873581)
    ·
      refine ⟨461647263504902117952593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1231059369346405647873581 461647263504902117952593)
      ·
        refine ⟨346235447628676588464445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 461647263504902117952593 346235447628676588464445)
        ·
          refine ⟨129838292860753720674167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 346235447628676588464445 129838292860753720674167)
          ·
            refine ⟨194757439291130581011251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129838292860753720674167 194757439291130581011251)
            ·
              refine ⟨292136158936695871516877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194757439291130581011251 292136158936695871516877)
              ·
                refine ⟨109551059601260951818829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 292136158936695871516877 109551059601260951818829)
                ·
                  refine ⟨41081647350472856932061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109551059601260951818829 41081647350472856932061)
                  ·
                    rfl

theorem cell21_180014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 3, 3].length) (baseStart_180014 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_180014 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_180014 prefixEnd_180014 := by exact prefixLift 180014
  have htrace : WordTrace (prefixWord ++ tailWord_180014) baseStart_180014 baseEnd_180014 := by
    simpa [prefixWord, tailWord_180014, baseEnd_180014] using wordTrace_append hprefix tailTrace_180014
  have hstable : (prefixWord ++ tailWord_180014).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180014).length < 2 ^ (prefixWord ++ tailWord_180014).sum := by decide
  have hdescent : baseEnd_180014 < baseStart_180014 := by decide
  rcases family_descends (prefixWord ++ tailWord_180014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180025 : List Nat := [1, 2, 1, 7, 2, 1, 7]
def baseStart_180025 : Nat := 118140960795 + 180025 * 2 ^ 59
def prefixEnd_180025 : Nat := 4983230072969 + 3 ^ 40 * 180025 * 2
def baseEnd_180025 : Nat := 4564906411148809138745

theorem tailTrace_180025 : CollatzResearch.WordTrace tailWord_180025 prefixEnd_180025 4564906411148809138745 := by
  unfold tailWord_180025
  simp only [CollatzResearch.WordTrace]
  refine ⟨6566051172807645667309529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4377367448538430444873019 6566051172807645667309529)
  ·
    refine ⟨4924538379605734250482147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6566051172807645667309529 4924538379605734250482147)
    ·
      refine ⟨7386807569408601375723221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4924538379605734250482147 7386807569408601375723221)
      ·
        refine ⟨173128302408014094743513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 7386807569408601375723221 173128302408014094743513)
        ·
          refine ⟨129846226806010571057635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173128302408014094743513 129846226806010571057635)
          ·
            refine ⟨194769340209015856586453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129846226806010571057635 194769340209015856586453)
            ·
              refine ⟨4564906411148809138745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 194769340209015856586453 4564906411148809138745)
              ·
                rfl

theorem cell21_180025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 7].length) (baseStart_180025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_180025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_180025 prefixEnd_180025 := by exact prefixLift 180025
  have htrace : WordTrace (prefixWord ++ tailWord_180025) baseStart_180025 baseEnd_180025 := by
    simpa [prefixWord, tailWord_180025, baseEnd_180025] using wordTrace_append hprefix tailTrace_180025
  have hstable : (prefixWord ++ tailWord_180025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180025).length < 2 ^ (prefixWord ++ tailWord_180025).sum := by decide
  have hdescent : baseEnd_180025 < baseStart_180025 := by decide
  rcases family_descends (prefixWord ++ tailWord_180025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180053 : List Nat := [1, 3, 2, 2, 2, 3, 1, 3, 4]
def baseStart_180053 : Nat := 118140960795 + 180053 * 2 ^ 59
def prefixEnd_180053 : Nat := 4983230072969 + 3 ^ 40 * 180053 * 2
def baseEnd_180053 : Nat := 41090547681817455781981

theorem tailTrace_180053 : CollatzResearch.WordTrace tailWord_180053 prefixEnd_180053 41090547681817455781981 := by
  unfold tailWord_180053
  simp only [CollatzResearch.WordTrace]
  refine ⟨6567072416706206449328813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4378048277804137632885875 6567072416706206449328813)
  ·
    refine ⟨2462652156264827418498305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6567072416706206449328813 2462652156264827418498305)
    ·
      refine ⟨1846989117198620563873729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2462652156264827418498305 1846989117198620563873729)
      ·
        refine ⟨1385241837898965422905297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1846989117198620563873729 1385241837898965422905297)
        ·
          refine ⟨1038931378424224067178973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1385241837898965422905297 1038931378424224067178973)
          ·
            refine ⟨389599266909084025192115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1038931378424224067178973 389599266909084025192115)
            ·
              refine ⟨584398900363626037788173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 389599266909084025192115 584398900363626037788173)
              ·
                refine ⟨219149587636359764170565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 584398900363626037788173 219149587636359764170565)
                ·
                  refine ⟨41090547681817455781981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 219149587636359764170565 41090547681817455781981)
                  ·
                    rfl

theorem cell21_180053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 3, 4].length) (baseStart_180053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_180053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_180053 prefixEnd_180053 := by exact prefixLift 180053
  have htrace : WordTrace (prefixWord ++ tailWord_180053) baseStart_180053 baseEnd_180053 := by
    simpa [prefixWord, tailWord_180053, baseEnd_180053] using wordTrace_append hprefix tailTrace_180053
  have hstable : (prefixWord ++ tailWord_180053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180053).length < 2 ^ (prefixWord ++ tailWord_180053).sum := by decide
  have hdescent : baseEnd_180053 < baseStart_180053 := by decide
  rcases family_descends (prefixWord ++ tailWord_180053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180191 : List Nat := [1, 1, 2, 3, 4, 1, 3, 3, 3]
def baseStart_180191 : Nat := 118140960795 + 180191 * 2 ^ 59
def prefixEnd_180191 : Nat := 4983230072969 + 3 ^ 40 * 180191 * 2
def baseEnd_180191 : Nat := 41122041161959882481699

theorem tailTrace_180191 : CollatzResearch.WordTrace tailWord_180191 prefixEnd_180191 41122041161959882481699 := by
  unfold tailWord_180191
  simp only [CollatzResearch.WordTrace]
  refine ⟨6572105690206256017852427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4381403793470837345234951 6572105690206256017852427)
  ·
    refine ⟨9858158535309384026778641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6572105690206256017852427 9858158535309384026778641)
    ·
      refine ⟨7393618901482038020083981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9858158535309384026778641 7393618901482038020083981)
      ·
        refine ⟨2772607088055764257531493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7393618901482038020083981 2772607088055764257531493)
        ·
          refine ⟨519863829010455798287155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2772607088055764257531493 519863829010455798287155)
          ·
            refine ⟨779795743515683697430733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 519863829010455798287155 779795743515683697430733)
            ·
              refine ⟨292423403818381386536525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 779795743515683697430733 292423403818381386536525)
              ·
                refine ⟨109658776431893019951197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 292423403818381386536525 109658776431893019951197)
                ·
                  refine ⟨41122041161959882481699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109658776431893019951197 41122041161959882481699)
                  ·
                    rfl

theorem cell21_180191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 3, 3].length) (baseStart_180191 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_180191 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_180191 prefixEnd_180191 := by exact prefixLift 180191
  have htrace : WordTrace (prefixWord ++ tailWord_180191) baseStart_180191 baseEnd_180191 := by
    simpa [prefixWord, tailWord_180191, baseEnd_180191] using wordTrace_append hprefix tailTrace_180191
  have hstable : (prefixWord ++ tailWord_180191).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180191).length < 2 ^ (prefixWord ++ tailWord_180191).sum := by decide
  have hdescent : baseEnd_180191 < baseStart_180191 := by decide
  rcases family_descends (prefixWord ++ tailWord_180191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180222 : List Nat := [4, 2, 2, 2, 1, 2, 1, 3, 4]
def baseStart_180222 : Nat := 118140960795 + 180222 * 2 ^ 59
def prefixEnd_180222 : Nat := 4983230072969 + 3 ^ 40 * 180222 * 2
def baseEnd_180222 : Nat := 41129115784310717464969

theorem tailTrace_180222 : CollatzResearch.WordTrace tailWord_180222 prefixEnd_180222 41129115784310717464969 := by
  unfold tailWord_180222
  simp only [CollatzResearch.WordTrace]
  refine ⟨821654544136743539028865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4382157568729298874820613 821654544136743539028865)
  ·
    refine ⟨616240908102557654271649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 821654544136743539028865 616240908102557654271649)
    ·
      refine ⟨462180681076918240703737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 616240908102557654271649 462180681076918240703737)
      ·
        refine ⟨346635510807688680527803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 462180681076918240703737 346635510807688680527803)
        ·
          refine ⟨519953266211533020791705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346635510807688680527803 519953266211533020791705)
          ·
            refine ⟨389964949658649765593779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 519953266211533020791705 389964949658649765593779)
            ·
              refine ⟨584947424487974648390669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 389964949658649765593779 584947424487974648390669)
              ·
                refine ⟨219355284182990493146501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 584947424487974648390669 219355284182990493146501)
                ·
                  refine ⟨41129115784310717464969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 219355284182990493146501 41129115784310717464969)
                  ·
                    rfl

theorem cell21_180222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_180222 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_180222 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_180222 prefixEnd_180222 := by exact prefixLift 180222
  have htrace : WordTrace (prefixWord ++ tailWord_180222) baseStart_180222 baseEnd_180222 := by
    simpa [prefixWord, tailWord_180222, baseEnd_180222] using wordTrace_append hprefix tailTrace_180222
  have hstable : (prefixWord ++ tailWord_180222).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180222).length < 2 ^ (prefixWord ++ tailWord_180222).sum := by decide
  have hdescent : baseEnd_180222 < baseStart_180222 := by decide
  rcases family_descends (prefixWord ++ tailWord_180222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180295 : List Nat := [1, 1, 4, 1, 3, 1, 5, 5]
def baseStart_180295 : Nat := 118140960795 + 180295 * 2 ^ 59
def prefixEnd_180295 : Nat := 4983230072969 + 3 ^ 40 * 180295 * 2
def baseEnd_180295 : Nat := 13715258459626270916051

theorem tailTrace_180295 : CollatzResearch.WordTrace tailWord_180295 prefixEnd_180295 13715258459626270916051 := by
  unfold tailWord_180295
  simp only [CollatzResearch.WordTrace]
  refine ⟨6575898881829481779638339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4383932587886321186425559 6575898881829481779638339)
  ·
    refine ⟨9863848322744222669457509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6575898881829481779638339 9863848322744222669457509)
    ·
      refine ⟨1849471560514541750523283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9863848322744222669457509 1849471560514541750523283)
      ·
        refine ⟨2774207340771812625784925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1849471560514541750523283 2774207340771812625784925)
        ·
          refine ⟨1040327752789429734669347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2774207340771812625784925 1040327752789429734669347)
          ·
            refine ⟨1560491629184144602004021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1040327752789429734669347 1560491629184144602004021)
            ·
              refine ⟨146296090236013556437877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1560491629184144602004021 146296090236013556437877)
              ·
                refine ⟨13715258459626270916051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 146296090236013556437877 13715258459626270916051)
                ·
                  rfl

theorem cell21_180295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 5].length) (baseStart_180295 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_180295 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_180295 prefixEnd_180295 := by exact prefixLift 180295
  have htrace : WordTrace (prefixWord ++ tailWord_180295) baseStart_180295 baseEnd_180295 := by
    simpa [prefixWord, tailWord_180295, baseEnd_180295] using wordTrace_append hprefix tailTrace_180295
  have hstable : (prefixWord ++ tailWord_180295).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180295).length < 2 ^ (prefixWord ++ tailWord_180295).sum := by decide
  have hdescent : baseEnd_180295 < baseStart_180295 := by decide
  rcases family_descends (prefixWord ++ tailWord_180295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180360 : List Nat := [2, 1, 3, 4, 1, 3, 1, 3, 3]
def baseStart_180360 : Nat := 118140960795 + 180360 * 2 ^ 59
def prefixEnd_180360 : Nat := 4983230072969 + 3 ^ 40 * 180360 * 2
def baseEnd_180360 : Nat := 41160609264453144164687

theorem tailTrace_180360 : CollatzResearch.WordTrace tailWord_180360 prefixEnd_180360 41160609264453144164687 := by
  unfold tailWord_180360
  simp only [CollatzResearch.WordTrace]
  refine ⟨3289134813296998940377267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4385513084395998587169689 3289134813296998940377267)
  ·
    refine ⟨4933702219945498410565901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3289134813296998940377267 4933702219945498410565901)
    ·
      refine ⟨1850138332479561903962213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4933702219945498410565901 1850138332479561903962213)
      ·
        refine ⟨346900937339917856992915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1850138332479561903962213 346900937339917856992915)
        ·
          refine ⟨520351406009876785489373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346900937339917856992915 520351406009876785489373)
          ·
            refine ⟨195131777253703794558515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 520351406009876785489373 195131777253703794558515)
            ·
              refine ⟨292697665880555691837773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195131777253703794558515 292697665880555691837773)
              ·
                refine ⟨109761624705208384439165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 292697665880555691837773 109761624705208384439165)
                ·
                  refine ⟨41160609264453144164687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109761624705208384439165 41160609264453144164687)
                  ·
                    rfl

theorem cell21_180360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 3, 3].length) (baseStart_180360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_180360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_180360 prefixEnd_180360 := by exact prefixLift 180360
  have htrace : WordTrace (prefixWord ++ tailWord_180360) baseStart_180360 baseEnd_180360 := by
    simpa [prefixWord, tailWord_180360, baseEnd_180360] using wordTrace_append hprefix tailTrace_180360
  have hstable : (prefixWord ++ tailWord_180360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180360).length < 2 ^ (prefixWord ++ tailWord_180360).sum := by decide
  have hdescent : baseEnd_180360 < baseStart_180360 := by decide
  rcases family_descends (prefixWord ++ tailWord_180360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180391 : List Nat := [1, 1, 6, 2, 2, 2, 2, 1, 4]
def baseStart_180391 : Nat := 118140960795 + 180391 * 2 ^ 59
def prefixEnd_180391 : Nat := 4983230072969 + 3 ^ 40 * 180391 * 2
def baseEnd_180391 : Nat := 41167683886803979147957

theorem tailTrace_180391 : CollatzResearch.WordTrace tailWord_180391 prefixEnd_180391 41167683886803979147957 := by
  unfold tailWord_180391
  simp only [CollatzResearch.WordTrace]
  refine ⟨6579400289481690175133027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4386266859654460116755351 6579400289481690175133027)
  ·
    refine ⟨9869100434222535262699541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6579400289481690175133027 9869100434222535262699541)
    ·
      refine ⟨462614082854181340439041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9869100434222535262699541 462614082854181340439041)
      ·
        refine ⟨346960562140636005329281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 462614082854181340439041 346960562140636005329281)
        ·
          refine ⟨260220421605477003996961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 346960562140636005329281 260220421605477003996961)
          ·
            refine ⟨195165316204107752997721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260220421605477003996961 195165316204107752997721)
            ·
              refine ⟨146373987153080814748291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195165316204107752997721 146373987153080814748291)
              ·
                refine ⟨219560980729621222122437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146373987153080814748291 219560980729621222122437)
                ·
                  refine ⟨41167683886803979147957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 219560980729621222122437 41167683886803979147957)
                  ·
                    rfl

theorem cell21_180391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 1, 4].length) (baseStart_180391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_180391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_180391 prefixEnd_180391 := by exact prefixLift 180391
  have htrace : WordTrace (prefixWord ++ tailWord_180391) baseStart_180391 baseEnd_180391 := by
    simpa [prefixWord, tailWord_180391, baseEnd_180391] using wordTrace_append hprefix tailTrace_180391
  have hstable : (prefixWord ++ tailWord_180391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180391).length < 2 ^ (prefixWord ++ tailWord_180391).sum := by decide
  have hdescent : baseEnd_180391 < baseStart_180391 := by decide
  rcases family_descends (prefixWord ++ tailWord_180391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180430 : List Nat := [4, 1, 1, 1, 4, 10]
def baseStart_180430 : Nat := 118140960795 + 180430 * 2 ^ 59
def prefixEnd_180430 : Nat := 4983230072969 + 3 ^ 40 * 180430 * 2
def baseEnd_180430 : Nat := 1525058674746243629551

theorem tailTrace_180430 : CollatzResearch.WordTrace tailWord_180430 prefixEnd_180430 1525058674746243629551 := by
  unfold tailWord_180430
  simp only [CollatzResearch.WordTrace]
  refine ⟨822602842042549979475343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4387215157560266557201829 822602842042549979475343)
  ·
    refine ⟨1233904263063824969213015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 822602842042549979475343 1233904263063824969213015)
    ·
      refine ⟨1850856394595737453819523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1233904263063824969213015 1850856394595737453819523)
      ·
        refine ⟨2776284591893606180729285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1850856394595737453819523 2776284591893606180729285)
        ·
          refine ⟨520553360980051158886741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2776284591893606180729285 520553360980051158886741)
          ·
            refine ⟨1525058674746243629551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 520553360980051158886741 1525058674746243629551)
            ·
              rfl

theorem cell21_180430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 10].length) (baseStart_180430 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_180430 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_180430 prefixEnd_180430 := by exact prefixLift 180430
  have htrace : WordTrace (prefixWord ++ tailWord_180430) baseStart_180430 baseEnd_180430 := by
    simpa [prefixWord, tailWord_180430, baseEnd_180430] using wordTrace_append hprefix tailTrace_180430
  have hstable : (prefixWord ++ tailWord_180430).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180430).length < 2 ^ (prefixWord ++ tailWord_180430).sum := by decide
  have hdescent : baseEnd_180430 < baseStart_180430 := by decide
  rcases family_descends (prefixWord ++ tailWord_180430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180551 : List Nat := [1, 1, 4, 1, 2, 2, 1, 3, 6]
def baseStart_180551 : Nat := 118140960795 + 180551 * 2 ^ 59
def prefixEnd_180551 : Nat := 4983230072969 + 3 ^ 40 * 180551 * 2
def baseEnd_180551 : Nat := 41204198066679256480963

theorem tailTrace_180551 : CollatzResearch.WordTrace tailWord_180551 prefixEnd_180551 41204198066679256480963 := by
  unfold tailWord_180551
  simp only [CollatzResearch.WordTrace]
  refine ⟨6585235968902037500957507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4390157312601358333971671 6585235968902037500957507)
  ·
    refine ⟨9877853953353056251436261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6585235968902037500957507 9877853953353056251436261)
    ·
      refine ⟨1852097616253698047144299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9877853953353056251436261 1852097616253698047144299)
      ·
        refine ⟨2778146424380547070716449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1852097616253698047144299 2778146424380547070716449)
        ·
          refine ⟨2083609818285410303037337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2778146424380547070716449 2083609818285410303037337)
          ·
            refine ⟨1562707363714057727278003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2083609818285410303037337 1562707363714057727278003)
            ·
              refine ⟨2344061045571086590917005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1562707363714057727278003 2344061045571086590917005)
              ·
                refine ⟨879022892089157471593877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2344061045571086590917005 879022892089157471593877)
                ·
                  refine ⟨41204198066679256480963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 879022892089157471593877 41204198066679256480963)
                  ·
                    rfl

theorem cell21_180551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 6].length) (baseStart_180551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_180551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_180551 prefixEnd_180551 := by exact prefixLift 180551
  have htrace : WordTrace (prefixWord ++ tailWord_180551) baseStart_180551 baseEnd_180551 := by
    simpa [prefixWord, tailWord_180551, baseEnd_180551] using wordTrace_append hprefix tailTrace_180551
  have hstable : (prefixWord ++ tailWord_180551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180551).length < 2 ^ (prefixWord ++ tailWord_180551).sum := by decide
  have hdescent : baseEnd_180551 < baseStart_180551 := by decide
  rcases family_descends (prefixWord ++ tailWord_180551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180647 : List Nat := [1, 1, 6, 1, 1, 3, 2, 3, 3]
def baseStart_180647 : Nat := 118140960795 + 180647 * 2 ^ 59
def prefixEnd_180647 : Nat := 4983230072969 + 3 ^ 40 * 180647 * 2
def baseEnd_180647 : Nat := 41226106574604422880767

theorem tailTrace_180647 : CollatzResearch.WordTrace tailWord_180647 prefixEnd_180647 41226106574604422880767 := by
  unfold tailWord_180647
  simp only [CollatzResearch.WordTrace]
  refine ⟨6588737376554245896452195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4392491584369497264301463 6588737376554245896452195)
  ·
    refine ⟨9883106064831368844678293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6588737376554245896452195 9883106064831368844678293)
    ·
      refine ⟨463270596788970414594295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9883106064831368844678293 463270596788970414594295)
      ·
        refine ⟨694905895183455621891443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463270596788970414594295 694905895183455621891443)
        ·
          refine ⟨1042358842775183432837165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 694905895183455621891443 1042358842775183432837165)
          ·
            refine ⟨390884566040693787313937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1042358842775183432837165 390884566040693787313937)
            ·
              refine ⟨293163424530520340485453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 390884566040693787313937 293163424530520340485453)
              ·
                refine ⟨109936284198945127682045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 293163424530520340485453 109936284198945127682045)
                ·
                  refine ⟨41226106574604422880767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109936284198945127682045 41226106574604422880767)
                  ·
                    rfl

theorem cell21_180647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 3, 3].length) (baseStart_180647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_180647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_180647 prefixEnd_180647 := by exact prefixLift 180647
  have htrace : WordTrace (prefixWord ++ tailWord_180647) baseStart_180647 baseEnd_180647 := by
    simpa [prefixWord, tailWord_180647, baseEnd_180647] using wordTrace_append hprefix tailTrace_180647
  have hstable : (prefixWord ++ tailWord_180647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180647).length < 2 ^ (prefixWord ++ tailWord_180647).sum := by decide
  have hdescent : baseEnd_180647 < baseStart_180647 := by decide
  rcases family_descends (prefixWord ++ tailWord_180647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180692 : List Nat := [2, 4, 1, 2, 2, 3, 2, 5]
def baseStart_180692 : Nat := 118140960795 + 180692 * 2 ^ 59
def prefixEnd_180692 : Nat := 4983230072969 + 3 ^ 40 * 180692 * 2
def baseEnd_180692 : Nat := 13745458729231448210225

theorem tailTrace_180692 : CollatzResearch.WordTrace tailWord_180692 prefixEnd_180692 13745458729231448210225 := by
  unfold tailWord_180692
  simp only [CollatzResearch.WordTrace]
  refine ⟨3295189330695609290920165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4393585774260812387893553 3295189330695609290920165)
  ·
    refine ⟨617847999505426742047531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3295189330695609290920165 617847999505426742047531)
    ·
      refine ⟨926771999258140113071297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 617847999505426742047531 926771999258140113071297)
      ·
        refine ⟨695078999443605084803473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 926771999258140113071297 695078999443605084803473)
        ·
          refine ⟨521309249582703813602605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 695078999443605084803473 521309249582703813602605)
          ·
            refine ⟨195490968593513930100977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 521309249582703813602605 195490968593513930100977)
            ·
              refine ⟨146618226445135447575733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195490968593513930100977 146618226445135447575733)
              ·
                refine ⟨13745458729231448210225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 146618226445135447575733 13745458729231448210225)
                ·
                  rfl

theorem cell21_180692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 5].length) (baseStart_180692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_180692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_180692 prefixEnd_180692 := by exact prefixLift 180692
  have htrace : WordTrace (prefixWord ++ tailWord_180692) baseStart_180692 baseEnd_180692 := by
    simpa [prefixWord, tailWord_180692, baseEnd_180692] using wordTrace_append hprefix tailTrace_180692
  have hstable : (prefixWord ++ tailWord_180692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180692).length < 2 ^ (prefixWord ++ tailWord_180692).sum := by decide
  have hdescent : baseEnd_180692 < baseStart_180692 := by decide
  rcases family_descends (prefixWord ++ tailWord_180692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180703 : List Nat := [1, 1, 2, 3, 3, 2, 1, 2, 6]
def baseStart_180703 : Nat := 118140960795 + 180703 * 2 ^ 59
def prefixEnd_180703 : Nat := 4983230072969 + 3 ^ 40 * 180703 * 2
def baseEnd_180703 : Nat := 41238886537560769947319

theorem tailTrace_180703 : CollatzResearch.WordTrace tailWord_180703 prefixEnd_180703 41238886537560769947319 := by
  unfold tailWord_180703
  simp only [CollatzResearch.WordTrace]
  refine ⟨6590779864351367460490763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4393853242900911640327175 6590779864351367460490763)
  ·
    refine ⟨9886169796527051190736145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6590779864351367460490763 9886169796527051190736145)
    ·
      refine ⟨7414627347395288393052109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9886169796527051190736145 7414627347395288393052109)
      ·
        refine ⟨2780485255273233147394541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7414627347395288393052109 2780485255273233147394541)
        ·
          refine ⟨1042681970727462430272953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2780485255273233147394541 1042681970727462430272953)
          ·
            refine ⟨782011478045596822704715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1042681970727462430272953 782011478045596822704715)
            ·
              refine ⟨1173017217068395234057073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 782011478045596822704715 1173017217068395234057073)
              ·
                refine ⟨879762912801296425542805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1173017217068395234057073 879762912801296425542805)
                ·
                  refine ⟨41238886537560769947319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 879762912801296425542805 41238886537560769947319)
                  ·
                    rfl

theorem cell21_180703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 6].length) (baseStart_180703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_180703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_180703 prefixEnd_180703 := by exact prefixLift 180703
  have htrace : WordTrace (prefixWord ++ tailWord_180703) baseStart_180703 baseEnd_180703 := by
    simpa [prefixWord, tailWord_180703, baseEnd_180703] using wordTrace_append hprefix tailTrace_180703
  have hstable : (prefixWord ++ tailWord_180703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180703).length < 2 ^ (prefixWord ++ tailWord_180703).sum := by decide
  have hdescent : baseEnd_180703 < baseStart_180703 := by decide
  rcases family_descends (prefixWord ++ tailWord_180703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180737 : List Nat := [1, 2, 4, 1, 3, 1, 4, 1, 4]
def baseStart_180737 : Nat := 118140960795 + 180737 * 2 ^ 59
def prefixEnd_180737 : Nat := 4983230072969 + 3 ^ 40 * 180737 * 2
def baseEnd_180737 : Nat := 41246645800784266380583

theorem tailTrace_180737 : CollatzResearch.WordTrace tailWord_180737 prefixEnd_180737 41246645800784266380583 := by
  unfold tailWord_180737
  simp only [CollatzResearch.WordTrace]
  refine ⟨6592019946228191267228465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4394679964152127511485643 6592019946228191267228465)
  ·
    refine ⟨4944014959671143450421349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6592019946228191267228465 4944014959671143450421349)
    ·
      refine ⟨927002804938339396954003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4944014959671143450421349 927002804938339396954003)
      ·
        refine ⟨1390504207407509095431005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 927002804938339396954003 1390504207407509095431005)
        ·
          refine ⟨521439077777815910786627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1390504207407509095431005 521439077777815910786627)
          ·
            refine ⟨782158616666723866179941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 521439077777815910786627 782158616666723866179941)
            ·
              refine ⟨146654740625010724908739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 782158616666723866179941 146654740625010724908739)
              ·
                refine ⟨219982110937516087363109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146654740625010724908739 219982110937516087363109)
                ·
                  refine ⟨41246645800784266380583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 219982110937516087363109 41246645800784266380583)
                  ·
                    rfl

theorem cell21_180737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 1, 4].length) (baseStart_180737 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_180737 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_180737 prefixEnd_180737 := by exact prefixLift 180737
  have htrace : WordTrace (prefixWord ++ tailWord_180737) baseStart_180737 baseEnd_180737 := by
    simpa [prefixWord, tailWord_180737, baseEnd_180737] using wordTrace_append hprefix tailTrace_180737
  have hstable : (prefixWord ++ tailWord_180737).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180737).length < 2 ^ (prefixWord ++ tailWord_180737).sum := by decide
  have hdescent : baseEnd_180737 < baseStart_180737 := by decide
  rcases family_descends (prefixWord ++ tailWord_180737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180796 : List Nat := [2, 2, 2, 2, 3, 1, 2, 3, 4]
def baseStart_180796 : Nat := 118140960795 + 180796 * 2 ^ 59
def prefixEnd_180796 : Nat := 4983230072969 + 3 ^ 40 * 180796 * 2
def baseEnd_180796 : Nat := 41260110404613274897129

theorem tailTrace_180796 : CollatzResearch.WordTrace tailWord_180796 prefixEnd_180796 41260110404613274897129 := by
  unfold tailWord_180796
  simp only [CollatzResearch.WordTrace]
  refine ⟨3297085926507222171813121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4396114568676296229084161 3297085926507222171813121)
  ·
    refine ⟨2472814444880416628859841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3297085926507222171813121 2472814444880416628859841)
    ·
      refine ⟨1854610833660312471644881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2472814444880416628859841 1854610833660312471644881)
      ·
        refine ⟨1390958125245234353733661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1854610833660312471644881 1390958125245234353733661)
        ·
          refine ⟨521609296966962882650123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1390958125245234353733661 521609296966962882650123)
          ·
            refine ⟨782413945450444323975185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 521609296966962882650123 782413945450444323975185)
            ·
              refine ⟨586810459087833242981389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 782413945450444323975185 586810459087833242981389)
              ·
                refine ⟨220053922157937466118021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 586810459087833242981389 220053922157937466118021)
                ·
                  refine ⟨41260110404613274897129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 220053922157937466118021 41260110404613274897129)
                  ·
                    rfl

theorem cell21_180796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 3, 4].length) (baseStart_180796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_180796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_180796 prefixEnd_180796 := by exact prefixLift 180796
  have htrace : WordTrace (prefixWord ++ tailWord_180796) baseStart_180796 baseEnd_180796 := by
    simpa [prefixWord, tailWord_180796, baseEnd_180796] using wordTrace_append hprefix tailTrace_180796
  have hstable : (prefixWord ++ tailWord_180796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180796).length < 2 ^ (prefixWord ++ tailWord_180796).sum := by decide
  have hdescent : baseEnd_180796 < baseStart_180796 := by decide
  rcases family_descends (prefixWord ++ tailWord_180796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180855 : List Nat := [1, 1, 3, 1, 1, 3, 2, 5, 4]
def baseStart_180855 : Nat := 118140960795 + 180855 * 2 ^ 59
def prefixEnd_180855 : Nat := 4983230072969 + 3 ^ 40 * 180855 * 2
def baseEnd_180855 : Nat := 41273575008442283413675

theorem tailTrace_180855 : CollatzResearch.WordTrace tailWord_180855 prefixEnd_180855 41273575008442283413675 := by
  unfold tailWord_180855
  simp only [CollatzResearch.WordTrace]
  refine ⟨6596323759800697420024019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4397549173200464946682679 6596323759800697420024019)
  ·
    refine ⟨9894485639701046130036029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6596323759800697420024019 9894485639701046130036029)
    ·
      refine ⟨3710432114887892298763511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9894485639701046130036029 3710432114887892298763511)
      ·
        refine ⟨5565648172331838448145267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3710432114887892298763511 5565648172331838448145267)
        ·
          refine ⟨8348472258497757672217901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5565648172331838448145267 8348472258497757672217901)
          ·
            refine ⟨3130677096936659127081713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8348472258497757672217901 3130677096936659127081713)
            ·
              refine ⟨2348007822702494345311285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3130677096936659127081713 2348007822702494345311285)
              ·
                refine ⟨220125733378358844872933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2348007822702494345311285 220125733378358844872933)
                ·
                  refine ⟨41273575008442283413675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 220125733378358844872933 41273575008442283413675)
                  ·
                    rfl

theorem cell21_180855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 5, 4].length) (baseStart_180855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_180855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_180855 prefixEnd_180855 := by exact prefixLift 180855
  have htrace : WordTrace (prefixWord ++ tailWord_180855) baseStart_180855 baseEnd_180855 := by
    simpa [prefixWord, tailWord_180855, baseEnd_180855] using wordTrace_append hprefix tailTrace_180855
  have hstable : (prefixWord ++ tailWord_180855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180855).length < 2 ^ (prefixWord ++ tailWord_180855).sum := by decide
  have hdescent : baseEnd_180855 < baseStart_180855 := by decide
  rcases family_descends (prefixWord ++ tailWord_180855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180906 : List Nat := [3, 1, 5, 2, 1, 1, 1, 3, 4]
def baseStart_180906 : Nat := 118140960795 + 180906 * 2 ^ 59
def prefixEnd_180906 : Nat := 4983230072969 + 3 ^ 40 * 180906 * 2
def baseEnd_180906 : Nat := 41285213903277528063571

theorem tailTrace_180906 : CollatzResearch.WordTrace tailWord_180906 prefixEnd_180906 41285213903277528063571 := by
  unfold tailWord_180906
  simp only [CollatzResearch.WordTrace]
  refine ⟨1649545970653983282532643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4398789255077288753420381 1649545970653983282532643)
  ·
    refine ⟨2474318955980974923798965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1649545970653983282532643 2474318955980974923798965)
    ·
      refine ⟨231967402123216399106153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2474318955980974923798965 231967402123216399106153)
      ·
        refine ⟨173975551592412299329615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231967402123216399106153 173975551592412299329615)
        ·
          refine ⟨260963327388618448994423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173975551592412299329615 260963327388618448994423)
          ·
            refine ⟨391444991082927673491635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260963327388618448994423 391444991082927673491635)
            ·
              refine ⟨587167486624391510237453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 391444991082927673491635 587167486624391510237453)
              ·
                refine ⟨220187807484146816339045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 587167486624391510237453 220187807484146816339045)
                ·
                  refine ⟨41285213903277528063571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 220187807484146816339045 41285213903277528063571)
                  ·
                    rfl

theorem cell21_180906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 3, 4].length) (baseStart_180906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_180906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_180906 prefixEnd_180906 := by exact prefixLift 180906
  have htrace : WordTrace (prefixWord ++ tailWord_180906) baseStart_180906 baseEnd_180906 := by
    simpa [prefixWord, tailWord_180906, baseEnd_180906] using wordTrace_append hprefix tailTrace_180906
  have hstable : (prefixWord ++ tailWord_180906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180906).length < 2 ^ (prefixWord ++ tailWord_180906).sum := by decide
  have hdescent : baseEnd_180906 < baseStart_180906 := by decide
  rcases family_descends (prefixWord ++ tailWord_180906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180951 : List Nat := [1, 1, 3, 2, 1, 6, 2, 2, 3]
def baseStart_180951 : Nat := 118140960795 + 180951 * 2 ^ 59
def prefixEnd_180951 : Nat := 4983230072969 + 3 ^ 40 * 180951 * 2
def baseEnd_180951 : Nat := 41295483516367449813479

theorem tailTrace_180951 : CollatzResearch.WordTrace tailWord_180951 prefixEnd_180951 41295483516367449813479 := by
  unfold tailWord_180951
  simp only [CollatzResearch.WordTrace]
  refine ⟨6599825167452905815518707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4399883444968603877012471 6599825167452905815518707)
  ·
    refine ⟨9899737751179358723278061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6599825167452905815518707 9899737751179358723278061)
    ·
      refine ⟨3712401656692259521229273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9899737751179358723278061 3712401656692259521229273)
      ·
        refine ⟨2784301242519194640921955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3712401656692259521229273 2784301242519194640921955)
        ·
          refine ⟨4176451863778791961382933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2784301242519194640921955 4176451863778791961382933)
          ·
            refine ⟨195771181114630873189825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4176451863778791961382933 195771181114630873189825)
            ·
              refine ⟨146828385835973154892369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195771181114630873189825 146828385835973154892369)
              ·
                refine ⟨110121289376979866169277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146828385835973154892369 110121289376979866169277)
                ·
                  refine ⟨41295483516367449813479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110121289376979866169277 41295483516367449813479)
                  ·
                    rfl

theorem cell21_180951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 2, 3].length) (baseStart_180951 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_180951 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_180951 prefixEnd_180951 := by exact prefixLift 180951
  have htrace : WordTrace (prefixWord ++ tailWord_180951) baseStart_180951 baseEnd_180951 := by
    simpa [prefixWord, tailWord_180951, baseEnd_180951] using wordTrace_append hprefix tailTrace_180951
  have hstable : (prefixWord ++ tailWord_180951).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180951).length < 2 ^ (prefixWord ++ tailWord_180951).sum := by decide
  have hdescent : baseEnd_180951 < baseStart_180951 := by decide
  rcases family_descends (prefixWord ++ tailWord_180951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180976 : List Nat := [2, 1, 1, 1, 3, 1, 5, 2, 5]
def baseStart_180976 : Nat := 118140960795 + 180976 * 2 ^ 59
def prefixEnd_180976 : Nat := 4983230072969 + 3 ^ 40 * 180976 * 2
def baseEnd_180976 : Nat := 41301188856972961896761

theorem tailTrace_180976 : CollatzResearch.WordTrace tailWord_180976 prefixEnd_180976 41301188856972961896761 := by
  unfold tailWord_180976
  simp only [CollatzResearch.WordTrace]
  refine ⟨3300368496181167542589391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4400491328241556723452521 3300368496181167542589391)
  ·
    refine ⟨4950552744271751313884087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3300368496181167542589391 4950552744271751313884087)
    ·
      refine ⟨7425829116407626970826131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4950552744271751313884087 7425829116407626970826131)
      ·
        refine ⟨11138743674611440456239197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7425829116407626970826131 11138743674611440456239197)
        ·
          refine ⟨4177028877979290171089699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11138743674611440456239197 4177028877979290171089699)
          ·
            refine ⟨6265543316968935256634549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4177028877979290171089699 6265543316968935256634549)
            ·
              refine ⟨587394685965837680309489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6265543316968935256634549 587394685965837680309489)
              ·
                refine ⟨440546014474378260232117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 587394685965837680309489 440546014474378260232117)
                ·
                  refine ⟨41301188856972961896761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 440546014474378260232117 41301188856972961896761)
                  ·
                    rfl

theorem cell21_180976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 5].length) (baseStart_180976 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_180976 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_180976 prefixEnd_180976 := by exact prefixLift 180976
  have htrace : WordTrace (prefixWord ++ tailWord_180976) baseStart_180976 baseEnd_180976 := by
    simpa [prefixWord, tailWord_180976, baseEnd_180976] using wordTrace_append hprefix tailTrace_180976
  have hstable : (prefixWord ++ tailWord_180976).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180976).length < 2 ^ (prefixWord ++ tailWord_180976).sum := by decide
  have hdescent : baseEnd_180976 < baseStart_180976 := by decide
  rcases family_descends (prefixWord ++ tailWord_180976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181044 : List Nat := [2, 5, 1, 1, 3, 2, 1, 3, 3]
def baseStart_181044 : Nat := 118140960795 + 181044 * 2 ^ 59
def prefixEnd_181044 : Nat := 4983230072969 + 3 ^ 40 * 181044 * 2
def baseEnd_181044 : Nat := 41316707383419954763289

theorem tailTrace_181044 : CollatzResearch.WordTrace tailWord_181044 prefixEnd_181044 41316707383419954763289 := by
  unfold tailWord_181044
  simp only [CollatzResearch.WordTrace]
  refine ⟨3301608578057991349327093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4402144770743988465769457 3301608578057991349327093)
  ·
    refine ⟨309525804192936688999415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3301608578057991349327093 309525804192936688999415)
    ·
      refine ⟨464288706289405033499123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309525804192936688999415 464288706289405033499123)
      ·
        refine ⟨696433059434107550248685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464288706289405033499123 696433059434107550248685)
        ·
          refine ⟨261162397287790331343257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 696433059434107550248685 261162397287790331343257)
          ·
            refine ⟨195871797965842748507443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 261162397287790331343257 195871797965842748507443)
            ·
              refine ⟨293807696948764122761165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195871797965842748507443 293807696948764122761165)
              ·
                refine ⟨110177886355786546035437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 293807696948764122761165 110177886355786546035437)
                ·
                  refine ⟨41316707383419954763289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110177886355786546035437 41316707383419954763289)
                  ·
                    rfl

theorem cell21_181044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_181044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_181044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_181044 prefixEnd_181044 := by exact prefixLift 181044
  have htrace : WordTrace (prefixWord ++ tailWord_181044) baseStart_181044 baseEnd_181044 := by
    simpa [prefixWord, tailWord_181044, baseEnd_181044] using wordTrace_append hprefix tailTrace_181044
  have hstable : (prefixWord ++ tailWord_181044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181044).length < 2 ^ (prefixWord ++ tailWord_181044).sum := by decide
  have hdescent : baseEnd_181044 < baseStart_181044 := by decide
  rcases family_descends (prefixWord ++ tailWord_181044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181173 : List Nat := [1, 3, 3, 2, 1, 1, 10]
def baseStart_181173 : Nat := 118140960795 + 181173 * 2 ^ 59
def prefixEnd_181173 : Nat := 4983230072969 + 3 ^ 40 * 181173 * 2
def baseEnd_181173 : Nat := 4594016326771599679225

theorem tailTrace_181173 : CollatzResearch.WordTrace tailWord_181173 prefixEnd_181173 4594016326771599679225 := by
  unfold tailWord_181173
  simp only [CollatzResearch.WordTrace]
  refine ⟨6607922172648637730100173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4405281448432425153400115 6607922172648637730100173)
  ·
    refine ⟨2477970814743239148787565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6607922172648637730100173 2477970814743239148787565)
    ·
      refine ⟨929239055528714680795337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2477970814743239148787565 929239055528714680795337)
      ·
        refine ⟨696929291646536010596503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 929239055528714680795337 696929291646536010596503)
        ·
          refine ⟨1045393937469804015894755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 696929291646536010596503 1045393937469804015894755)
          ·
            refine ⟨1568090906204706023842133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1045393937469804015894755 1568090906204706023842133)
            ·
              refine ⟨4594016326771599679225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1568090906204706023842133 4594016326771599679225)
              ·
                rfl

theorem cell21_181173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 10].length) (baseStart_181173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_181173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_181173 prefixEnd_181173 := by exact prefixLift 181173
  have htrace : WordTrace (prefixWord ++ tailWord_181173) baseStart_181173 baseEnd_181173 := by
    simpa [prefixWord, tailWord_181173, baseEnd_181173] using wordTrace_append hprefix tailTrace_181173
  have hstable : (prefixWord ++ tailWord_181173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181173).length < 2 ^ (prefixWord ++ tailWord_181173).sum := by decide
  have hdescent : baseEnd_181173 < baseStart_181173 := by decide
  rcases family_descends (prefixWord ++ tailWord_181173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181176 : List Nat := [2, 1, 2, 1, 2, 6, 1, 2, 4]
def baseStart_181176 : Nat := 118140960795 + 181176 * 2 ^ 59
def prefixEnd_181176 : Nat := 4983230072969 + 3 ^ 40 * 181176 * 2
def baseEnd_181176 : Nat := 41346831581817058563019

theorem tailTrace_181176 : CollatzResearch.WordTrace tailWord_181176 prefixEnd_181176 41346831581817058563019 := by
  unfold tailWord_181176
  simp only [CollatzResearch.WordTrace]
  refine ⟨3304015795818884621229691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4405354394425179494972921 3304015795818884621229691)
  ·
    refine ⟨4956023693728326931844537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3304015795818884621229691 4956023693728326931844537)
    ·
      refine ⟨3717017770296245198883403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4956023693728326931844537 3717017770296245198883403)
      ·
        refine ⟨5575526655444367798325105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3717017770296245198883403 5575526655444367798325105)
        ·
          refine ⟨4181644991583275848743829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5575526655444367798325105 4181644991583275848743829)
          ·
            refine ⟨196014608980466055409867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4181644991583275848743829 196014608980466055409867)
            ·
              refine ⟨294021913470699083114801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196014608980466055409867 294021913470699083114801)
              ·
                refine ⟨220516435103024312336101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 294021913470699083114801 220516435103024312336101)
                ·
                  refine ⟨41346831581817058563019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 220516435103024312336101 41346831581817058563019)
                  ·
                    rfl

theorem cell21_181176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 2, 4].length) (baseStart_181176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_181176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_181176 prefixEnd_181176 := by exact prefixLift 181176
  have htrace : WordTrace (prefixWord ++ tailWord_181176) baseStart_181176 baseEnd_181176 := by
    simpa [prefixWord, tailWord_181176, baseEnd_181176] using wordTrace_append hprefix tailTrace_181176
  have hstable : (prefixWord ++ tailWord_181176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181176).length < 2 ^ (prefixWord ++ tailWord_181176).sum := by decide
  have hdescent : baseEnd_181176 < baseStart_181176 := by decide
  rcases family_descends (prefixWord ++ tailWord_181176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181187 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 9]
def baseStart_181187 : Nat := 118140960795 + 181187 * 2 ^ 59
def prefixEnd_181187 : Nat := 4983230072969 + 3 ^ 40 * 181187 * 2
def baseEnd_181187 : Nat := 41349341931683483879663

theorem tailTrace_181187 : CollatzResearch.WordTrace tailWord_181187 prefixEnd_181187 41349341931683483879663 := by
  unfold tailWord_181187
  simp only [CollatzResearch.WordTrace]
  refine ⟨6608432794597918121109815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4405621863065278747406543 6608432794597918121109815)
  ·
    refine ⟨9912649191896877181664723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6608432794597918121109815 9912649191896877181664723)
    ·
      refine ⟨14868973787845315772497085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9912649191896877181664723 14868973787845315772497085)
      ·
        refine ⟨5575865170441993414686407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14868973787845315772497085 5575865170441993414686407)
        ·
          refine ⟨8363797755662990122029611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5575865170441993414686407 8363797755662990122029611)
          ·
            refine ⟨12545696633494485183044417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8363797755662990122029611 12545696633494485183044417)
            ·
              refine ⟨9409272475120863887283313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12545696633494485183044417 9409272475120863887283313)
              ·
                refine ⟨7056954356340647915462485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9409272475120863887283313 7056954356340647915462485)
                ·
                  refine ⟨41349341931683483879663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 7056954356340647915462485 41349341931683483879663)
                  ·
                    rfl

theorem cell21_181187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 9].length) (baseStart_181187 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_181187 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_181187 prefixEnd_181187 := by exact prefixLift 181187
  have htrace : WordTrace (prefixWord ++ tailWord_181187) baseStart_181187 baseEnd_181187 := by
    simpa [prefixWord, tailWord_181187, baseEnd_181187] using wordTrace_append hprefix tailTrace_181187
  have hstable : (prefixWord ++ tailWord_181187).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181187).length < 2 ^ (prefixWord ++ tailWord_181187).sum := by decide
  have hdescent : baseEnd_181187 < baseStart_181187 := by decide
  rcases family_descends (prefixWord ++ tailWord_181187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181238 : List Nat := [5, 1, 1, 1, 3, 3, 1, 1, 5]
def baseStart_181238 : Nat := 118140960795 + 181238 * 2 ^ 59
def prefixEnd_181238 : Nat := 4983230072969 + 3 ^ 40 * 181238 * 2
def baseEnd_181238 : Nat := 41360980826518728529559

theorem tailTrace_181238 : CollatzResearch.WordTrace tailWord_181238 prefixEnd_181238 41360980826518728529559 := by
  unfold tailWord_181238
  simp only [CollatzResearch.WordTrace]
  refine ⟨413143307338322114451023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4406861944942102554144245 413143307338322114451023)
  ·
    refine ⟨619714961007483171676535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 413143307338322114451023 619714961007483171676535)
    ·
      refine ⟨929572441511224757514803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 619714961007483171676535 929572441511224757514803)
      ·
        refine ⟨1394358662266837136272205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 929572441511224757514803 1394358662266837136272205)
        ·
          refine ⟨522884498350063926102077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1394358662266837136272205 522884498350063926102077)
          ·
            refine ⟨196081686881273972288279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 522884498350063926102077 196081686881273972288279)
            ·
              refine ⟨294122530321910958432419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196081686881273972288279 294122530321910958432419)
              ·
                refine ⟨441183795482866437648629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 294122530321910958432419 441183795482866437648629)
                ·
                  refine ⟨41360980826518728529559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 441183795482866437648629 41360980826518728529559)
                  ·
                    rfl

theorem cell21_181238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_181238 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_181238 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_181238 prefixEnd_181238 := by exact prefixLift 181238
  have htrace : WordTrace (prefixWord ++ tailWord_181238) baseStart_181238 baseEnd_181238 := by
    simpa [prefixWord, tailWord_181238, baseEnd_181238] using wordTrace_append hprefix tailTrace_181238
  have hstable : (prefixWord ++ tailWord_181238).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181238).length < 2 ^ (prefixWord ++ tailWord_181238).sum := by decide
  have hdescent : baseEnd_181238 < baseStart_181238 := by decide
  rcases family_descends (prefixWord ++ tailWord_181238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181249 : List Nat := [1, 2, 4, 1, 2, 2, 1, 8]
def baseStart_181249 : Nat := 118140960795 + 181249 * 2 ^ 59
def prefixEnd_181249 : Nat := 4983230072969 + 3 ^ 40 * 181249 * 2
def baseEnd_181249 : Nat := 13787830392128384615401

theorem tailTrace_181249 : CollatzResearch.WordTrace tailWord_181249 prefixEnd_181249 13787830392128384615401 := by
  unfold tailWord_181249
  simp only [CollatzResearch.WordTrace]
  refine ⟨6610694120373302709866801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4407129413582201806577867 6610694120373302709866801)
  ·
    refine ⟨4958020590279977032400101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6610694120373302709866801 4958020590279977032400101)
    ·
      refine ⟨929628860677495693575019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4958020590279977032400101 929628860677495693575019)
      ·
        refine ⟨1394443291016243540362529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 929628860677495693575019 1394443291016243540362529)
        ·
          refine ⟨1045832468262182655271897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1394443291016243540362529 1045832468262182655271897)
          ·
            refine ⟨784374351196636991453923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1045832468262182655271897 784374351196636991453923)
            ·
              refine ⟨1176561526794955487180885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 784374351196636991453923 1176561526794955487180885)
              ·
                refine ⟨13787830392128384615401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1176561526794955487180885 13787830392128384615401)
                ·
                  rfl

theorem cell21_181249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 8].length) (baseStart_181249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_181249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_181249 prefixEnd_181249 := by exact prefixLift 181249
  have htrace : WordTrace (prefixWord ++ tailWord_181249) baseStart_181249 baseEnd_181249 := by
    simpa [prefixWord, tailWord_181249, baseEnd_181249] using wordTrace_append hprefix tailTrace_181249
  have hstable : (prefixWord ++ tailWord_181249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181249).length < 2 ^ (prefixWord ++ tailWord_181249).sum := by decide
  have hdescent : baseEnd_181249 < baseStart_181249 := by decide
  rcases family_descends (prefixWord ++ tailWord_181249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181297 : List Nat := [1, 2, 2, 3, 1, 2, 3, 4, 3]
def baseStart_181297 : Nat := 118140960795 + 181297 * 2 ^ 59
def prefixEnd_181297 : Nat := 4983230072969 + 3 ^ 40 * 181297 * 2
def baseEnd_181297 : Nat := 41374445430347737046105

theorem tailTrace_181297 : CollatzResearch.WordTrace tailWord_181297 prefixEnd_181297 41374445430347737046105 := by
  unfold tailWord_181297
  simp only [CollatzResearch.WordTrace]
  refine ⟨6612444824199406907614145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4408296549466271271742763 6612444824199406907614145)
  ·
    refine ⟨4959333618149555180710609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6612444824199406907614145 4959333618149555180710609)
    ·
      refine ⟨3719500213612166385532957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4959333618149555180710609 3719500213612166385532957)
      ·
        refine ⟨1394812580104562394574859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3719500213612166385532957 1394812580104562394574859)
        ·
          refine ⟨2092218870156843591862289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1394812580104562394574859 2092218870156843591862289)
          ·
            refine ⟨1569164152617632693896717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2092218870156843591862289 1569164152617632693896717)
            ·
              refine ⟨588436557231612260211269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1569164152617632693896717 588436557231612260211269)
              ·
                refine ⟨110331854480927298789613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 588436557231612260211269 110331854480927298789613)
                ·
                  refine ⟨41374445430347737046105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110331854480927298789613 41374445430347737046105)
                  ·
                    rfl

theorem cell21_181297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 4, 3].length) (baseStart_181297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_181297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_181297 prefixEnd_181297 := by exact prefixLift 181297
  have htrace : WordTrace (prefixWord ++ tailWord_181297) baseStart_181297 baseEnd_181297 := by
    simpa [prefixWord, tailWord_181297, baseEnd_181297] using wordTrace_append hprefix tailTrace_181297
  have hstable : (prefixWord ++ tailWord_181297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181297).length < 2 ^ (prefixWord ++ tailWord_181297).sum := by decide
  have hdescent : baseEnd_181297 < baseStart_181297 := by decide
  rcases family_descends (prefixWord ++ tailWord_181297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181356 : List Nat := [2, 2, 1, 1, 3, 2, 4, 1, 5]
def baseStart_181356 : Nat := 118140960795 + 181356 * 2 ^ 59
def prefixEnd_181356 : Nat := 4983230072969 + 3 ^ 40 * 181356 * 2
def baseEnd_181356 : Nat := 41387910034176745562651

theorem tailTrace_181356 : CollatzResearch.WordTrace tailWord_181356 prefixEnd_181356 41387910034176745562651 := by
  unfold tailWord_181356
  simp only [CollatzResearch.WordTrace]
  refine ⟨3307298365492829992005961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4409731153990439989341281 3307298365492829992005961)
  ·
    refine ⟨2480473774119622494004471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3307298365492829992005961 2480473774119622494004471)
    ·
      refine ⟨3720710661179433741006707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2480473774119622494004471 3720710661179433741006707)
      ·
        refine ⟨5581065991769150611510061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3720710661179433741006707 5581065991769150611510061)
        ·
          refine ⟨2092899746913431479316273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5581065991769150611510061 2092899746913431479316273)
          ·
            refine ⟨1569674810185073609487205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2092899746913431479316273 1569674810185073609487205)
            ·
              refine ⟨294314026909701301778851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1569674810185073609487205 294314026909701301778851)
              ·
                refine ⟨441471040364551952668277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 294314026909701301778851 441471040364551952668277)
                ·
                  refine ⟨41387910034176745562651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 441471040364551952668277 41387910034176745562651)
                  ·
                    rfl

theorem cell21_181356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 5].length) (baseStart_181356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_181356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_181356 prefixEnd_181356 := by exact prefixLift 181356
  have htrace : WordTrace (prefixWord ++ tailWord_181356) baseStart_181356 baseEnd_181356 := by
    simpa [prefixWord, tailWord_181356, baseEnd_181356] using wordTrace_append hprefix tailTrace_181356
  have hstable : (prefixWord ++ tailWord_181356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181356).length < 2 ^ (prefixWord ++ tailWord_181356).sum := by decide
  have hdescent : baseEnd_181356 < baseStart_181356 := by decide
  rcases family_descends (prefixWord ++ tailWord_181356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181390 : List Nat := [4, 1, 1, 3, 2, 1, 3, 3, 3]
def baseStart_181390 : Nat := 118140960795 + 181390 * 2 ^ 59
def prefixEnd_181390 : Nat := 4983230072969 + 3 ^ 40 * 181390 * 2
def baseEnd_181390 : Nat := 41395669297400241995915

theorem tailTrace_181390 : CollatzResearch.WordTrace tailWord_181390 prefixEnd_181390 41395669297400241995915 := by
  unfold tailWord_181390
  simp only [CollatzResearch.WordTrace]
  refine ⟨826979601607810473843703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4410557875241655860499749 826979601607810473843703)
  ·
    refine ⟨1240469402411715710765555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 826979601607810473843703 1240469402411715710765555)
    ·
      refine ⟨1860704103617573566148333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1240469402411715710765555 1860704103617573566148333)
      ·
        refine ⟨697764038856590087305625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1860704103617573566148333 697764038856590087305625)
        ·
          refine ⟨523323029142442565479219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 697764038856590087305625 523323029142442565479219)
          ·
            refine ⟨784984543713663848218829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 523323029142442565479219 784984543713663848218829)
            ·
              refine ⟨294369203892623943082061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 784984543713663848218829 294369203892623943082061)
              ·
                refine ⟨110388451459733978655773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 294369203892623943082061 110388451459733978655773)
                ·
                  refine ⟨41395669297400241995915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110388451459733978655773 41395669297400241995915)
                  ·
                    rfl

theorem cell21_181390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 3, 3].length) (baseStart_181390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_181390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_181390 prefixEnd_181390 := by exact prefixLift 181390
  have htrace : WordTrace (prefixWord ++ tailWord_181390) baseStart_181390 baseEnd_181390 := by
    simpa [prefixWord, tailWord_181390, baseEnd_181390] using wordTrace_append hprefix tailTrace_181390
  have hstable : (prefixWord ++ tailWord_181390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181390).length < 2 ^ (prefixWord ++ tailWord_181390).sum := by decide
  have hdescent : baseEnd_181390 < baseStart_181390 := by decide
  rcases family_descends (prefixWord ++ tailWord_181390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181407 : List Nat := [1, 1, 2, 6, 2, 1, 3, 2, 3]
def baseStart_181407 : Nat := 118140960795 + 181407 * 2 ^ 59
def prefixEnd_181407 : Nat := 4983230072969 + 3 ^ 40 * 181407 * 2
def baseEnd_181407 : Nat := 41399548929011990212547

theorem tailTrace_181407 : CollatzResearch.WordTrace tailWord_181407 prefixEnd_181407 41399548929011990212547 := by
  unfold tailWord_181407
  simp only [CollatzResearch.WordTrace]
  refine ⟨6616456853800895694118475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4410971235867263796078983 6616456853800895694118475)
  ·
    refine ⟨9924685280701343541177713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6616456853800895694118475 9924685280701343541177713)
    ·
      refine ⟨7443513960526007655883285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9924685280701343541177713 7443513960526007655883285)
      ·
        refine ⟨348914716899656608869529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7443513960526007655883285 348914716899656608869529)
        ·
          refine ⟨261686037674742456652147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 348914716899656608869529 261686037674742456652147)
          ·
            refine ⟨392529056512113684978221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261686037674742456652147 392529056512113684978221)
            ·
              refine ⟨147198396192042631866833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 392529056512113684978221 147198396192042631866833)
              ·
                refine ⟨110398797144031973900125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147198396192042631866833 110398797144031973900125)
                ·
                  refine ⟨41399548929011990212547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110398797144031973900125 41399548929011990212547)
                  ·
                    rfl

theorem cell21_181407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 2, 3].length) (baseStart_181407 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_181407 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_181407 prefixEnd_181407 := by exact prefixLift 181407
  have htrace : WordTrace (prefixWord ++ tailWord_181407) baseStart_181407 baseEnd_181407 := by
    simpa [prefixWord, tailWord_181407, baseEnd_181407] using wordTrace_append hprefix tailTrace_181407
  have hstable : (prefixWord ++ tailWord_181407).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181407).length < 2 ^ (prefixWord ++ tailWord_181407).sum := by decide
  have hdescent : baseEnd_181407 < baseStart_181407 := by decide
  rcases family_descends (prefixWord ++ tailWord_181407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181418 : List Nat := [3, 1, 5, 1, 1, 1, 1, 8]
def baseStart_181418 : Nat := 118140960795 + 181418 * 2 ^ 59
def prefixEnd_181418 : Nat := 4983230072969 + 3 ^ 40 * 181418 * 2
def baseEnd_181418 : Nat := 13800686426292805176397

theorem tailTrace_181418 : CollatzResearch.WordTrace tailWord_181418 prefixEnd_181418 13800686426292805176397 := by
  unfold tailWord_181418
  simp only [CollatzResearch.WordTrace]
  refine ⟨1654214514190261143192227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4411238704507363048512605 1654214514190261143192227)
  ·
    refine ⟨2481321771285391714788341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1654214514190261143192227 2481321771285391714788341)
    ·
      refine ⟨232623916058005473261407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2481321771285391714788341 232623916058005473261407)
      ·
        refine ⟨348935874087008209892111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232623916058005473261407 348935874087008209892111)
        ·
          refine ⟨523403811130512314838167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348935874087008209892111 523403811130512314838167)
          ·
            refine ⟨785105716695768472257251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 523403811130512314838167 785105716695768472257251)
            ·
              refine ⟨1177658575043652708385877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 785105716695768472257251 1177658575043652708385877)
              ·
                refine ⟨13800686426292805176397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1177658575043652708385877 13800686426292805176397)
                ·
                  rfl

theorem cell21_181418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 8].length) (baseStart_181418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_181418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_181418 prefixEnd_181418 := by exact prefixLift 181418
  have htrace : WordTrace (prefixWord ++ tailWord_181418) baseStart_181418 baseEnd_181418 := by
    simpa [prefixWord, tailWord_181418, baseEnd_181418] using wordTrace_append hprefix tailTrace_181418
  have hstable : (prefixWord ++ tailWord_181418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181418).length < 2 ^ (prefixWord ++ tailWord_181418).sum := by decide
  have hdescent : baseEnd_181418 < baseStart_181418 := by decide
  rcases family_descends (prefixWord ++ tailWord_181418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181491 : List Nat := [1, 1, 1, 2, 2, 5, 1, 1, 7]
def baseStart_181491 : Nat := 118140960795 + 181491 * 2 ^ 59
def prefixEnd_181491 : Nat := 4983230072969 + 3 ^ 40 * 181491 * 2
def baseEnd_181491 : Nat := 41418718873446510812375

theorem tailTrace_181491 : CollatzResearch.WordTrace tailWord_181491 prefixEnd_181491 41418718873446510812375 := by
  unfold tailWord_181491
  simp only [CollatzResearch.WordTrace]
  refine ⟨6619520585496578040176327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4413013723664385360117551 6619520585496578040176327)
  ·
    refine ⟨9929280878244867060264491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6619520585496578040176327 9929280878244867060264491)
    ·
      refine ⟨14893921317367300590396737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9929280878244867060264491 14893921317367300590396737)
      ·
        refine ⟨11170440988025475442797553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14893921317367300590396737 11170440988025475442797553)
        ·
          refine ⟨8377830741019106582098165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11170440988025475442797553 8377830741019106582098165)
          ·
            refine ⟨785421631970541242071703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8377830741019106582098165 785421631970541242071703)
            ·
              refine ⟨1178132447955811863107555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 785421631970541242071703 1178132447955811863107555)
              ·
                refine ⟨1767198671933717794661333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1178132447955811863107555 1767198671933717794661333)
                ·
                  refine ⟨41418718873446510812375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1767198671933717794661333 41418718873446510812375)
                  ·
                    rfl

theorem cell21_181491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 7].length) (baseStart_181491 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_181491 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_181491 prefixEnd_181491 := by exact prefixLift 181491
  have htrace : WordTrace (prefixWord ++ tailWord_181491) baseStart_181491 baseEnd_181491 := by
    simpa [prefixWord, tailWord_181491, baseEnd_181491] using wordTrace_append hprefix tailTrace_181491
  have hstable : (prefixWord ++ tailWord_181491).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181491).length < 2 ^ (prefixWord ++ tailWord_181491).sum := by decide
  have hdescent : baseEnd_181491 < baseStart_181491 := by decide
  rcases family_descends (prefixWord ++ tailWord_181491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
