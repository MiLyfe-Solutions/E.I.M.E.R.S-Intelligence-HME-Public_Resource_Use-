import V185TrunkScan23Chunk0451

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2673885 : List Nat := [1, 4, 3, 2, 2, 1, 2, 2, 1, 5]
def baseStart_2673885 : Nat := 118140960795 + 2673885 * 2 ^ 59
def prefixEnd_2673885 : Nat := 4983230072969 + 3 ^ 40 * 2673885 * 2
def baseEnd_2673885 : Nat := 457662739949125382113511

theorem tailTrace_2673885 : CollatzResearch.WordTrace tailWord_2673885 prefixEnd_2673885 457662739949125382113511 := by
  unfold tailWord_2673885
  simp only [CollatzResearch.WordTrace]
  refine ⟨97524597917978783046295109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65016398611985855364196739 97524597917978783046295109)
  ·
    refine ⟨18285862109621021821180333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97524597917978783046295109 18285862109621021821180333)
    ·
      refine ⟨6857198291107883182942625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18285862109621021821180333 6857198291107883182942625)
      ·
        refine ⟨5142898718330912387206969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6857198291107883182942625 5142898718330912387206969)
        ·
          refine ⟨3857174038748184290405227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5142898718330912387206969 3857174038748184290405227)
          ·
            refine ⟨5785761058122276435607841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3857174038748184290405227 5785761058122276435607841)
            ·
              refine ⟨4339320793591707326705881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5785761058122276435607841 4339320793591707326705881)
              ·
                refine ⟨3254490595193780495029411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4339320793591707326705881 3254490595193780495029411)
                ·
                  refine ⟨4881735892790670742544117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3254490595193780495029411 4881735892790670742544117)
                  ·
                    refine ⟨457662739949125382113511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4881735892790670742544117 457662739949125382113511)
                    ·
                      rfl

theorem cell23_2673885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_2673885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2673885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2673885 prefixEnd_2673885 := by exact prefixLift 2673885
  have htrace : WordTrace (prefixWord ++ tailWord_2673885) baseStart_2673885 baseEnd_2673885 := by
    simpa [prefixWord, tailWord_2673885, baseEnd_2673885] using wordTrace_append hprefix tailTrace_2673885
  have hstable : (prefixWord ++ tailWord_2673885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673885).length < 2 ^ (prefixWord ++ tailWord_2673885).sum := by decide
  have hdescent : baseEnd_2673885 < baseStart_2673885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673888 : List Nat := [2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 4]
def baseStart_2673888 : Nat := 118140960795 + 2673888 * 2 ^ 59
def prefixEnd_2673888 : Nat := 4983230072969 + 3 ^ 40 * 2673888 * 2
def baseEnd_2673888 : Nat := 1372989760289339634603019

theorem tailTrace_2673888 : CollatzResearch.WordTrace tailWord_2673888 prefixEnd_2673888 1372989760289339634603019 := by
  unfold tailWord_2673888
  simp only [CollatzResearch.WordTrace]
  refine ⟨48762353668483957279327159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65016471557978609705769545 48762353668483957279327159)
  ·
    refine ⟨73143530502725935918990739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48762353668483957279327159 73143530502725935918990739)
    ·
      refine ⟨109715295754088903878486109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73143530502725935918990739 109715295754088903878486109)
      ·
        refine ⟨41143235907783338954432291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109715295754088903878486109 41143235907783338954432291)
        ·
          refine ⟨61714853861675008431648437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41143235907783338954432291 61714853861675008431648437)
          ·
            refine ⟨5785767549532032040467041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61714853861675008431648437 5785767549532032040467041)
            ·
              refine ⟨4339325662149024030350281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5785767549532032040467041 4339325662149024030350281)
              ·
                refine ⟨3254494246611768022762711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4339325662149024030350281 3254494246611768022762711)
                ·
                  refine ⟨4881741369917652034144067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3254494246611768022762711 4881741369917652034144067)
                  ·
                    refine ⟨7322612054876478051216101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4881741369917652034144067 7322612054876478051216101)
                    ·
                      refine ⟨1372989760289339634603019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7322612054876478051216101 1372989760289339634603019)
                      ·
                        rfl

theorem cell23_2673888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 4].length) (baseStart_2673888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2673888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2673888 prefixEnd_2673888 := by exact prefixLift 2673888
  have htrace : WordTrace (prefixWord ++ tailWord_2673888) baseStart_2673888 baseEnd_2673888 := by
    simpa [prefixWord, tailWord_2673888, baseEnd_2673888] using wordTrace_append hprefix tailTrace_2673888
  have hstable : (prefixWord ++ tailWord_2673888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673888).length < 2 ^ (prefixWord ++ tailWord_2673888).sum := by decide
  have hdescent : baseEnd_2673888 < baseStart_2673888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673972 : List Nat := [2, 5, 1, 1, 1, 1, 4, 2, 2, 1, 3]
def baseStart_2673972 : Nat := 118140960795 + 2673972 * 2 ^ 59
def prefixEnd_2673972 : Nat := 4983230072969 + 3 ^ 40 * 2673972 * 2
def baseEnd_2673972 : Nat := 1373032892664317305952633

theorem tailTrace_2673972 : CollatzResearch.WordTrace tailWord_2673972 prefixEnd_2673972 1373032892664317305952633 := by
  unfold tailWord_2673972
  simp only [CollatzResearch.WordTrace]
  refine ⟨48763885534331798452356085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65018514045775731269808113 48763885534331798452356085)
  ·
    refine ⟨4571614268843606104908383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48763885534331798452356085 4571614268843606104908383)
    ·
      refine ⟨6857421403265409157362575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4571614268843606104908383 6857421403265409157362575)
      ·
        refine ⟨10286132104898113736043863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6857421403265409157362575 10286132104898113736043863)
        ·
          refine ⟨15429198157347170604065795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10286132104898113736043863 15429198157347170604065795)
          ·
            refine ⟨23143797236020755906098693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15429198157347170604065795 23143797236020755906098693)
            ·
              refine ⟨4339461981753891732393505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23143797236020755906098693 4339461981753891732393505)
              ·
                refine ⟨3254596486315418799295129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4339461981753891732393505 3254596486315418799295129)
                ·
                  refine ⟨2440947364736564099471347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3254596486315418799295129 2440947364736564099471347)
                  ·
                    refine ⟨3661421047104846149207021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2440947364736564099471347 3661421047104846149207021)
                    ·
                      refine ⟨1373032892664317305952633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3661421047104846149207021 1373032892664317305952633)
                      ·
                        rfl

theorem cell23_2673972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_2673972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2673972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2673972 prefixEnd_2673972 := by exact prefixLift 2673972
  have htrace : WordTrace (prefixWord ++ tailWord_2673972) baseStart_2673972 baseEnd_2673972 := by
    simpa [prefixWord, tailWord_2673972, baseEnd_2673972] using wordTrace_append hprefix tailTrace_2673972
  have hstable : (prefixWord ++ tailWord_2673972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673972).length < 2 ^ (prefixWord ++ tailWord_2673972).sum := by decide
  have hdescent : baseEnd_2673972 < baseStart_2673972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673978 : List Nat := [3, 1, 1, 1, 4, 1, 1, 2, 3, 4, 2]
def baseStart_2673978 : Nat := 118140960795 + 2673978 * 2 ^ 59
def prefixEnd_2673978 : Nat := 4983230072969 + 3 ^ 40 * 2673978 * 2
def baseEnd_2673978 : Nat := 1373035973548244282477605

theorem tailTrace_2673978 : CollatzResearch.WordTrace tailWord_2673978 prefixEnd_2673978 1373035973548244282477605 := by
  unfold tailWord_2673978
  simp only [CollatzResearch.WordTrace]
  refine ⟨24381997476660464982357647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65018659937761239952953725 24381997476660464982357647)
  ·
    refine ⟨36572996214990697473536471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24381997476660464982357647 36572996214990697473536471)
    ·
      refine ⟨54859494322486046210304707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36572996214990697473536471 54859494322486046210304707)
      ·
        refine ⟨82289241483729069315457061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54859494322486046210304707 82289241483729069315457061)
        ·
          refine ⟨15429232778199200496648199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82289241483729069315457061 15429232778199200496648199)
          ·
            refine ⟨23143849167298800744972299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15429232778199200496648199 23143849167298800744972299)
            ·
              refine ⟨34715773750948201117458449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23143849167298800744972299 34715773750948201117458449)
              ·
                refine ⟨26036830313211150838093837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34715773750948201117458449 26036830313211150838093837)
                ·
                  refine ⟨9763811367454181564285189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26036830313211150838093837 9763811367454181564285189)
                  ·
                    refine ⟨1830714631397659043303473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9763811367454181564285189 1830714631397659043303473)
                    ·
                      refine ⟨1373035973548244282477605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1830714631397659043303473 1373035973548244282477605)
                      ·
                        rfl

theorem cell23_2673978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 3, 4, 2].length) (baseStart_2673978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2673978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2673978 prefixEnd_2673978 := by exact prefixLift 2673978
  have htrace : WordTrace (prefixWord ++ tailWord_2673978) baseStart_2673978 baseEnd_2673978 := by
    simpa [prefixWord, tailWord_2673978, baseEnd_2673978] using wordTrace_append hprefix tailTrace_2673978
  have hstable : (prefixWord ++ tailWord_2673978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673978).length < 2 ^ (prefixWord ++ tailWord_2673978).sum := by decide
  have hdescent : baseEnd_2673978 < baseStart_2673978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673988 : List Nat := [2, 3, 4, 1, 1, 1, 1, 1, 1, 8]
def baseStart_2673988 : Nat := 118140960795 + 2673988 * 2 ^ 59
def prefixEnd_2673988 : Nat := 4983230072969 + 3 ^ 40 * 2673988 * 2
def baseEnd_2673988 : Nat := 457680369451596414450853

theorem tailTrace_2673988 : CollatzResearch.WordTrace tailWord_2673988 prefixEnd_2673988 457680369451596414450853 := by
  unfold tailWord_2673988
  simp only [CollatzResearch.WordTrace]
  refine ⟨48764177318302815818647309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65018903091070421091529745 48764177318302815818647309)
  ·
    refine ⟨18286566494363555931992741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48764177318302815818647309 18286566494363555931992741)
    ·
      refine ⟨3428731217693166737248639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18286566494363555931992741 3428731217693166737248639)
      ·
        refine ⟨5143096826539750105872959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3428731217693166737248639 5143096826539750105872959)
        ·
          refine ⟨7714645239809625158809439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5143096826539750105872959 7714645239809625158809439)
          ·
            refine ⟨11571967859714437738214159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7714645239809625158809439 11571967859714437738214159)
            ·
              refine ⟨17357951789571656607321239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11571967859714437738214159 17357951789571656607321239)
              ·
                refine ⟨26036927684357484910981859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17357951789571656607321239 26036927684357484910981859)
                ·
                  refine ⟨39055391526536227366472789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26036927684357484910981859 39055391526536227366472789)
                  ·
                    refine ⟨457680369451596414450853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 39055391526536227366472789 457680369451596414450853)
                    ·
                      rfl

theorem cell23_2673988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_2673988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2673988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2673988 prefixEnd_2673988 := by exact prefixLift 2673988
  have htrace : WordTrace (prefixWord ++ tailWord_2673988) baseStart_2673988 baseEnd_2673988 := by
    simpa [prefixWord, tailWord_2673988, baseEnd_2673988] using wordTrace_append hprefix tailTrace_2673988
  have hstable : (prefixWord ++ tailWord_2673988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673988).length < 2 ^ (prefixWord ++ tailWord_2673988).sum := by decide
  have hdescent : baseEnd_2673988 < baseStart_2673988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673991 : List Nat := [1, 1, 4, 1, 2, 3, 1, 1, 1, 4, 4]
def baseStart_2673991 : Nat := 118140960795 + 2673991 * 2 ^ 59
def prefixEnd_2673991 : Nat := 4983230072969 + 3 ^ 40 * 2673991 * 2
def baseEnd_2673991 : Nat := 1373042648796752731615045

theorem tailTrace_2673991 : CollatzResearch.WordTrace tailWord_2673991 prefixEnd_2673991 1373042648796752731615045 := by
  unfold tailWord_2673991
  simp only [CollatzResearch.WordTrace]
  refine ⟨97528464055594763149653827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65018976037063175433102551 97528464055594763149653827)
  ·
    refine ⟨146292696083392144724480741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97528464055594763149653827 146292696083392144724480741)
    ·
      refine ⟨27429880515636027135840139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146292696083392144724480741 27429880515636027135840139)
      ·
        refine ⟨41144820773454040703760209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27429880515636027135840139 41144820773454040703760209)
        ·
          refine ⟨30858615580090530527820157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41144820773454040703760209 30858615580090530527820157)
          ·
            refine ⟨11571980842533948947932559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30858615580090530527820157 11571980842533948947932559)
            ·
              refine ⟨17357971263800923421898839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11571980842533948947932559 17357971263800923421898839)
              ·
                refine ⟨26036956895701385132848259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17357971263800923421898839 26036956895701385132848259)
                ·
                  refine ⟨39055435343552077699272389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26036956895701385132848259 39055435343552077699272389)
                  ·
                    refine ⟨7322894126916014568613573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39055435343552077699272389 7322894126916014568613573)
                    ·
                      refine ⟨1373042648796752731615045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7322894126916014568613573 1373042648796752731615045)
                      ·
                        rfl

theorem cell23_2673991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_2673991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2673991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2673991 prefixEnd_2673991 := by exact prefixLift 2673991
  have htrace : WordTrace (prefixWord ++ tailWord_2673991) baseStart_2673991 baseEnd_2673991 := by
    simpa [prefixWord, tailWord_2673991, baseEnd_2673991] using wordTrace_append hprefix tailTrace_2673991
  have hstable : (prefixWord ++ tailWord_2673991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673991).length < 2 ^ (prefixWord ++ tailWord_2673991).sum := by decide
  have hdescent : baseEnd_2673991 < baseStart_2673991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674001 : List Nat := [1, 2, 2, 1, 4, 1, 3, 2, 7]
def baseStart_2674001 : Nat := 118140960795 + 2674001 * 2 ^ 59
def prefixEnd_2674001 : Nat := 4983230072969 + 3 ^ 40 * 2674001 * 2
def baseEnd_2674001 : Nat := 152560864844810854721111

theorem tailTrace_2674001 : CollatzResearch.WordTrace tailWord_2674001 prefixEnd_2674001 152560864844810854721111 := by
  unfold tailWord_2674001
  simp only [CollatzResearch.WordTrace]
  refine ⟨97528828785558534857517857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65019219190372356571678571 97528828785558534857517857)
  ·
    refine ⟨73146621589168901143138393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97528828785558534857517857 73146621589168901143138393)
    ·
      refine ⟨54859966191876675857353795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73146621589168901143138393 54859966191876675857353795)
      ·
        refine ⟨82289949287815013786030693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54859966191876675857353795 82289949287815013786030693)
        ·
          refine ⟨15429365491465315084880755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82289949287815013786030693 15429365491465315084880755)
          ·
            refine ⟨23144048237197972627321133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15429365491465315084880755 23144048237197972627321133)
            ·
              refine ⟨8679018088949239735245425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23144048237197972627321133 8679018088949239735245425)
              ·
                refine ⟨6509263566711929801434069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8679018088949239735245425 6509263566711929801434069)
                ·
                  refine ⟨152560864844810854721111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6509263566711929801434069 152560864844810854721111)
                  ·
                    rfl

theorem cell23_2674001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 7].length) (baseStart_2674001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674001 prefixEnd_2674001 := by exact prefixLift 2674001
  have htrace : WordTrace (prefixWord ++ tailWord_2674001) baseStart_2674001 baseEnd_2674001 := by
    simpa [prefixWord, tailWord_2674001, baseEnd_2674001] using wordTrace_append hprefix tailTrace_2674001
  have hstable : (prefixWord ++ tailWord_2674001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674001).length < 2 ^ (prefixWord ++ tailWord_2674001).sum := by decide
  have hdescent : baseEnd_2674001 < baseStart_2674001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674028 : List Nat := [2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 3]
def baseStart_2674028 : Nat := 118140960795 + 2674028 * 2 ^ 59
def prefixEnd_2674028 : Nat := 4983230072969 + 3 ^ 40 * 2674028 * 2
def baseEnd_2674028 : Nat := 1373061647580969086852375

theorem tailTrace_2674028 : CollatzResearch.WordTrace tailWord_2674028 prefixEnd_2674028 1373061647580969086852375 := by
  unfold tailWord_2674028
  simp only [CollatzResearch.WordTrace]
  refine ⟨48764906778230359234375369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65019875704307145645833825 48764906778230359234375369)
  ·
    refine ⟨36573680083672769425781527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48764906778230359234375369 36573680083672769425781527)
    ·
      refine ⟨54860520125509154138672291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36573680083672769425781527 54860520125509154138672291)
      ·
        refine ⟨82290780188263731208008437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54860520125509154138672291 82290780188263731208008437)
        ·
          refine ⟨7714760642649724800750791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82290780188263731208008437 7714760642649724800750791)
          ·
            refine ⟨11572140963974587201126187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7714760642649724800750791 11572140963974587201126187)
            ·
              refine ⟨17358211445961880801689281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11572140963974587201126187 17358211445961880801689281)
              ·
                refine ⟨13018658584471410601266961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17358211445961880801689281 13018658584471410601266961)
                ·
                  refine ⟨9763993938353557950950221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13018658584471410601266961 9763993938353557950950221)
                  ·
                    refine ⟨3661497726882584231606333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9763993938353557950950221 3661497726882584231606333)
                    ·
                      refine ⟨1373061647580969086852375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3661497726882584231606333 1373061647580969086852375)
                      ·
                        rfl

theorem cell23_2674028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 3].length) (baseStart_2674028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674028 prefixEnd_2674028 := by exact prefixLift 2674028
  have htrace : WordTrace (prefixWord ++ tailWord_2674028) baseStart_2674028 baseEnd_2674028 := by
    simpa [prefixWord, tailWord_2674028, baseEnd_2674028] using wordTrace_append hprefix tailTrace_2674028
  have hstable : (prefixWord ++ tailWord_2674028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674028).length < 2 ^ (prefixWord ++ tailWord_2674028).sum := by decide
  have hdescent : baseEnd_2674028 < baseStart_2674028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674029 : List Nat := [1, 5, 1, 1, 1, 5, 1, 2, 2, 2, 2]
def baseStart_2674029 : Nat := 118140960795 + 2674029 * 2 ^ 59
def prefixEnd_2674029 : Nat := 4983230072969 + 3 ^ 40 * 2674029 * 2
def baseEnd_2674029 : Nat := 1373062161061623582939871

theorem tailTrace_2674029 : CollatzResearch.WordTrace tailWord_2674029 prefixEnd_2674029 1373062161061623582939871 := by
  unfold tailWord_2674029
  simp only [CollatzResearch.WordTrace]
  refine ⟨97529850029457095639537141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65019900019638063759691427 97529850029457095639537141)
  ·
    refine ⟨9143423440261602716206607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97529850029457095639537141 9143423440261602716206607)
    ·
      refine ⟨13715135160392404074309911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9143423440261602716206607 13715135160392404074309911)
      ·
        refine ⟨20572702740588606111464867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13715135160392404074309911 20572702740588606111464867)
        ·
          refine ⟨30859054110882909167197301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20572702740588606111464867 30859054110882909167197301)
          ·
            refine ⟨2893036322895272734424747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30859054110882909167197301 2893036322895272734424747)
            ·
              refine ⟨4339554484342909101637121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2893036322895272734424747 4339554484342909101637121)
              ·
                refine ⟨3254665863257181826227841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4339554484342909101637121 3254665863257181826227841)
                ·
                  refine ⟨2440999397442886369670881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3254665863257181826227841 2440999397442886369670881)
                  ·
                    refine ⟨1830749548082164777253161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2440999397442886369670881 1830749548082164777253161)
                    ·
                      refine ⟨1373062161061623582939871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1830749548082164777253161 1373062161061623582939871)
                      ·
                        rfl

theorem cell23_2674029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 2, 2, 2, 2].length) (baseStart_2674029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674029 prefixEnd_2674029 := by exact prefixLift 2674029
  have htrace : WordTrace (prefixWord ++ tailWord_2674029) baseStart_2674029 baseEnd_2674029 := by
    simpa [prefixWord, tailWord_2674029, baseEnd_2674029] using wordTrace_append hprefix tailTrace_2674029
  have hstable : (prefixWord ++ tailWord_2674029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674029).length < 2 ^ (prefixWord ++ tailWord_2674029).sum := by decide
  have hdescent : baseEnd_2674029 < baseStart_2674029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674031 : List Nat := [1, 1, 2, 1, 3, 1, 4, 1, 4, 5]
def baseStart_2674031 : Nat := 118140960795 + 2674031 * 2 ^ 59
def prefixEnd_2674031 : Nat := 4983230072969 + 3 ^ 40 * 2674031 * 2
def baseEnd_2674031 : Nat := 457687729340977525038287

theorem tailTrace_2674031 : CollatzResearch.WordTrace tailWord_2674031 prefixEnd_2674031 457687729340977525038287 := by
  unfold tailWord_2674031
  simp only [CollatzResearch.WordTrace]
  refine ⟨97529922975449849981109947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65019948650299899987406631 97529922975449849981109947)
  ·
    refine ⟨146294884463174774971664921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97529922975449849981109947 146294884463174774971664921)
    ·
      refine ⟨109721163347381081228748691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146294884463174774971664921 109721163347381081228748691)
      ·
        refine ⟨164581745021071621843123037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109721163347381081228748691 164581745021071621843123037)
        ·
          refine ⟨61718154382901858191171139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164581745021071621843123037 61718154382901858191171139)
          ·
            refine ⟨92577231574352787286756709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61718154382901858191171139 92577231574352787286756709)
            ·
              refine ⟨17358230920191147616266883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92577231574352787286756709 17358230920191147616266883)
              ·
                refine ⟨26037346380286721424400325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17358230920191147616266883 26037346380286721424400325)
                ·
                  refine ⟨4882002446303760267075061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26037346380286721424400325 4882002446303760267075061)
                  ·
                    refine ⟨457687729340977525038287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4882002446303760267075061 457687729340977525038287)
                    ·
                      rfl

theorem cell23_2674031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 4, 5].length) (baseStart_2674031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674031 prefixEnd_2674031 := by exact prefixLift 2674031
  have htrace : WordTrace (prefixWord ++ tailWord_2674031) baseStart_2674031 baseEnd_2674031 := by
    simpa [prefixWord, tailWord_2674031, baseEnd_2674031] using wordTrace_append hprefix tailTrace_2674031
  have hstable : (prefixWord ++ tailWord_2674031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674031).length < 2 ^ (prefixWord ++ tailWord_2674031).sum := by decide
  have hdescent : baseEnd_2674031 < baseStart_2674031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674041 : List Nat := [1, 2, 1, 3, 2, 1, 2, 3, 1, 2, 5]
def baseStart_2674041 : Nat := 118140960795 + 2674041 * 2 ^ 59
def prefixEnd_2674041 : Nat := 4983230072969 + 3 ^ 40 * 2674041 * 2
def baseEnd_2674041 : Nat := 1373068322829477535989815

theorem tailTrace_2674041 : CollatzResearch.WordTrace tailWord_2674041 prefixEnd_2674041 1373068322829477535989815 := by
  unfold tailWord_2674041
  simp only [CollatzResearch.WordTrace]
  refine ⟨97530287705413621688973977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65020191803609081125982651 97530287705413621688973977)
  ·
    refine ⟨73147715779060216266730483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97530287705413621688973977 73147715779060216266730483)
    ·
      refine ⟨109721573668590324400095725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73147715779060216266730483 109721573668590324400095725)
      ·
        refine ⟨41145590125721371650035897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109721573668590324400095725 41145590125721371650035897)
        ·
          refine ⟨30859192594291028737526923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41145590125721371650035897 30859192594291028737526923)
          ·
            refine ⟨46288788891436543106290385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30859192594291028737526923 46288788891436543106290385)
            ·
              refine ⟨34716591668577407329717789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46288788891436543106290385 34716591668577407329717789)
              ·
                refine ⟨13018721875716527748644171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34716591668577407329717789 13018721875716527748644171)
                ·
                  refine ⟨19528082813574791622966257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13018721875716527748644171 19528082813574791622966257)
                  ·
                    refine ⟨14646062110181093717224693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19528082813574791622966257 14646062110181093717224693)
                    ·
                      refine ⟨1373068322829477535989815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14646062110181093717224693 1373068322829477535989815)
                      ·
                        rfl

theorem cell23_2674041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_2674041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674041 prefixEnd_2674041 := by exact prefixLift 2674041
  have htrace : WordTrace (prefixWord ++ tailWord_2674041) baseStart_2674041 baseEnd_2674041 := by
    simpa [prefixWord, tailWord_2674041, baseEnd_2674041] using wordTrace_append hprefix tailTrace_2674041
  have hstable : (prefixWord ++ tailWord_2674041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674041).length < 2 ^ (prefixWord ++ tailWord_2674041).sum := by decide
  have hdescent : baseEnd_2674041 < baseStart_2674041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674046 : List Nat := [4, 2, 3, 2, 1, 2, 1, 1, 1, 4, 2]
def baseStart_2674046 : Nat := 118140960795 + 2674046 * 2 ^ 59
def prefixEnd_2674046 : Nat := 4983230072969 + 3 ^ 40 * 2674046 * 2
def baseEnd_2674046 : Nat := 1373070890232750016427293

theorem tailTrace_2674046 : CollatzResearch.WordTrace tailWord_2674046 prefixEnd_2674046 1373070890232750016427293 := by
  unfold tailWord_2674046
  simp only [CollatzResearch.WordTrace]
  refine ⟨12191308758799438442863249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65020313380263671695270661 12191308758799438442863249)
  ·
    refine ⟨9143481569099578832147437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12191308758799438442863249 9143481569099578832147437)
    ·
      refine ⟨3428805588412342062055289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9143481569099578832147437 3428805588412342062055289)
      ·
        refine ⟨2571604191309256546541467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3428805588412342062055289 2571604191309256546541467)
        ·
          refine ⟨3857406286963884819812201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2571604191309256546541467 3857406286963884819812201)
          ·
            refine ⟨2893054715222913614859151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3857406286963884819812201 2893054715222913614859151)
            ·
              refine ⟨4339582072834370422288727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2893054715222913614859151 4339582072834370422288727)
              ·
                refine ⟨6509373109251555633433091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4339582072834370422288727 6509373109251555633433091)
                ·
                  refine ⟨9764059663877333450149637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6509373109251555633433091 9764059663877333450149637)
                  ·
                    refine ⟨1830761186977000021903057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9764059663877333450149637 1830761186977000021903057)
                    ·
                      refine ⟨1373070890232750016427293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1830761186977000021903057 1373070890232750016427293)
                      ·
                        rfl

theorem cell23_2674046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_2674046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674046 prefixEnd_2674046 := by exact prefixLift 2674046
  have htrace : WordTrace (prefixWord ++ tailWord_2674046) baseStart_2674046 baseEnd_2674046 := by
    simpa [prefixWord, tailWord_2674046, baseEnd_2674046] using wordTrace_append hprefix tailTrace_2674046
  have hstable : (prefixWord ++ tailWord_2674046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674046).length < 2 ^ (prefixWord ++ tailWord_2674046).sum := by decide
  have hdescent : baseEnd_2674046 < baseStart_2674046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674071 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 5]
def baseStart_2674071 : Nat := 118140960795 + 2674071 * 2 ^ 59
def prefixEnd_2674071 : Nat := 4983230072969 + 3 ^ 40 * 2674071 * 2
def baseEnd_2674071 : Nat := 1373083727249112418614677

theorem tailTrace_2674071 : CollatzResearch.WordTrace tailWord_2674071 prefixEnd_2674071 1373083727249112418614677 := by
  unfold tailWord_2674071
  simp only [CollatzResearch.WordTrace]
  refine ⟨97531381895304936812566067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65020921263536624541710711 97531381895304936812566067)
  ·
    refine ⟨146297072842957405218849101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97531381895304936812566067 146297072842957405218849101)
    ·
      refine ⟨54861402316109026957068413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146297072842957405218849101 54861402316109026957068413)
      ·
        refine ⟨20573025868540885108900655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54861402316109026957068413 20573025868540885108900655)
        ·
          refine ⟨30859538802811327663350983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20573025868540885108900655 30859538802811327663350983)
          ·
            refine ⟨46289308204216991495026475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30859538802811327663350983 46289308204216991495026475)
            ·
              refine ⟨69433962306325487242539713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46289308204216991495026475 69433962306325487242539713)
              ·
                refine ⟨52075471729744115431904785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69433962306325487242539713 52075471729744115431904785)
                ·
                  refine ⟨39056603797308086573928589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52075471729744115431904785 39056603797308086573928589)
                  ·
                    refine ⟨14646226423990532465223221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39056603797308086573928589 14646226423990532465223221)
                    ·
                      refine ⟨1373083727249112418614677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14646226423990532465223221 1373083727249112418614677)
                      ·
                        rfl

theorem cell23_2674071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_2674071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674071 prefixEnd_2674071 := by exact prefixLift 2674071
  have htrace : WordTrace (prefixWord ++ tailWord_2674071) baseStart_2674071 baseEnd_2674071 := by
    simpa [prefixWord, tailWord_2674071, baseEnd_2674071] using wordTrace_append hprefix tailTrace_2674071
  have hstable : (prefixWord ++ tailWord_2674071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674071).length < 2 ^ (prefixWord ++ tailWord_2674071).sum := by decide
  have hdescent : baseEnd_2674071 < baseStart_2674071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674095 : List Nat := [1, 1, 2, 1, 2, 2, 1, 8, 1, 4]
def baseStart_2674095 : Nat := 118140960795 + 2674095 * 2 ^ 59
def prefixEnd_2674095 : Nat := 4983230072969 + 3 ^ 40 * 2674095 * 2
def baseEnd_2674095 : Nat := 457698683594940108238189

theorem tailTrace_2674095 : CollatzResearch.WordTrace tailWord_2674095 prefixEnd_2674095 457698683594940108238189 := by
  unfold tailWord_2674095
  simp only [CollatzResearch.WordTrace]
  refine ⟨97532257247217988911439739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65021504831478659274293159 97532257247217988911439739)
  ·
    refine ⟨146298385870826983367159609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97532257247217988911439739 146298385870826983367159609)
    ·
      refine ⟨109723789403120237525369707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146298385870826983367159609 109723789403120237525369707)
      ·
        refine ⟨164585684104680356288054561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109723789403120237525369707 164585684104680356288054561)
        ·
          refine ⟨123439263078510267216040921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164585684104680356288054561 123439263078510267216040921)
          ·
            refine ⟨92579447308882700412030691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123439263078510267216040921 92579447308882700412030691)
            ·
              refine ⟨138869170963324050618046037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92579447308882700412030691 138869170963324050618046037)
              ·
                refine ⟨1627373097226453718180227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 138869170963324050618046037 1627373097226453718180227)
                ·
                  refine ⟨2441059645839680577270341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1627373097226453718180227 2441059645839680577270341)
                  ·
                    refine ⟨457698683594940108238189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2441059645839680577270341 457698683594940108238189)
                    ·
                      rfl

theorem cell23_2674095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 8, 1, 4].length) (baseStart_2674095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674095 prefixEnd_2674095 := by exact prefixLift 2674095
  have htrace : WordTrace (prefixWord ++ tailWord_2674095) baseStart_2674095 baseEnd_2674095 := by
    simpa [prefixWord, tailWord_2674095, baseEnd_2674095] using wordTrace_append hprefix tailTrace_2674095
  have hstable : (prefixWord ++ tailWord_2674095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674095).length < 2 ^ (prefixWord ++ tailWord_2674095).sum := by decide
  have hdescent : baseEnd_2674095 < baseStart_2674095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674111 : List Nat := [1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 6]
def baseStart_2674111 : Nat := 118140960795 + 2674111 * 2 ^ 59
def prefixEnd_2674111 : Nat := 4983230072969 + 3 ^ 40 * 2674111 * 2
def baseEnd_2674111 : Nat := 1373104266475292262114493

theorem tailTrace_2674111 : CollatzResearch.WordTrace tailWord_2674111 prefixEnd_2674111 1373104266475292262114493 := by
  unfold tailWord_2674111
  simp only [CollatzResearch.WordTrace]
  refine ⟨97532840815160023644022187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65021893876773349096014791 97532840815160023644022187)
  ·
    refine ⟨146299261222740035466033281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97532840815160023644022187 146299261222740035466033281)
    ·
      refine ⟨109724445917055026599524961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146299261222740035466033281 109724445917055026599524961)
      ·
        refine ⟨82293334437791269949643721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109724445917055026599524961 82293334437791269949643721)
        ·
          refine ⟨61720000828343452462232791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82293334437791269949643721 61720000828343452462232791)
          ·
            refine ⟨92580001242515178693349187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61720000828343452462232791 92580001242515178693349187)
            ·
              refine ⟨138870001863772768040023781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92580001242515178693349187 138870001863772768040023781)
              ·
                refine ⟨26038125349457394007504459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 138870001863772768040023781 26038125349457394007504459)
                ·
                  refine ⟨39057188024186091011256689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26038125349457394007504459 39057188024186091011256689)
                  ·
                    refine ⟨29292891018139568258442517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39057188024186091011256689 29292891018139568258442517)
                    ·
                      refine ⟨1373104266475292262114493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29292891018139568258442517 1373104266475292262114493)
                      ·
                        rfl

theorem cell23_2674111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_2674111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674111 prefixEnd_2674111 := by exact prefixLift 2674111
  have htrace : WordTrace (prefixWord ++ tailWord_2674111) baseStart_2674111 baseEnd_2674111 := by
    simpa [prefixWord, tailWord_2674111, baseEnd_2674111] using wordTrace_append hprefix tailTrace_2674111
  have hstable : (prefixWord ++ tailWord_2674111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674111).length < 2 ^ (prefixWord ++ tailWord_2674111).sum := by decide
  have hdescent : baseEnd_2674111 < baseStart_2674111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674168 : List Nat := [2, 1, 2, 1, 1, 5, 1, 3, 1, 6]
def baseStart_2674168 : Nat := 118140960795 + 2674168 * 2 ^ 59
def prefixEnd_2674168 : Nat := 4983230072969 + 3 ^ 40 * 2674168 * 2
def baseEnd_2674168 : Nat := 457711178290866179700577

theorem tailTrace_2674168 : CollatzResearch.WordTrace tailWord_2674168 prefixEnd_2674168 457711178290866179700577 := by
  unfold tailWord_2674168
  simp only [CollatzResearch.WordTrace]
  refine ⟨48767459887976761189423579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65023279850635681585898105 48767459887976761189423579)
  ·
    refine ⟨73151189831965141784135369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48767459887976761189423579 73151189831965141784135369)
    ·
      refine ⟨54863392373973856338101527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73151189831965141784135369 54863392373973856338101527)
      ·
        refine ⟨82295088560960784507152291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54863392373973856338101527 82295088560960784507152291)
        ·
          refine ⟨123442632841441176760728437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82295088560960784507152291 123442632841441176760728437)
          ·
            refine ⟨11572746828885110321318291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 123442632841441176760728437 11572746828885110321318291)
            ·
              refine ⟨17359120243327665481977437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11572746828885110321318291 17359120243327665481977437)
              ·
                refine ⟨6509670091247874555741539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17359120243327665481977437 6509670091247874555741539)
                ·
                  refine ⟨9764505136871811833612309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6509670091247874555741539 9764505136871811833612309)
                  ·
                    refine ⟨457711178290866179700577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9764505136871811833612309 457711178290866179700577)
                    ·
                      rfl

theorem cell23_2674168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 1, 6].length) (baseStart_2674168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674168 prefixEnd_2674168 := by exact prefixLift 2674168
  have htrace : WordTrace (prefixWord ++ tailWord_2674168) baseStart_2674168 baseEnd_2674168 := by
    simpa [prefixWord, tailWord_2674168, baseEnd_2674168] using wordTrace_append hprefix tailTrace_2674168
  have hstable : (prefixWord ++ tailWord_2674168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674168).length < 2 ^ (prefixWord ++ tailWord_2674168).sum := by decide
  have hdescent : baseEnd_2674168 < baseStart_2674168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674209 : List Nat := [1, 2, 3, 2, 2, 3, 2, 1, 3, 2, 2]
def baseStart_2674209 : Nat := 118140960795 + 2674209 * 2 ^ 59
def prefixEnd_2674209 : Nat := 4983230072969 + 3 ^ 40 * 2674209 * 2
def baseEnd_2674209 : Nat := 1373154587579432878689043

theorem tailTrace_2674209 : CollatzResearch.WordTrace tailWord_2674209 prefixEnd_2674209 1373154587579432878689043 := by
  unfold tailWord_2674209
  simp only [CollatzResearch.WordTrace]
  refine ⟨97536415168804986381089681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65024276779203324254059787 97536415168804986381089681)
  ·
    refine ⟨73152311376603739785817261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97536415168804986381089681 73152311376603739785817261)
    ·
      refine ⟨27432116766226402419681473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73152311376603739785817261 27432116766226402419681473)
      ·
        refine ⟨20574087574669801814761105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27432116766226402419681473 20574087574669801814761105)
        ·
          refine ⟨15430565681002351361070829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20574087574669801814761105 15430565681002351361070829)
          ·
            refine ⟨5786462130375881760401561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15430565681002351361070829 5786462130375881760401561)
            ·
              refine ⟨4339846597781911320301171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5786462130375881760401561 4339846597781911320301171)
              ·
                refine ⟨6509769896672866980451757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4339846597781911320301171 6509769896672866980451757)
                ·
                  refine ⟨2441163711252325117669409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6509769896672866980451757 2441163711252325117669409)
                  ·
                    refine ⟨1830872783439243838252057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2441163711252325117669409 1830872783439243838252057)
                    ·
                      refine ⟨1373154587579432878689043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1830872783439243838252057 1373154587579432878689043)
                      ·
                        rfl

theorem cell23_2674209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 3, 2, 2].length) (baseStart_2674209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674209 prefixEnd_2674209 := by exact prefixLift 2674209
  have htrace : WordTrace (prefixWord ++ tailWord_2674209) baseStart_2674209 baseEnd_2674209 := by
    simpa [prefixWord, tailWord_2674209, baseEnd_2674209] using wordTrace_append hprefix tailTrace_2674209
  have hstable : (prefixWord ++ tailWord_2674209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674209).length < 2 ^ (prefixWord ++ tailWord_2674209).sum := by decide
  have hdescent : baseEnd_2674209 < baseStart_2674209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674222 : List Nat := [4, 1, 3, 1, 2, 1, 3, 1, 1, 2, 4]
def baseStart_2674222 : Nat := 118140960795 + 2674222 * 2 ^ 59
def prefixEnd_2674222 : Nat := 4983230072969 + 3 ^ 40 * 2674222 * 2
def baseEnd_2674222 : Nat := 1373161262827941327826483

theorem tailTrace_2674222 : CollatzResearch.WordTrace tailWord_2674222 prefixEnd_2674222 1373161262827941327826483 := by
  unfold tailWord_2674222
  simp only [CollatzResearch.WordTrace]
  refine ⟨12192111164719736200164115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65024592878505259734208613 12192111164719736200164115)
  ·
    refine ⟨18288166747079604300246173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12192111164719736200164115 18288166747079604300246173)
    ·
      refine ⟨6858062530154851612592315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18288166747079604300246173 6858062530154851612592315)
      ·
        refine ⟨10287093795232277418888473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6858062530154851612592315 10287093795232277418888473)
        ·
          refine ⟨7715320346424208064166355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10287093795232277418888473 7715320346424208064166355)
          ·
            refine ⟨11572980519636312096249533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7715320346424208064166355 11572980519636312096249533)
            ·
              refine ⟨4339867694863617036093575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11572980519636312096249533 4339867694863617036093575)
              ·
                refine ⟨6509801542295425554140363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4339867694863617036093575 6509801542295425554140363)
                ·
                  refine ⟨9764702313443138331210545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6509801542295425554140363 9764702313443138331210545)
                  ·
                    refine ⟨7323526735082353748407909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9764702313443138331210545 7323526735082353748407909)
                    ·
                      refine ⟨1373161262827941327826483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7323526735082353748407909 1373161262827941327826483)
                      ·
                        rfl

theorem cell23_2674222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_2674222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674222 prefixEnd_2674222 := by exact prefixLift 2674222
  have htrace : WordTrace (prefixWord ++ tailWord_2674222) baseStart_2674222 baseEnd_2674222 := by
    simpa [prefixWord, tailWord_2674222, baseEnd_2674222] using wordTrace_append hprefix tailTrace_2674222
  have hstable : (prefixWord ++ tailWord_2674222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674222).length < 2 ^ (prefixWord ++ tailWord_2674222).sum := by decide
  have hdescent : baseEnd_2674222 < baseStart_2674222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674248 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 3, 5, 4]
def baseStart_2674248 : Nat := 118140960795 + 2674248 * 2 ^ 59
def prefixEnd_2674248 : Nat := 4983230072969 + 3 ^ 40 * 2674248 * 2
def baseEnd_2674248 : Nat := 1373174613324958226101363

theorem tailTrace_2674248 : CollatzResearch.WordTrace tailWord_2674248 prefixEnd_2674248 1373174613324958226101363 := by
  unfold tailWord_2674248
  simp only [CollatzResearch.WordTrace]
  refine ⟨48768918807831848020879699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65025225077109130694506265 48768918807831848020879699)
  ·
    refine ⟨73153378211747772031319549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48768918807831848020879699 73153378211747772031319549)
    ·
      refine ⟨27432516829405414511744831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73153378211747772031319549 27432516829405414511744831)
      ·
        refine ⟨41148775244108121767617247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27432516829405414511744831 41148775244108121767617247)
        ·
          refine ⟨61723162866162182651425871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41148775244108121767617247 61723162866162182651425871)
          ·
            refine ⟨92584744299243273977138807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61723162866162182651425871 92584744299243273977138807)
            ·
              refine ⟨138877116448864910965708211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92584744299243273977138807 138877116448864910965708211)
              ·
                refine ⟨208315674673297366448562317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138877116448864910965708211 208315674673297366448562317)
                ·
                  refine ⟨78118378002486512418210869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 208315674673297366448562317 78118378002486512418210869)
                  ·
                    refine ⟨7323597937733110539207269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 78118378002486512418210869 7323597937733110539207269)
                    ·
                      refine ⟨1373174613324958226101363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7323597937733110539207269 1373174613324958226101363)
                      ·
                        rfl

theorem cell23_2674248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_2674248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674248 prefixEnd_2674248 := by exact prefixLift 2674248
  have htrace : WordTrace (prefixWord ++ tailWord_2674248) baseStart_2674248 baseEnd_2674248 := by
    simpa [prefixWord, tailWord_2674248, baseEnd_2674248] using wordTrace_append hprefix tailTrace_2674248
  have hstable : (prefixWord ++ tailWord_2674248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674248).length < 2 ^ (prefixWord ++ tailWord_2674248).sum := by decide
  have hdescent : baseEnd_2674248 < baseStart_2674248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674276 : List Nat := [2, 3, 1, 1, 2, 5, 2, 1, 2, 1, 3]
def baseStart_2674276 : Nat := 118140960795 + 2674276 * 2 ^ 59
def prefixEnd_2674276 : Nat := 4983230072969 + 3 ^ 40 * 2674276 * 2
def baseEnd_2674276 : Nat := 1373188990783284116551235

theorem tailTrace_2674276 : CollatzResearch.WordTrace tailWord_2674276 prefixEnd_2674276 1373188990783284116551235 := by
  unfold tailWord_2674276
  simp only [CollatzResearch.WordTrace]
  refine ⟨48769429429781128411889341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65025905906374837882519121 48769429429781128411889341)
  ·
    refine ⟨18288536036167923154458503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48769429429781128411889341 18288536036167923154458503)
    ·
      refine ⟨27432804054251884731687755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18288536036167923154458503 27432804054251884731687755)
      ·
        refine ⟨41149206081377827097531633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27432804054251884731687755 41149206081377827097531633)
        ·
          refine ⟨30861904561033370323148725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41149206081377827097531633 30861904561033370323148725)
          ·
            refine ⟨2893303552596878467795193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30861904561033370323148725 2893303552596878467795193)
            ·
              refine ⟨2169977664447658850846395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2893303552596878467795193 2169977664447658850846395)
              ·
                refine ⟨3254966496671488276269593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2169977664447658850846395 3254966496671488276269593)
                ·
                  refine ⟨2441224872503616207202195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3254966496671488276269593 2441224872503616207202195)
                  ·
                    refine ⟨3661837308755424310803293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2441224872503616207202195 3661837308755424310803293)
                    ·
                      refine ⟨1373188990783284116551235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3661837308755424310803293 1373188990783284116551235)
                      ·
                        rfl

theorem cell23_2674276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 1, 2, 1, 3].length) (baseStart_2674276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674276 prefixEnd_2674276 := by exact prefixLift 2674276
  have htrace : WordTrace (prefixWord ++ tailWord_2674276) baseStart_2674276 baseEnd_2674276 := by
    simpa [prefixWord, tailWord_2674276, baseEnd_2674276] using wordTrace_append hprefix tailTrace_2674276
  have hstable : (prefixWord ++ tailWord_2674276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674276).length < 2 ^ (prefixWord ++ tailWord_2674276).sum := by decide
  have hdescent : baseEnd_2674276 < baseStart_2674276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674298 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 1, 2, 7]
def baseStart_2674298 : Nat := 118140960795 + 2674298 * 2 ^ 59
def prefixEnd_2674298 : Nat := 4983230072969 + 3 ^ 40 * 2674298 * 2
def baseEnd_2674298 : Nat := 1373200287357683030476133

theorem tailTrace_2674298 : CollatzResearch.WordTrace tailWord_2674298 prefixEnd_2674298 1373200287357683030476133 := by
  unfold tailWord_2674298
  simp only [CollatzResearch.WordTrace]
  refine ⟨24384915316370638645269887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65026440843655036387386365 24384915316370638645269887)
  ·
    refine ⟨36577372974555957967904831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24384915316370638645269887 36577372974555957967904831)
    ·
      refine ⟨54866059461833936951857247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36577372974555957967904831 54866059461833936951857247)
      ·
        refine ⟨82299089192750905427785871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54866059461833936951857247 82299089192750905427785871)
        ·
          refine ⟨123448633789126358141678807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82299089192750905427785871 123448633789126358141678807)
          ·
            refine ⟨185172950683689537212518211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123448633789126358141678807 185172950683689537212518211)
            ·
              refine ⟨277759426025534305818777317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185172950683689537212518211 277759426025534305818777317)
              ·
                refine ⟨52079892379787682341020747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 277759426025534305818777317 52079892379787682341020747)
                ·
                  refine ⟨78119838569681523511531121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52079892379787682341020747 78119838569681523511531121)
                  ·
                    refine ⟨58589878927261142633648341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78119838569681523511531121 58589878927261142633648341)
                    ·
                      refine ⟨1373200287357683030476133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 58589878927261142633648341 1373200287357683030476133)
                      ·
                        rfl

theorem cell23_2674298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_2674298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674298 prefixEnd_2674298 := by exact prefixLift 2674298
  have htrace : WordTrace (prefixWord ++ tailWord_2674298) baseStart_2674298 baseEnd_2674298 := by
    simpa [prefixWord, tailWord_2674298, baseEnd_2674298] using wordTrace_append hprefix tailTrace_2674298
  have hstable : (prefixWord ++ tailWord_2674298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674298).length < 2 ^ (prefixWord ++ tailWord_2674298).sum := by decide
  have hdescent : baseEnd_2674298 < baseStart_2674298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674315 : List Nat := [1, 1, 1, 1, 4, 1, 4, 2, 2, 3, 3]
def baseStart_2674315 : Nat := 118140960795 + 2674315 * 2 ^ 59
def prefixEnd_2674315 : Nat := 4983230072969 + 3 ^ 40 * 2674315 * 2
def baseEnd_2674315 : Nat := 1373209016528809463963555

theorem tailTrace_2674315 : CollatzResearch.WordTrace tailWord_2674315 prefixEnd_2674315 1373209016528809463963555 := by
  unfold tailWord_2674315
  simp only [CollatzResearch.WordTrace]
  refine ⟨97540281306420966484448399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65026854204280644322965599 97540281306420966484448399)
  ·
    refine ⟨146310421959631449726672599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97540281306420966484448399 146310421959631449726672599)
    ·
      refine ⟨219465632939447174590008899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146310421959631449726672599 219465632939447174590008899)
      ·
        refine ⟨329198449409170761885013349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219465632939447174590008899 329198449409170761885013349)
        ·
          refine ⟨61724709264219517853440003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 329198449409170761885013349 61724709264219517853440003)
          ·
            refine ⟨92587063896329276780160005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61724709264219517853440003 92587063896329276780160005)
            ·
              refine ⟨17360074480561739396280001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92587063896329276780160005 17360074480561739396280001)
              ·
                refine ⟨13020055860421304547210001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17360074480561739396280001 13020055860421304547210001)
                ·
                  refine ⟨9765041895315978410407501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13020055860421304547210001 9765041895315978410407501)
                  ·
                    refine ⟨3661890710743491903902813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9765041895315978410407501 3661890710743491903902813)
                    ·
                      refine ⟨1373209016528809463963555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3661890710743491903902813 1373209016528809463963555)
                      ·
                        rfl

theorem cell23_2674315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 3, 3].length) (baseStart_2674315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674315 prefixEnd_2674315 := by exact prefixLift 2674315
  have htrace : WordTrace (prefixWord ++ tailWord_2674315) baseStart_2674315 baseEnd_2674315 := by
    simpa [prefixWord, tailWord_2674315, baseEnd_2674315] using wordTrace_append hprefix tailTrace_2674315
  have hstable : (prefixWord ++ tailWord_2674315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674315).length < 2 ^ (prefixWord ++ tailWord_2674315).sum := by decide
  have hdescent : baseEnd_2674315 < baseStart_2674315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674355 : List Nat := [1, 1, 1, 2, 3, 3, 3, 1, 1, 3, 4]
def baseStart_2674355 : Nat := 118140960795 + 2674355 * 2 ^ 59
def prefixEnd_2674355 : Nat := 4983230072969 + 3 ^ 40 * 2674355 * 2
def baseEnd_2674355 : Nat := 1373229555754989307463371

theorem tailTrace_2674355 : CollatzResearch.WordTrace tailWord_2674355 prefixEnd_2674355 1373229555754989307463371 := by
  unfold tailWord_2674355
  simp only [CollatzResearch.WordTrace]
  refine ⟨97541740226276053315904519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65027826817517368877269679 97541740226276053315904519)
  ·
    refine ⟨146312610339414079973856779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97541740226276053315904519 146312610339414079973856779)
    ·
      refine ⟨219468915509121119960785169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146312610339414079973856779 219468915509121119960785169)
      ·
        refine ⟨164601686631840839970588877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219468915509121119960785169 164601686631840839970588877)
        ·
          refine ⟨61725632486940314988970829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164601686631840839970588877 61725632486940314988970829)
          ·
            refine ⟨23147112182602618120864061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61725632486940314988970829 23147112182602618120864061)
            ·
              refine ⟨8680167068475981795324023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23147112182602618120864061 8680167068475981795324023)
              ·
                refine ⟨13020250602713972692986035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8680167068475981795324023 13020250602713972692986035)
                ·
                  refine ⟨19530375904070959039479053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13020250602713972692986035 19530375904070959039479053)
                  ·
                    refine ⟨7323890964026609639804645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19530375904070959039479053 7323890964026609639804645)
                    ·
                      refine ⟨1373229555754989307463371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7323890964026609639804645 1373229555754989307463371)
                      ·
                        rfl

theorem cell23_2674355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 3, 4].length) (baseStart_2674355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674355 prefixEnd_2674355 := by exact prefixLift 2674355
  have htrace : WordTrace (prefixWord ++ tailWord_2674355) baseStart_2674355 baseEnd_2674355 := by
    simpa [prefixWord, tailWord_2674355, baseEnd_2674355] using wordTrace_append hprefix tailTrace_2674355
  have hstable : (prefixWord ++ tailWord_2674355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674355).length < 2 ^ (prefixWord ++ tailWord_2674355).sum := by decide
  have hdescent : baseEnd_2674355 < baseStart_2674355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674372 : List Nat := [2, 3, 3, 1, 1, 1, 2, 1, 4, 1, 4]
def baseStart_2674372 : Nat := 118140960795 + 2674372 * 2 ^ 59
def prefixEnd_2674372 : Nat := 4983230072969 + 3 ^ 40 * 2674372 * 2
def baseEnd_2674372 : Nat := 1373238284926115740950793

theorem tailTrace_2674372 : CollatzResearch.WordTrace tailWord_2674372 prefixEnd_2674372 1373238284926115740950793 := by
  unfold tailWord_2674372
  simp only [CollatzResearch.WordTrace]
  refine ⟨48771180133607232609636685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65028240178142976812848913 48771180133607232609636685)
  ·
    refine ⟨18289192550102712228613757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48771180133607232609636685 18289192550102712228613757)
    ·
      refine ⟨6858447206288517085730159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18289192550102712228613757 6858447206288517085730159)
      ·
        refine ⟨10287670809432775628595239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6858447206288517085730159 10287670809432775628595239)
        ·
          refine ⟨15431506214149163442892859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10287670809432775628595239 15431506214149163442892859)
          ·
            refine ⟨23147259321223745164339289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15431506214149163442892859 23147259321223745164339289)
            ·
              refine ⟨17360444490917808873254467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23147259321223745164339289 17360444490917808873254467)
              ·
                refine ⟨26040666736376713309881701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17360444490917808873254467 26040666736376713309881701)
                ·
                  refine ⟨4882625013070633745602819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26040666736376713309881701 4882625013070633745602819)
                  ·
                    refine ⟨7323937519605950618404229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4882625013070633745602819 7323937519605950618404229)
                    ·
                      refine ⟨1373238284926115740950793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7323937519605950618404229 1373238284926115740950793)
                      ·
                        rfl

theorem cell23_2674372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_2674372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674372 prefixEnd_2674372 := by exact prefixLift 2674372
  have htrace : WordTrace (prefixWord ++ tailWord_2674372) baseStart_2674372 baseEnd_2674372 := by
    simpa [prefixWord, tailWord_2674372, baseEnd_2674372] using wordTrace_append hprefix tailTrace_2674372
  have hstable : (prefixWord ++ tailWord_2674372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674372).length < 2 ^ (prefixWord ++ tailWord_2674372).sum := by decide
  have hdescent : baseEnd_2674372 < baseStart_2674372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674425 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 7, 5]
def baseStart_2674425 : Nat := 118140960795 + 2674425 * 2 ^ 59
def prefixEnd_2674425 : Nat := 4983230072969 + 3 ^ 40 * 2674425 * 2
def baseEnd_2674425 : Nat := 457755166466934677862683

theorem tailTrace_2674425 : CollatzResearch.WordTrace tailWord_2674425 prefixEnd_2674425 457755166466934677862683 := by
  unfold tailWord_2674425
  simp only [CollatzResearch.WordTrace]
  refine ⟨97544293336022455270952729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65029528890681636847301819 97544293336022455270952729)
  ·
    refine ⟨73158220002016841453214547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97544293336022455270952729 73158220002016841453214547)
    ·
      refine ⟨109737330003025262179821821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73158220002016841453214547 109737330003025262179821821)
      ·
        refine ⟨41151498751134473317433183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109737330003025262179821821 41151498751134473317433183)
        ·
          refine ⟨61727248126701709976149775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41151498751134473317433183 61727248126701709976149775)
          ·
            refine ⟨92590872190052564964224663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61727248126701709976149775 92590872190052564964224663)
            ·
              refine ⟨138886308285078847446336995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92590872190052564964224663 138886308285078847446336995)
              ·
                refine ⟨208329462427618271169505493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138886308285078847446336995 208329462427618271169505493)
                ·
                  refine ⟨4882721775647303230535285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 208329462427618271169505493 4882721775647303230535285)
                  ·
                    refine ⟨457755166466934677862683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4882721775647303230535285 457755166466934677862683)
                    ·
                      rfl

theorem cell23_2674425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 7, 5].length) (baseStart_2674425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674425 prefixEnd_2674425 := by exact prefixLift 2674425
  have htrace : WordTrace (prefixWord ++ tailWord_2674425) baseStart_2674425 baseEnd_2674425 := by
    simpa [prefixWord, tailWord_2674425, baseEnd_2674425] using wordTrace_append hprefix tailTrace_2674425
  have hstable : (prefixWord ++ tailWord_2674425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674425).length < 2 ^ (prefixWord ++ tailWord_2674425).sum := by decide
  have hdescent : baseEnd_2674425 < baseStart_2674425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674466 : List Nat := [3, 3, 1, 1, 2, 1, 4, 1, 2, 3, 2]
def baseStart_2674466 : Nat := 118140960795 + 2674466 * 2 ^ 59
def prefixEnd_2674466 : Nat := 4983230072969 + 3 ^ 40 * 2674466 * 2
def baseEnd_2674466 : Nat := 1373286552107638373175361

theorem tailTrace_2674466 : CollatzResearch.WordTrace tailWord_2674466 prefixEnd_2674466 1373286552107638373175361 := by
  unfold tailWord_2674466
  simp only [CollatzResearch.WordTrace]
  refine ⟨24386447182218479818298813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65030525819249279515463501 24386447182218479818298813)
  ·
    refine ⟨9144917693331929931862055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24386447182218479818298813 9144917693331929931862055)
    ·
      refine ⟨13717376539997894897793083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9144917693331929931862055 13717376539997894897793083)
      ·
        refine ⟨20576064809996842346689625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13717376539997894897793083 20576064809996842346689625)
        ·
          refine ⟨15432048607497631760017219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20576064809996842346689625 15432048607497631760017219)
          ·
            refine ⟨23148072911246447640025829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15432048607497631760017219 23148072911246447640025829)
            ·
              refine ⟨4340263670858708932504843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23148072911246447640025829 4340263670858708932504843)
              ·
                refine ⟨6510395506288063398757265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4340263670858708932504843 6510395506288063398757265)
                ·
                  refine ⟨4882796629716047549067949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6510395506288063398757265 4882796629716047549067949)
                  ·
                    refine ⟨1831048736143517830900481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4882796629716047549067949 1831048736143517830900481)
                    ·
                      refine ⟨1373286552107638373175361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1831048736143517830900481 1373286552107638373175361)
                      ·
                        rfl

theorem cell23_2674466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 2, 3, 2].length) (baseStart_2674466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674466 prefixEnd_2674466 := by exact prefixLift 2674466
  have htrace : WordTrace (prefixWord ++ tailWord_2674466) baseStart_2674466 baseEnd_2674466 := by
    simpa [prefixWord, tailWord_2674466, baseEnd_2674466] using wordTrace_append hprefix tailTrace_2674466
  have hstable : (prefixWord ++ tailWord_2674466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674466).length < 2 ^ (prefixWord ++ tailWord_2674466).sum := by decide
  have hdescent : baseEnd_2674466 < baseStart_2674466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674472 : List Nat := [2, 1, 5, 1, 1, 2, 1, 1, 3, 6]
def baseStart_2674472 : Nat := 118140960795 + 2674472 * 2 ^ 59
def prefixEnd_2674472 : Nat := 4983230072969 + 3 ^ 40 * 2674472 * 2
def baseEnd_2674472 : Nat := 457763210997188449900111

theorem tailTrace_2674472 : CollatzResearch.WordTrace tailWord_2674472 prefixEnd_2674472 457763210997188449900111 := by
  unfold tailWord_2674472
  simp only [CollatzResearch.WordTrace]
  refine ⟨48773003783426091148956835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65030671711234788198609113 48773003783426091148956835)
  ·
    refine ⟨73159505675139136723435253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48773003783426091148956835 73159505675139136723435253)
    ·
      refine ⟨6858703657044294067822055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73159505675139136723435253 6858703657044294067822055)
      ·
        refine ⟨10288055485566441101733083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6858703657044294067822055 10288055485566441101733083)
        ·
          refine ⟨15432083228349661652599625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10288055485566441101733083 15432083228349661652599625)
          ·
            refine ⟨11574062421262246239449719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15432083228349661652599625 11574062421262246239449719)
            ·
              refine ⟨17361093631893369359174579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11574062421262246239449719 17361093631893369359174579)
              ·
                refine ⟨26041640447840054038761869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17361093631893369359174579 26041640447840054038761869)
                ·
                  refine ⟨9765615167940020264535701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26041640447840054038761869 9765615167940020264535701)
                  ·
                    refine ⟨457763210997188449900111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9765615167940020264535701 457763210997188449900111)
                    ·
                      rfl

theorem cell23_2674472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_2674472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674472 prefixEnd_2674472 := by exact prefixLift 2674472
  have htrace : WordTrace (prefixWord ++ tailWord_2674472) baseStart_2674472 baseEnd_2674472 := by
    simpa [prefixWord, tailWord_2674472, baseEnd_2674472] using wordTrace_append hprefix tailTrace_2674472
  have hstable : (prefixWord ++ tailWord_2674472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674472).length < 2 ^ (prefixWord ++ tailWord_2674472).sum := by decide
  have hdescent : baseEnd_2674472 < baseStart_2674472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674475 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 2, 6, 4]
def baseStart_2674475 : Nat := 118140960795 + 2674475 * 2 ^ 59
def prefixEnd_2674475 : Nat := 4983230072969 + 3 ^ 40 * 2674475 * 2
def baseEnd_2674475 : Nat := 1373291173433528837962819

theorem tailTrace_2674475 : CollatzResearch.WordTrace tailWord_2674475 prefixEnd_2674475 1373291173433528837962819 := by
  unfold tailWord_2674475
  simp only [CollatzResearch.WordTrace]
  refine ⟨97546116985841313810272879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65030744657227542540181919 97546116985841313810272879)
  ·
    refine ⟨146319175478761970715409319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97546116985841313810272879 146319175478761970715409319)
    ·
      refine ⟨219478763218142956073113979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146319175478761970715409319 219478763218142956073113979)
      ·
        refine ⟨329218144827214434109670969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219478763218142956073113979 329218144827214434109670969)
        ·
          refine ⟨246913608620410825582253227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 329218144827214434109670969 246913608620410825582253227)
          ·
            refine ⟨370370412930616238373379841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246913608620410825582253227 370370412930616238373379841)
            ·
              refine ⟨277777809697962178780034881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 370370412930616238373379841 277777809697962178780034881)
              ·
                refine ⟨208333357273471634085026161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 277777809697962178780034881 208333357273471634085026161)
                ·
                  refine ⟨156250017955103725563769621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 208333357273471634085026161 156250017955103725563769621)
                  ·
                    refine ⟨7324219591645487135801701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 156250017955103725563769621 7324219591645487135801701)
                    ·
                      refine ⟨1373291173433528837962819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7324219591645487135801701 1373291173433528837962819)
                      ·
                        rfl

theorem cell23_2674475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 6, 4].length) (baseStart_2674475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674475 prefixEnd_2674475 := by exact prefixLift 2674475
  have htrace : WordTrace (prefixWord ++ tailWord_2674475) baseStart_2674475 baseEnd_2674475 := by
    simpa [prefixWord, tailWord_2674475, baseEnd_2674475] using wordTrace_append hprefix tailTrace_2674475
  have hstable : (prefixWord ++ tailWord_2674475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674475).length < 2 ^ (prefixWord ++ tailWord_2674475).sum := by decide
  have hdescent : baseEnd_2674475 < baseStart_2674475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674479 : List Nat := [1, 1, 2, 1, 2, 1, 2, 4, 5, 2, 2]
def baseStart_2674479 : Nat := 118140960795 + 2674479 * 2 ^ 59
def prefixEnd_2674479 : Nat := 4983230072969 + 3 ^ 40 * 2674479 * 2
def baseEnd_2674479 : Nat := 1373293227356146822312801

theorem tailTrace_2674479 : CollatzResearch.WordTrace tailWord_2674479 prefixEnd_2674479 1373293227356146822312801 := by
  unfold tailWord_2674479
  simp only [CollatzResearch.WordTrace]
  refine ⟨97546262877826822493418491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65030841918551214995612327 97546262877826822493418491)
  ·
    refine ⟨146319394316740233740127737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97546262877826822493418491 146319394316740233740127737)
    ·
      refine ⟨109739545737555175305095803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146319394316740233740127737 109739545737555175305095803)
      ·
        refine ⟨164609318606332762957643705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109739545737555175305095803 164609318606332762957643705)
        ·
          refine ⟨123456988954749572218232779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164609318606332762957643705 123456988954749572218232779)
          ·
            refine ⟨185185483432124358327349169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123456988954749572218232779 185185483432124358327349169)
            ·
              refine ⟨138889112574093268745511877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185185483432124358327349169 138889112574093268745511877)
              ·
                refine ⟨26041708607642487889783477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 138889112574093268745511877 26041708607642487889783477)
                ·
                  refine ⟨2441410181966483239667201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26041708607642487889783477 2441410181966483239667201)
                  ·
                    refine ⟨1831057636474862429750401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2441410181966483239667201 1831057636474862429750401)
                    ·
                      refine ⟨1373293227356146822312801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1831057636474862429750401 1373293227356146822312801)
                      ·
                        rfl

theorem cell23_2674479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 5, 2, 2].length) (baseStart_2674479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674479 prefixEnd_2674479 := by exact prefixLift 2674479
  have htrace : WordTrace (prefixWord ++ tailWord_2674479) baseStart_2674479 baseEnd_2674479 := by
    simpa [prefixWord, tailWord_2674479, baseEnd_2674479] using wordTrace_append hprefix tailTrace_2674479
  have hstable : (prefixWord ++ tailWord_2674479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674479).length < 2 ^ (prefixWord ++ tailWord_2674479).sum := by decide
  have hdescent : baseEnd_2674479 < baseStart_2674479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674485 : List Nat := [1, 3, 3, 1, 15]
def baseStart_2674485 : Nat := 118140960795 + 2674485 * 2 ^ 59
def prefixEnd_2674485 : Nat := 4983230072969 + 3 ^ 40 * 2674485 * 2
def baseEnd_2674485 : Nat := 1883808378930142385237

theorem tailTrace_2674485 : CollatzResearch.WordTrace tailWord_2674485 prefixEnd_2674485 1883808378930142385237 := by
  unfold tailWord_2674485
  simp only [CollatzResearch.WordTrace]
  refine ⟨97546481715805085518136909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65030987810536723678757939 97546481715805085518136909)
  ·
    refine ⟨36579930643426907069301341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97546481715805085518136909 36579930643426907069301341)
    ·
      refine ⟨13717473991285090150988003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36579930643426907069301341 13717473991285090150988003)
      ·
        refine ⟨20576210986927635226482005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13717473991285090150988003 20576210986927635226482005)
        ·
          refine ⟨1883808378930142385237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 20576210986927635226482005 1883808378930142385237)
          ·
            rfl

theorem cell23_2674485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 15].length) (baseStart_2674485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674485 prefixEnd_2674485 := by exact prefixLift 2674485
  have htrace : WordTrace (prefixWord ++ tailWord_2674485) baseStart_2674485 baseEnd_2674485 := by
    simpa [prefixWord, tailWord_2674485, baseEnd_2674485] using wordTrace_append hprefix tailTrace_2674485
  have hstable : (prefixWord ++ tailWord_2674485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674485).length < 2 ^ (prefixWord ++ tailWord_2674485).sum := by decide
  have hdescent : baseEnd_2674485 < baseStart_2674485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674490 : List Nat := [3, 1, 1, 1, 5, 3, 2, 2, 1, 1, 3]
def baseStart_2674490 : Nat := 118140960795 + 2674490 * 2 ^ 59
def prefixEnd_2674490 : Nat := 4983230072969 + 3 ^ 40 * 2674490 * 2
def baseEnd_2674490 : Nat := 1373298875643346279275251

theorem tailTrace_2674490 : CollatzResearch.WordTrace tailWord_2674490 prefixEnd_2674490 1373298875643346279275251 := by
  unfold tailWord_2674490
  simp only [CollatzResearch.WordTrace]
  refine ⟨24386666020196742843017231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65031109387191314248045949 24386666020196742843017231)
  ·
    refine ⟨36579999030295114264525847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24386666020196742843017231 36579999030295114264525847)
    ·
      refine ⟨54869998545442671396788771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36579999030295114264525847 54869998545442671396788771)
      ·
        refine ⟨82304997818164007095183157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54869998545442671396788771 82304997818164007095183157)
        ·
          refine ⟨7716093545452875665173421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82304997818164007095183157 7716093545452875665173421)
          ·
            refine ⟨2893535079544828374440033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7716093545452875665173421 2893535079544828374440033)
            ·
              refine ⟨2170151309658621280830025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2893535079544828374440033 2170151309658621280830025)
              ·
                refine ⟨1627613482243965960622519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2170151309658621280830025 1627613482243965960622519)
                ·
                  refine ⟨2441420223365948940933779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1627613482243965960622519 2441420223365948940933779)
                  ·
                    refine ⟨3662130335048923411400669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2441420223365948940933779 3662130335048923411400669)
                    ·
                      refine ⟨1373298875643346279275251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3662130335048923411400669 1373298875643346279275251)
                      ·
                        rfl

theorem cell23_2674490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 2, 1, 1, 3].length) (baseStart_2674490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674490 prefixEnd_2674490 := by exact prefixLift 2674490
  have htrace : WordTrace (prefixWord ++ tailWord_2674490) baseStart_2674490 baseEnd_2674490 := by
    simpa [prefixWord, tailWord_2674490, baseEnd_2674490] using wordTrace_append hprefix tailTrace_2674490
  have hstable : (prefixWord ++ tailWord_2674490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674490).length < 2 ^ (prefixWord ++ tailWord_2674490).sum := by decide
  have hdescent : baseEnd_2674490 < baseStart_2674490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674519 : List Nat := [1, 1, 3, 2, 5, 1, 3, 7]
def baseStart_2674519 : Nat := 118140960795 + 2674519 * 2 ^ 59
def prefixEnd_2674519 : Nat := 4983230072969 + 3 ^ 40 * 2674519 * 2
def baseEnd_2674519 : Nat := 50863472836382469104171

theorem tailTrace_2674519 : CollatzResearch.WordTrace tailWord_2674519 prefixEnd_2674519 50863472836382469104171 := by
  unfold tailWord_2674519
  simp only [CollatzResearch.WordTrace]
  refine ⟨97547721797681909324874611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65031814531787939549916407 97547721797681909324874611)
  ·
    refine ⟨146321582696522863987311917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97547721797681909324874611 146321582696522863987311917)
    ·
      refine ⟨54870593511196073995241969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146321582696522863987311917 54870593511196073995241969)
      ·
        refine ⟨41152945133397055496431477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54870593511196073995241969 41152945133397055496431477)
        ·
          refine ⟨3858088606255973952790451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41152945133397055496431477 3858088606255973952790451)
          ·
            refine ⟨5787132909383960929185677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3858088606255973952790451 5787132909383960929185677)
            ·
              refine ⟨2170174841018985348444629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5787132909383960929185677 2170174841018985348444629)
              ·
                refine ⟨50863472836382469104171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2170174841018985348444629 50863472836382469104171)
                ·
                  rfl

theorem cell23_2674519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 7].length) (baseStart_2674519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674519 prefixEnd_2674519 := by exact prefixLift 2674519
  have htrace : WordTrace (prefixWord ++ tailWord_2674519) baseStart_2674519 baseEnd_2674519 := by
    simpa [prefixWord, tailWord_2674519, baseEnd_2674519] using wordTrace_append hprefix tailTrace_2674519
  have hstable : (prefixWord ++ tailWord_2674519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674519).length < 2 ^ (prefixWord ++ tailWord_2674519).sum := by decide
  have hdescent : baseEnd_2674519 < baseStart_2674519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674529 : List Nat := [1, 2, 3, 1, 1, 1, 4, 2, 4, 1, 3]
def baseStart_2674529 : Nat := 118140960795 + 2674529 * 2 ^ 59
def prefixEnd_2674529 : Nat := 4983230072969 + 3 ^ 40 * 2674529 * 2
def baseEnd_2674529 : Nat := 1373318901388871626687571

theorem tailTrace_2674529 : CollatzResearch.WordTrace tailWord_2674529 prefixEnd_2674529 1373318901388871626687571 := by
  unfold tailWord_2674529
  simp only [CollatzResearch.WordTrace]
  refine ⟨97548086527645681032738641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65032057685097120688492427 97548086527645681032738641)
  ·
    refine ⟨73161064895734260774553981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97548086527645681032738641 73161064895734260774553981)
    ·
      refine ⟨27435399335900347790457743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73161064895734260774553981 27435399335900347790457743)
      ·
        refine ⟨41153099003850521685686615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27435399335900347790457743 41153099003850521685686615)
        ·
          refine ⟨61729648505775782528529923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41153099003850521685686615 61729648505775782528529923)
          ·
            refine ⟨92594472758663673792794885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61729648505775782528529923 92594472758663673792794885)
            ·
              refine ⟨17361463642249438836149041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92594472758663673792794885 17361463642249438836149041)
              ·
                refine ⟨13021097731687079127111781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17361463642249438836149041 13021097731687079127111781)
                ·
                  refine ⟨2441455824691327336333459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13021097731687079127111781 2441455824691327336333459)
                  ·
                    refine ⟨3662183737036991004500189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2441455824691327336333459 3662183737036991004500189)
                    ·
                      refine ⟨1373318901388871626687571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3662183737036991004500189 1373318901388871626687571)
                      ·
                        rfl

theorem cell23_2674529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 4, 1, 3].length) (baseStart_2674529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674529 prefixEnd_2674529 := by exact prefixLift 2674529
  have htrace : WordTrace (prefixWord ++ tailWord_2674529) baseStart_2674529 baseEnd_2674529 := by
    simpa [prefixWord, tailWord_2674529, baseEnd_2674529] using wordTrace_append hprefix tailTrace_2674529
  have hstable : (prefixWord ++ tailWord_2674529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674529).length < 2 ^ (prefixWord ++ tailWord_2674529).sum := by decide
  have hdescent : baseEnd_2674529 < baseStart_2674529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674530 : List Nat := [3, 3, 2, 1, 2, 1, 1, 5, 1, 2, 2]
def baseStart_2674530 : Nat := 118140960795 + 2674530 * 2 ^ 59
def prefixEnd_2674530 : Nat := 4983230072969 + 3 ^ 40 * 2674530 * 2
def baseEnd_2674530 : Nat := 1373319414869526122775067

theorem tailTrace_2674530 : CollatzResearch.WordTrace tailWord_2674530 prefixEnd_2674530 1373319414869526122775067 := by
  unfold tailWord_2674530
  simp only [CollatzResearch.WordTrace]
  refine ⟨24387030750160514550881261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65032082000428038802350029 24387030750160514550881261)
  ·
    refine ⟨9145136531310192956580473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24387030750160514550881261 9145136531310192956580473)
    ·
      refine ⟨6858852398482644717435355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9145136531310192956580473 6858852398482644717435355)
      ·
        refine ⟨10288278597723967076153033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6858852398482644717435355 10288278597723967076153033)
        ·
          refine ⟨7716208948292975307114775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10288278597723967076153033 7716208948292975307114775)
          ·
            refine ⟨11574313422439462960672163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7716208948292975307114775 11574313422439462960672163)
            ·
              refine ⟨17361470133659194441008245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11574313422439462960672163 17361470133659194441008245)
              ·
                refine ⟨1627637825030549478844523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17361470133659194441008245 1627637825030549478844523)
                ·
                  refine ⟨2441456737545824218266785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1627637825030549478844523 2441456737545824218266785)
                  ·
                    refine ⟨1831092553159368163700089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2441456737545824218266785 1831092553159368163700089)
                    ·
                      refine ⟨1373319414869526122775067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1831092553159368163700089 1373319414869526122775067)
                      ·
                        rfl

theorem cell23_2674530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_2674530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674530 prefixEnd_2674530 := by exact prefixLift 2674530
  have htrace : WordTrace (prefixWord ++ tailWord_2674530) baseStart_2674530 baseEnd_2674530 := by
    simpa [prefixWord, tailWord_2674530, baseEnd_2674530] using wordTrace_append hprefix tailTrace_2674530
  have hstable : (prefixWord ++ tailWord_2674530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674530).length < 2 ^ (prefixWord ++ tailWord_2674530).sum := by decide
  have hdescent : baseEnd_2674530 < baseStart_2674530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674563 : List Nat := [1, 1, 1, 3, 4, 3, 3, 1, 2, 1, 3]
def baseStart_2674563 : Nat := 118140960795 + 2674563 * 2 ^ 59
def prefixEnd_2674563 : Nat := 4983230072969 + 3 ^ 40 * 2674563 * 2
def baseEnd_2674563 : Nat := 1373336359731124493662415

theorem tailTrace_2674563 : CollatzResearch.WordTrace tailWord_2674563 prefixEnd_2674563 1373336359731124493662415 := by
  unfold tailWord_2674563
  simp only [CollatzResearch.WordTrace]
  refine ⟨97549326609522504839476343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65032884406348336559650895 97549326609522504839476343)
  ·
    refine ⟨146323989914283757259214515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97549326609522504839476343 146323989914283757259214515)
    ·
      refine ⟨219485984871425635888821773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146323989914283757259214515 219485984871425635888821773)
      ·
        refine ⟨82307244326784613458308165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 219485984871425635888821773 82307244326784613458308165)
        ·
          refine ⟨15432608311272115023432781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82307244326784613458308165 15432608311272115023432781)
          ·
            refine ⟨5787228116727043133787293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15432608311272115023432781 5787228116727043133787293)
            ·
              refine ⟨2170210543772641175170235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5787228116727043133787293 2170210543772641175170235)
              ·
                refine ⟨3255315815658961762755353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2170210543772641175170235 3255315815658961762755353)
                ·
                  refine ⟨2441486861744221322066515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3255315815658961762755353 2441486861744221322066515)
                  ·
                    refine ⟨3662230292616331983099773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2441486861744221322066515 3662230292616331983099773)
                    ·
                      refine ⟨1373336359731124493662415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3662230292616331983099773 1373336359731124493662415)
                      ·
                        rfl

theorem cell23_2674563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 1, 2, 1, 3].length) (baseStart_2674563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674563 prefixEnd_2674563 := by exact prefixLift 2674563
  have htrace : WordTrace (prefixWord ++ tailWord_2674563) baseStart_2674563 baseEnd_2674563 := by
    simpa [prefixWord, tailWord_2674563, baseEnd_2674563] using wordTrace_append hprefix tailTrace_2674563
  have hstable : (prefixWord ++ tailWord_2674563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674563).length < 2 ^ (prefixWord ++ tailWord_2674563).sum := by decide
  have hdescent : baseEnd_2674563 < baseStart_2674563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674572 : List Nat := [2, 2, 1, 2, 1, 2, 1, 4, 2, 1, 5]
def baseStart_2674572 : Nat := 118140960795 + 2674572 * 2 ^ 59
def prefixEnd_2674572 : Nat := 4983230072969 + 3 ^ 40 * 2674572 * 2
def baseEnd_2674572 : Nat := 1373340981057014958449873

theorem tailTrace_2674572 : CollatzResearch.WordTrace tailWord_2674572 prefixEnd_2674572 1373340981057014958449873 := by
  unfold tailWord_2674572
  simp only [CollatzResearch.WordTrace]
  refine ⟨48774827433244949688276985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65033103244326599584369313 48774827433244949688276985)
  ·
    refine ⟨36581120574933712266207739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48774827433244949688276985 36581120574933712266207739)
    ·
      refine ⟨54871680862400568399311609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36581120574933712266207739 54871680862400568399311609)
      ·
        refine ⟨41153760646800426299483707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54871680862400568399311609 41153760646800426299483707)
        ·
          refine ⟨61730640970200639449225561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41153760646800426299483707 61730640970200639449225561)
          ·
            refine ⟨46297980727650479586919171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61730640970200639449225561 46297980727650479586919171)
            ·
              refine ⟨69446971091475719380378757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46297980727650479586919171 69446971091475719380378757)
              ·
                refine ⟨13021307079651697383821017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69446971091475719380378757 13021307079651697383821017)
                ·
                  refine ⟨9765980309738773037865763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13021307079651697383821017 9765980309738773037865763)
                  ·
                    refine ⟨14648970464608159556798645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9765980309738773037865763 14648970464608159556798645)
                    ·
                      refine ⟨1373340981057014958449873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14648970464608159556798645 1373340981057014958449873)
                      ·
                        rfl

theorem cell23_2674572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_2674572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674572 prefixEnd_2674572 := by exact prefixLift 2674572
  have htrace : WordTrace (prefixWord ++ tailWord_2674572) baseStart_2674572 baseEnd_2674572 := by
    simpa [prefixWord, tailWord_2674572, baseEnd_2674572] using wordTrace_append hprefix tailTrace_2674572
  have hstable : (prefixWord ++ tailWord_2674572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674572).length < 2 ^ (prefixWord ++ tailWord_2674572).sum := by decide
  have hdescent : baseEnd_2674572 < baseStart_2674572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674589 : List Nat := [1, 4, 2, 1, 2, 3, 1, 1, 2, 1, 5]
def baseStart_2674589 : Nat := 118140960795 + 2674589 * 2 ^ 59
def prefixEnd_2674589 : Nat := 4983230072969 + 3 ^ 40 * 2674589 * 2
def baseEnd_2674589 : Nat := 1373349710228141391937295

theorem tailTrace_2674589 : CollatzResearch.WordTrace tailWord_2674589 prefixEnd_2674589 1373349710228141391937295 := by
  unfold tailWord_2674589
  simp only [CollatzResearch.WordTrace]
  refine ⟨97550274907428311279922821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65033516604952207519948547 97550274907428311279922821)
  ·
    refine ⟨18290676545142808364985529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97550274907428311279922821 18290676545142808364985529)
    ·
      refine ⟨13718007408857106273739147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18290676545142808364985529 13718007408857106273739147)
      ·
        refine ⟨20577011113285659410608721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13718007408857106273739147 20577011113285659410608721)
        ·
          refine ⟨15432758334964244557956541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20577011113285659410608721 15432758334964244557956541)
          ·
            refine ⟨5787284375611591709233703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15432758334964244557956541 5787284375611591709233703)
            ·
              refine ⟨8680926563417387563850555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5787284375611591709233703 8680926563417387563850555)
              ·
                refine ⟨13021389845126081345775833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8680926563417387563850555 13021389845126081345775833)
                ·
                  refine ⟨9766042383844561009331875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13021389845126081345775833 9766042383844561009331875)
                  ·
                    refine ⟨14649063575766841513997813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9766042383844561009331875 14649063575766841513997813)
                    ·
                      refine ⟨1373349710228141391937295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14649063575766841513997813 1373349710228141391937295)
                      ·
                        rfl

theorem cell23_2674589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_2674589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674589 prefixEnd_2674589 := by exact prefixLift 2674589
  have htrace : WordTrace (prefixWord ++ tailWord_2674589) baseStart_2674589 baseEnd_2674589 := by
    simpa [prefixWord, tailWord_2674589, baseEnd_2674589] using wordTrace_append hprefix tailTrace_2674589
  have hstable : (prefixWord ++ tailWord_2674589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674589).length < 2 ^ (prefixWord ++ tailWord_2674589).sum := by decide
  have hdescent : baseEnd_2674589 < baseStart_2674589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674609 : List Nat := [1, 2, 2, 4, 2, 1, 3, 1, 7]
def baseStart_2674609 : Nat := 118140960795 + 2674609 * 2 ^ 59
def prefixEnd_2674609 : Nat := 4983230072969 + 3 ^ 40 * 2674609 * 2
def baseEnd_2674609 : Nat := 152595553315692368187467

theorem tailTrace_2674609 : CollatzResearch.WordTrace tailWord_2674609 prefixEnd_2674609 152595553315692368187467 := by
  unfold tailWord_2674609
  simp only [CollatzResearch.WordTrace]
  refine ⟨97551004367355854695650881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65034002911570569797100587 97551004367355854695650881)
  ·
    refine ⟨73163253275516891021738161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97551004367355854695650881 73163253275516891021738161)
    ·
      refine ⟨54872439956637668266303621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73163253275516891021738161 54872439956637668266303621)
      ·
        refine ⟨10288582491869562799931929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54872439956637668266303621 10288582491869562799931929)
        ·
          refine ⟨7716436868902172099948947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10288582491869562799931929 7716436868902172099948947)
          ·
            refine ⟨11574655303353258149923421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7716436868902172099948947 11574655303353258149923421)
            ·
              refine ⟨4340495738757471806221283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11574655303353258149923421 4340495738757471806221283)
              ·
                refine ⟨6510743608136207709331925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4340495738757471806221283 6510743608136207709331925)
                ·
                  refine ⟨152595553315692368187467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6510743608136207709331925 152595553315692368187467)
                  ·
                    rfl

theorem cell23_2674609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 7].length) (baseStart_2674609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674609 prefixEnd_2674609 := by exact prefixLift 2674609
  have htrace : WordTrace (prefixWord ++ tailWord_2674609) baseStart_2674609 baseEnd_2674609 := by
    simpa [prefixWord, tailWord_2674609, baseEnd_2674609] using wordTrace_append hprefix tailTrace_2674609
  have hstable : (prefixWord ++ tailWord_2674609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674609).length < 2 ^ (prefixWord ++ tailWord_2674609).sum := by decide
  have hdescent : baseEnd_2674609 < baseStart_2674609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674629 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 4, 5, 2]
def baseStart_2674629 : Nat := 118140960795 + 2674629 * 2 ^ 59
def prefixEnd_2674629 : Nat := 4983230072969 + 3 ^ 40 * 2674629 * 2
def baseEnd_2674629 : Nat := 1373370249454321235437111

theorem tailTrace_2674629 : CollatzResearch.WordTrace tailWord_2674629 prefixEnd_2674629 1373370249454321235437111 := by
  unfold tailWord_2674629
  simp only [CollatzResearch.WordTrace]
  refine ⟨97551733827283398111378941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65034489218188932074252627 97551733827283398111378941)
  ·
    refine ⟨36581900185231274291767103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97551733827283398111378941 36581900185231274291767103)
    ·
      refine ⟨54872850277846911437650655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36581900185231274291767103 54872850277846911437650655)
      ·
        refine ⟨82309275416770367156475983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54872850277846911437650655 82309275416770367156475983)
        ·
          refine ⟨123463913125155550734713975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82309275416770367156475983 123463913125155550734713975)
          ·
            refine ⟨185195869687733326102070963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123463913125155550734713975 185195869687733326102070963)
            ·
              refine ⟨277793804531599989153106445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185195869687733326102070963 277793804531599989153106445)
              ·
                refine ⟨104172676699349995932414917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 277793804531599989153106445 104172676699349995932414917)
                ·
                  refine ⟨19532376881128124237327797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 104172676699349995932414917 19532376881128124237327797)
                  ·
                    refine ⟨1831160332605761647249481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19532376881128124237327797 1831160332605761647249481)
                    ·
                      refine ⟨1373370249454321235437111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1831160332605761647249481 1373370249454321235437111)
                      ·
                        rfl

theorem cell23_2674629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 5, 2].length) (baseStart_2674629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674629 prefixEnd_2674629 := by exact prefixLift 2674629
  have htrace : WordTrace (prefixWord ++ tailWord_2674629) baseStart_2674629 baseEnd_2674629 := by
    simpa [prefixWord, tailWord_2674629, baseEnd_2674629] using wordTrace_append hprefix tailTrace_2674629
  have hstable : (prefixWord ++ tailWord_2674629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674629).length < 2 ^ (prefixWord ++ tailWord_2674629).sum := by decide
  have hdescent : baseEnd_2674629 < baseStart_2674629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674639 : List Nat := [1, 1, 2, 1, 1, 5, 4, 1, 2, 5]
def baseStart_2674639 : Nat := 118140960795 + 2674639 * 2 ^ 59
def prefixEnd_2674639 : Nat := 4983230072969 + 3 ^ 40 * 2674639 * 2
def baseEnd_2674639 : Nat := 457791794753622065437355

theorem tailTrace_2674639 : CollatzResearch.WordTrace tailWord_2674639 prefixEnd_2674639 457791794753622065437355 := by
  unfold tailWord_2674639
  simp only [CollatzResearch.WordTrace]
  refine ⟨97552098557247169819242971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65034732371498113212828647 97552098557247169819242971)
  ·
    refine ⟨146328147835870754728864457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97552098557247169819242971 146328147835870754728864457)
    ·
      refine ⟨109746110876903066046648343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146328147835870754728864457 109746110876903066046648343)
      ·
        refine ⟨164619166315354599069972515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109746110876903066046648343 164619166315354599069972515)
        ·
          refine ⟨246928749473031898604958773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164619166315354599069972515 246928749473031898604958773)
          ·
            refine ⟨23149570263096740494214885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 246928749473031898604958773 23149570263096740494214885)
            ·
              refine ⟨4340544424330638842665291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23149570263096740494214885 4340544424330638842665291)
              ·
                refine ⟨6510816636495958263997937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4340544424330638842665291 6510816636495958263997937)
                ·
                  refine ⟨4883112477371968697998453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6510816636495958263997937 4883112477371968697998453)
                  ·
                    refine ⟨457791794753622065437355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4883112477371968697998453 457791794753622065437355)
                    ·
                      rfl

theorem cell23_2674639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 2, 5].length) (baseStart_2674639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674639 prefixEnd_2674639 := by exact prefixLift 2674639
  have htrace : WordTrace (prefixWord ++ tailWord_2674639) baseStart_2674639 baseEnd_2674639 := by
    simpa [prefixWord, tailWord_2674639, baseEnd_2674639] using wordTrace_append hprefix tailTrace_2674639
  have hstable : (prefixWord ++ tailWord_2674639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674639).length < 2 ^ (prefixWord ++ tailWord_2674639).sum := by decide
  have hdescent : baseEnd_2674639 < baseStart_2674639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674682 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 12]
def baseStart_2674682 : Nat := 118140960795 + 2674682 * 2 ^ 59
def prefixEnd_2674682 : Nat := 4983230072969 + 3 ^ 40 * 2674682 * 2
def baseEnd_2674682 : Nat := 152599718214334392008263

theorem tailTrace_2674682 : CollatzResearch.WordTrace tailWord_2674682 prefixEnd_2674682 152599718214334392008263 := by
  unfold tailWord_2674682
  simp only [CollatzResearch.WordTrace]
  refine ⟨24388416724022847040764575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65035777930727592108705533 24388416724022847040764575)
  ·
    refine ⟨36582625086034270561146863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24388416724022847040764575 36582625086034270561146863)
    ·
      refine ⟨54873937629051405841720295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36582625086034270561146863 54873937629051405841720295)
      ·
        refine ⟨82310906443577108762580443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54873937629051405841720295 82310906443577108762580443)
        ·
          refine ⟨123466359665365663143870665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82310906443577108762580443 123466359665365663143870665)
          ·
            refine ⟨92599769749024247357902999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123466359665365663143870665 92599769749024247357902999)
            ·
              refine ⟨138899654623536371036854499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92599769749024247357902999 138899654623536371036854499)
              ·
                refine ⟨208349481935304556555281749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138899654623536371036854499 208349481935304556555281749)
                ·
                  refine ⟨152599718214334392008263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 208349481935304556555281749 152599718214334392008263)
                  ·
                    rfl

theorem cell23_2674682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 12].length) (baseStart_2674682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674682 prefixEnd_2674682 := by exact prefixLift 2674682
  have htrace : WordTrace (prefixWord ++ tailWord_2674682) baseStart_2674682 baseEnd_2674682 := by
    simpa [prefixWord, tailWord_2674682, baseEnd_2674682] using wordTrace_append hprefix tailTrace_2674682
  have hstable : (prefixWord ++ tailWord_2674682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674682).length < 2 ^ (prefixWord ++ tailWord_2674682).sum := by decide
  have hdescent : baseEnd_2674682 < baseStart_2674682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674694 : List Nat := [6, 2, 1, 2, 1, 1, 2, 3, 5]
def baseStart_2674694 : Nat := 118140960795 + 2674694 * 2 ^ 59
def prefixEnd_2674694 : Nat := 4983230072969 + 3 ^ 40 * 2674694 * 2
def baseEnd_2674694 : Nat := 152600402855207053458257

theorem tailTrace_2674694 : CollatzResearch.WordTrace tailWord_2674694 prefixEnd_2674694 152600402855207053458257 := by
  unfold tailWord_2674694
  simp only [CollatzResearch.WordTrace]
  refine ⟨3048565767876497319140473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 65036069714698609474996757 3048565767876497319140473)
  ·
    refine ⟨2286424325907372989355355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3048565767876497319140473 2286424325907372989355355)
    ·
      refine ⟨3429636488861059484033033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2286424325907372989355355 3429636488861059484033033)
      ·
        refine ⟨2572227366645794613024775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3429636488861059484033033 2572227366645794613024775)
        ·
          refine ⟨3858341049968691919537163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2572227366645794613024775 3858341049968691919537163)
          ·
            refine ⟨5787511574953037879305745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3858341049968691919537163 5787511574953037879305745)
            ·
              refine ⟨4340633681214778409479309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5787511574953037879305745 4340633681214778409479309)
              ·
                refine ⟨1627737630455541903554741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4340633681214778409479309 1627737630455541903554741)
                ·
                  refine ⟨152600402855207053458257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1627737630455541903554741 152600402855207053458257)
                  ·
                    rfl

theorem cell23_2674694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_2674694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674694 prefixEnd_2674694 := by exact prefixLift 2674694
  have htrace : WordTrace (prefixWord ++ tailWord_2674694) baseStart_2674694 baseEnd_2674694 := by
    simpa [prefixWord, tailWord_2674694, baseEnd_2674694] using wordTrace_append hprefix tailTrace_2674694
  have hstable : (prefixWord ++ tailWord_2674694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674694).length < 2 ^ (prefixWord ++ tailWord_2674694).sum := by decide
  have hdescent : baseEnd_2674694 < baseStart_2674694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674716 : List Nat := [2, 2, 3, 1, 3, 1, 3, 2, 6]
def baseStart_2674716 : Nat := 118140960795 + 2674716 * 2 ^ 59
def prefixEnd_2674716 : Nat := 4983230072969 + 3 ^ 40 * 2674716 * 2
def baseEnd_2674716 : Nat := 152601658030140266116579

theorem tailTrace_2674716 : CollatzResearch.WordTrace tailWord_2674716 prefixEnd_2674716 152601658030140266116579 := by
  unfold tailWord_2674716
  simp only [CollatzResearch.WordTrace]
  refine ⟨48777453488984105984898001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65036604651978807979864001 48777453488984105984898001)
  ·
    refine ⟨36583090116738079488673501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48777453488984105984898001 36583090116738079488673501)
    ·
      refine ⟨13718658793776779808252563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36583090116738079488673501 13718658793776779808252563)
      ·
        refine ⟨20577988190665169712378845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13718658793776779808252563 20577988190665169712378845)
        ·
          refine ⟨7716745571499438642142067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20577988190665169712378845 7716745571499438642142067)
          ·
            refine ⟨11575118357249157963213101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7716745571499438642142067 11575118357249157963213101)
            ·
              refine ⟨4340669383968434236204913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11575118357249157963213101 4340669383968434236204913)
              ·
                refine ⟨3255502037976325677153685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4340669383968434236204913 3255502037976325677153685)
                ·
                  refine ⟨152601658030140266116579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3255502037976325677153685 152601658030140266116579)
                  ·
                    rfl

theorem cell23_2674716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 2, 6].length) (baseStart_2674716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674716 prefixEnd_2674716 := by exact prefixLift 2674716
  have htrace : WordTrace (prefixWord ++ tailWord_2674716) baseStart_2674716 baseEnd_2674716 := by
    simpa [prefixWord, tailWord_2674716, baseEnd_2674716] using wordTrace_append hprefix tailTrace_2674716
  have hstable : (prefixWord ++ tailWord_2674716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674716).length < 2 ^ (prefixWord ++ tailWord_2674716).sum := by decide
  have hdescent : baseEnd_2674716 < baseStart_2674716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674736 : List Nat := [2, 1, 1, 1, 2, 5, 1, 2, 1, 5, 2]
def baseStart_2674736 : Nat := 118140960795 + 2674736 * 2 ^ 59
def prefixEnd_2674736 : Nat := 4983230072969 + 3 ^ 40 * 2674736 * 2
def baseEnd_2674736 : Nat := 1373425191884352316799119

theorem tailTrace_2674736 : CollatzResearch.WordTrace tailWord_2674736 prefixEnd_2674736 1373425191884352316799119 := by
  unfold tailWord_2674736
  simp only [CollatzResearch.WordTrace]
  refine ⟨48777818218947877692762031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65037090958597170257016041 48777818218947877692762031)
  ·
    refine ⟨73166727328421816539143047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48777818218947877692762031 73166727328421816539143047)
    ·
      refine ⟨109750090992632724808714571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73166727328421816539143047 109750090992632724808714571)
      ·
        refine ⟨164625136488949087213071857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109750090992632724808714571 164625136488949087213071857)
        ·
          refine ⟨123468852366711815409803893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164625136488949087213071857 123468852366711815409803893)
          ·
            refine ⟨11575204909379232694669115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 123468852366711815409803893 11575204909379232694669115)
            ·
              refine ⟨17362807364068849042003673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11575204909379232694669115 17362807364068849042003673)
              ·
                refine ⟨13022105523051636781502755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17362807364068849042003673 13022105523051636781502755)
                ·
                  refine ⟨19533158284577455172254133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13022105523051636781502755 19533158284577455172254133)
                  ·
                    refine ⟨1831233589179136422398825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19533158284577455172254133 1831233589179136422398825)
                    ·
                      refine ⟨1373425191884352316799119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1831233589179136422398825 1373425191884352316799119)
                      ·
                        rfl

theorem cell23_2674736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 1, 5, 2].length) (baseStart_2674736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674736 prefixEnd_2674736 := by exact prefixLift 2674736
  have htrace : WordTrace (prefixWord ++ tailWord_2674736) baseStart_2674736 baseEnd_2674736 := by
    simpa [prefixWord, tailWord_2674736, baseEnd_2674736] using wordTrace_append hprefix tailTrace_2674736
  have hstable : (prefixWord ++ tailWord_2674736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674736).length < 2 ^ (prefixWord ++ tailWord_2674736).sum := by decide
  have hdescent : baseEnd_2674736 < baseStart_2674736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674753 : List Nat := [1, 2, 5, 1, 2, 1, 2, 1, 1, 5, 2]
def baseStart_2674753 : Nat := 118140960795 + 2674753 * 2 ^ 59
def prefixEnd_2674753 : Nat := 4983230072969 + 3 ^ 40 * 2674753 * 2
def baseEnd_2674753 : Nat := 1373433921055478750286541

theorem tailTrace_2674753 : CollatzResearch.WordTrace tailWord_2674753 prefixEnd_2674753 1373433921055478750286541 := by
  unfold tailWord_2674753
  simp only [CollatzResearch.WordTrace]
  refine ⟨97556256478834167288892913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65037504319222778192595275 97556256478834167288892913)
  ·
    refine ⟨73167192359125625466669685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97556256478834167288892913 73167192359125625466669685)
    ·
      refine ⟨6859424283668027387500283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73167192359125625466669685 6859424283668027387500283)
      ·
        refine ⟨10289136425502041081250425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6859424283668027387500283 10289136425502041081250425)
        ·
          refine ⟨7716852319126530810937819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10289136425502041081250425 7716852319126530810937819)
          ·
            refine ⟨11575278478689796216406729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7716852319126530810937819 11575278478689796216406729)
            ·
              refine ⟨8681458859017347162305047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11575278478689796216406729 8681458859017347162305047)
              ·
                refine ⟨13022188288526020743457571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8681458859017347162305047 13022188288526020743457571)
                ·
                  refine ⟨19533282432789031115186357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13022188288526020743457571 19533282432789031115186357)
                  ·
                    refine ⟨1831245228073971667048721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19533282432789031115186357 1831245228073971667048721)
                    ·
                      refine ⟨1373433921055478750286541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1831245228073971667048721 1373433921055478750286541)
                      ·
                        rfl

theorem cell23_2674753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_2674753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674753 prefixEnd_2674753 := by exact prefixLift 2674753
  have htrace : WordTrace (prefixWord ++ tailWord_2674753) baseStart_2674753 baseEnd_2674753 := by
    simpa [prefixWord, tailWord_2674753, baseEnd_2674753] using wordTrace_append hprefix tailTrace_2674753
  have hstable : (prefixWord ++ tailWord_2674753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674753).length < 2 ^ (prefixWord ++ tailWord_2674753).sum := by decide
  have hdescent : baseEnd_2674753 < baseStart_2674753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674759 : List Nat := [1, 1, 4, 1, 3, 1, 2, 1, 3, 6]
def baseStart_2674759 : Nat := 118140960795 + 2674759 * 2 ^ 59
def prefixEnd_2674759 : Nat := 4983230072969 + 3 ^ 40 * 2674759 * 2
def baseEnd_2674759 : Nat := 457812333979801908937171

theorem tailTrace_2674759 : CollatzResearch.WordTrace tailWord_2674759 prefixEnd_2674759 457812333979801908937171 := by
  unfold tailWord_2674759
  simp only [CollatzResearch.WordTrace]
  refine ⟨97556475316812430313611331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65037650211208286875740887 97556475316812430313611331)
  ·
    refine ⟨146334712975218645470416997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97556475316812430313611331 146334712975218645470416997)
    ·
      refine ⟨27437758682853496025703187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146334712975218645470416997 27437758682853496025703187)
      ·
        refine ⟨41156638024280244038554781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27437758682853496025703187 41156638024280244038554781)
        ·
          refine ⟨15433739259105091514458043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41156638024280244038554781 15433739259105091514458043)
          ·
            refine ⟨23150608888657637271687065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15433739259105091514458043 23150608888657637271687065)
            ·
              refine ⟨17362956666493227953765299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23150608888657637271687065 17362956666493227953765299)
              ·
                refine ⟨26044434999739841930647949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17362956666493227953765299 26044434999739841930647949)
                ·
                  refine ⟨9766663124902440723992981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26044434999739841930647949 9766663124902440723992981)
                  ·
                    refine ⟨457812333979801908937171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9766663124902440723992981 457812333979801908937171)
                    ·
                      rfl

theorem cell23_2674759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_2674759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674759 prefixEnd_2674759 := by exact prefixLift 2674759
  have htrace : WordTrace (prefixWord ++ tailWord_2674759) baseStart_2674759 baseEnd_2674759 := by
    simpa [prefixWord, tailWord_2674759, baseEnd_2674759] using wordTrace_append hprefix tailTrace_2674759
  have hstable : (prefixWord ++ tailWord_2674759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674759).length < 2 ^ (prefixWord ++ tailWord_2674759).sum := by decide
  have hdescent : baseEnd_2674759 < baseStart_2674759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674770 : List Nat := [3, 2, 2, 1, 4, 1, 1, 2, 2, 3, 2]
def baseStart_2674770 : Nat := 118140960795 + 2674770 * 2 ^ 59
def prefixEnd_2674770 : Nat := 4983230072969 + 3 ^ 40 * 2674770 * 2
def baseEnd_2674770 : Nat := 1373442650226605183773963

theorem tailTrace_2674770 : CollatzResearch.WordTrace tailWord_2674770 prefixEnd_2674770 1373442650226605183773963 := by
  unfold tailWord_2674770
  simp only [CollatzResearch.WordTrace]
  refine ⟨24389219129943144798065441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65037917679848386128174509 24389219129943144798065441)
  ·
    refine ⟨18291914347457358598549081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24389219129943144798065441 18291914347457358598549081)
    ·
      refine ⟨13718935760593018948911811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18291914347457358598549081 13718935760593018948911811)
      ·
        refine ⟨20578403640889528423367717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13718935760593018948911811 20578403640889528423367717)
        ·
          refine ⟨3858450682666786579381447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20578403640889528423367717 3858450682666786579381447)
          ·
            refine ⟨5787676024000179869072171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3858450682666786579381447 5787676024000179869072171)
            ·
              refine ⟨8681514036000269803608257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5787676024000179869072171 8681514036000269803608257)
              ·
                refine ⟨6511135527000202352706193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8681514036000269803608257 6511135527000202352706193)
                ·
                  refine ⟨4883351645250151764529645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6511135527000202352706193 4883351645250151764529645)
                  ·
                    refine ⟨1831256866968806911698617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4883351645250151764529645 1831256866968806911698617)
                    ·
                      refine ⟨1373442650226605183773963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1831256866968806911698617 1373442650226605183773963)
                      ·
                        rfl

theorem cell23_2674770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 2, 3, 2].length) (baseStart_2674770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674770 prefixEnd_2674770 := by exact prefixLift 2674770
  have htrace : WordTrace (prefixWord ++ tailWord_2674770) baseStart_2674770 baseEnd_2674770 := by
    simpa [prefixWord, tailWord_2674770, baseEnd_2674770] using wordTrace_append hprefix tailTrace_2674770
  have hstable : (prefixWord ++ tailWord_2674770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674770).length < 2 ^ (prefixWord ++ tailWord_2674770).sum := by decide
  have hdescent : baseEnd_2674770 < baseStart_2674770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674776 : List Nat := [2, 1, 2, 2, 1, 4, 2, 1, 4, 4]
def baseStart_2674776 : Nat := 118140960795 + 2674776 * 2 ^ 59
def prefixEnd_2674776 : Nat := 4983230072969 + 3 ^ 40 * 2674776 * 2
def baseEnd_2674776 : Nat := 457815243703510720099645

theorem tailTrace_2674776 : CollatzResearch.WordTrace tailWord_2674776 prefixEnd_2674776 457815243703510720099645 := by
  unfold tailWord_2674776
  simp only [CollatzResearch.WordTrace]
  refine ⟨48778547678875421108490091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65038063571833894811320121 48778547678875421108490091)
  ·
    refine ⟨73167821518313131662735137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48778547678875421108490091 73167821518313131662735137)
    ·
      refine ⟨54875866138734848747051353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73167821518313131662735137 54875866138734848747051353)
      ·
        refine ⟨41156899604051136560288515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54875866138734848747051353 41156899604051136560288515)
        ·
          refine ⟨61735349406076704840432773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41156899604051136560288515 61735349406076704840432773)
          ·
            refine ⟨11575378013639382157581145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61735349406076704840432773 11575378013639382157581145)
            ·
              refine ⟨8681533510229536618185859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11575378013639382157581145 8681533510229536618185859)
              ·
                refine ⟨13022300265344304927278789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8681533510229536618185859 13022300265344304927278789)
                ·
                  refine ⟨2441681299752057173864773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13022300265344304927278789 2441681299752057173864773)
                  ·
                    refine ⟨457815243703510720099645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2441681299752057173864773 457815243703510720099645)
                    ·
                      rfl

theorem cell23_2674776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 4, 4].length) (baseStart_2674776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674776 prefixEnd_2674776 := by exact prefixLift 2674776
  have htrace : WordTrace (prefixWord ++ tailWord_2674776) baseStart_2674776 baseEnd_2674776 := by
    simpa [prefixWord, tailWord_2674776, baseEnd_2674776] using wordTrace_append hprefix tailTrace_2674776
  have hstable : (prefixWord ++ tailWord_2674776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674776).length < 2 ^ (prefixWord ++ tailWord_2674776).sum := by decide
  have hdescent : baseEnd_2674776 < baseStart_2674776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674783 : List Nat := [1, 1, 2, 3, 1, 1, 2, 5, 3, 2, 2]
def baseStart_2674783 : Nat := 118140960795 + 2674783 * 2 ^ 59
def prefixEnd_2674783 : Nat := 4983230072969 + 3 ^ 40 * 2674783 * 2
def baseEnd_2674783 : Nat := 1373449325475113632911403

theorem tailTrace_2674783 : CollatzResearch.WordTrace tailWord_2674783 prefixEnd_2674783 1373449325475113632911403 := by
  unfold tailWord_2674783
  simp only [CollatzResearch.WordTrace]
  refine ⟨97557350668725482412485003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65038233779150321608323335 97557350668725482412485003)
  ·
    refine ⟨146336026003088223618727505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97557350668725482412485003 146336026003088223618727505)
    ·
      refine ⟨109752019502316167714045629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146336026003088223618727505 109752019502316167714045629)
      ·
        refine ⟨41157007313368562892767111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109752019502316167714045629 41157007313368562892767111)
        ·
          refine ⟨61735510970052844339150667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41157007313368562892767111 61735510970052844339150667)
          ·
            refine ⟨92603266455079266508726001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61735510970052844339150667 92603266455079266508726001)
            ·
              refine ⟨69452449841309449881544501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92603266455079266508726001 69452449841309449881544501)
              ·
                refine ⟨6511167172622760926394797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69452449841309449881544501 6511167172622760926394797)
                ·
                  refine ⟨2441687689733535347398049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6511167172622760926394797 2441687689733535347398049)
                  ·
                    refine ⟨1831265767300151510548537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2441687689733535347398049 1831265767300151510548537)
                    ·
                      refine ⟨1373449325475113632911403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1831265767300151510548537 1373449325475113632911403)
                      ·
                        rfl

theorem cell23_2674783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 3, 2, 2].length) (baseStart_2674783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674783 prefixEnd_2674783 := by exact prefixLift 2674783
  have htrace : WordTrace (prefixWord ++ tailWord_2674783) baseStart_2674783 baseEnd_2674783 := by
    simpa [prefixWord, tailWord_2674783, baseEnd_2674783] using wordTrace_append hprefix tailTrace_2674783
  have hstable : (prefixWord ++ tailWord_2674783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674783).length < 2 ^ (prefixWord ++ tailWord_2674783).sum := by decide
  have hdescent : baseEnd_2674783 < baseStart_2674783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674789 : List Nat := [1, 3, 1, 3, 2, 2, 1, 10]
def baseStart_2674789 : Nat := 118140960795 + 2674789 * 2 ^ 59
def prefixEnd_2674789 : Nat := 4983230072969 + 3 ^ 40 * 2674789 * 2
def baseEnd_2674789 : Nat := 50868607642927429979125

theorem tailTrace_2674789 : CollatzResearch.WordTrace tailWord_2674789 prefixEnd_2674789 50868607642927429979125 := by
  unfold tailWord_2674789
  simp only [CollatzResearch.WordTrace]
  refine ⟨97557569506703745437203421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65038379671135830291468947 97557569506703745437203421)
  ·
    refine ⟨36584088565013904538951283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97557569506703745437203421 36584088565013904538951283)
    ·
      refine ⟨54876132847520856808426925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36584088565013904538951283 54876132847520856808426925)
      ·
        refine ⟨20578549817820321303160097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54876132847520856808426925 20578549817820321303160097)
        ·
          refine ⟨15433912363365240977370073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20578549817820321303160097 15433912363365240977370073)
          ·
            refine ⟨11575434272523930733027555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15433912363365240977370073 11575434272523930733027555)
            ·
              refine ⟨17363151408785896099541333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11575434272523930733027555 17363151408785896099541333)
              ·
                refine ⟨50868607642927429979125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 17363151408785896099541333 50868607642927429979125)
                ·
                  rfl

theorem cell23_2674789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 10].length) (baseStart_2674789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674789 prefixEnd_2674789 := by exact prefixLift 2674789
  have htrace : WordTrace (prefixWord ++ tailWord_2674789) baseStart_2674789 baseEnd_2674789 := by
    simpa [prefixWord, tailWord_2674789, baseEnd_2674789] using wordTrace_append hprefix tailTrace_2674789
  have hstable : (prefixWord ++ tailWord_2674789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674789).length < 2 ^ (prefixWord ++ tailWord_2674789).sum := by decide
  have hdescent : baseEnd_2674789 < baseStart_2674789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674806 : List Nat := [5, 1, 1, 2, 1, 2, 2, 9]
def baseStart_2674806 : Nat := 118140960795 + 2674806 * 2 ^ 59
def prefixEnd_2674806 : Nat := 4983230072969 + 3 ^ 40 * 2674806 * 2
def baseEnd_2674806 : Nat := 50868930945561742330511

theorem tailTrace_2674806 : CollatzResearch.WordTrace tailWord_2674806 prefixEnd_2674806 50868930945561742330511 := by
  unfold tailWord_2674806
  simp only [CollatzResearch.WordTrace]
  refine ⟨6097386846727634833785767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65038793031761438227048181 6097386846727634833785767)
  ·
    refine ⟨9146080270091452250678651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6097386846727634833785767 9146080270091452250678651)
    ·
      refine ⟨13719120405137178376017977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9146080270091452250678651 13719120405137178376017977)
      ·
        refine ⟨10289340303852883782013483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13719120405137178376017977 10289340303852883782013483)
        ·
          refine ⟨15434010455779325673020225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10289340303852883782013483 15434010455779325673020225)
          ·
            refine ⟨11575507841834494254765169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15434010455779325673020225 11575507841834494254765169)
            ·
              refine ⟨8681630881375870691073877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11575507841834494254765169 8681630881375870691073877)
              ·
                refine ⟨50868930945561742330511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8681630881375870691073877 50868930945561742330511)
                ·
                  rfl

theorem cell23_2674806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 9].length) (baseStart_2674806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674806 prefixEnd_2674806 := by exact prefixLift 2674806
  have htrace : WordTrace (prefixWord ++ tailWord_2674806) baseStart_2674806 baseEnd_2674806 := by
    simpa [prefixWord, tailWord_2674806, baseEnd_2674806] using wordTrace_append hprefix tailTrace_2674806
  have hstable : (prefixWord ++ tailWord_2674806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674806).length < 2 ^ (prefixWord ++ tailWord_2674806).sum := by decide
  have hdescent : baseEnd_2674806 < baseStart_2674806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674820 : List Nat := [2, 3, 2, 1, 2, 1, 5, 1, 1, 2, 3]
def baseStart_2674820 : Nat := 118140960795 + 2674820 * 2 ^ 59
def prefixEnd_2674820 : Nat := 4983230072969 + 3 ^ 40 * 2674820 * 2
def baseEnd_2674820 : Nat := 1373468324259329988148733

theorem tailTrace_2674820 : CollatzResearch.WordTrace tailWord_2674820 prefixEnd_2674820 1373468324259329988148733 := by
  unfold tailWord_2674820
  simp only [CollatzResearch.WordTrace]
  refine ⟨48779350084795718865790957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65039133446394291821054609 48779350084795718865790957)
  ·
    refine ⟨18292256281798394574671609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48779350084795718865790957 18292256281798394574671609)
    ·
      refine ⟨13719192211348795931003707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18292256281798394574671609 13719192211348795931003707)
      ·
        refine ⟨20578788317023193896505561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13719192211348795931003707 20578788317023193896505561)
        ·
          refine ⟨15434091237767395422379171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20578788317023193896505561 15434091237767395422379171)
          ·
            refine ⟨23151136856651093133568757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15434091237767395422379171 23151136856651093133568757)
            ·
              refine ⟨2170419080311039981272071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23151136856651093133568757 2170419080311039981272071)
              ·
                refine ⟨3255628620466559971908107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2170419080311039981272071 3255628620466559971908107)
                ·
                  refine ⟨4883442930699839957862161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3255628620466559971908107 4883442930699839957862161)
                  ·
                    refine ⟨3662582198024879968396621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4883442930699839957862161 3662582198024879968396621)
                    ·
                      refine ⟨1373468324259329988148733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3662582198024879968396621 1373468324259329988148733)
                      ·
                        rfl

theorem cell23_2674820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 1, 1, 2, 3].length) (baseStart_2674820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674820 prefixEnd_2674820 := by exact prefixLift 2674820
  have htrace : WordTrace (prefixWord ++ tailWord_2674820) baseStart_2674820 baseEnd_2674820 := by
    simpa [prefixWord, tailWord_2674820, baseEnd_2674820] using wordTrace_append hprefix tailTrace_2674820
  have hstable : (prefixWord ++ tailWord_2674820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674820).length < 2 ^ (prefixWord ++ tailWord_2674820).sum := by decide
  have hdescent : baseEnd_2674820 < baseStart_2674820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674850 : List Nat := [3, 3, 1, 3, 1, 2, 2, 1, 1, 3, 3]
def baseStart_2674850 : Nat := 118140960795 + 2674850 * 2 ^ 59
def prefixEnd_2674850 : Nat := 4983230072969 + 3 ^ 40 * 2674850 * 2
def baseEnd_2674850 : Nat := 1373483728678964870773595

theorem tailTrace_2674850 : CollatzResearch.WordTrace tailWord_2674850 prefixEnd_2674850 1373483728678964870773595 := by
  unfold tailWord_2674850
  simp only [CollatzResearch.WordTrace]
  refine ⟨24389948589870688213793501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65039862906321835236782669 24389948589870688213793501)
  ·
    refine ⟨9146230721201508080172563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24389948589870688213793501 9146230721201508080172563)
    ·
      refine ⟨13719346081802262120258845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9146230721201508080172563 13719346081802262120258845)
      ·
        refine ⟨5144754780675848295097067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13719346081802262120258845 5144754780675848295097067)
        ·
          refine ⟨7717132171013772442645601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5144754780675848295097067 7717132171013772442645601)
          ·
            refine ⟨5787849128260329331984201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7717132171013772442645601 5787849128260329331984201)
            ·
              refine ⟨4340886846195246998988151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5787849128260329331984201 4340886846195246998988151)
              ·
                refine ⟨6511330269292870498482227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4340886846195246998988151 6511330269292870498482227)
                ·
                  refine ⟨9766995403939305747723341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6511330269292870498482227 9766995403939305747723341)
                  ·
                    refine ⟨3662623276477239655396253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9766995403939305747723341 3662623276477239655396253)
                    ·
                      refine ⟨1373483728678964870773595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3662623276477239655396253 1373483728678964870773595)
                      ·
                        rfl

theorem cell23_2674850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_2674850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674850 prefixEnd_2674850 := by exact prefixLift 2674850
  have htrace : WordTrace (prefixWord ++ tailWord_2674850) baseStart_2674850 baseEnd_2674850 := by
    simpa [prefixWord, tailWord_2674850, baseEnd_2674850] using wordTrace_append hprefix tailTrace_2674850
  have hstable : (prefixWord ++ tailWord_2674850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674850).length < 2 ^ (prefixWord ++ tailWord_2674850).sum := by decide
  have hdescent : baseEnd_2674850 < baseStart_2674850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674868 : List Nat := [2, 5, 3, 1, 2, 1, 2, 1, 1, 1, 4]
def baseStart_2674868 : Nat := 118140960795 + 2674868 * 2 ^ 59
def prefixEnd_2674868 : Nat := 4983230072969 + 3 ^ 40 * 2674868 * 2
def baseEnd_2674868 : Nat := 1373492971330745800348513

theorem tailTrace_2674868 : CollatzResearch.WordTrace tailWord_2674868 prefixEnd_2674868 1373492971330745800348513 := by
  unfold tailWord_2674868
  simp only [CollatzResearch.WordTrace]
  refine ⟨48780225436708770964664629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65040300582278361286219505 48780225436708770964664629)
  ·
    refine ⟨4573146134691447277937309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48780225436708770964664629 4573146134691447277937309)
    ·
      refine ⟨1714929800509292729226491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4573146134691447277937309 1714929800509292729226491)
      ·
        refine ⟨2572394700763939093839737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1714929800509292729226491 2572394700763939093839737)
        ·
          refine ⟨1929296025572954320379803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2572394700763939093839737 1929296025572954320379803)
          ·
            refine ⟨2893944038359431480569705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1929296025572954320379803 2893944038359431480569705)
            ·
              refine ⟨2170458028769573610427279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2893944038359431480569705 2170458028769573610427279)
              ·
                refine ⟨3255687043154360415640919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2170458028769573610427279 3255687043154360415640919)
                ·
                  refine ⟨4883530564731540623461379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3255687043154360415640919 4883530564731540623461379)
                  ·
                    refine ⟨7325295847097310935192069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4883530564731540623461379 7325295847097310935192069)
                    ·
                      refine ⟨1373492971330745800348513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7325295847097310935192069 1373492971330745800348513)
                      ·
                        rfl

theorem cell23_2674868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_2674868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674868 prefixEnd_2674868 := by exact prefixLift 2674868
  have htrace : WordTrace (prefixWord ++ tailWord_2674868) baseStart_2674868 baseEnd_2674868 := by
    simpa [prefixWord, tailWord_2674868, baseEnd_2674868] using wordTrace_append hprefix tailTrace_2674868
  have hstable : (prefixWord ++ tailWord_2674868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674868).length < 2 ^ (prefixWord ++ tailWord_2674868).sum := by decide
  have hdescent : baseEnd_2674868 < baseStart_2674868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674873 : List Nat := [1, 2, 1, 4, 1, 2, 1, 4, 1, 4, 2]
def baseStart_2674873 : Nat := 118140960795 + 2674873 * 2 ^ 59
def prefixEnd_2674873 : Nat := 4983230072969 + 3 ^ 40 * 2674873 * 2
def baseEnd_2674873 : Nat := 1373495538734018280785989

theorem tailTrace_2674873 : CollatzResearch.WordTrace tailWord_2674873 prefixEnd_2674873 1373495538734018280785989 := by
  unfold tailWord_2674873
  simp only [CollatzResearch.WordTrace]
  refine ⟨97560633238399427783261273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65040422158932951855507515 97560633238399427783261273)
  ·
    refine ⟨73170474928799570837445955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97560633238399427783261273 73170474928799570837445955)
    ·
      refine ⟨109755712393199356256168933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73170474928799570837445955 109755712393199356256168933)
      ·
        refine ⟨20579196073724879298031675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109755712393199356256168933 20579196073724879298031675)
        ·
          refine ⟨30868794110587318947047513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20579196073724879298031675 30868794110587318947047513)
          ·
            refine ⟨23151595582940489210285635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30868794110587318947047513 23151595582940489210285635)
            ·
              refine ⟨34727393374410733815428453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23151595582940489210285635 34727393374410733815428453)
              ·
                refine ⟨6511386257702012590392835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34727393374410733815428453 6511386257702012590392835)
                ·
                  refine ⟨9767079386553018885589253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6511386257702012590392835 9767079386553018885589253)
                  ·
                    refine ⟨1831327384978691041047985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9767079386553018885589253 1831327384978691041047985)
                    ·
                      refine ⟨1373495538734018280785989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1831327384978691041047985 1373495538734018280785989)
                      ·
                        rfl

theorem cell23_2674873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 4, 2].length) (baseStart_2674873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674873 prefixEnd_2674873 := by exact prefixLift 2674873
  have htrace : WordTrace (prefixWord ++ tailWord_2674873) baseStart_2674873 baseEnd_2674873 := by
    simpa [prefixWord, tailWord_2674873, baseEnd_2674873] using wordTrace_append hprefix tailTrace_2674873
  have hstable : (prefixWord ++ tailWord_2674873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674873).length < 2 ^ (prefixWord ++ tailWord_2674873).sum := by decide
  have hdescent : baseEnd_2674873 < baseStart_2674873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674879 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 11]
def baseStart_2674879 : Nat := 118140960795 + 2674879 * 2 ^ 59
def prefixEnd_2674879 : Nat := 4983230072969 + 3 ^ 40 * 2674879 * 2
def baseEnd_2674879 : Nat := 152610957735327250812329

theorem tailTrace_2674879 : CollatzResearch.WordTrace tailWord_2674879 prefixEnd_2674879 152610957735327250812329 := by
  unfold tailWord_2674879
  simp only [CollatzResearch.WordTrace]
  refine ⟨97560852076377690807979691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65040568050918460538653127 97560852076377690807979691)
  ·
    refine ⟨146341278114566536211969537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97560852076377690807979691 146341278114566536211969537)
    ·
      refine ⟨109755958585924902158977153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146341278114566536211969537 109755958585924902158977153)
      ·
        refine ⟨82316968939443676619232865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109755958585924902158977153 82316968939443676619232865)
        ·
          refine ⟨61737726704582757464424649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82316968939443676619232865 61737726704582757464424649)
          ·
            refine ⟨46303295028437068098318487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61737726704582757464424649 46303295028437068098318487)
            ·
              refine ⟨69454942542655602147477731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46303295028437068098318487 69454942542655602147477731)
              ·
                refine ⟨104182413813983403221216597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69454942542655602147477731 104182413813983403221216597)
                ·
                  refine ⟨152610957735327250812329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 104182413813983403221216597 152610957735327250812329)
                  ·
                    rfl

theorem cell23_2674879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 11].length) (baseStart_2674879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674879 prefixEnd_2674879 := by exact prefixLift 2674879
  have htrace : WordTrace (prefixWord ++ tailWord_2674879) baseStart_2674879 baseEnd_2674879 := by
    simpa [prefixWord, tailWord_2674879, baseEnd_2674879] using wordTrace_append hprefix tailTrace_2674879
  have hstable : (prefixWord ++ tailWord_2674879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674879).length < 2 ^ (prefixWord ++ tailWord_2674879).sum := by decide
  have hdescent : baseEnd_2674879 < baseStart_2674879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674889 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 1, 1, 9]
def baseStart_2674889 : Nat := 118140960795 + 2674889 * 2 ^ 59
def prefixEnd_2674889 : Nat := 4983230072969 + 3 ^ 40 * 2674889 * 2
def baseEnd_2674889 : Nat := 1373503754424490218185915

theorem tailTrace_2674889 : CollatzResearch.WordTrace tailWord_2674889 prefixEnd_2674889 1373503754424490218185915 := by
  unfold tailWord_2674889
  simp only [CollatzResearch.WordTrace]
  refine ⟨97561216806341462515843721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65040811204227641677229147 97561216806341462515843721)
  ·
    refine ⟨73170912604756096886882791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97561216806341462515843721 73170912604756096886882791)
    ·
      refine ⟨109756368907134145330324187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73170912604756096886882791 109756368907134145330324187)
      ·
        refine ⟨164634553360701217995486281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109756368907134145330324187 164634553360701217995486281)
        ·
          refine ⟨123475915020525913496614711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164634553360701217995486281 123475915020525913496614711)
          ·
            refine ⟨185213872530788870244922067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123475915020525913496614711 185213872530788870244922067)
            ·
              refine ⟨277820808796183305367383101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185213872530788870244922067 277820808796183305367383101)
              ·
                refine ⟨104182803298568739512768663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 277820808796183305367383101 104182803298568739512768663)
                ·
                  refine ⟨156274204947853109269152995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104182803298568739512768663 156274204947853109269152995)
                  ·
                    refine ⟨234411307421779663903729493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 156274204947853109269152995 234411307421779663903729493)
                    ·
                      refine ⟨1373503754424490218185915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 234411307421779663903729493 1373503754424490218185915)
                      ·
                        rfl

theorem cell23_2674889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 1, 9].length) (baseStart_2674889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674889 prefixEnd_2674889 := by exact prefixLift 2674889
  have htrace : WordTrace (prefixWord ++ tailWord_2674889) baseStart_2674889 baseEnd_2674889 := by
    simpa [prefixWord, tailWord_2674889, baseEnd_2674889] using wordTrace_append hprefix tailTrace_2674889
  have hstable : (prefixWord ++ tailWord_2674889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674889).length < 2 ^ (prefixWord ++ tailWord_2674889).sum := by decide
  have hdescent : baseEnd_2674889 < baseStart_2674889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674890 : List Nat := [3, 1, 2, 1, 3, 1, 3, 1, 4, 2, 2]
def baseStart_2674890 : Nat := 118140960795 + 2674890 * 2 ^ 59
def prefixEnd_2674890 : Nat := 4983230072969 + 3 ^ 40 * 2674890 * 2
def baseEnd_2674890 : Nat := 1373504267905144714273411

theorem tailTrace_2674890 : CollatzResearch.WordTrace tailWord_2674890 prefixEnd_2674890 1373504267905144714273411 := by
  unfold tailWord_2674890
  simp only [CollatzResearch.WordTrace]
  refine ⟨24390313319834459921657531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65040835519558559791086749 24390313319834459921657531)
  ·
    refine ⟨36585469979751689882486297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24390313319834459921657531 36585469979751689882486297)
    ·
      refine ⟨27439102484813767411864723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36585469979751689882486297 27439102484813767411864723)
      ·
        refine ⟨41158653727220651117797085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27439102484813767411864723 41158653727220651117797085)
        ·
          refine ⟨15434495147707744169173907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41158653727220651117797085 15434495147707744169173907)
          ·
            refine ⟨23151742721561616253760861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15434495147707744169173907 23151742721561616253760861)
            ·
              refine ⟨8681903520585606095160323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23151742721561616253760861 8681903520585606095160323)
              ·
                refine ⟨13022855280878409142740485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8681903520585606095160323 13022855280878409142740485)
                ·
                  refine ⟨2441785365164701714263841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13022855280878409142740485 2441785365164701714263841)
                  ·
                    refine ⟨1831339023873526285697881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2441785365164701714263841 1831339023873526285697881)
                    ·
                      refine ⟨1373504267905144714273411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1831339023873526285697881 1373504267905144714273411)
                      ·
                        rfl

theorem cell23_2674890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 4, 2, 2].length) (baseStart_2674890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674890 prefixEnd_2674890 := by exact prefixLift 2674890
  have htrace : WordTrace (prefixWord ++ tailWord_2674890) baseStart_2674890 baseEnd_2674890 := by
    simpa [prefixWord, tailWord_2674890, baseEnd_2674890] using wordTrace_append hprefix tailTrace_2674890
  have hstable : (prefixWord ++ tailWord_2674890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674890).length < 2 ^ (prefixWord ++ tailWord_2674890).sum := by decide
  have hdescent : baseEnd_2674890 < baseStart_2674890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674899 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 8]
def baseStart_2674899 : Nat := 118140960795 + 2674899 * 2 ^ 59
def prefixEnd_2674899 : Nat := 4983230072969 + 3 ^ 40 * 2674899 * 2
def baseEnd_2674899 : Nat := 1373508889231035179060869

theorem tailTrace_2674899 : CollatzResearch.WordTrace tailWord_2674899 prefixEnd_2674899 1373508889231035179060869 := by
  unfold tailWord_2674899
  simp only [CollatzResearch.WordTrace]
  refine ⟨97561581536305234223707751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65041054357536822815805167 97561581536305234223707751)
  ·
    refine ⟨146342372304457851335561627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97561581536305234223707751 146342372304457851335561627)
    ·
      refine ⟨219513558456686777003342441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146342372304457851335561627 219513558456686777003342441)
      ·
        refine ⟨164635168842515082752506831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219513558456686777003342441 164635168842515082752506831)
        ·
          refine ⟨246952753263772624128760247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164635168842515082752506831 246952753263772624128760247)
          ·
            refine ⟨370429129895658936193140371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246952753263772624128760247 370429129895658936193140371)
            ·
              refine ⟨555643694843488404289710557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 370429129895658936193140371 555643694843488404289710557)
              ·
                refine ⟨208366385566308151608641459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 555643694843488404289710557 208366385566308151608641459)
                ·
                  refine ⟨312549578349462227412962189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 208366385566308151608641459 312549578349462227412962189)
                  ·
                    refine ⟨117206091881048335279860821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 312549578349462227412962189 117206091881048335279860821)
                    ·
                      refine ⟨1373508889231035179060869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 117206091881048335279860821 1373508889231035179060869)
                      ·
                        rfl

theorem cell23_2674899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 8].length) (baseStart_2674899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674899 prefixEnd_2674899 := by exact prefixLift 2674899
  have htrace : WordTrace (prefixWord ++ tailWord_2674899) baseStart_2674899 baseEnd_2674899 := by
    simpa [prefixWord, tailWord_2674899, baseEnd_2674899] using wordTrace_append hprefix tailTrace_2674899
  have hstable : (prefixWord ++ tailWord_2674899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674899).length < 2 ^ (prefixWord ++ tailWord_2674899).sum := by decide
  have hdescent : baseEnd_2674899 < baseStart_2674899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674930 : List Nat := [3, 2, 1, 3, 2, 1, 3, 3, 5]
def baseStart_2674930 : Nat := 118140960795 + 2674930 * 2 ^ 59
def prefixEnd_2674930 : Nat := 4983230072969 + 3 ^ 40 * 2674930 * 2
def baseEnd_2674930 : Nat := 152613867459036061974803

theorem tailTrace_2674930 : CollatzResearch.WordTrace tailWord_2674930 prefixEnd_2674930 152613867459036061974803 := by
  unfold tailWord_2674930
  simp only [CollatzResearch.WordTrace]
  refine ⟨24390678049798231629521561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65041808132795284345390829 24390678049798231629521561)
  ·
    refine ⟨18293008537348673722141171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24390678049798231629521561 18293008537348673722141171)
    ·
      refine ⟨27439512806023010583211757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18293008537348673722141171 27439512806023010583211757)
      ·
        refine ⟨10289817302258628968704409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27439512806023010583211757 10289817302258628968704409)
        ·
          refine ⟨7717362976693971726528307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10289817302258628968704409 7717362976693971726528307)
          ·
            refine ⟨11576044465040957589792461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7717362976693971726528307 11576044465040957589792461)
            ·
              refine ⟨4341016674390359096172173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11576044465040957589792461 4341016674390359096172173)
              ·
                refine ⟨1627881252896384661064565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4341016674390359096172173 1627881252896384661064565)
                ·
                  refine ⟨152613867459036061974803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1627881252896384661064565 152613867459036061974803)
                  ·
                    rfl

theorem cell23_2674930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 3, 5].length) (baseStart_2674930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674930 prefixEnd_2674930 := by exact prefixLift 2674930
  have htrace : WordTrace (prefixWord ++ tailWord_2674930) baseStart_2674930 baseEnd_2674930 := by
    simpa [prefixWord, tailWord_2674930, baseEnd_2674930] using wordTrace_append hprefix tailTrace_2674930
  have hstable : (prefixWord ++ tailWord_2674930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674930).length < 2 ^ (prefixWord ++ tailWord_2674930).sum := by decide
  have hdescent : baseEnd_2674930 < baseStart_2674930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674963 : List Nat := [1, 1, 1, 2, 1, 3, 1, 5, 2, 4, 2]
def baseStart_2674963 : Nat := 118140960795 + 2674963 * 2 ^ 59
def prefixEnd_2674963 : Nat := 4983230072969 + 3 ^ 40 * 2674963 * 2
def baseEnd_2674963 : Nat := 1373541751992922928660575

theorem tailTrace_2674963 : CollatzResearch.WordTrace tailWord_2674963 prefixEnd_2674963 1373541751992922928660575 := by
  unfold tailWord_2674963
  simp only [CollatzResearch.WordTrace]
  refine ⟨97563915808073373154037543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65042610538715582102691695 97563915808073373154037543)
  ·
    refine ⟨146345873712110059731056315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97563915808073373154037543 146345873712110059731056315)
    ·
      refine ⟨219518810568165089596584473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146345873712110059731056315 219518810568165089596584473)
      ·
        refine ⟨164639107926123817197438355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219518810568165089596584473 164639107926123817197438355)
        ·
          refine ⟨246958661889185725796157533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164639107926123817197438355 246958661889185725796157533)
          ·
            refine ⟨92609498208444647173559075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 246958661889185725796157533 92609498208444647173559075)
            ·
              refine ⟨138914247312666970760338613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92609498208444647173559075 138914247312666970760338613)
              ·
                refine ⟨13023210685562528508781745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 138914247312666970760338613 13023210685562528508781745)
                ·
                  refine ⟨9767408014171896381586309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13023210685562528508781745 9767408014171896381586309)
                  ·
                    refine ⟨1831389002657230571547433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9767408014171896381586309 1831389002657230571547433)
                    ·
                      refine ⟨1373541751992922928660575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1831389002657230571547433 1373541751992922928660575)
                      ·
                        rfl

theorem cell23_2674963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 4, 2].length) (baseStart_2674963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674963 prefixEnd_2674963 := by exact prefixLift 2674963
  have htrace : WordTrace (prefixWord ++ tailWord_2674963) baseStart_2674963 baseEnd_2674963 := by
    simpa [prefixWord, tailWord_2674963, baseEnd_2674963] using wordTrace_append hprefix tailTrace_2674963
  have hstable : (prefixWord ++ tailWord_2674963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674963).length < 2 ^ (prefixWord ++ tailWord_2674963).sum := by decide
  have hdescent : baseEnd_2674963 < baseStart_2674963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674980 : List Nat := [2, 3, 1, 3, 1, 3, 2, 1, 2, 1, 4]
def baseStart_2674980 : Nat := 118140960795 + 2674980 * 2 ^ 59
def prefixEnd_2674980 : Nat := 4983230072969 + 3 ^ 40 * 2674980 * 2
def baseEnd_2674980 : Nat := 1373550481164049362147997

theorem tailTrace_2674980 : CollatzResearch.WordTrace tailWord_2674980 prefixEnd_2674980 1373550481164049362147997 := by
  unfold tailWord_2674980
  simp only [CollatzResearch.WordTrace]
  refine ⟨48782267924505892528703197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65043023899341190038270929 48782267924505892528703197)
  ·
    refine ⟨18293350471689709698263699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48782267924505892528703197 18293350471689709698263699)
    ·
      refine ⟨27440025707534564547395549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18293350471689709698263699 27440025707534564547395549)
      ·
        refine ⟨10290009640325461705273331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27440025707534564547395549 10290009640325461705273331)
        ·
          refine ⟨15435014460488192557909997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10290009640325461705273331 15435014460488192557909997)
          ·
            refine ⟨5788130422683072209216249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15435014460488192557909997 5788130422683072209216249)
            ·
              refine ⟨4341097817012304156912187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5788130422683072209216249 4341097817012304156912187)
              ·
                refine ⟨6511646725518456235368281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4341097817012304156912187 6511646725518456235368281)
                ·
                  refine ⟨4883735044138842176526211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6511646725518456235368281 4883735044138842176526211)
                  ·
                    refine ⟨7325602566208263264789317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4883735044138842176526211 7325602566208263264789317)
                    ·
                      refine ⟨1373550481164049362147997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7325602566208263264789317 1373550481164049362147997)
                      ·
                        rfl

theorem cell23_2674980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_2674980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2674980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2674980 prefixEnd_2674980 := by exact prefixLift 2674980
  have htrace : WordTrace (prefixWord ++ tailWord_2674980) baseStart_2674980 baseEnd_2674980 := by
    simpa [prefixWord, tailWord_2674980, baseEnd_2674980] using wordTrace_append hprefix tailTrace_2674980
  have hstable : (prefixWord ++ tailWord_2674980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674980).length < 2 ^ (prefixWord ++ tailWord_2674980).sum := by decide
  have hdescent : baseEnd_2674980 < baseStart_2674980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675033 : List Nat := [1, 2, 1, 2, 2, 2, 1, 6, 1, 5]
def baseStart_2675033 : Nat := 118140960795 + 2675033 * 2 ^ 59
def prefixEnd_2675033 : Nat := 4983230072969 + 3 ^ 40 * 2675033 * 2
def baseEnd_2675033 : Nat := 457859231879579218261751

theorem tailTrace_2675033 : CollatzResearch.WordTrace tailWord_2675033 prefixEnd_2675033 457859231879579218261751 := by
  unfold tailWord_2675033
  simp only [CollatzResearch.WordTrace]
  refine ⟨97566468917819775109085753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65044312611879850072723835 97566468917819775109085753)
  ·
    refine ⟨73174851688364831331814315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97566468917819775109085753 73174851688364831331814315)
    ·
      refine ⟨109762277532547246997721473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73174851688364831331814315 109762277532547246997721473)
      ·
        refine ⟨82321708149410435248291105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109762277532547246997721473 82321708149410435248291105)
        ·
          refine ⟨61741281112057826436218329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82321708149410435248291105 61741281112057826436218329)
          ·
            refine ⟨46305960834043369827163747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61741281112057826436218329 46305960834043369827163747)
            ·
              refine ⟨69458941251065054740745621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46305960834043369827163747 69458941251065054740745621)
              ·
                refine ⟨3255887871143674440972451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 69458941251065054740745621 3255887871143674440972451)
                ·
                  refine ⟨4883831806715511661458677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3255887871143674440972451 4883831806715511661458677)
                  ·
                    refine ⟨457859231879579218261751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4883831806715511661458677 457859231879579218261751)
                    ·
                      rfl

theorem cell23_2675033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 6, 1, 5].length) (baseStart_2675033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2675033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2675033 prefixEnd_2675033 := by exact prefixLift 2675033
  have htrace : WordTrace (prefixWord ++ tailWord_2675033) baseStart_2675033 baseEnd_2675033 := by
    simpa [prefixWord, tailWord_2675033, baseEnd_2675033] using wordTrace_append hprefix tailTrace_2675033
  have hstable : (prefixWord ++ tailWord_2675033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675033).length < 2 ^ (prefixWord ++ tailWord_2675033).sum := by decide
  have hdescent : baseEnd_2675033 < baseStart_2675033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675083 : List Nat := [1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 6]
def baseStart_2675083 : Nat := 118140960795 + 2675083 * 2 ^ 59
def prefixEnd_2675083 : Nat := 4983230072969 + 3 ^ 40 * 2675083 * 2
def baseEnd_2675083 : Nat := 1373603369671462459160023

theorem tailTrace_2675083 : CollatzResearch.WordTrace tailWord_2675083 prefixEnd_2675083 1373603369671462459160023 := by
  unfold tailWord_2675083
  simp only [CollatzResearch.WordTrace]
  refine ⟨97568292567638633648405903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65045528378425755765603935 97568292567638633648405903)
  ·
    refine ⟨146352438851457950472608855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97568292567638633648405903 146352438851457950472608855)
    ·
      refine ⟨219528658277186925708913283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146352438851457950472608855 219528658277186925708913283)
      ·
        refine ⟨329292987415780388563369925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219528658277186925708913283 329292987415780388563369925)
        ·
          refine ⟨61742435140458822855631861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 329292987415780388563369925 61742435140458822855631861)
          ·
            refine ⟨5788353294418014642715487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61742435140458822855631861 5788353294418014642715487)
            ·
              refine ⟨8682529941627021964073231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5788353294418014642715487 8682529941627021964073231)
              ·
                refine ⟨13023794912440532946109847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8682529941627021964073231 13023794912440532946109847)
                ·
                  refine ⟨19535692368660799419164771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13023794912440532946109847 19535692368660799419164771)
                  ·
                    refine ⟨29303538552991199128747157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19535692368660799419164771 29303538552991199128747157)
                    ·
                      refine ⟨1373603369671462459160023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29303538552991199128747157 1373603369671462459160023)
                      ·
                        rfl

theorem cell23_2675083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 6].length) (baseStart_2675083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2675083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2675083 prefixEnd_2675083 := by exact prefixLift 2675083
  have htrace : WordTrace (prefixWord ++ tailWord_2675083) baseStart_2675083 baseEnd_2675083 := by
    simpa [prefixWord, tailWord_2675083, baseEnd_2675083] using wordTrace_append hprefix tailTrace_2675083
  have hstable : (prefixWord ++ tailWord_2675083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675083).length < 2 ^ (prefixWord ++ tailWord_2675083).sum := by decide
  have hdescent : baseEnd_2675083 < baseStart_2675083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675154 : List Nat := [3, 2, 2, 4, 1, 1, 1, 2, 1, 3, 3]
def baseStart_2675154 : Nat := 118140960795 + 2675154 * 2 ^ 59
def prefixEnd_2675154 : Nat := 4983230072969 + 3 ^ 40 * 2675154 * 2
def baseEnd_2675154 : Nat := 1373639826797931681372197

theorem tailTrace_2675154 : CollatzResearch.WordTrace tailWord_2675154 prefixEnd_2675154 1373639826797931681372197 := by
  unfold tailWord_2675154
  simp only [CollatzResearch.WordTrace]
  refine ⟨24392720537595353193560129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65047254766920941849493677 24392720537595353193560129)
  ·
    refine ⟨18294540403196514895170097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24392720537595353193560129 18294540403196514895170097)
    ·
      refine ⟨13720905302397386171377573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18294540403196514895170097 13720905302397386171377573)
      ·
        refine ⟨2572669744199509907133295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13720905302397386171377573 2572669744199509907133295)
        ·
          refine ⟨3859004616299264860699943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2572669744199509907133295 3859004616299264860699943)
          ·
            refine ⟨5788506924448897291049915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3859004616299264860699943 5788506924448897291049915)
            ·
              refine ⟨8682760386673345936574873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5788506924448897291049915 8682760386673345936574873)
              ·
                refine ⟨6512070290005009452431155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8682760386673345936574873 6512070290005009452431155)
                ·
                  refine ⟨9768105435007514178646733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6512070290005009452431155 9768105435007514178646733)
                  ·
                    refine ⟨3663039538127817816992525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9768105435007514178646733 3663039538127817816992525)
                    ·
                      refine ⟨1373639826797931681372197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3663039538127817816992525 1373639826797931681372197)
                      ·
                        rfl

theorem cell23_2675154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_2675154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2675154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2675154 prefixEnd_2675154 := by exact prefixLift 2675154
  have htrace : WordTrace (prefixWord ++ tailWord_2675154) baseStart_2675154 baseEnd_2675154 := by
    simpa [prefixWord, tailWord_2675154, baseEnd_2675154] using wordTrace_append hprefix tailTrace_2675154
  have hstable : (prefixWord ++ tailWord_2675154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675154).length < 2 ^ (prefixWord ++ tailWord_2675154).sum := by decide
  have hdescent : baseEnd_2675154 < baseStart_2675154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675183 : List Nat := [1, 1, 2, 1, 4, 1, 1, 5, 7]
def baseStart_2675183 : Nat := 118140960795 + 2675183 * 2 ^ 59
def prefixEnd_2675183 : Nat := 4983230072969 + 3 ^ 40 * 2675183 * 2
def baseEnd_2675183 : Nat := 152628301970768007545507

theorem tailTrace_2675183 : CollatzResearch.WordTrace tailWord_2675183 prefixEnd_2675183 152628301970768007545507 := by
  unfold tailWord_2675183
  simp only [CollatzResearch.WordTrace]
  refine ⟨97571939867276350727046203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65047959911517567151364135 97571939867276350727046203)
  ·
    refine ⟨146357909800914526090569305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97571939867276350727046203 146357909800914526090569305)
    ·
      refine ⟨109768432350685894567926979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146357909800914526090569305 109768432350685894567926979)
      ·
        refine ⟨164652648526028841851890469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109768432350685894567926979 164652648526028841851890469)
        ·
          refine ⟨30872371598630407847229463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 164652648526028841851890469 30872371598630407847229463)
          ·
            refine ⟨46308557397945611770844195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30872371598630407847229463 46308557397945611770844195)
            ·
              refine ⟨69462836096918417656266293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46308557397945611770844195 69462836096918417656266293)
              ·
                refine ⟨6512140884086101655274965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69462836096918417656266293 6512140884086101655274965)
                ·
                  refine ⟨152628301970768007545507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6512140884086101655274965 152628301970768007545507)
                  ·
                    rfl

theorem cell23_2675183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 7].length) (baseStart_2675183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2675183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2675183 prefixEnd_2675183 := by exact prefixLift 2675183
  have htrace : WordTrace (prefixWord ++ tailWord_2675183) baseStart_2675183 baseEnd_2675183 := by
    simpa [prefixWord, tailWord_2675183, baseEnd_2675183] using wordTrace_append hprefix tailTrace_2675183
  have hstable : (prefixWord ++ tailWord_2675183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675183).length < 2 ^ (prefixWord ++ tailWord_2675183).sum := by decide
  have hdescent : baseEnd_2675183 < baseStart_2675183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675210 : List Nat := [3, 1, 2, 2, 2, 1, 1, 2, 1, 5, 3]
def baseStart_2675210 : Nat := 118140960795 + 2675210 * 2 ^ 59
def prefixEnd_2675210 : Nat := 4983230072969 + 3 ^ 40 * 2675210 * 2
def baseEnd_2675210 : Nat := 1373668581714583462271939

theorem tailTrace_2675210 : CollatzResearch.WordTrace tailWord_2675210 prefixEnd_2675210 1373668581714583462271939 := by
  unfold tailWord_2675210
  simp only [CollatzResearch.WordTrace]
  refine ⟨24393231159544633584569771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65048616425452356225519389 24393231159544633584569771)
  ·
    refine ⟨36589846739316950376854657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24393231159544633584569771 36589846739316950376854657)
    ·
      refine ⟨27442385054487712782640993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36589846739316950376854657 27442385054487712782640993)
      ·
        refine ⟨20581788790865784586980745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27442385054487712782640993 20581788790865784586980745)
        ·
          refine ⟨15436341593149338440235559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20581788790865784586980745 15436341593149338440235559)
          ·
            refine ⟨23154512389724007660353339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15436341593149338440235559 23154512389724007660353339)
            ·
              refine ⟨34731768584586011490530009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23154512389724007660353339 34731768584586011490530009)
              ·
                refine ⟨26048826438439508617897507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34731768584586011490530009 26048826438439508617897507)
                ·
                  refine ⟨39073239657659262926846261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26048826438439508617897507 39073239657659262926846261)
                  ·
                    refine ⟨3663116217905555899391837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39073239657659262926846261 3663116217905555899391837)
                    ·
                      refine ⟨1373668581714583462271939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3663116217905555899391837 1373668581714583462271939)
                      ·
                        rfl

theorem cell23_2675210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_2675210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2675210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2675210 prefixEnd_2675210 := by exact prefixLift 2675210
  have htrace : WordTrace (prefixWord ++ tailWord_2675210) baseStart_2675210 baseEnd_2675210 := by
    simpa [prefixWord, tailWord_2675210, baseEnd_2675210] using wordTrace_append hprefix tailTrace_2675210
  have hstable : (prefixWord ++ tailWord_2675210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675210).length < 2 ^ (prefixWord ++ tailWord_2675210).sum := by decide
  have hdescent : baseEnd_2675210 < baseStart_2675210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675245 : List Nat := [1, 5, 4, 1, 1, 2, 1, 1, 1, 4, 2]
def baseStart_2675245 : Nat := 118140960795 + 2675245 * 2 ^ 59
def prefixEnd_2675245 : Nat := 4983230072969 + 3 ^ 40 * 2675245 * 2
def baseEnd_2675245 : Nat := 1373686553537490825334279

theorem tailTrace_2675245 : CollatzResearch.WordTrace tailWord_2675245 prefixEnd_2675245 1373686553537490825334279 := by
  unfold tailWord_2675245
  simp only [CollatzResearch.WordTrace]
  refine ⟨97574201193051735315803189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65049467462034490210535459 97574201193051735315803189)
  ·
    refine ⟨9147581361848600185856549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97574201193051735315803189 9147581361848600185856549)
    ·
      refine ⟨1715171505346612534848103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9147581361848600185856549 1715171505346612534848103)
      ·
        refine ⟨2572757258019918802272155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1715171505346612534848103 2572757258019918802272155)
        ·
          refine ⟨3859135887029878203408233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2572757258019918802272155 3859135887029878203408233)
          ·
            refine ⟨2894351915272408652556175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3859135887029878203408233 2894351915272408652556175)
            ·
              refine ⟨4341527872908612978834263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2894351915272408652556175 4341527872908612978834263)
              ·
                refine ⟨6512291809362919468251395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4341527872908612978834263 6512291809362919468251395)
                ·
                  refine ⟨9768437714044379202377093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6512291809362919468251395 9768437714044379202377093)
                  ·
                    refine ⟨1831582071383321100445705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9768437714044379202377093 1831582071383321100445705)
                    ·
                      refine ⟨1373686553537490825334279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1831582071383321100445705 1373686553537490825334279)
                      ·
                        rfl

theorem cell23_2675245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_2675245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2675245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2675245 prefixEnd_2675245 := by exact prefixLift 2675245
  have htrace : WordTrace (prefixWord ++ tailWord_2675245) baseStart_2675245 baseEnd_2675245 := by
    simpa [prefixWord, tailWord_2675245, baseEnd_2675245] using wordTrace_append hprefix tailTrace_2675245
  have hstable : (prefixWord ++ tailWord_2675245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675245).length < 2 ^ (prefixWord ++ tailWord_2675245).sum := by decide
  have hdescent : baseEnd_2675245 < baseStart_2675245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675250 : List Nat := [3, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4]
def baseStart_2675250 : Nat := 118140960795 + 2675250 * 2 ^ 59
def prefixEnd_2675250 : Nat := 4983230072969 + 3 ^ 40 * 2675250 * 2
def baseEnd_2675250 : Nat := 1373689120940763305771755

theorem tailTrace_2675250 : CollatzResearch.WordTrace tailWord_2675250 prefixEnd_2675250 1373689120940763305771755 := by
  unfold tailWord_2675250
  simp only [CollatzResearch.WordTrace]
  refine ⟨24393595889508405292433801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65049589038689080779823469 24393595889508405292433801)
  ·
    refine ⟨18295196917131303969325351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24393595889508405292433801 18295196917131303969325351)
    ·
      refine ⟨27442795375696955953988027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18295196917131303969325351 27442795375696955953988027)
      ·
        refine ⟨41164193063545433930982041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27442795375696955953988027 41164193063545433930982041)
        ·
          refine ⟨30873144797659075448236531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41164193063545433930982041 30873144797659075448236531)
          ·
            refine ⟨46309717196488613172354797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30873144797659075448236531 46309717196488613172354797)
            ·
              refine ⟨17366143948683229939633049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46309717196488613172354797 17366143948683229939633049)
              ·
                refine ⟨13024607961512422454724787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17366143948683229939633049 13024607961512422454724787)
                ·
                  refine ⟨19536911942268633682087181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13024607961512422454724787 19536911942268633682087181)
                  ·
                    refine ⟨7326341978350737630782693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19536911942268633682087181 7326341978350737630782693)
                    ·
                      refine ⟨1373689120940763305771755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7326341978350737630782693 1373689120940763305771755)
                      ·
                        rfl

theorem cell23_2675250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_2675250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2675250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2675250 prefixEnd_2675250 := by exact prefixLift 2675250
  have htrace : WordTrace (prefixWord ++ tailWord_2675250) baseStart_2675250 baseEnd_2675250 := by
    simpa [prefixWord, tailWord_2675250, baseEnd_2675250] using wordTrace_append hprefix tailTrace_2675250
  have hstable : (prefixWord ++ tailWord_2675250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675250).length < 2 ^ (prefixWord ++ tailWord_2675250).sum := by decide
  have hdescent : baseEnd_2675250 < baseStart_2675250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675287 : List Nat := [1, 1, 3, 2, 2, 2, 3, 2, 2, 2, 3]
def baseStart_2675287 : Nat := 118140960795 + 2675287 * 2 ^ 59
def prefixEnd_2675287 : Nat := 4983230072969 + 3 ^ 40 * 2675287 * 2
def baseEnd_2675287 : Nat := 1373708119724979661009085

theorem tailTrace_2675287 : CollatzResearch.WordTrace tailWord_2675287 prefixEnd_2675287 1373708119724979661009085 := by
  unfold tailWord_2675287
  simp only [CollatzResearch.WordTrace]
  refine ⟨97575733058899576488832115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65050488705933050992554743 97575733058899576488832115)
  ·
    refine ⟨146363599588349364733248173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97575733058899576488832115 146363599588349364733248173)
    ·
      refine ⟨54886349845631011774968065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146363599588349364733248173 54886349845631011774968065)
      ·
        refine ⟨41164762384223258831226049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54886349845631011774968065 41164762384223258831226049)
        ·
          refine ⟨30873571788167444123419537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41164762384223258831226049 30873571788167444123419537)
          ·
            refine ⟨23155178841125583092564653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30873571788167444123419537 23155178841125583092564653)
            ·
              refine ⟨8683192065422093659711745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23155178841125583092564653 8683192065422093659711745)
              ·
                refine ⟨6512394049066570244783809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8683192065422093659711745 6512394049066570244783809)
                ·
                  refine ⟨4884295536799927683587857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6512394049066570244783809 4884295536799927683587857)
                  ·
                    refine ⟨3663221652599945762690893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4884295536799927683587857 3663221652599945762690893)
                    ·
                      refine ⟨1373708119724979661009085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3663221652599945762690893 1373708119724979661009085)
                      ·
                        rfl

theorem cell23_2675287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 2, 2, 3].length) (baseStart_2675287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2675287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2675287 prefixEnd_2675287 := by exact prefixLift 2675287
  have htrace : WordTrace (prefixWord ++ tailWord_2675287) baseStart_2675287 baseEnd_2675287 := by
    simpa [prefixWord, tailWord_2675287, baseEnd_2675287] using wordTrace_append hprefix tailTrace_2675287
  have hstable : (prefixWord ++ tailWord_2675287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675287).length < 2 ^ (prefixWord ++ tailWord_2675287).sum := by decide
  have hdescent : baseEnd_2675287 < baseStart_2675287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675320 : List Nat := [2, 1, 2, 1, 1, 1, 2, 5, 3, 5]
def baseStart_2675320 : Nat := 118140960795 + 2675320 * 2 ^ 59
def prefixEnd_2675320 : Nat := 4983230072969 + 3 ^ 40 * 2675320 * 2
def baseEnd_2675320 : Nat := 457908354862192677298811

theorem tailTrace_2675320 : CollatzResearch.WordTrace tailWord_2675320 prefixEnd_2675320 457908354862192677298811 := by
  unfold tailWord_2675320
  simp only [CollatzResearch.WordTrace]
  refine ⟨48788468333890011562391707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65051291111853348749855609 48788468333890011562391707)
  ·
    refine ⟨73182702500835017343587561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48788468333890011562391707 73182702500835017343587561)
    ·
      refine ⟨54887026875626263007690671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73182702500835017343587561 54887026875626263007690671)
      ·
        refine ⟨82330540313439394511536007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54887026875626263007690671 82330540313439394511536007)
        ·
          refine ⟨123495810470159091767304011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82330540313439394511536007 123495810470159091767304011)
          ·
            refine ⟨185243715705238637650956017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123495810470159091767304011 185243715705238637650956017)
            ·
              refine ⟨138932786778928978238217013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185243715705238637650956017 138932786778928978238217013)
              ·
                refine ⟨13024948760524591709832845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 138932786778928978238217013 13024948760524591709832845)
                ·
                  refine ⟨4884355785196721891187317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13024948760524591709832845 4884355785196721891187317)
                  ·
                    refine ⟨457908354862192677298811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4884355785196721891187317 457908354862192677298811)
                    ·
                      rfl

theorem cell23_2675320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 3, 5].length) (baseStart_2675320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2675320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2675320 prefixEnd_2675320 := by exact prefixLift 2675320
  have htrace : WordTrace (prefixWord ++ tailWord_2675320) baseStart_2675320 baseEnd_2675320 := by
    simpa [prefixWord, tailWord_2675320, baseEnd_2675320] using wordTrace_append hprefix tailTrace_2675320
  have hstable : (prefixWord ++ tailWord_2675320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675320).length < 2 ^ (prefixWord ++ tailWord_2675320).sum := by decide
  have hdescent : baseEnd_2675320 < baseStart_2675320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675351 : List Nat := [1, 1, 3, 3, 2, 1, 3, 4, 1, 1, 3]
def baseStart_2675351 : Nat := 118140960795 + 2675351 * 2 ^ 59
def prefixEnd_2675351 : Nat := 4983230072969 + 3 ^ 40 * 2675351 * 2
def baseEnd_2675351 : Nat := 1373740982486867410608791

theorem tailTrace_2675351 : CollatzResearch.WordTrace tailWord_2675351 prefixEnd_2675351 1373740982486867410608791 := by
  unfold tailWord_2675351
  simp only [CollatzResearch.WordTrace]
  refine ⟨97578067330667715419161907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65052044887111810279441271 97578067330667715419161907)
  ·
    refine ⟨146367100996001573128742861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97578067330667715419161907 146367100996001573128742861)
    ·
      refine ⟨54887662873500589923278573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146367100996001573128742861 54887662873500589923278573)
      ·
        refine ⟨20582873577562721221229465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54887662873500589923278573 20582873577562721221229465)
        ·
          refine ⟨15437155183172040915922099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20582873577562721221229465 15437155183172040915922099)
          ·
            refine ⟨23155732774758061373883149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15437155183172040915922099 23155732774758061373883149)
            ·
              refine ⟨8683399790534273015206181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23155732774758061373883149 8683399790534273015206181)
              ·
                refine ⟨1628137460725176190351159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8683399790534273015206181 1628137460725176190351159)
                ·
                  refine ⟨2442206191087764285526739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1628137460725176190351159 2442206191087764285526739)
                  ·
                    refine ⟨3663309286631646428290109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2442206191087764285526739 3663309286631646428290109)
                    ·
                      refine ⟨1373740982486867410608791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3663309286631646428290109 1373740982486867410608791)
                      ·
                        rfl

theorem cell23_2675351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 4, 1, 1, 3].length) (baseStart_2675351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2675351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2675351 prefixEnd_2675351 := by exact prefixLift 2675351
  have htrace : WordTrace (prefixWord ++ tailWord_2675351) baseStart_2675351 baseEnd_2675351 := by
    simpa [prefixWord, tailWord_2675351, baseEnd_2675351] using wordTrace_append hprefix tailTrace_2675351
  have hstable : (prefixWord ++ tailWord_2675351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675351).length < 2 ^ (prefixWord ++ tailWord_2675351).sum := by decide
  have hdescent : baseEnd_2675351 < baseStart_2675351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675357 : List Nat := [1, 4, 2, 1, 1, 1, 3, 2, 3, 1, 4]
def baseStart_2675357 : Nat := 118140960795 + 2675357 * 2 ^ 59
def prefixEnd_2675357 : Nat := 4983230072969 + 3 ^ 40 * 2675357 * 2
def baseEnd_2675357 : Nat := 1373744063370794387133763

theorem tailTrace_2675357 : CollatzResearch.WordTrace tailWord_2675357 prefixEnd_2675357 1373744063370794387133763 := by
  unfold tailWord_2675357
  simp only [CollatzResearch.WordTrace]
  refine ⟨97578286168645978443880325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65052190779097318962586883 97578286168645978443880325)
  ·
    refine ⟨18295928656621120958227561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97578286168645978443880325 18295928656621120958227561)
    ·
      refine ⟨13721946492465840718670671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18295928656621120958227561 13721946492465840718670671)
      ·
        refine ⟨20582919738698761078006007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13721946492465840718670671 20582919738698761078006007)
        ·
          refine ⟨30874379608048141617009011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20582919738698761078006007 30874379608048141617009011)
          ·
            refine ⟨46311569412072212425513517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30874379608048141617009011 46311569412072212425513517)
            ·
              refine ⟨17366838529527079659567569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46311569412072212425513517 17366838529527079659567569)
              ·
                refine ⟨13025128897145309744675677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17366838529527079659567569 13025128897145309744675677)
                ·
                  refine ⟨4884423336429491154253379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13025128897145309744675677 4884423336429491154253379)
                  ·
                    refine ⟨7326635004644236731380069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4884423336429491154253379 7326635004644236731380069)
                    ·
                      refine ⟨1373744063370794387133763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7326635004644236731380069 1373744063370794387133763)
                      ·
                        rfl

theorem cell23_2675357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_2675357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2675357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2675357 prefixEnd_2675357 := by exact prefixLift 2675357
  have htrace : WordTrace (prefixWord ++ tailWord_2675357) baseStart_2675357 baseEnd_2675357 := by
    simpa [prefixWord, tailWord_2675357, baseEnd_2675357] using wordTrace_append hprefix tailTrace_2675357
  have hstable : (prefixWord ++ tailWord_2675357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675357).length < 2 ^ (prefixWord ++ tailWord_2675357).sum := by decide
  have hdescent : baseEnd_2675357 < baseStart_2675357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675391 : List Nat := [1, 1, 2, 2, 2, 6, 2, 1, 1, 1, 4]
def baseStart_2675391 : Nat := 118140960795 + 2675391 * 2 ^ 59
def prefixEnd_2675391 : Nat := 4983230072969 + 3 ^ 40 * 2675391 * 2
def baseEnd_2675391 : Nat := 1373761521713047254108607

theorem tailTrace_2675391 : CollatzResearch.WordTrace tailWord_2675391 prefixEnd_2675391 1373761521713047254108607 := by
  unfold tailWord_2675391
  simp only [CollatzResearch.WordTrace]
  refine ⟨97579526250522802250618027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65053017500348534833745351 97579526250522802250618027)
  ·
    refine ⟨146369289375784203375927041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97579526250522802250618027 146369289375784203375927041)
    ·
      refine ⟨109776967031838152531945281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146369289375784203375927041 109776967031838152531945281)
      ·
        refine ⟨82332725273878614398958961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109776967031838152531945281 82332725273878614398958961)
        ·
          refine ⟨61749543955408960799219221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82332725273878614398958961 61749543955408960799219221)
          ·
            refine ⟨2894509872909795037463401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 61749543955408960799219221 2894509872909795037463401)
            ·
              refine ⟨2170882404682346278097551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2894509872909795037463401 2170882404682346278097551)
              ·
                refine ⟨3256323607023519417146327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2170882404682346278097551 3256323607023519417146327)
                ·
                  refine ⟨4884485410535279125719491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3256323607023519417146327 4884485410535279125719491)
                  ·
                    refine ⟨7326728115802918688579237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4884485410535279125719491 7326728115802918688579237)
                    ·
                      refine ⟨1373761521713047254108607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7326728115802918688579237 1373761521713047254108607)
                      ·
                        rfl

theorem cell23_2675391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 1, 1, 1, 4].length) (baseStart_2675391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2675391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2675391 prefixEnd_2675391 := by exact prefixLift 2675391
  have htrace : WordTrace (prefixWord ++ tailWord_2675391) baseStart_2675391 baseEnd_2675391 := by
    simpa [prefixWord, tailWord_2675391, baseEnd_2675391] using wordTrace_append hprefix tailTrace_2675391
  have hstable : (prefixWord ++ tailWord_2675391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675391).length < 2 ^ (prefixWord ++ tailWord_2675391).sum := by decide
  have hdescent : baseEnd_2675391 < baseStart_2675391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675437 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 1, 4, 5]
def baseStart_2675437 : Nat := 118140960795 + 2675437 * 2 ^ 59
def prefixEnd_2675437 : Nat := 4983230072969 + 3 ^ 40 * 2675437 * 2
def baseEnd_2675437 : Nat := 1373785141823154074133395

theorem tailTrace_2675437 : CollatzResearch.WordTrace tailWord_2675437 prefixEnd_2675437 1373785141823154074133395 := by
  unfold tailWord_2675437
  simp only [CollatzResearch.WordTrace]
  refine ⟨97581204008356152106792565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65054136005570768071195043 97581204008356152106792565)
  ·
    refine ⟨9148237875783389260011803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97581204008356152106792565 9148237875783389260011803)
    ·
      refine ⟨13722356813675083890017705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9148237875783389260011803 13722356813675083890017705)
      ·
        refine ⟨10291767610256312917513279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13722356813675083890017705 10291767610256312917513279)
        ·
          refine ⟨15437651415384469376269919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10291767610256312917513279 15437651415384469376269919)
          ·
            refine ⟨23156477123076704064404879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15437651415384469376269919 23156477123076704064404879)
            ·
              refine ⟨34734715684615056096607319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23156477123076704064404879 34734715684615056096607319)
              ·
                refine ⟨52102073526922584144910979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34734715684615056096607319 52102073526922584144910979)
                ·
                  refine ⟨78153110290383876217366469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52102073526922584144910979 78153110290383876217366469)
                  ·
                    refine ⟨14653708179446976790756213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 78153110290383876217366469 14653708179446976790756213)
                    ·
                      refine ⟨1373785141823154074133395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14653708179446976790756213 1373785141823154074133395)
                      ·
                        rfl

theorem cell23_2675437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_2675437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2675437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2675437 prefixEnd_2675437 := by exact prefixLift 2675437
  have htrace : WordTrace (prefixWord ++ tailWord_2675437) baseStart_2675437 baseEnd_2675437 := by
    simpa [prefixWord, tailWord_2675437, baseEnd_2675437] using wordTrace_append hprefix tailTrace_2675437
  have hstable : (prefixWord ++ tailWord_2675437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675437).length < 2 ^ (prefixWord ++ tailWord_2675437).sum := by decide
  have hdescent : baseEnd_2675437 < baseStart_2675437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675467 : List Nat := [1, 1, 1, 1, 5, 1, 1, 3, 2, 4, 3]
def baseStart_2675467 : Nat := 118140960795 + 2675467 * 2 ^ 59
def prefixEnd_2675467 : Nat := 4983230072969 + 3 ^ 40 * 2675467 * 2
def baseEnd_2675467 : Nat := 1373800546242788956758257

theorem tailTrace_2675467 : CollatzResearch.WordTrace tailWord_2675467 prefixEnd_2675467 1373800546242788956758257 := by
  unfold tailWord_2675467
  simp only [CollatzResearch.WordTrace]
  refine ⟨97582298198247467230384655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65054865465498311486923103 97582298198247467230384655)
  ·
    refine ⟨146373447297371200845576983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97582298198247467230384655 146373447297371200845576983)
    ·
      refine ⟨219560170946056801268365475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146373447297371200845576983 219560170946056801268365475)
      ·
        refine ⟨329340256419085201902548213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219560170946056801268365475 329340256419085201902548213)
        ·
          refine ⟨30875649039289237678363895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 329340256419085201902548213 30875649039289237678363895)
          ·
            refine ⟨46313473558933856517545843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30875649039289237678363895 46313473558933856517545843)
            ·
              refine ⟨69470210338400784776318765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46313473558933856517545843 69470210338400784776318765)
              ·
                refine ⟨26051328876900294291119537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69470210338400784776318765 26051328876900294291119537)
                ·
                  refine ⟨19538496657675220718339653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26051328876900294291119537 19538496657675220718339653)
                  ·
                    refine ⟨3663468123314103884688685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19538496657675220718339653 3663468123314103884688685)
                    ·
                      refine ⟨1373800546242788956758257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3663468123314103884688685 1373800546242788956758257)
                      ·
                        rfl

theorem cell23_2675467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 4, 3].length) (baseStart_2675467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2675467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2675467 prefixEnd_2675467 := by exact prefixLift 2675467
  have htrace : WordTrace (prefixWord ++ tailWord_2675467) baseStart_2675467 baseEnd_2675467 := by
    simpa [prefixWord, tailWord_2675467, baseEnd_2675467] using wordTrace_append hprefix tailTrace_2675467
  have hstable : (prefixWord ++ tailWord_2675467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675467).length < 2 ^ (prefixWord ++ tailWord_2675467).sum := by decide
  have hdescent : baseEnd_2675467 < baseStart_2675467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675477 : List Nat := [1, 3, 2, 1, 2, 2, 2, 1, 1, 4, 4]
def baseStart_2675477 : Nat := 118140960795 + 2675477 * 2 ^ 59
def prefixEnd_2675477 : Nat := 4983230072969 + 3 ^ 40 * 2675477 * 2
def baseEnd_2675477 : Nat := 1373805681049333917633211

theorem tailTrace_2675477 : CollatzResearch.WordTrace tailWord_2675477 prefixEnd_2675477 1373805681049333917633211 := by
  unfold tailWord_2675477
  simp only [CollatzResearch.WordTrace]
  refine ⟨97582662928211238938248685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65055108618807492625499123 97582662928211238938248685)
  ·
    refine ⟨36593498598079214601843257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97582662928211238938248685 36593498598079214601843257)
    ·
      refine ⟨27445123948559410951382443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36593498598079214601843257 27445123948559410951382443)
      ·
        refine ⟨41167685922839116427073665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27445123948559410951382443 41167685922839116427073665)
        ·
          refine ⟨30875764442129337320305249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41167685922839116427073665 30875764442129337320305249)
          ·
            refine ⟨23156823331597002990228937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30875764442129337320305249 23156823331597002990228937)
            ·
              refine ⟨17367617498697752242671703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23156823331597002990228937 17367617498697752242671703)
              ·
                refine ⟨26051426248046628364007555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17367617498697752242671703 26051426248046628364007555)
                ·
                  refine ⟨39077139372069942546011333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26051426248046628364007555 39077139372069942546011333)
                  ·
                    refine ⟨7326963632263114227377125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39077139372069942546011333 7326963632263114227377125)
                    ·
                      refine ⟨1373805681049333917633211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7326963632263114227377125 1373805681049333917633211)
                      ·
                        rfl

theorem cell23_2675477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_2675477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2675477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2675477 prefixEnd_2675477 := by exact prefixLift 2675477
  have htrace : WordTrace (prefixWord ++ tailWord_2675477) baseStart_2675477 baseEnd_2675477 := by
    simpa [prefixWord, tailWord_2675477, baseEnd_2675477] using wordTrace_append hprefix tailTrace_2675477
  have hstable : (prefixWord ++ tailWord_2675477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675477).length < 2 ^ (prefixWord ++ tailWord_2675477).sum := by decide
  have hdescent : baseEnd_2675477 < baseStart_2675477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675497 : List Nat := [1, 2, 1, 1, 1, 1, 1, 6, 1, 5, 3]
def baseStart_2675497 : Nat := 118140960795 + 2675497 * 2 ^ 59
def prefixEnd_2675497 : Nat := 4983230072969 + 3 ^ 40 * 2675497 * 2
def baseEnd_2675497 : Nat := 1373815950662423839383119

theorem tailTrace_2675497 : CollatzResearch.WordTrace tailWord_2675497 prefixEnd_2675497 1373815950662423839383119 := by
  unfold tailWord_2675497
  simp only [CollatzResearch.WordTrace]
  refine ⟨97583392388138782353976745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65055594925425854902651163 97583392388138782353976745)
  ·
    refine ⟨73187544291104086765482559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97583392388138782353976745 73187544291104086765482559)
    ·
      refine ⟨109781316436656130148223839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73187544291104086765482559 109781316436656130148223839)
      ·
        refine ⟨164671974654984195222335759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109781316436656130148223839 164671974654984195222335759)
        ·
          refine ⟨247007961982476292833503639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164671974654984195222335759 247007961982476292833503639)
          ·
            refine ⟨370511942973714439250255459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247007961982476292833503639 370511942973714439250255459)
            ·
              refine ⟨555767914460571658875383189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 370511942973714439250255459 555767914460571658875383189)
              ·
                refine ⟨26051620990339296509783587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 555767914460571658875383189 26051620990339296509783587)
                ·
                  refine ⟨39077431485508944764675381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26051620990339296509783587 39077431485508944764675381)
                  ·
                    refine ⟨3663509201766463571688317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39077431485508944764675381 3663509201766463571688317)
                    ·
                      refine ⟨1373815950662423839383119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3663509201766463571688317 1373815950662423839383119)
                      ·
                        rfl

theorem cell23_2675497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 5, 3].length) (baseStart_2675497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2675497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2675497 prefixEnd_2675497 := by exact prefixLift 2675497
  have htrace : WordTrace (prefixWord ++ tailWord_2675497) baseStart_2675497 baseEnd_2675497 := by
    simpa [prefixWord, tailWord_2675497, baseEnd_2675497] using wordTrace_append hprefix tailTrace_2675497
  have hstable : (prefixWord ++ tailWord_2675497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675497).length < 2 ^ (prefixWord ++ tailWord_2675497).sum := by decide
  have hdescent : baseEnd_2675497 < baseStart_2675497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675564 : List Nat := [2, 2, 1, 1, 4, 1, 1, 2, 5, 4]
def baseStart_2675564 : Nat := 118140960795 + 2675564 * 2 ^ 59
def prefixEnd_2675564 : Nat := 4983230072969 + 3 ^ 40 * 2675564 * 2
def baseEnd_2675564 : Nat := 457950117955425025748437

theorem tailTrace_2675564 : CollatzResearch.WordTrace tailWord_2675564 prefixEnd_2675564 457950117955425025748437 := by
  unfold tailWord_2675564
  simp only [CollatzResearch.WordTrace]
  refine ⟨48792918039448026398332873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65057224052597368531110497 48792918039448026398332873)
  ·
    refine ⟨36594688529586019798749655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48792918039448026398332873 36594688529586019798749655)
    ·
      refine ⟨54892032794379029698124483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36594688529586019798749655 54892032794379029698124483)
      ·
        refine ⟨82338049191568544547186725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54892032794379029698124483 82338049191568544547186725)
        ·
          refine ⟨15438384223419102102597511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82338049191568544547186725 15438384223419102102597511)
          ·
            refine ⟨23157576335128653153896267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15438384223419102102597511 23157576335128653153896267)
            ·
              refine ⟨34736364502692979730844401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23157576335128653153896267 34736364502692979730844401)
              ·
                refine ⟨26052273377019734798133301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34736364502692979730844401 26052273377019734798133301)
                ·
                  refine ⟨2442400629095600137324997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26052273377019734798133301 2442400629095600137324997)
                  ·
                    refine ⟨457950117955425025748437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2442400629095600137324997 457950117955425025748437)
                    ·
                      rfl

theorem cell23_2675564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 4].length) (baseStart_2675564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2675564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2675564 prefixEnd_2675564 := by exact prefixLift 2675564
  have htrace : WordTrace (prefixWord ++ tailWord_2675564) baseStart_2675564 baseEnd_2675564 := by
    simpa [prefixWord, tailWord_2675564, baseEnd_2675564] using wordTrace_append hprefix tailTrace_2675564
  have hstable : (prefixWord ++ tailWord_2675564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675564).length < 2 ^ (prefixWord ++ tailWord_2675564).sum := by decide
  have hdescent : baseEnd_2675564 < baseStart_2675564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675567 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 1, 6, 4]
def baseStart_2675567 : Nat := 118140960795 + 2675567 * 2 ^ 59
def prefixEnd_2675567 : Nat := 4983230072969 + 3 ^ 40 * 2675567 * 2
def baseEnd_2675567 : Nat := 1373851894308238565507797

theorem tailTrace_2675567 : CollatzResearch.WordTrace tailWord_2675567 prefixEnd_2675567 1373851894308238565507797 := by
  unfold tailWord_2675567
  simp only [CollatzResearch.WordTrace]
  refine ⟨97585945497885184309024955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65057296998590122872683303 97585945497885184309024955)
  ·
    refine ⟨146378918246827776463537433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97585945497885184309024955 146378918246827776463537433)
    ·
      refine ⟨109784188685120832347653075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146378918246827776463537433 109784188685120832347653075)
      ·
        refine ⟨164676283027681248521479613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109784188685120832347653075 164676283027681248521479613)
        ·
          refine ⟨61753606135380468195554855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164676283027681248521479613 61753606135380468195554855)
          ·
            refine ⟨92630409203070702293332283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61753606135380468195554855 92630409203070702293332283)
            ·
              refine ⟨138945613804606053439998425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92630409203070702293332283 138945613804606053439998425)
              ·
                refine ⟨104209210353454540079998819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138945613804606053439998425 104209210353454540079998819)
                ·
                  refine ⟨156313815530181810119998229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104209210353454540079998819 156313815530181810119998229)
                  ·
                    refine ⟨7327210102977272349374917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 156313815530181810119998229 7327210102977272349374917)
                    ·
                      refine ⟨1373851894308238565507797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7327210102977272349374917 1373851894308238565507797)
                      ·
                        rfl

theorem cell23_2675567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 6, 4].length) (baseStart_2675567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2675567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2675567 prefixEnd_2675567 := by exact prefixLift 2675567
  have htrace : WordTrace (prefixWord ++ tailWord_2675567) baseStart_2675567 baseEnd_2675567 := by
    simpa [prefixWord, tailWord_2675567, baseEnd_2675567] using wordTrace_append hprefix tailTrace_2675567
  have hstable : (prefixWord ++ tailWord_2675567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675567).length < 2 ^ (prefixWord ++ tailWord_2675567).sum := by decide
  have hdescent : baseEnd_2675567 < baseStart_2675567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675615 : List Nat := [1, 1, 2, 5, 2, 3, 1, 3, 1, 4]
def baseStart_2675615 : Nat := 118140960795 + 2675615 * 2 ^ 59
def prefixEnd_2675615 : Nat := 4983230072969 + 3 ^ 40 * 2675615 * 2
def baseEnd_2675615 : Nat := 457958847126551459235859

theorem tailTrace_2675615 : CollatzResearch.WordTrace tailWord_2675615 prefixEnd_2675615 457958847126551459235859 := by
  unfold tailWord_2675615
  simp only [CollatzResearch.WordTrace]
  refine ⟨97587696201711288506772299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65058464134474192337848199 97587696201711288506772299)
  ·
    refine ⟨146381544302566932760158449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97587696201711288506772299 146381544302566932760158449)
    ·
      refine ⟨109786158226925199570118837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146381544302566932760158449 109786158226925199570118837)
      ·
        refine ⟨10292452333774237459698641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 109786158226925199570118837 10292452333774237459698641)
        ·
          refine ⟨7719339250330678094773981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10292452333774237459698641 7719339250330678094773981)
          ·
            refine ⟨2894752218874004285540243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7719339250330678094773981 2894752218874004285540243)
            ·
              refine ⟨4342128328311006428310365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2894752218874004285540243 4342128328311006428310365)
              ·
                refine ⟨1628298123116627410616387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4342128328311006428310365 1628298123116627410616387)
                ·
                  refine ⟨2442447184674941115924581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1628298123116627410616387 2442447184674941115924581)
                  ·
                    refine ⟨457958847126551459235859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2442447184674941115924581 457958847126551459235859)
                    ·
                      rfl

theorem cell23_2675615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 3, 1, 4].length) (baseStart_2675615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2675615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2675615 prefixEnd_2675615 := by exact prefixLift 2675615
  have htrace : WordTrace (prefixWord ++ tailWord_2675615) baseStart_2675615 baseEnd_2675615 := by
    simpa [prefixWord, tailWord_2675615, baseEnd_2675615] using wordTrace_append hprefix tailTrace_2675615
  have hstable : (prefixWord ++ tailWord_2675615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675615).length < 2 ^ (prefixWord ++ tailWord_2675615).sum := by decide
  have hdescent : baseEnd_2675615 < baseStart_2675615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675645 : List Nat := [1, 4, 1, 2, 5, 1, 2, 1, 6]
def baseStart_2675645 : Nat := 118140960795 + 2675645 * 2 ^ 59
def prefixEnd_2675645 : Nat := 4983230072969 + 3 ^ 40 * 2675645 * 2
def baseEnd_2675645 : Nat := 152654660644365473370271

theorem tailTrace_2675645 : CollatzResearch.WordTrace tailWord_2675645 prefixEnd_2675645 152654660644365473370271 := by
  unfold tailWord_2675645
  simp only [CollatzResearch.WordTrace]
  refine ⟨97588790391602603630364389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65059193594401735753576259 97588790391602603630364389)
  ·
    refine ⟨18297898198425488180693323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97588790391602603630364389 18297898198425488180693323)
    ·
      refine ⟨27446847297638232271039985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18297898198425488180693323 27446847297638232271039985)
      ·
        refine ⟨20585135473228674203279989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27446847297638232271039985 20585135473228674203279989)
        ·
          refine ⟨1929856450615188206557499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20585135473228674203279989 1929856450615188206557499)
          ·
            refine ⟨2894784675922782309836249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1929856450615188206557499 2894784675922782309836249)
            ·
              refine ⟨2171088506942086732377187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2894784675922782309836249 2171088506942086732377187)
              ·
                refine ⟨3256632760413130098565781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2171088506942086732377187 3256632760413130098565781)
                ·
                  refine ⟨152654660644365473370271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3256632760413130098565781 152654660644365473370271)
                  ·
                    rfl

theorem cell23_2675645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 1, 6].length) (baseStart_2675645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2675645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2675645 prefixEnd_2675645 := by exact prefixLift 2675645
  have htrace : WordTrace (prefixWord ++ tailWord_2675645) baseStart_2675645 baseEnd_2675645 := by
    simpa [prefixWord, tailWord_2675645, baseEnd_2675645] using wordTrace_append hprefix tailTrace_2675645
  have hstable : (prefixWord ++ tailWord_2675645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675645).length < 2 ^ (prefixWord ++ tailWord_2675645).sum := by decide
  have hdescent : baseEnd_2675645 < baseStart_2675645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675711 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 8, 1, 3]
def baseStart_2675711 : Nat := 118140960795 + 2675711 * 2 ^ 59
def prefixEnd_2675711 : Nat := 4983230072969 + 3 ^ 40 * 2675711 * 2
def baseEnd_2675711 : Nat := 1373925835522486002107135

theorem tailTrace_2675711 : CollatzResearch.WordTrace tailWord_2675711 prefixEnd_2675711 1373925835522486002107135 := by
  unfold tailWord_2675711
  simp only [CollatzResearch.WordTrace]
  refine ⟨97591197609363496902266987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65060798406242331268177991 97591197609363496902266987)
  ·
    refine ⟨146386796414045245353400481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97591197609363496902266987 146386796414045245353400481)
    ·
      refine ⟨109790097310533934015050361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146386796414045245353400481 109790097310533934015050361)
      ·
        refine ⟨82342572982900450511287771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109790097310533934015050361 82342572982900450511287771)
        ·
          refine ⟨123513859474350675766931657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82342572982900450511287771 123513859474350675766931657)
          ·
            refine ⟨92635394605763006825198743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123513859474350675766931657 92635394605763006825198743)
            ·
              refine ⟨138953091908644510237798115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92635394605763006825198743 138953091908644510237798115)
              ·
                refine ⟨208429637862966765356697173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138953091908644510237798115 208429637862966765356697173)
                ·
                  refine ⟨2442534818706641781523795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 208429637862966765356697173 2442534818706641781523795)
                  ·
                    refine ⟨3663802228059962672285693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2442534818706641781523795 3663802228059962672285693)
                    ·
                      refine ⟨1373925835522486002107135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3663802228059962672285693 1373925835522486002107135)
                      ·
                        rfl

theorem cell23_2675711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 8, 1, 3].length) (baseStart_2675711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2675711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2675711 prefixEnd_2675711 := by exact prefixLift 2675711
  have htrace : WordTrace (prefixWord ++ tailWord_2675711) baseStart_2675711 baseEnd_2675711 := by
    simpa [prefixWord, tailWord_2675711, baseEnd_2675711] using wordTrace_append hprefix tailTrace_2675711
  have hstable : (prefixWord ++ tailWord_2675711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675711).length < 2 ^ (prefixWord ++ tailWord_2675711).sum := by decide
  have hdescent : baseEnd_2675711 < baseStart_2675711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675745 : List Nat := [1, 2, 3, 2, 3, 1, 3, 2, 2, 1, 3]
def baseStart_2675745 : Nat := 118140960795 + 2675745 * 2 ^ 59
def prefixEnd_2675745 : Nat := 4983230072969 + 3 ^ 40 * 2675745 * 2
def baseEnd_2675745 : Nat := 1373943293864738869081979

theorem tailTrace_2675745 : CollatzResearch.WordTrace tailWord_2675745 prefixEnd_2675745 1373943293864738869081979 := by
  unfold tailWord_2675745
  simp only [CollatzResearch.WordTrace]
  refine ⟨97592437691240320709004689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65061625127493547139336459 97592437691240320709004689)
  ·
    refine ⟨73194328268430240531753517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97592437691240320709004689 73194328268430240531753517)
    ·
      refine ⟨27447873100661340199407569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73194328268430240531753517 27447873100661340199407569)
      ·
        refine ⟨20585904825496005149555677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27447873100661340199407569 20585904825496005149555677)
        ·
          refine ⟨7719714309561001931083379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20585904825496005149555677 7719714309561001931083379)
          ·
            refine ⟨11579571464341502896625069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7719714309561001931083379 11579571464341502896625069)
            ·
              refine ⟨4342339299128063586234401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11579571464341502896625069 4342339299128063586234401)
              ·
                refine ⟨3256754474346047689675801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4342339299128063586234401 3256754474346047689675801)
                ·
                  refine ⟨2442565855759535767256851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3256754474346047689675801 2442565855759535767256851)
                  ·
                    refine ⟨3663848783639303650885277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2442565855759535767256851 3663848783639303650885277)
                    ·
                      refine ⟨1373943293864738869081979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3663848783639303650885277 1373943293864738869081979)
                      ·
                        rfl

theorem cell23_2675745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_2675745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2675745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2675745 prefixEnd_2675745 := by exact prefixLift 2675745
  have htrace : WordTrace (prefixWord ++ tailWord_2675745) baseStart_2675745 baseEnd_2675745 := by
    simpa [prefixWord, tailWord_2675745, baseEnd_2675745] using wordTrace_append hprefix tailTrace_2675745
  have hstable : (prefixWord ++ tailWord_2675745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675745).length < 2 ^ (prefixWord ++ tailWord_2675745).sum := by decide
  have hdescent : baseEnd_2675745 < baseStart_2675745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675801 : List Nat := [1, 2, 1, 2, 2, 1, 2, 4, 2, 3, 3]
def baseStart_2675801 : Nat := 118140960795 + 2675801 * 2 ^ 59
def prefixEnd_2675801 : Nat := 4983230072969 + 3 ^ 40 * 2675801 * 2
def baseEnd_2675801 : Nat := 1373972048781390649981721

theorem tailTrace_2675801 : CollatzResearch.WordTrace tailWord_2675801 prefixEnd_2675801 1373972048781390649981721 := by
  unfold tailWord_2675801
  simp only [CollatzResearch.WordTrace]
  refine ⟨97594480179037442273043257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65062986786024961515362171 97594480179037442273043257)
  ·
    refine ⟨73195860134278081704782443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97594480179037442273043257 73195860134278081704782443)
    ·
      refine ⟨109793790201417122557173665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73195860134278081704782443 109793790201417122557173665)
      ·
        refine ⟨82345342651062841917880249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109793790201417122557173665 82345342651062841917880249)
        ·
          refine ⟨61759006988297131438410187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82345342651062841917880249 61759006988297131438410187)
          ·
            refine ⟨92638510482445697157615281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61759006988297131438410187 92638510482445697157615281)
            ·
              refine ⟨69478882861834272868211461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92638510482445697157615281 69478882861834272868211461)
              ·
                refine ⟨13027290536593926162789649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69478882861834272868211461 13027290536593926162789649)
                ·
                  refine ⟨9770467902445444622092237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13027290536593926162789649 9770467902445444622092237)
                  ·
                    refine ⟨3663925463417041733284589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9770467902445444622092237 3663925463417041733284589)
                    ·
                      refine ⟨1373972048781390649981721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3663925463417041733284589 1373972048781390649981721)
                      ·
                        rfl

theorem cell23_2675801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 3, 3].length) (baseStart_2675801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2675801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2675801 prefixEnd_2675801 := by exact prefixLift 2675801
  have htrace : WordTrace (prefixWord ++ tailWord_2675801) baseStart_2675801 baseEnd_2675801 := by
    simpa [prefixWord, tailWord_2675801, baseEnd_2675801] using wordTrace_append hprefix tailTrace_2675801
  have hstable : (prefixWord ++ tailWord_2675801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675801).length < 2 ^ (prefixWord ++ tailWord_2675801).sum := by decide
  have hdescent : baseEnd_2675801 < baseStart_2675801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675902 : List Nat := [4, 2, 1, 1, 3, 1, 1, 5, 1, 4]
def baseStart_2675902 : Nat := 118140960795 + 2675902 * 2 ^ 59
def prefixEnd_2675902 : Nat := 4983230072969 + 3 ^ 40 * 2675902 * 2
def baseEnd_2675902 : Nat := 458007970109164918272919

theorem tailTrace_2675902 : CollatzResearch.WordTrace tailWord_2675902 prefixEnd_2675902 458007970109164918272919 := by
  unfold tailWord_2675902
  simp only [CollatzResearch.WordTrace]
  refine ⟨12199770493958942065308745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65065442634447691014979973 12199770493958942065308745)
  ·
    refine ⟨9149827870469206548981559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12199770493958942065308745 9149827870469206548981559)
    ·
      refine ⟨13724741805703809823472339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9149827870469206548981559 13724741805703809823472339)
      ·
        refine ⟨20587112708555714735208509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13724741805703809823472339 20587112708555714735208509)
        ·
          refine ⟨7720167265708393025703191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20587112708555714735208509 7720167265708393025703191)
          ·
            refine ⟨11580250898562589538554787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7720167265708393025703191 11580250898562589538554787)
            ·
              refine ⟨17370376347843884307832181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11580250898562589538554787 17370376347843884307832181)
              ·
                refine ⟨1628472782610364153859267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17370376347843884307832181 1628472782610364153859267)
                ·
                  refine ⟨2442709173915546230788901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1628472782610364153859267 2442709173915546230788901)
                  ·
                    refine ⟨458007970109164918272919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2442709173915546230788901 458007970109164918272919)
                    ·
                      rfl

theorem cell23_2675902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_2675902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2675902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2675902 prefixEnd_2675902 := by exact prefixLift 2675902
  have htrace : WordTrace (prefixWord ++ tailWord_2675902) baseStart_2675902 baseEnd_2675902 := by
    simpa [prefixWord, tailWord_2675902, baseEnd_2675902] using wordTrace_append hprefix tailTrace_2675902
  have hstable : (prefixWord ++ tailWord_2675902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675902).length < 2 ^ (prefixWord ++ tailWord_2675902).sum := by decide
  have hdescent : baseEnd_2675902 < baseStart_2675902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675958 : List Nat := [5, 1, 1, 1, 1, 1, 1, 3, 3, 6]
def baseStart_2675958 : Nat := 118140960795 + 2675958 * 2 ^ 59
def prefixEnd_2675958 : Nat := 4983230072969 + 3 ^ 40 * 2675958 * 2
def baseEnd_2675958 : Nat := 458017555081382178572833

theorem tailTrace_2675958 : CollatzResearch.WordTrace tailWord_2675958 prefixEnd_2675958 458017555081382178572833 := by
  unfold tailWord_2675958
  simp only [CollatzResearch.WordTrace]
  refine ⟨6100012902466791130406783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65066804292979105391005685 6100012902466791130406783)
  ·
    refine ⟨9150019353700186695610175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6100012902466791130406783 9150019353700186695610175)
    ·
      refine ⟨13725029030550280043415263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9150019353700186695610175 13725029030550280043415263)
      ·
        refine ⟨20587543545825420065122895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13725029030550280043415263 20587543545825420065122895)
        ·
          refine ⟨30881315318738130097684343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20587543545825420065122895 30881315318738130097684343)
          ·
            refine ⟨46321972978107195146526515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30881315318738130097684343 46321972978107195146526515)
            ·
              refine ⟨69482959467160792719789773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46321972978107195146526515 69482959467160792719789773)
              ·
                refine ⟨26056109800185297269921165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69482959467160792719789773 26056109800185297269921165)
                ·
                  refine ⟨9771041175069486476220437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26056109800185297269921165 9771041175069486476220437)
                  ·
                    refine ⟨458017555081382178572833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9771041175069486476220437 458017555081382178572833)
                    ·
                      rfl

theorem cell23_2675958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_2675958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2675958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2675958 prefixEnd_2675958 := by exact prefixLift 2675958
  have htrace : WordTrace (prefixWord ++ tailWord_2675958) baseStart_2675958 baseEnd_2675958 := by
    simpa [prefixWord, tailWord_2675958, baseEnd_2675958] using wordTrace_append hprefix tailTrace_2675958
  have hstable : (prefixWord ++ tailWord_2675958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675958).length < 2 ^ (prefixWord ++ tailWord_2675958).sum := by decide
  have hdescent : baseEnd_2675958 < baseStart_2675958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675968 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 3]
def baseStart_2675968 : Nat := 118140960795 + 2675968 * 2 ^ 59
def prefixEnd_2675968 : Nat := 4983230072969 + 3 ^ 40 * 2675968 * 2
def baseEnd_2675968 : Nat := 1374057800050691496593453

theorem tailTrace_2675968 : CollatzResearch.WordTrace tailWord_2675968 prefixEnd_2675968 1374057800050691496593453 := by
  unfold tailWord_2675968
  simp only [CollatzResearch.WordTrace]
  refine ⟨48800285584716214897186279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65067047446288286529581705 48800285584716214897186279)
  ·
    refine ⟨73200428377074322345779419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48800285584716214897186279 73200428377074322345779419)
    ·
      refine ⟨109800642565611483518669129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73200428377074322345779419 109800642565611483518669129)
      ·
        refine ⟨82350481924208612639001847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109800642565611483518669129 82350481924208612639001847)
        ·
          refine ⟨123525722886312918958502771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82350481924208612639001847 123525722886312918958502771)
          ·
            refine ⟨185288584329469378437754157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123525722886312918958502771 185288584329469378437754157)
            ·
              refine ⟨69483219123551016914157809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 185288584329469378437754157 69483219123551016914157809)
              ·
                refine ⟨52112414342663262685618357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69483219123551016914157809 52112414342663262685618357)
                ·
                  refine ⟨4885538844624680876776721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52112414342663262685618357 4885538844624680876776721)
                  ·
                    refine ⟨3664154133468510657582541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4885538844624680876776721 3664154133468510657582541)
                    ·
                      refine ⟨1374057800050691496593453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3664154133468510657582541 1374057800050691496593453)
                      ·
                        rfl

theorem cell23_2675968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 3].length) (baseStart_2675968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2675968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2675968 prefixEnd_2675968 := by exact prefixLift 2675968
  have htrace : WordTrace (prefixWord ++ tailWord_2675968) baseStart_2675968 baseEnd_2675968 := by
    simpa [prefixWord, tailWord_2675968, baseEnd_2675968] using wordTrace_append hprefix tailTrace_2675968
  have hstable : (prefixWord ++ tailWord_2675968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675968).length < 2 ^ (prefixWord ++ tailWord_2675968).sum := by decide
  have hdescent : baseEnd_2675968 < baseStart_2675968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675971 : List Nat := [1, 1, 1, 3, 2, 4, 11]
def baseStart_2675971 : Nat := 118140960795 + 2675971 * 2 ^ 59
def prefixEnd_2675971 : Nat := 4983230072969 + 3 ^ 40 * 2675971 * 2
def baseEnd_2675971 : Nat := 16963695561637715862419

theorem tailTrace_2675971 : CollatzResearch.WordTrace tailWord_2675971 prefixEnd_2675971 16963695561637715862419 := by
  unfold tailWord_2675971
  simp only [CollatzResearch.WordTrace]
  refine ⟨97600680588421561306731767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65067120392281040871154511 97600680588421561306731767)
  ·
    refine ⟨146401020882632341960097651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97600680588421561306731767 146401020882632341960097651)
    ·
      refine ⟨219601531323948512940146477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146401020882632341960097651 219601531323948512940146477)
      ·
        refine ⟨82350574246480692352554929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 219601531323948512940146477 82350574246480692352554929)
        ·
          refine ⟨61762930684860519264416197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82350574246480692352554929 61762930684860519264416197)
          ·
            refine ⟨11580549503411347362078037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61762930684860519264416197 11580549503411347362078037)
            ·
              refine ⟨16963695561637715862419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 11580549503411347362078037 16963695561637715862419)
              ·
                rfl

theorem cell23_2675971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 11].length) (baseStart_2675971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2675971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2675971 prefixEnd_2675971 := by exact prefixLift 2675971
  have htrace : WordTrace (prefixWord ++ tailWord_2675971) baseStart_2675971 baseEnd_2675971 := by
    simpa [prefixWord, tailWord_2675971, baseEnd_2675971] using wordTrace_append hprefix tailTrace_2675971
  have hstable : (prefixWord ++ tailWord_2675971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675971).length < 2 ^ (prefixWord ++ tailWord_2675971).sum := by decide
  have hdescent : baseEnd_2675971 < baseStart_2675971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675976 : List Nat := [2, 1, 3, 2, 4, 1, 3, 2, 1, 1, 3]
def baseStart_2675976 : Nat := 118140960795 + 2675976 * 2 ^ 59
def prefixEnd_2675976 : Nat := 4983230072969 + 3 ^ 40 * 2675976 * 2
def baseEnd_2675976 : Nat := 1374061907895927465293417

theorem tailTrace_2675976 : CollatzResearch.WordTrace tailWord_2675976 prefixEnd_2675976 1374061907895927465293417 := by
  unfold tailWord_2675976
  simp only [CollatzResearch.WordTrace]
  refine ⟨48800431476701723580331891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65067241968935631440442521 48800431476701723580331891)
  ·
    refine ⟨73200647215052585370497837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48800431476701723580331891 73200647215052585370497837)
    ·
      refine ⟨27450242705644719513936689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73200647215052585370497837 27450242705644719513936689)
      ·
        refine ⟨20587682029233539635452517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27450242705644719513936689 20587682029233539635452517)
        ·
          refine ⟨3860190380481288681647347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20587682029233539635452517 3860190380481288681647347)
          ·
            refine ⟨5790285570721933022471021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3860190380481288681647347 5790285570721933022471021)
            ·
              refine ⟨2171357089020724883426633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5790285570721933022471021 2171357089020724883426633)
              ·
                refine ⟨1628517816765543662569975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2171357089020724883426633 1628517816765543662569975)
                ·
                  refine ⟨2442776725148315493854963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1628517816765543662569975 2442776725148315493854963)
                  ·
                    refine ⟨3664165087722473240782445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2442776725148315493854963 3664165087722473240782445)
                    ·
                      refine ⟨1374061907895927465293417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3664165087722473240782445 1374061907895927465293417)
                      ·
                        rfl

theorem cell23_2675976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 2, 1, 1, 3].length) (baseStart_2675976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2675976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2675976 prefixEnd_2675976 := by exact prefixLift 2675976
  have htrace : WordTrace (prefixWord ++ tailWord_2675976) baseStart_2675976 baseEnd_2675976 := by
    simpa [prefixWord, tailWord_2675976, baseEnd_2675976] using wordTrace_append hprefix tailTrace_2675976
  have hstable : (prefixWord ++ tailWord_2675976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675976).length < 2 ^ (prefixWord ++ tailWord_2675976).sum := by decide
  have hdescent : baseEnd_2675976 < baseStart_2675976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675992 : List Nat := [2, 1, 2, 3, 1, 3, 4, 1, 2, 4]
def baseStart_2675992 : Nat := 118140960795 + 2675992 * 2 ^ 59
def prefixEnd_2675992 : Nat := 4983230072969 + 3 ^ 40 * 2675992 * 2
def baseEnd_2675992 : Nat := 458023374528799800897781

theorem tailTrace_2675992 : CollatzResearch.WordTrace tailWord_2675992 prefixEnd_2675992 458023374528799800897781 := by
  unfold tailWord_2675992
  simp only [CollatzResearch.WordTrace]
  refine ⟨48800723260672740946623115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65067631014230321262164153 48800723260672740946623115)
  ·
    refine ⟨73201084891009111419934673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48800723260672740946623115 73201084891009111419934673)
    ·
      refine ⟨54900813668256833564951005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73201084891009111419934673 54900813668256833564951005)
      ·
        refine ⟨20587805125596312586856627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54900813668256833564951005 20587805125596312586856627)
        ·
          refine ⟨30881707688394468880284941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20587805125596312586856627 30881707688394468880284941)
          ·
            refine ⟨11580640383147925830106853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30881707688394468880284941 11580640383147925830106853)
            ·
              refine ⟨2171370071840236093145035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11580640383147925830106853 2171370071840236093145035)
              ·
                refine ⟨3257055107760354139717553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2171370071840236093145035 3257055107760354139717553)
                ·
                  refine ⟨2442791330820265604788165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3257055107760354139717553 2442791330820265604788165)
                  ·
                    refine ⟨458023374528799800897781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2442791330820265604788165 458023374528799800897781)
                    ·
                      rfl

theorem cell23_2675992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 1, 2, 4].length) (baseStart_2675992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2675992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2675992 prefixEnd_2675992 := by exact prefixLift 2675992
  have htrace : WordTrace (prefixWord ++ tailWord_2675992) baseStart_2675992 baseEnd_2675992 := by
    simpa [prefixWord, tailWord_2675992, baseEnd_2675992] using wordTrace_append hprefix tailTrace_2675992
  have hstable : (prefixWord ++ tailWord_2675992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675992).length < 2 ^ (prefixWord ++ tailWord_2675992).sum := by decide
  have hdescent : baseEnd_2675992 < baseStart_2675992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675999 : List Nat := [1, 1, 2, 4, 5, 1, 1, 2, 1, 1, 4]
def baseStart_2675999 : Nat := 118140960795 + 2675999 * 2 ^ 59
def prefixEnd_2675999 : Nat := 4983230072969 + 3 ^ 40 * 2675999 * 2
def baseEnd_2675999 : Nat := 1374073717950980875305811

theorem tailTrace_2675999 : CollatzResearch.WordTrace tailWord_2675999 prefixEnd_2675999 1374073717950980875305811 := by
  unfold tailWord_2675999
  simp only [CollatzResearch.WordTrace]
  refine ⟨97601701832320122088751051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65067801221546748059167367 97601701832320122088751051)
  ·
    refine ⟨146402552748480183133126577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97601701832320122088751051 146402552748480183133126577)
    ·
      refine ⟨109801914561360137349844933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146402552748480183133126577 109801914561360137349844933)
      ·
        refine ⟨20587858980255025753095925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109801914561360137349844933 20587858980255025753095925)
        ·
          refine ⟨1930111779398908664352743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20587858980255025753095925 1930111779398908664352743)
          ·
            refine ⟨2895167669098362996529115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1930111779398908664352743 2895167669098362996529115)
            ·
              refine ⟨4342751503647544494793673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2895167669098362996529115 4342751503647544494793673)
              ·
                refine ⟨3257063627735658371095255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4342751503647544494793673 3257063627735658371095255)
                ·
                  refine ⟨4885595441603487556642883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3257063627735658371095255 4885595441603487556642883)
                  ·
                    refine ⟨7328393162405231334964325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4885595441603487556642883 7328393162405231334964325)
                    ·
                      refine ⟨1374073717950980875305811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7328393162405231334964325 1374073717950980875305811)
                      ·
                        rfl

theorem cell23_2675999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 2, 1, 1, 4].length) (baseStart_2675999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2675999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2675999 prefixEnd_2675999 := by exact prefixLift 2675999
  have htrace : WordTrace (prefixWord ++ tailWord_2675999) baseStart_2675999 baseEnd_2675999 := by
    simpa [prefixWord, tailWord_2675999, baseEnd_2675999] using wordTrace_append hprefix tailTrace_2675999
  have hstable : (prefixWord ++ tailWord_2675999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675999).length < 2 ^ (prefixWord ++ tailWord_2675999).sum := by decide
  have hdescent : baseEnd_2675999 < baseStart_2675999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676002 : List Nat := [3, 3, 1, 1, 4, 1, 1, 1, 3, 2, 3]
def baseStart_2676002 : Nat := 118140960795 + 2676002 * 2 ^ 59
def prefixEnd_2676002 : Nat := 4983230072969 + 3 ^ 40 * 2676002 * 2
def baseEnd_2676002 : Nat := 1374075258392944363568297

theorem tailTrace_2676002 : CollatzResearch.WordTrace tailWord_2676002 prefixEnd_2676002 1374075258392944363568297 := by
  unfold tailWord_2676002
  simp only [CollatzResearch.WordTrace]
  refine ⟨24400452812827313400277565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65067874167539502400740173 24400452812827313400277565)
  ·
    refine ⟨9150169804810242525104087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24400452812827313400277565 9150169804810242525104087)
    ·
      refine ⟨13725254707215363787656131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9150169804810242525104087 13725254707215363787656131)
      ·
        refine ⟨20587882060823045681484197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13725254707215363787656131 20587882060823045681484197)
        ·
          refine ⟨3860227886404321065278287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20587882060823045681484197 3860227886404321065278287)
          ·
            refine ⟨5790341829606481597917431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3860227886404321065278287 5790341829606481597917431)
            ·
              refine ⟨8685512744409722396876147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5790341829606481597917431 8685512744409722396876147)
              ·
                refine ⟨13028269116614583595314221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8685512744409722396876147 13028269116614583595314221)
                ·
                  refine ⟨4885600918730468848242833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13028269116614583595314221 4885600918730468848242833)
                  ·
                    refine ⟨3664200689047851636182125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4885600918730468848242833 3664200689047851636182125)
                    ·
                      refine ⟨1374075258392944363568297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3664200689047851636182125 1374075258392944363568297)
                      ·
                        rfl

theorem cell23_2676002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_2676002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2676002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2676002 prefixEnd_2676002 := by exact prefixLift 2676002
  have htrace : WordTrace (prefixWord ++ tailWord_2676002) baseStart_2676002 baseEnd_2676002 := by
    simpa [prefixWord, tailWord_2676002, baseEnd_2676002] using wordTrace_append hprefix tailTrace_2676002
  have hstable : (prefixWord ++ tailWord_2676002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676002).length < 2 ^ (prefixWord ++ tailWord_2676002).sum := by decide
  have hdescent : baseEnd_2676002 < baseStart_2676002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676022 : List Nat := [5, 1, 2, 3, 2, 10]
def baseStart_2676022 : Nat := 118140960795 + 2676022 * 2 ^ 59
def prefixEnd_2676022 : Nat := 4983230072969 + 3 ^ 40 * 2676022 * 2
def baseEnd_2676022 : Nat := 5654672954757342737935

theorem tailTrace_2676022 : CollatzResearch.WordTrace tailWord_2676022 prefixEnd_2676022 5654672954757342737935 := by
  unfold tailWord_2676022
  simp only [CollatzResearch.WordTrace]
  refine ⟨6100158794452299813552395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65068360474157864677892213 6100158794452299813552395)
  ·
    refine ⟨9150238191678449720328593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6100158794452299813552395 9150238191678449720328593)
    ·
      refine ⟨6862678643758837290246445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9150238191678449720328593 6862678643758837290246445)
      ·
        refine ⟨2573504491409563983842417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6862678643758837290246445 2573504491409563983842417)
        ·
          refine ⟨1930128368557172987881813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2573504491409563983842417 1930128368557172987881813)
          ·
            refine ⟨5654672954757342737935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1930128368557172987881813 5654672954757342737935)
            ·
              rfl

theorem cell23_2676022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 10].length) (baseStart_2676022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2676022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2676022 prefixEnd_2676022 := by exact prefixLift 2676022
  have htrace : WordTrace (prefixWord ++ tailWord_2676022) baseStart_2676022 baseEnd_2676022 := by
    simpa [prefixWord, tailWord_2676022, baseEnd_2676022] using wordTrace_append hprefix tailTrace_2676022
  have hstable : (prefixWord ++ tailWord_2676022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676022).length < 2 ^ (prefixWord ++ tailWord_2676022).sum := by decide
  have hdescent : baseEnd_2676022 < baseStart_2676022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676032 : List Nat := [2, 1, 1, 2, 2, 1, 6, 2, 2, 1, 3]
def baseStart_2676032 : Nat := 118140960795 + 2676032 * 2 ^ 59
def prefixEnd_2676032 : Nat := 4983230072969 + 3 ^ 40 * 2676032 * 2
def baseEnd_2676032 : Nat := 1374090662812579246193159

theorem tailTrace_2676032 : CollatzResearch.WordTrace tailWord_2676032 prefixEnd_2676032 1374090662812579246193159 := by
  unfold tailWord_2676032
  simp only [CollatzResearch.WordTrace]
  refine ⟨48801452720600284362351175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65068603627467045816468233 48801452720600284362351175)
  ·
    refine ⟨73202179080900426543526763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48801452720600284362351175 73202179080900426543526763)
    ·
      refine ⟨109803268621350639815290145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73202179080900426543526763 109803268621350639815290145)
      ·
        refine ⟨82352451466012979861467609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109803268621350639815290145 82352451466012979861467609)
        ·
          refine ⟨61764338599509734896100707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82352451466012979861467609 61764338599509734896100707)
          ·
            refine ⟨92646507899264602344151061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61764338599509734896100707 92646507899264602344151061)
            ·
              refine ⟨4342805057778028234882081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 92646507899264602344151061 4342805057778028234882081)
              ·
                refine ⟨3257103793333521176161561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4342805057778028234882081 3257103793333521176161561)
                ·
                  refine ⟨2442827845000140882121171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3257103793333521176161561 2442827845000140882121171)
                  ·
                    refine ⟨3664241767500211323181757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2442827845000140882121171 3664241767500211323181757)
                    ·
                      refine ⟨1374090662812579246193159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3664241767500211323181757 1374090662812579246193159)
                      ·
                        rfl

theorem cell23_2676032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2, 2, 1, 3].length) (baseStart_2676032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2676032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2676032 prefixEnd_2676032 := by exact prefixLift 2676032
  have htrace : WordTrace (prefixWord ++ tailWord_2676032) baseStart_2676032 baseEnd_2676032 := by
    simpa [prefixWord, tailWord_2676032, baseEnd_2676032] using wordTrace_append hprefix tailTrace_2676032
  have hstable : (prefixWord ++ tailWord_2676032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676032).length < 2 ^ (prefixWord ++ tailWord_2676032).sum := by decide
  have hdescent : baseEnd_2676032 < baseStart_2676032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676033 : List Nat := [1, 2, 5, 2, 1, 1, 4, 2, 1, 2, 2]
def baseStart_2676033 : Nat := 118140960795 + 2676033 * 2 ^ 59
def prefixEnd_2676033 : Nat := 4983230072969 + 3 ^ 40 * 2676033 * 2
def baseEnd_2676033 : Nat := 1374091176293233742280655

theorem tailTrace_2676033 : CollatzResearch.WordTrace tailWord_2676033 prefixEnd_2676033 1374091176293233742280655 := by
  unfold tailWord_2676033
  simp only [CollatzResearch.WordTrace]
  refine ⟨97602941914196945895488753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65068627942797963930325835 97602941914196945895488753)
  ·
    refine ⟨73202206435647709421616565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97602941914196945895488753 73202206435647709421616565)
    ·
      refine ⟨6862706853341972758276553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73202206435647709421616565 6862706853341972758276553)
      ·
        refine ⟨5147030140006479568707415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6862706853341972758276553 5147030140006479568707415)
        ·
          refine ⟨7720545210009719353061123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5147030140006479568707415 7720545210009719353061123)
          ·
            refine ⟨11580817815014579029591685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7720545210009719353061123 11580817815014579029591685)
            ·
              refine ⟨2171403340315233568048441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11580817815014579029591685 2171403340315233568048441)
              ·
                refine ⟨1628552505236425176036331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2171403340315233568048441 1628552505236425176036331)
                ·
                  refine ⟨2442828757854637764054497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1628552505236425176036331 2442828757854637764054497)
                  ·
                    refine ⟨1832121568390978323040873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2442828757854637764054497 1832121568390978323040873)
                    ·
                      refine ⟨1374091176293233742280655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1832121568390978323040873 1374091176293233742280655)
                      ·
                        rfl

theorem cell23_2676033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_2676033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2676033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2676033 prefixEnd_2676033 := by exact prefixLift 2676033
  have htrace : WordTrace (prefixWord ++ tailWord_2676033) baseStart_2676033 baseEnd_2676033 := by
    simpa [prefixWord, tailWord_2676033, baseEnd_2676033] using wordTrace_append hprefix tailTrace_2676033
  have hstable : (prefixWord ++ tailWord_2676033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676033).length < 2 ^ (prefixWord ++ tailWord_2676033).sum := by decide
  have hdescent : baseEnd_2676033 < baseStart_2676033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676048 : List Nat := [2, 1, 1, 1, 1, 5, 3, 1, 2, 6]
def baseStart_2676048 : Nat := 118140960795 + 2676048 * 2 ^ 59
def prefixEnd_2676048 : Nat := 4983230072969 + 3 ^ 40 * 2676048 * 2
def baseEnd_2676048 : Nat := 458032959501017061197695

theorem tailTrace_2676048 : CollatzResearch.WordTrace tailWord_2676048 prefixEnd_2676048 458032959501017061197695 := by
  unfold tailWord_2676048
  simp only [CollatzResearch.WordTrace]
  refine ⟨48801744504571301728642399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65068992672761735638189865 48801744504571301728642399)
  ·
    refine ⟨73202616756856952592963599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48801744504571301728642399 73202616756856952592963599)
    ·
      refine ⟨109803925135285428889445399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73202616756856952592963599 109803925135285428889445399)
      ·
        refine ⟨164705887702928143334168099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109803925135285428889445399 164705887702928143334168099)
        ·
          refine ⟨247058831554392215001252149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164705887702928143334168099 247058831554392215001252149)
          ·
            refine ⟨23161765458224270156367389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 247058831554392215001252149 23161765458224270156367389)
            ·
              refine ⟨8685662046834101308637771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23161765458224270156367389 8685662046834101308637771)
              ·
                refine ⟨13028493070251151962956657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8685662046834101308637771 13028493070251151962956657)
                ·
                  refine ⟨9771369802688363972217493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13028493070251151962956657 9771369802688363972217493)
                  ·
                    refine ⟨458032959501017061197695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9771369802688363972217493 458032959501017061197695)
                    ·
                      rfl

theorem cell23_2676048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 2, 6].length) (baseStart_2676048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2676048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2676048 prefixEnd_2676048 := by exact prefixLift 2676048
  have htrace : WordTrace (prefixWord ++ tailWord_2676048) baseStart_2676048 baseEnd_2676048 := by
    simpa [prefixWord, tailWord_2676048, baseEnd_2676048] using wordTrace_append hprefix tailTrace_2676048
  have hstable : (prefixWord ++ tailWord_2676048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676048).length < 2 ^ (prefixWord ++ tailWord_2676048).sum := by decide
  have hdescent : baseEnd_2676048 < baseStart_2676048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676058 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 4, 1, 5]
def baseStart_2676058 : Nat := 118140960795 + 2676058 * 2 ^ 59
def prefixEnd_2676058 : Nat := 4983230072969 + 3 ^ 40 * 2676058 * 2
def baseEnd_2676058 : Nat := 1374104013309596144468039

theorem tailTrace_2676058 : CollatzResearch.WordTrace tailWord_2676058 prefixEnd_2676058 1374104013309596144468039 := by
  unfold tailWord_2676058
  simp only [CollatzResearch.WordTrace]
  refine ⟨24400963434776593791287207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65069235826070916776765885 24400963434776593791287207)
  ·
    refine ⟨36601445152164890686930811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24400963434776593791287207 36601445152164890686930811)
    ·
      refine ⟨54902167728247336030396217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36601445152164890686930811 54902167728247336030396217)
      ·
        refine ⟨41176625796185502022797163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54902167728247336030396217 41176625796185502022797163)
        ·
          refine ⟨61764938694278253034195745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41176625796185502022797163 61764938694278253034195745)
          ·
            refine ⟨46323704020708689775646809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61764938694278253034195745 46323704020708689775646809)
            ·
              refine ⟨34742778015531517331735107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46323704020708689775646809 34742778015531517331735107)
              ·
                refine ⟨52114167023297275997602661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34742778015531517331735107 52114167023297275997602661)
                ·
                  refine ⟨9771406316868239249550499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52114167023297275997602661 9771406316868239249550499)
                  ·
                    refine ⟨14657109475302358874325749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9771406316868239249550499 14657109475302358874325749)
                    ·
                      refine ⟨1374104013309596144468039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14657109475302358874325749 1374104013309596144468039)
                      ·
                        rfl

theorem cell23_2676058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_2676058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2676058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2676058 prefixEnd_2676058 := by exact prefixLift 2676058
  have htrace : WordTrace (prefixWord ++ tailWord_2676058) baseStart_2676058 baseEnd_2676058 := by
    simpa [prefixWord, tailWord_2676058, baseEnd_2676058] using wordTrace_append hprefix tailTrace_2676058
  have hstable : (prefixWord ++ tailWord_2676058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676058).length < 2 ^ (prefixWord ++ tailWord_2676058).sum := by decide
  have hdescent : baseEnd_2676058 < baseStart_2676058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676076 : List Nat := [2, 2, 1, 1, 5, 3, 2, 1, 1, 3, 2]
def baseStart_2676076 : Nat := 118140960795 + 2676076 * 2 ^ 59
def prefixEnd_2676076 : Nat := 4983230072969 + 3 ^ 40 * 2676076 * 2
def baseEnd_2676076 : Nat := 1374113255961377074042957

theorem tailTrace_2676076 : CollatzResearch.WordTrace tailWord_2676076 prefixEnd_2676076 1374113255961377074042957 := by
  unfold tailWord_2676076
  simp only [CollatzResearch.WordTrace]
  refine ⟨48802255126520582119652041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65069673502027442826202721 48802255126520582119652041)
  ·
    refine ⟨36601691344890436589739031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48802255126520582119652041 36601691344890436589739031)
    ·
      refine ⟨54902537017335654884608547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36601691344890436589739031 54902537017335654884608547)
      ·
        refine ⟨82353805526003482326912821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54902537017335654884608547 82353805526003482326912821)
        ·
          refine ⟨7720669268062826468148077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82353805526003482326912821 7720669268062826468148077)
          ·
            refine ⟨2895250975523559925555529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7720669268062826468148077 2895250975523559925555529)
            ·
              refine ⟨2171438231642669944166647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2895250975523559925555529 2171438231642669944166647)
              ·
                refine ⟨3257157347464004916249971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2171438231642669944166647 3257157347464004916249971)
                ·
                  refine ⟨4885736021196007374374957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3257157347464004916249971 4885736021196007374374957)
                  ·
                    refine ⟨1832151007948502765390609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4885736021196007374374957 1832151007948502765390609)
                    ·
                      refine ⟨1374113255961377074042957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1832151007948502765390609 1374113255961377074042957)
                      ·
                        rfl

theorem cell23_2676076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 3, 2].length) (baseStart_2676076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2676076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2676076 prefixEnd_2676076 := by exact prefixLift 2676076
  have htrace : WordTrace (prefixWord ++ tailWord_2676076) baseStart_2676076 baseEnd_2676076 := by
    simpa [prefixWord, tailWord_2676076, baseEnd_2676076] using wordTrace_append hprefix tailTrace_2676076
  have hstable : (prefixWord ++ tailWord_2676076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676076).length < 2 ^ (prefixWord ++ tailWord_2676076).sum := by decide
  have hdescent : baseEnd_2676076 < baseStart_2676076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676089 : List Nat := [1, 2, 1, 3, 2, 1, 5, 2, 2, 2, 2]
def baseStart_2676089 : Nat := 118140960795 + 2676089 * 2 ^ 59
def prefixEnd_2676089 : Nat := 4983230072969 + 3 ^ 40 * 2676089 * 2
def baseEnd_2676089 : Nat := 1374119931209885523180397

theorem tailTrace_2676089 : CollatzResearch.WordTrace tailWord_2676089 prefixEnd_2676089 1374119931209885523180397 := by
  unfold tailWord_2676089
  simp only [CollatzResearch.WordTrace]
  refine ⟨97604984401994067459527321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65069989601329378306351547 97604984401994067459527321)
  ·
    refine ⟨73203738301495550594645491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97604984401994067459527321 73203738301495550594645491)
    ·
      refine ⟨109805607452243325891968237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73203738301495550594645491 109805607452243325891968237)
      ·
        refine ⟨41177102794591247209488089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109805607452243325891968237 41177102794591247209488089)
        ·
          refine ⟨30882827095943435407116067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41177102794591247209488089 30882827095943435407116067)
          ·
            refine ⟨46324240643915153110674101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30882827095943435407116067 46324240643915153110674101)
            ·
              refine ⟨4342897560367045604125697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46324240643915153110674101 4342897560367045604125697)
              ·
                refine ⟨3257173170275284203094273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4342897560367045604125697 3257173170275284203094273)
                ·
                  refine ⟨2442879877706463152320705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3257173170275284203094273 2442879877706463152320705)
                  ·
                    refine ⟨1832159908279847364240529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2442879877706463152320705 1832159908279847364240529)
                    ·
                      refine ⟨1374119931209885523180397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1832159908279847364240529 1374119931209885523180397)
                      ·
                        rfl

theorem cell23_2676089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 2, 2, 2, 2].length) (baseStart_2676089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2676089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2676089 prefixEnd_2676089 := by exact prefixLift 2676089
  have htrace : WordTrace (prefixWord ++ tailWord_2676089) baseStart_2676089 baseEnd_2676089 := by
    simpa [prefixWord, tailWord_2676089, baseEnd_2676089] using wordTrace_append hprefix tailTrace_2676089
  have hstable : (prefixWord ++ tailWord_2676089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676089).length < 2 ^ (prefixWord ++ tailWord_2676089).sum := by decide
  have hdescent : baseEnd_2676089 < baseStart_2676089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676108 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 3, 7]
def baseStart_2676108 : Nat := 118140960795 + 2676108 * 2 ^ 59
def prefixEnd_2676108 : Nat := 4983230072969 + 3 ^ 40 * 2676108 * 2
def baseEnd_2676108 : Nat := 458043229114106982947603

theorem tailTrace_2676108 : CollatzResearch.WordTrace tailWord_2676108 prefixEnd_2676108 458043229114106982947603 := by
  unfold tailWord_2676108
  simp only [CollatzResearch.WordTrace]
  refine ⟨48802838694462616852234489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65070451592616822469645985 48802838694462616852234489)
  ·
    refine ⟨36602129020846962639175867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48802838694462616852234489 36602129020846962639175867)
    ·
      refine ⟨54903193531270443958763801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36602129020846962639175867 54903193531270443958763801)
      ·
        refine ⟨41177395148452832969072851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54903193531270443958763801 41177395148452832969072851)
        ·
          refine ⟨61766092722679249453609277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41177395148452832969072851 61766092722679249453609277)
          ·
            refine ⟨23162284771004718545103479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61766092722679249453609277 23162284771004718545103479)
            ·
              refine ⟨34743427156507077817655219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23162284771004718545103479 34743427156507077817655219)
              ·
                refine ⟨52115140734760616726482829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34743427156507077817655219 52115140734760616726482829)
                ·
                  refine ⟨19543177775535231272431061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52115140734760616726482829 19543177775535231272431061)
                  ·
                    refine ⟨458043229114106982947603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19543177775535231272431061 458043229114106982947603)
                    ·
                      rfl

theorem cell23_2676108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 3, 7].length) (baseStart_2676108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2676108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2676108 prefixEnd_2676108 := by exact prefixLift 2676108
  have htrace : WordTrace (prefixWord ++ tailWord_2676108) baseStart_2676108 baseEnd_2676108 := by
    simpa [prefixWord, tailWord_2676108, baseEnd_2676108] using wordTrace_append hprefix tailTrace_2676108
  have hstable : (prefixWord ++ tailWord_2676108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676108).length < 2 ^ (prefixWord ++ tailWord_2676108).sum := by decide
  have hdescent : baseEnd_2676108 < baseStart_2676108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676125 : List Nat := [1, 4, 2, 1, 3, 1, 2, 1, 1, 7]
def baseStart_2676125 : Nat := 118140960795 + 2676125 * 2 ^ 59
def prefixEnd_2676125 : Nat := 4983230072969 + 3 ^ 40 * 2676125 * 2
def baseEnd_2676125 : Nat := 458046138837815794110077

theorem tailTrace_2676125 : CollatzResearch.WordTrace tailWord_2676125 prefixEnd_2676125 458046138837815794110077 := by
  unfold tailWord_2676125
  simp only [CollatzResearch.WordTrace]
  refine ⟨97606297429863645607837829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65070864953242430405225219 97606297429863645607837829)
  ·
    refine ⟨18301180768099433551469593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97606297429863645607837829 18301180768099433551469593)
    ·
      refine ⟨13725885576074575163602195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18301180768099433551469593 13725885576074575163602195)
      ·
        refine ⟨20588828364111862745403293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13725885576074575163602195 20588828364111862745403293)
        ·
          refine ⟨7720810636541948529526235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20588828364111862745403293 7720810636541948529526235)
          ·
            refine ⟨11581215954812922794289353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7720810636541948529526235 11581215954812922794289353)
            ·
              refine ⟨8685911966109692095717015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11581215954812922794289353 8685911966109692095717015)
              ·
                refine ⟨13028867949164538143575523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8685911966109692095717015 13028867949164538143575523)
                ·
                  refine ⟨19543301923746807215363285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13028867949164538143575523 19543301923746807215363285)
                  ·
                    refine ⟨458046138837815794110077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19543301923746807215363285 458046138837815794110077)
                    ·
                      rfl

theorem cell23_2676125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_2676125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2676125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2676125 prefixEnd_2676125 := by exact prefixLift 2676125
  have htrace : WordTrace (prefixWord ++ tailWord_2676125) baseStart_2676125 baseEnd_2676125 := by
    simpa [prefixWord, tailWord_2676125, baseEnd_2676125] using wordTrace_append hprefix tailTrace_2676125
  have hstable : (prefixWord ++ tailWord_2676125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676125).length < 2 ^ (prefixWord ++ tailWord_2676125).sum := by decide
  have hdescent : baseEnd_2676125 < baseStart_2676125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676135 : List Nat := [1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 5]
def baseStart_2676135 : Nat := 118140960795 + 2676135 * 2 ^ 59
def prefixEnd_2676135 : Nat := 4983230072969 + 3 ^ 40 * 2676135 * 2
def baseEnd_2676135 : Nat := 1374143551319992343205185

theorem tailTrace_2676135 : CollatzResearch.WordTrace tailWord_2676135 prefixEnd_2676135 1374143551319992343205185 := by
  unfold tailWord_2676135
  simp only [CollatzResearch.WordTrace]
  refine ⟨97606662159827417315701859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65071108106551611543801239 97606662159827417315701859)
  ·
    refine ⟨146409993239741125973552789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97606662159827417315701859 146409993239741125973552789)
    ·
      refine ⟨6862968433112865280010287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 146409993239741125973552789 6862968433112865280010287)
      ·
        refine ⟨10294452649669297920015431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6862968433112865280010287 10294452649669297920015431)
        ·
          refine ⟨15441678974503946880023147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10294452649669297920015431 15441678974503946880023147)
          ·
            refine ⟨23162518461755920320034721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15441678974503946880023147 23162518461755920320034721)
            ·
              refine ⟨17371888846316940240026041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23162518461755920320034721 17371888846316940240026041)
              ·
                refine ⟨13028916634737705180019531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17371888846316940240026041 13028916634737705180019531)
                ·
                  refine ⟨19543374952106557770029297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13028916634737705180019531 19543374952106557770029297)
                  ·
                    refine ⟨14657531214079918327521973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19543374952106557770029297 14657531214079918327521973)
                    ·
                      refine ⟨1374143551319992343205185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14657531214079918327521973 1374143551319992343205185)
                      ·
                        rfl

theorem cell23_2676135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_2676135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2676135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2676135 prefixEnd_2676135 := by exact prefixLift 2676135
  have htrace : WordTrace (prefixWord ++ tailWord_2676135) baseStart_2676135 baseEnd_2676135 := by
    simpa [prefixWord, tailWord_2676135, baseEnd_2676135] using wordTrace_append hprefix tailTrace_2676135
  have hstable : (prefixWord ++ tailWord_2676135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676135).length < 2 ^ (prefixWord ++ tailWord_2676135).sum := by decide
  have hdescent : baseEnd_2676135 < baseStart_2676135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676230 : List Nat := [6, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4]
def baseStart_2676230 : Nat := 118140960795 + 2676230 * 2 ^ 59
def prefixEnd_2676230 : Nat := 4983230072969 + 3 ^ 40 * 2676230 * 2
def baseEnd_2676230 : Nat := 1374192331982169471517249

theorem tailTrace_2676230 : CollatzResearch.WordTrace tailWord_2676230 prefixEnd_2676230 1374192331982169471517249 := by
  unfold tailWord_2676230
  simp only [CollatzResearch.WordTrace]
  refine ⟨3050316471702601516887817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 65073418062988832360273429 3050316471702601516887817)
  ·
    refine ⟨2287737353776951137665863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3050316471702601516887817 2287737353776951137665863)
    ·
      refine ⟨3431606030665426706498795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2287737353776951137665863 3431606030665426706498795)
      ·
        refine ⟨5147409045998140059748193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3431606030665426706498795 5147409045998140059748193)
        ·
          refine ⟨3860556784498605044811145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5147409045998140059748193 3860556784498605044811145)
          ·
            refine ⟨2895417588373953783608359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3860556784498605044811145 2895417588373953783608359)
            ·
              refine ⟨4343126382560930675412539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2895417588373953783608359 4343126382560930675412539)
              ·
                refine ⟨6514689573841396013118809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4343126382560930675412539 6514689573841396013118809)
                ·
                  refine ⟨4886017180381047009839107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6514689573841396013118809 4886017180381047009839107)
                  ·
                    refine ⟨7329025770571570514758661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4886017180381047009839107 7329025770571570514758661)
                    ·
                      refine ⟨1374192331982169471517249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7329025770571570514758661 1374192331982169471517249)
                      ·
                        rfl

theorem cell23_2676230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_2676230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2676230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2676230 prefixEnd_2676230 := by exact prefixLift 2676230
  have htrace : WordTrace (prefixWord ++ tailWord_2676230) baseStart_2676230 baseEnd_2676230 := by
    simpa [prefixWord, tailWord_2676230, baseEnd_2676230] using wordTrace_append hprefix tailTrace_2676230
  have hstable : (prefixWord ++ tailWord_2676230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676230).length < 2 ^ (prefixWord ++ tailWord_2676230).sum := by decide
  have hdescent : baseEnd_2676230 < baseStart_2676230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676302 : List Nat := [4, 1, 1, 1, 1, 2, 1, 3, 3, 3, 3]
def baseStart_2676302 : Nat := 118140960795 + 2676302 * 2 ^ 59
def prefixEnd_2676302 : Nat := 4983230072969 + 3 ^ 40 * 2676302 * 2
def baseEnd_2676302 : Nat := 1374229302589293189816917

theorem tailTrace_2676302 : CollatzResearch.WordTrace tailWord_2676302 prefixEnd_2676302 1374229302589293189816917 := by
  unfold tailWord_2676302
  simp only [CollatzResearch.WordTrace]
  refine ⟨12201594143777800604628895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65075168766814936558020773 12201594143777800604628895)
  ·
    refine ⟨18302391215666700906943343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12201594143777800604628895 18302391215666700906943343)
    ·
      refine ⟨27453586823500051360415015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18302391215666700906943343 27453586823500051360415015)
      ·
        refine ⟨41180380235250077040622523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27453586823500051360415015 41180380235250077040622523)
        ·
          refine ⟨61770570352875115560933785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41180380235250077040622523 61770570352875115560933785)
          ·
            refine ⟨46327927764656336670700339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61770570352875115560933785 46327927764656336670700339)
            ·
              refine ⟨69491891646984505006050509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46327927764656336670700339 69491891646984505006050509)
              ·
                refine ⟨26059459367619189377268941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69491891646984505006050509 26059459367619189377268941)
                ·
                  refine ⟨9772297262857196016475853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26059459367619189377268941 9772297262857196016475853)
                  ·
                    refine ⟨3664611473571448506178445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9772297262857196016475853 3664611473571448506178445)
                    ·
                      refine ⟨1374229302589293189816917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3664611473571448506178445 1374229302589293189816917)
                      ·
                        rfl

theorem cell23_2676302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 3, 3, 3].length) (baseStart_2676302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2676302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2676302 prefixEnd_2676302 := by exact prefixLift 2676302
  have htrace : WordTrace (prefixWord ++ tailWord_2676302) baseStart_2676302 baseEnd_2676302 := by
    simpa [prefixWord, tailWord_2676302, baseEnd_2676302] using wordTrace_append hprefix tailTrace_2676302
  have hstable : (prefixWord ++ tailWord_2676302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676302).length < 2 ^ (prefixWord ++ tailWord_2676302).sum := by decide
  have hdescent : baseEnd_2676302 < baseStart_2676302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676335 : List Nat := [1, 1, 2, 1, 3, 2, 1, 3, 1, 8]
def baseStart_2676335 : Nat := 118140960795 + 2676335 * 2 ^ 59
def prefixEnd_2676335 : Nat := 4983230072969 + 3 ^ 40 * 2676335 * 2
def baseEnd_2676335 : Nat := 458082082483630520234755

theorem tailTrace_2676335 : CollatzResearch.WordTrace tailWord_2676335 prefixEnd_2676335 458082082483630520234755 := by
  unfold tailWord_2676335
  simp only [CollatzResearch.WordTrace]
  refine ⟨97613956759102851472982459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65075971172735234315321639 97613956759102851472982459)
  ·
    refine ⟨146420935138654277209473689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97613956759102851472982459 146420935138654277209473689)
    ·
      refine ⟨109815701353990707907105267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146420935138654277209473689 109815701353990707907105267)
      ·
        refine ⟨164723552030986061860657901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109815701353990707907105267 164723552030986061860657901)
        ·
          refine ⟨61771332011619773197746713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164723552030986061860657901 61771332011619773197746713)
          ·
            refine ⟨46328499008714829898310035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61771332011619773197746713 46328499008714829898310035)
            ·
              refine ⟨69492748513072244847465053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46328499008714829898310035 69492748513072244847465053)
              ·
                refine ⟨26059780692402091817799395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69492748513072244847465053 26059780692402091817799395)
                ·
                  refine ⟨39089671038603137726699093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26059780692402091817799395 39089671038603137726699093)
                  ·
                    refine ⟨458082082483630520234755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 39089671038603137726699093 458082082483630520234755)
                    ·
                      rfl

theorem cell23_2676335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 8].length) (baseStart_2676335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2676335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2676335 prefixEnd_2676335 := by exact prefixLift 2676335
  have htrace : WordTrace (prefixWord ++ tailWord_2676335) baseStart_2676335 baseEnd_2676335 := by
    simpa [prefixWord, tailWord_2676335, baseEnd_2676335] using wordTrace_append hprefix tailTrace_2676335
  have hstable : (prefixWord ++ tailWord_2676335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676335).length < 2 ^ (prefixWord ++ tailWord_2676335).sum := by decide
  have hdescent : baseEnd_2676335 < baseStart_2676335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676336 : List Nat := [2, 1, 1, 1, 6, 2, 1, 3, 2, 1, 3]
def baseStart_2676336 : Nat := 118140960795 + 2676336 * 2 ^ 59
def prefixEnd_2676336 : Nat := 4983230072969 + 3 ^ 40 * 2676336 * 2
def baseEnd_2676336 : Nat := 1374246760931546056791761

theorem tailTrace_2676336 : CollatzResearch.WordTrace tailWord_2676336 prefixEnd_2676336 1374246760931546056791761 := by
  unfold tailWord_2676336
  simp only [CollatzResearch.WordTrace]
  refine ⟨48806996616049614321884431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65075995488066152429179241 48806996616049614321884431)
  ·
    refine ⟨73210494924074421482826647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48806996616049614321884431 73210494924074421482826647)
    ·
      refine ⟨109815742386111632224239971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73210494924074421482826647 109815742386111632224239971)
      ·
        refine ⟨164723613579167448336359957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109815742386111632224239971 164723613579167448336359957)
        ·
          refine ⟨7721419386523474140766873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 164723613579167448336359957 7721419386523474140766873)
          ·
            refine ⟨5791064539892605605575155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7721419386523474140766873 5791064539892605605575155)
            ·
              refine ⟨8686596809838908408362733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5791064539892605605575155 8686596809838908408362733)
              ·
                refine ⟨3257473803689590653136025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8686596809838908408362733 3257473803689590653136025)
                ·
                  refine ⟨2443105352767192989852019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3257473803689590653136025 2443105352767192989852019)
                  ·
                    refine ⟨3664658029150789484778029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2443105352767192989852019 3664658029150789484778029)
                    ·
                      refine ⟨1374246760931546056791761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3664658029150789484778029 1374246760931546056791761)
                      ·
                        rfl

theorem cell23_2676336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 3, 2, 1, 3].length) (baseStart_2676336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2676336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2676336 prefixEnd_2676336 := by exact prefixLift 2676336
  have htrace : WordTrace (prefixWord ++ tailWord_2676336) baseStart_2676336 baseEnd_2676336 := by
    simpa [prefixWord, tailWord_2676336, baseEnd_2676336] using wordTrace_append hprefix tailTrace_2676336
  have hstable : (prefixWord ++ tailWord_2676336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676336).length < 2 ^ (prefixWord ++ tailWord_2676336).sum := by decide
  have hdescent : baseEnd_2676336 < baseStart_2676336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676359 : List Nat := [1, 1, 4, 2, 1, 3, 1, 1, 3, 4, 2]
def baseStart_2676359 : Nat := 118140960795 + 2676359 * 2 ^ 59
def prefixEnd_2676359 : Nat := 4983230072969 + 3 ^ 40 * 2676359 * 2
def baseEnd_2676359 : Nat := 1374258570986599466804155

theorem tailTrace_2676359 : CollatzResearch.WordTrace tailWord_2676359 prefixEnd_2676359 1374258570986599466804155 := by
  unfold tailWord_2676359
  simp only [CollatzResearch.WordTrace]
  refine ⟨97614832111015903571856131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65076554740677269047904087 97614832111015903571856131)
  ·
    refine ⟨146422248166523855357784197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97614832111015903571856131 146422248166523855357784197)
    ·
      refine ⟨27454171531223222879584537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146422248166523855357784197 27454171531223222879584537)
      ·
        refine ⟨20590628648417417159688403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27454171531223222879584537 20590628648417417159688403)
        ·
          refine ⟨30885942972626125739532605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20590628648417417159688403 30885942972626125739532605)
          ·
            refine ⟨11582228614734797152324727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30885942972626125739532605 11582228614734797152324727)
            ·
              refine ⟨17373342922102195728487091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11582228614734797152324727 17373342922102195728487091)
              ·
                refine ⟨26060014383153293592730637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17373342922102195728487091 26060014383153293592730637)
                ·
                  refine ⟨9772505393682485097273989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26060014383153293592730637 9772505393682485097273989)
                  ·
                    refine ⟨1832344761315465955738873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9772505393682485097273989 1832344761315465955738873)
                    ·
                      refine ⟨1374258570986599466804155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1832344761315465955738873 1374258570986599466804155)
                      ·
                        rfl

theorem cell23_2676359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 4, 2].length) (baseStart_2676359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2676359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2676359 prefixEnd_2676359 := by exact prefixLift 2676359
  have htrace : WordTrace (prefixWord ++ tailWord_2676359) baseStart_2676359 baseEnd_2676359 := by
    simpa [prefixWord, tailWord_2676359, baseEnd_2676359] using wordTrace_append hprefix tailTrace_2676359
  have hstable : (prefixWord ++ tailWord_2676359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676359).length < 2 ^ (prefixWord ++ tailWord_2676359).sum := by decide
  have hdescent : baseEnd_2676359 < baseStart_2676359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676386 : List Nat := [3, 3, 1, 4, 1, 1, 1, 1, 2, 6]
def baseStart_2676386 : Nat := 118140960795 + 2676386 * 2 ^ 59
def prefixEnd_2676386 : Nat := 4983230072969 + 3 ^ 40 * 2676386 * 2
def baseEnd_2676386 : Nat := 458090811654756953722177

theorem tailTrace_2676386 : CollatzResearch.WordTrace tailWord_2676386 prefixEnd_2676386 458090811654756953722177 := by
  unfold tailWord_2676386
  simp only [CollatzResearch.WordTrace]
  refine ⟨24403954220479521795772253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65077211254612058122059341 24403954220479521795772253)
  ·
    refine ⟨9151482832679820673414595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24403954220479521795772253 9151482832679820673414595)
    ·
      refine ⟨13727224249019731010121893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9151482832679820673414595 13727224249019731010121893)
      ·
        refine ⟨2573854546691199564397855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13727224249019731010121893 2573854546691199564397855)
        ·
          refine ⟨3860781820036799346596783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2573854546691199564397855 3860781820036799346596783)
          ·
            refine ⟨5791172730055199019895175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3860781820036799346596783 5791172730055199019895175)
            ·
              refine ⟨8686759095082798529842763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5791172730055199019895175 8686759095082798529842763)
              ·
                refine ⟨13030138642624197794764145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8686759095082798529842763 13030138642624197794764145)
                ·
                  refine ⟨9772603981968148346073109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13030138642624197794764145 9772603981968148346073109)
                  ·
                    refine ⟨458090811654756953722177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9772603981968148346073109 458090811654756953722177)
                    ·
                      rfl

theorem cell23_2676386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_2676386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2676386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2676386 prefixEnd_2676386 := by exact prefixLift 2676386
  have htrace : WordTrace (prefixWord ++ tailWord_2676386) baseStart_2676386 baseEnd_2676386 := by
    simpa [prefixWord, tailWord_2676386, baseEnd_2676386] using wordTrace_append hprefix tailTrace_2676386
  have hstable : (prefixWord ++ tailWord_2676386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676386).length < 2 ^ (prefixWord ++ tailWord_2676386).sum := by decide
  have hdescent : baseEnd_2676386 < baseStart_2676386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676459 : List Nat := [1, 1, 1, 1, 2, 4, 4, 2, 3, 4]
def baseStart_2676459 : Nat := 118140960795 + 2676459 * 2 ^ 59
def prefixEnd_2676459 : Nat := 4983230072969 + 3 ^ 40 * 2676459 * 2
def baseEnd_2676459 : Nat := 458103306350683025184565

theorem tailTrace_2676459 : CollatzResearch.WordTrace tailWord_2676459 prefixEnd_2676459 458103306350683025184565 := by
  unfold tailWord_2676459
  simp only [CollatzResearch.WordTrace]
  refine ⟨97618479410653620650496431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65078986273769080433664287 97618479410653620650496431)
  ·
    refine ⟨146427719115980430975744647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97618479410653620650496431 146427719115980430975744647)
    ·
      refine ⟨219641578673970646463616971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146427719115980430975744647 219641578673970646463616971)
      ·
        refine ⟨329462368010955969695425457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219641578673970646463616971 329462368010955969695425457)
        ·
          refine ⟨247096776008216977271569093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 329462368010955969695425457 247096776008216977271569093)
          ·
            refine ⟨46330645501540683238419205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 247096776008216977271569093 46330645501540683238419205)
            ·
              refine ⟨8686996031538878107203601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46330645501540683238419205 8686996031538878107203601)
              ·
                refine ⟨6515247023654158580402701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8686996031538878107203601 6515247023654158580402701)
                ·
                  refine ⟨2443217633870309467651013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6515247023654158580402701 2443217633870309467651013)
                  ·
                    refine ⟨458103306350683025184565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2443217633870309467651013 458103306350683025184565)
                    ·
                      rfl

theorem cell23_2676459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 3, 4].length) (baseStart_2676459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2676459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2676459 prefixEnd_2676459 := by exact prefixLift 2676459
  have htrace : WordTrace (prefixWord ++ tailWord_2676459) baseStart_2676459 baseEnd_2676459 := by
    simpa [prefixWord, tailWord_2676459, baseEnd_2676459] using wordTrace_append hprefix tailTrace_2676459
  have hstable : (prefixWord ++ tailWord_2676459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676459).length < 2 ^ (prefixWord ++ tailWord_2676459).sum := by decide
  have hdescent : baseEnd_2676459 < baseStart_2676459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676492 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 1, 1, 8]
def baseStart_2676492 : Nat := 118140960795 + 2676492 * 2 ^ 59
def prefixEnd_2676492 : Nat := 4983230072969 + 3 ^ 40 * 2676492 * 2
def baseEnd_2676492 : Nat := 1374326863913647446441043

theorem tailTrace_2676492 : CollatzResearch.WordTrace tailWord_2676492 prefixEnd_2676492 1374326863913647446441043 := by
  unfold tailWord_2676492
  simp only [CollatzResearch.WordTrace]
  refine ⟨48809841509767033643223865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65079788679689378190965153 48809841509767033643223865)
  ·
    refine ⟨36607381132325275232417899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48809841509767033643223865 36607381132325275232417899)
    ·
      refine ⟨54911071698487912848626849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36607381132325275232417899 54911071698487912848626849)
      ·
        refine ⟨41183303773865934636470137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54911071698487912848626849 41183303773865934636470137)
        ·
          refine ⟨30887477830399450977352603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41183303773865934636470137 30887477830399450977352603)
          ·
            refine ⟨46331216745599176466028905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30887477830399450977352603 46331216745599176466028905)
            ·
              refine ⟨34748412559199382349521679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46331216745599176466028905 34748412559199382349521679)
              ·
                refine ⟨52122618838799073524282519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34748412559199382349521679 52122618838799073524282519)
                ·
                  refine ⟨78183928258198610286423779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52122618838799073524282519 78183928258198610286423779)
                  ·
                    refine ⟨117275892387297915429635669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 78183928258198610286423779 117275892387297915429635669)
                    ·
                      refine ⟨1374326863913647446441043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 117275892387297915429635669 1374326863913647446441043)
                      ·
                        rfl

theorem cell23_2676492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_2676492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2676492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2676492 prefixEnd_2676492 := by exact prefixLift 2676492
  have htrace : WordTrace (prefixWord ++ tailWord_2676492) baseStart_2676492 baseEnd_2676492 := by
    simpa [prefixWord, tailWord_2676492, baseEnd_2676492] using wordTrace_append hprefix tailTrace_2676492
  have hstable : (prefixWord ++ tailWord_2676492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676492).length < 2 ^ (prefixWord ++ tailWord_2676492).sum := by decide
  have hdescent : baseEnd_2676492 < baseStart_2676492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676506 : List Nat := [3, 1, 1, 3, 2, 2, 4, 1, 6]
def baseStart_2676506 : Nat := 118140960795 + 2676506 * 2 ^ 59
def prefixEnd_2676506 : Nat := 4983230072969 + 3 ^ 40 * 2676506 * 2
def baseEnd_2676506 : Nat := 152703783626978932407331

theorem tailTrace_2676506 : CollatzResearch.WordTrace tailWord_2676506 prefixEnd_2676506 152703783626978932407331 := by
  unfold tailWord_2676506
  simp only [CollatzResearch.WordTrace]
  refine ⟨24405048410370836919364343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65080129094322231784971581 24405048410370836919364343)
  ·
    refine ⟨36607572615556255379046515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24405048410370836919364343 36607572615556255379046515)
    ·
      refine ⟨54911358923334383068569773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36607572615556255379046515 54911358923334383068569773)
      ·
        refine ⟨20591759596250393650713665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54911358923334383068569773 20591759596250393650713665)
        ·
          refine ⟨15443819697187795238035249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20591759596250393650713665 15443819697187795238035249)
          ·
            refine ⟨11582864772890846428526437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15443819697187795238035249 11582864772890846428526437)
            ·
              refine ⟨2171787144917033705348707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11582864772890846428526437 2171787144917033705348707)
              ·
                refine ⟨3257680717375550558023061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2171787144917033705348707 3257680717375550558023061)
                ·
                  refine ⟨152703783626978932407331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3257680717375550558023061 152703783626978932407331)
                  ·
                    rfl

theorem cell23_2676506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 1, 6].length) (baseStart_2676506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2676506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2676506 prefixEnd_2676506 := by exact prefixLift 2676506
  have htrace : WordTrace (prefixWord ++ tailWord_2676506) baseStart_2676506 baseEnd_2676506 := by
    simpa [prefixWord, tailWord_2676506, baseEnd_2676506] using wordTrace_append hprefix tailTrace_2676506
  have hstable : (prefixWord ++ tailWord_2676506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676506).length < 2 ^ (prefixWord ++ tailWord_2676506).sum := by decide
  have hdescent : baseEnd_2676506 < baseStart_2676506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676576 : List Nat := [2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 3]
def baseStart_2676576 : Nat := 118140960795 + 2676576 * 2 ^ 59
def prefixEnd_2676576 : Nat := 4983230072969 + 3 ^ 40 * 2676576 * 2
def baseEnd_2676576 : Nat := 1374369996288625117790657

theorem tailTrace_2676576 : CollatzResearch.WordTrace tailWord_2676576 prefixEnd_2676576 1374369996288625117790657 := by
  unfold tailWord_2676576
  simp only [CollatzResearch.WordTrace]
  refine ⟨48811373375614874816252791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65081831167486499755003721 48811373375614874816252791)
  ·
    refine ⟨73217060063422312224379187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48811373375614874816252791 73217060063422312224379187)
    ·
      refine ⟨109825590095133468336568781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73217060063422312224379187 109825590095133468336568781)
      ·
        refine ⟨41184596285675050626213293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109825590095133468336568781 41184596285675050626213293)
        ·
          refine ⟨15444223607128143984829985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41184596285675050626213293 15444223607128143984829985)
          ·
            refine ⟨11583167705346107988622489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15444223607128143984829985 11583167705346107988622489)
            ·
              refine ⟨8687375779009580991466867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11583167705346107988622489 8687375779009580991466867)
              ·
                refine ⟨13031063668514371487200301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8687375779009580991466867 13031063668514371487200301)
                ·
                  refine ⟨4886648875692889307700113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13031063668514371487200301 4886648875692889307700113)
                  ·
                    refine ⟨3664986656769666980775085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4886648875692889307700113 3664986656769666980775085)
                    ·
                      refine ⟨1374369996288625117790657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3664986656769666980775085 1374369996288625117790657)
                      ·
                        rfl

theorem cell23_2676576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 3].length) (baseStart_2676576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2676576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2676576 prefixEnd_2676576 := by exact prefixLift 2676576
  have htrace : WordTrace (prefixWord ++ tailWord_2676576) baseStart_2676576 baseEnd_2676576 := by
    simpa [prefixWord, tailWord_2676576, baseEnd_2676576] using wordTrace_append hprefix tailTrace_2676576
  have hstable : (prefixWord ++ tailWord_2676576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676576).length < 2 ^ (prefixWord ++ tailWord_2676576).sum := by decide
  have hdescent : baseEnd_2676576 < baseStart_2676576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676590 : List Nat := [4, 1, 2, 3, 1, 1, 4, 1, 1, 1, 4]
def baseStart_2676590 : Nat := 118140960795 + 2676590 * 2 ^ 59
def prefixEnd_2676590 : Nat := 4983230072969 + 3 ^ 40 * 2676590 * 2
def baseEnd_2676590 : Nat := 1374377185017788063015593

theorem tailTrace_2676590 : CollatzResearch.WordTrace tailWord_2676590 prefixEnd_2676590 1374377185017788063015593 := by
  unfold tailWord_2676590
  simp only [CollatzResearch.WordTrace]
  refine ⟨12202907171647378752939403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65082171582119353349010149 12202907171647378752939403)
  ·
    refine ⟨18304360757471068129409105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12202907171647378752939403 18304360757471068129409105)
    ·
      refine ⟨13728270568103301097056829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18304360757471068129409105 13728270568103301097056829)
      ·
        refine ⟨5148101463038737911396311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13728270568103301097056829 5148101463038737911396311)
        ·
          refine ⟨7722152194558106867094467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5148101463038737911396311 7722152194558106867094467)
          ·
            refine ⟨11583228291837160300641701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7722152194558106867094467 11583228291837160300641701)
            ·
              refine ⟨2171855304719467556370319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11583228291837160300641701 2171855304719467556370319)
              ·
                refine ⟨3257782957079201334555479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2171855304719467556370319 3257782957079201334555479)
                ·
                  refine ⟨4886674435618802001833219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3257782957079201334555479 4886674435618802001833219)
                  ·
                    refine ⟨7330011653428203002749829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4886674435618802001833219 7330011653428203002749829)
                    ·
                      refine ⟨1374377185017788063015593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7330011653428203002749829 1374377185017788063015593)
                      ·
                        rfl

theorem cell23_2676590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_2676590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2676590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2676590 prefixEnd_2676590 := by exact prefixLift 2676590
  have htrace : WordTrace (prefixWord ++ tailWord_2676590) baseStart_2676590 baseEnd_2676590 := by
    simpa [prefixWord, tailWord_2676590, baseEnd_2676590] using wordTrace_append hprefix tailTrace_2676590
  have hstable : (prefixWord ++ tailWord_2676590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676590).length < 2 ^ (prefixWord ++ tailWord_2676590).sum := by decide
  have hdescent : baseEnd_2676590 < baseStart_2676590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676630 : List Nat := [5, 3, 1, 1, 2, 1, 1, 9]
def baseStart_2676630 : Nat := 118140960795 + 2676630 * 2 ^ 59
def prefixEnd_2676630 : Nat := 4983230072969 + 3 ^ 40 * 2676630 * 2
def baseEnd_2676630 : Nat := 50903619416443255796867

theorem tailTrace_2676630 : CollatzResearch.WordTrace tailWord_2676630 prefixEnd_2676630 50903619416443255796867 := by
  unfold tailWord_2676630
  simp only [CollatzResearch.WordTrace]
  refine ⟨6101544768314632303435709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65083144195356077903314229 6101544768314632303435709)
  ·
    refine ⟨2288079288117987113788391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6101544768314632303435709 2288079288117987113788391)
    ·
      refine ⟨3432118932176980670682587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2288079288117987113788391 3432118932176980670682587)
      ·
        refine ⟨5148178398265471006023881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3432118932176980670682587 5148178398265471006023881)
        ·
          refine ⟨3861133798699103254517911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5148178398265471006023881 3861133798699103254517911)
          ·
            refine ⟨5791700698048654881776867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3861133798699103254517911 5791700698048654881776867)
            ·
              refine ⟨8687551047072982322665301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5791700698048654881776867 8687551047072982322665301)
              ·
                refine ⟨50903619416443255796867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8687551047072982322665301 50903619416443255796867)
                ·
                  rfl

theorem cell23_2676630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 9].length) (baseStart_2676630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2676630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2676630 prefixEnd_2676630 := by exact prefixLift 2676630
  have htrace : WordTrace (prefixWord ++ tailWord_2676630) baseStart_2676630 baseEnd_2676630 := by
    simpa [prefixWord, tailWord_2676630, baseEnd_2676630] using wordTrace_append hprefix tailTrace_2676630
  have hstable : (prefixWord ++ tailWord_2676630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676630).length < 2 ^ (prefixWord ++ tailWord_2676630).sum := by decide
  have hdescent : baseEnd_2676630 < baseStart_2676630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676633 : List Nat := [1, 2, 1, 2, 1, 3, 3, 4, 1, 3, 2]
def baseStart_2676633 : Nat := 118140960795 + 2676633 * 2 ^ 59
def prefixEnd_2676633 : Nat := 4983230072969 + 3 ^ 40 * 2676633 * 2
def baseEnd_2676633 : Nat := 1374399264685931394777895

theorem tailTrace_2676633 : CollatzResearch.WordTrace tailWord_2676633 prefixEnd_2676633 1374399264685931394777895 := by
  unfold tailWord_2676633
  simp only [CollatzResearch.WordTrace]
  refine ⟨97624825712023248367330553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65083217141348832244887035 97624825712023248367330553)
  ·
    refine ⟨73218619284017436275497915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97624825712023248367330553 73218619284017436275497915)
    ·
      refine ⟨109827928926026154413246873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73218619284017436275497915 109827928926026154413246873)
      ·
        refine ⟨82370946694519615809935155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109827928926026154413246873 82370946694519615809935155)
        ·
          refine ⟨123556420041779423714902733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82370946694519615809935155 123556420041779423714902733)
          ·
            refine ⟨46333657515667283893088525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123556420041779423714902733 46333657515667283893088525)
            ·
              refine ⟨17375121568375231459908197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46333657515667283893088525 17375121568375231459908197)
              ·
                refine ⟨3257835294070355898732787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17375121568375231459908197 3257835294070355898732787)
                ·
                  refine ⟨4886752941105533848099181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3257835294070355898732787 4886752941105533848099181)
                  ·
                    refine ⟨1832532352914575193037193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4886752941105533848099181 1832532352914575193037193)
                    ·
                      refine ⟨1374399264685931394777895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1832532352914575193037193 1374399264685931394777895)
                      ·
                        rfl

theorem cell23_2676633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 4, 1, 3, 2].length) (baseStart_2676633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2676633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2676633 prefixEnd_2676633 := by exact prefixLift 2676633
  have htrace : WordTrace (prefixWord ++ tailWord_2676633) baseStart_2676633 baseEnd_2676633 := by
    simpa [prefixWord, tailWord_2676633, baseEnd_2676633] using wordTrace_append hprefix tailTrace_2676633
  have hstable : (prefixWord ++ tailWord_2676633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676633).length < 2 ^ (prefixWord ++ tailWord_2676633).sum := by decide
  have hdescent : baseEnd_2676633 < baseStart_2676633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676636 : List Nat := [2, 2, 3, 3, 1, 1, 1, 1, 2, 2, 5]
def baseStart_2676636 : Nat := 118140960795 + 2676636 * 2 ^ 59
def prefixEnd_2676636 : Nat := 4983230072969 + 3 ^ 40 * 2676636 * 2
def baseEnd_2676636 : Nat := 1374400805127894883040381

theorem tailTrace_2676636 : CollatzResearch.WordTrace tailWord_2676636 prefixEnd_2676636 1374400805127894883040381 := by
  unfold tailWord_2676636
  simp only [CollatzResearch.WordTrace]
  refine ⟨48812467565506189939844881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65083290087341586586459841 48812467565506189939844881)
  ·
    refine ⟨36609350674129642454883661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48812467565506189939844881 36609350674129642454883661)
    ·
      refine ⟨13728506502798615920581373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36609350674129642454883661 13728506502798615920581373)
      ·
        refine ⟨5148189938549480970218015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13728506502798615920581373 5148189938549480970218015)
        ·
          refine ⟨7722284907824221455327023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5148189938549480970218015 7722284907824221455327023)
          ·
            refine ⟨11583427361736332182990535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7722284907824221455327023 11583427361736332182990535)
            ·
              refine ⟨17375141042604498274485803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11583427361736332182990535 17375141042604498274485803)
              ·
                refine ⟨26062711563906747411728705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17375141042604498274485803 26062711563906747411728705)
                ·
                  refine ⟨19547033672930060558796529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26062711563906747411728705 19547033672930060558796529)
                  ·
                    refine ⟨14660275254697545419097397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19547033672930060558796529 14660275254697545419097397)
                    ·
                      refine ⟨1374400805127894883040381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14660275254697545419097397 1374400805127894883040381)
                      ·
                        rfl

theorem cell23_2676636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_2676636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2676636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2676636 prefixEnd_2676636 := by exact prefixLift 2676636
  have htrace : WordTrace (prefixWord ++ tailWord_2676636) baseStart_2676636 baseEnd_2676636 := by
    simpa [prefixWord, tailWord_2676636, baseEnd_2676636] using wordTrace_append hprefix tailTrace_2676636
  have hstable : (prefixWord ++ tailWord_2676636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676636).length < 2 ^ (prefixWord ++ tailWord_2676636).sum := by decide
  have hdescent : baseEnd_2676636 < baseStart_2676636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676641 : List Nat := [1, 2, 3, 4, 3, 1, 1, 3, 1, 2, 2]
def baseStart_2676641 : Nat := 118140960795 + 2676641 * 2 ^ 59
def prefixEnd_2676641 : Nat := 4983230072969 + 3 ^ 40 * 2676641 * 2
def baseEnd_2676641 : Nat := 1374403372531167363477859

theorem tailTrace_2676641 : CollatzResearch.WordTrace tailWord_2676641 prefixEnd_2676641 1374403372531167363477859 := by
  unfold tailWord_2676641
  simp only [CollatzResearch.WordTrace]
  refine ⟨97625117495994265733621777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65083411663996177155747851 97625117495994265733621777)
  ·
    refine ⟨73218838121995699300216333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97625117495994265733621777 73218838121995699300216333)
    ·
      refine ⟨27457064295748387237581125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73218838121995699300216333 27457064295748387237581125)
      ·
        refine ⟨5148199555452822607046461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27457064295748387237581125 5148199555452822607046461)
        ·
          refine ⟨1930574833294808477642423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5148199555452822607046461 1930574833294808477642423)
          ·
            refine ⟨2895862249942212716463635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1930574833294808477642423 2895862249942212716463635)
            ·
              refine ⟨4343793374913319074695453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2895862249942212716463635 4343793374913319074695453)
              ·
                refine ⟨1628922515592494653010795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4343793374913319074695453 1628922515592494653010795)
                ·
                  refine ⟨2443383773388741979516193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1628922515592494653010795 2443383773388741979516193)
                  ·
                    refine ⟨1832537830041556484637145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2443383773388741979516193 1832537830041556484637145)
                    ·
                      refine ⟨1374403372531167363477859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1832537830041556484637145 1374403372531167363477859)
                      ·
                        rfl

theorem cell23_2676641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_2676641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2676641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2676641 prefixEnd_2676641 := by exact prefixLift 2676641
  have htrace : WordTrace (prefixWord ++ tailWord_2676641) baseStart_2676641 baseEnd_2676641 := by
    simpa [prefixWord, tailWord_2676641, baseEnd_2676641] using wordTrace_append hprefix tailTrace_2676641
  have hstable : (prefixWord ++ tailWord_2676641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676641).length < 2 ^ (prefixWord ++ tailWord_2676641).sum := by decide
  have hdescent : baseEnd_2676641 < baseStart_2676641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676796 : List Nat := [2, 2, 2, 2, 2, 1, 1, 2, 1, 2, 6]
def baseStart_2676796 : Nat := 118140960795 + 2676796 * 2 ^ 59
def prefixEnd_2676796 : Nat := 4983230072969 + 3 ^ 40 * 2676796 * 2
def baseEnd_2676796 : Nat := 1374482962032614257039645

theorem tailTrace_2676796 : CollatzResearch.WordTrace tailWord_2676796 prefixEnd_2676796 1374482962032614257039645 := by
  unfold tailWord_2676796
  simp only [CollatzResearch.WordTrace]
  refine ⟨48815385405216363602757121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65087180540288484803676161 48815385405216363602757121)
  ·
    refine ⟨36611539053912272702067841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48815385405216363602757121 36611539053912272702067841)
    ·
      refine ⟨27458654290434204526550881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36611539053912272702067841 27458654290434204526550881)
      ·
        refine ⟨20593990717825653394913161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27458654290434204526550881 20593990717825653394913161)
        ·
          refine ⟨15445493038369240046184871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20593990717825653394913161 15445493038369240046184871)
          ·
            refine ⟨23168239557553860069277307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15445493038369240046184871 23168239557553860069277307)
            ·
              refine ⟨34752359336330790103915961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23168239557553860069277307 34752359336330790103915961)
              ·
                refine ⟨26064269502248092577936971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34752359336330790103915961 26064269502248092577936971)
                ·
                  refine ⟨39096404253372138866905457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26064269502248092577936971 39096404253372138866905457)
                  ·
                    refine ⟨29322303190029104150179093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39096404253372138866905457 29322303190029104150179093)
                    ·
                      refine ⟨1374482962032614257039645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29322303190029104150179093 1374482962032614257039645)
                      ·
                        rfl

theorem cell23_2676796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_2676796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2676796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2676796 prefixEnd_2676796 := by exact prefixLift 2676796
  have htrace : WordTrace (prefixWord ++ tailWord_2676796) baseStart_2676796 baseEnd_2676796 := by
    simpa [prefixWord, tailWord_2676796, baseEnd_2676796] using wordTrace_append hprefix tailTrace_2676796
  have hstable : (prefixWord ++ tailWord_2676796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676796).length < 2 ^ (prefixWord ++ tailWord_2676796).sum := by decide
  have hdescent : baseEnd_2676796 < baseStart_2676796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676803 : List Nat := [1, 1, 1, 3, 1, 2, 2, 3, 5, 1, 3]
def baseStart_2676803 : Nat := 118140960795 + 2676803 * 2 ^ 59
def prefixEnd_2676803 : Nat := 4983230072969 + 3 ^ 40 * 2676803 * 2
def baseEnd_2676803 : Nat := 1374486556397195729652113

theorem tailTrace_2676803 : CollatzResearch.WordTrace tailWord_2676803 prefixEnd_2676803 1374486556397195729652113 := by
  unfold tailWord_2676803
  simp only [CollatzResearch.WordTrace]
  refine ⟨97631026121407367401019063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65087350747604911600679375 97631026121407367401019063)
  ·
    refine ⟨146446539182111051101528595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97631026121407367401019063 146446539182111051101528595)
    ·
      refine ⟨219669808773166576652292893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146446539182111051101528595 219669808773166576652292893)
      ·
        refine ⟨82376178289937466244609835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 219669808773166576652292893 82376178289937466244609835)
        ·
          refine ⟨123564267434906199366914753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82376178289937466244609835 123564267434906199366914753)
          ·
            refine ⟨92673200576179649525186065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123564267434906199366914753 92673200576179649525186065)
            ·
              refine ⟨69504900432134737143889549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92673200576179649525186065 69504900432134737143889549)
              ·
                refine ⟨26064337662050526428958581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69504900432134737143889549 26064337662050526428958581)
                ·
                  refine ⟨2443531655817236852714867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26064337662050526428958581 2443531655817236852714867)
                  ·
                    refine ⟨3665297483725855279072301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2443531655817236852714867 3665297483725855279072301)
                    ·
                      refine ⟨1374486556397195729652113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3665297483725855279072301 1374486556397195729652113)
                      ·
                        rfl

theorem cell23_2676803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 5, 1, 3].length) (baseStart_2676803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2676803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2676803 prefixEnd_2676803 := by exact prefixLift 2676803
  have htrace : WordTrace (prefixWord ++ tailWord_2676803) baseStart_2676803 baseEnd_2676803 := by
    simpa [prefixWord, tailWord_2676803, baseEnd_2676803] using wordTrace_append hprefix tailTrace_2676803
  have hstable : (prefixWord ++ tailWord_2676803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676803).length < 2 ^ (prefixWord ++ tailWord_2676803).sum := by decide
  have hdescent : baseEnd_2676803 < baseStart_2676803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676823 : List Nat := [1, 1, 3, 2, 2, 1, 4, 3, 1, 5]
def baseStart_2676823 : Nat := 118140960795 + 2676823 * 2 ^ 59
def prefixEnd_2676823 : Nat := 4983230072969 + 3 ^ 40 * 2676823 * 2
def baseEnd_2676823 : Nat := 458165608670095217134007

theorem tailTrace_2676823 : CollatzResearch.WordTrace tailWord_2676823 prefixEnd_2676823 458165608670095217134007 := by
  unfold tailWord_2676823
  simp only [CollatzResearch.WordTrace]
  refine ⟨97631755581334910816747123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65087837054223273877831415 97631755581334910816747123)
  ·
    refine ⟨146447633372002366225120685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97631755581334910816747123 146447633372002366225120685)
    ·
      refine ⟨54917862514500887334420257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146447633372002366225120685 54917862514500887334420257)
      ·
        refine ⟨41188396885875665500815193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54917862514500887334420257 41188396885875665500815193)
        ·
          refine ⟨30891297664406749125611395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41188396885875665500815193 30891297664406749125611395)
          ·
            refine ⟨46336946496610123688417093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30891297664406749125611395 46336946496610123688417093)
            ·
              refine ⟨8688177468114398191578205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46336946496610123688417093 8688177468114398191578205)
              ·
                refine ⟨3258066550542899321841827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8688177468114398191578205 3258066550542899321841827)
                ·
                  refine ⟨4887099825814348982762741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3258066550542899321841827 4887099825814348982762741)
                  ·
                    refine ⟨458165608670095217134007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4887099825814348982762741 458165608670095217134007)
                    ·
                      rfl

theorem cell23_2676823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 3, 1, 5].length) (baseStart_2676823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2676823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2676823 prefixEnd_2676823 := by exact prefixLift 2676823
  have htrace : WordTrace (prefixWord ++ tailWord_2676823) baseStart_2676823 baseEnd_2676823 := by
    simpa [prefixWord, tailWord_2676823, baseEnd_2676823] using wordTrace_append hprefix tailTrace_2676823
  have hstable : (prefixWord ++ tailWord_2676823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676823).length < 2 ^ (prefixWord ++ tailWord_2676823).sum := by decide
  have hdescent : baseEnd_2676823 < baseStart_2676823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676837 : List Nat := [1, 3, 1, 3, 2, 4, 1, 1, 3, 1, 3]
def baseStart_2676837 : Nat := 118140960795 + 2676837 * 2 ^ 59
def prefixEnd_2676837 : Nat := 4983230072969 + 3 ^ 40 * 2676837 * 2
def baseEnd_2676837 : Nat := 1374504014739448596626957

theorem tailTrace_2676837 : CollatzResearch.WordTrace tailWord_2676837 prefixEnd_2676837 1374504014739448596626957 := by
  unfold tailWord_2676837
  simp only [CollatzResearch.WordTrace]
  refine ⟨97632266203284191207756765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65088177468856127471837843 97632266203284191207756765)
  ·
    refine ⟨36612099826231571702908787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97632266203284191207756765 36612099826231571702908787)
    ·
      refine ⟨54918149739347357554363181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36612099826231571702908787 54918149739347357554363181)
      ·
        refine ⟨20594306152255259082886193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54918149739347357554363181 20594306152255259082886193)
        ·
          refine ⟨15445729614191444312164645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20594306152255259082886193 15445729614191444312164645)
          ·
            refine ⟨2896074302660895808530871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15445729614191444312164645 2896074302660895808530871)
            ·
              refine ⟨4344111453991343712796307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2896074302660895808530871 4344111453991343712796307)
              ·
                refine ⟨6516167180987015569194461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4344111453991343712796307 6516167180987015569194461)
                ·
                  refine ⟨2443562692870130838447923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6516167180987015569194461 2443562692870130838447923)
                  ·
                    refine ⟨3665344039305196257671885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2443562692870130838447923 3665344039305196257671885)
                    ·
                      refine ⟨1374504014739448596626957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3665344039305196257671885 1374504014739448596626957)
                      ·
                        rfl

theorem cell23_2676837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_2676837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2676837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2676837 prefixEnd_2676837 := by exact prefixLift 2676837
  have htrace : WordTrace (prefixWord ++ tailWord_2676837) baseStart_2676837 baseEnd_2676837 := by
    simpa [prefixWord, tailWord_2676837, baseEnd_2676837] using wordTrace_append hprefix tailTrace_2676837
  have hstable : (prefixWord ++ tailWord_2676837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676837).length < 2 ^ (prefixWord ++ tailWord_2676837).sum := by decide
  have hdescent : baseEnd_2676837 < baseStart_2676837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676860 : List Nat := [2, 2, 2, 1, 1, 4, 3, 2, 1, 1, 4]
def baseStart_2676860 : Nat := 118140960795 + 2676860 * 2 ^ 59
def prefixEnd_2676860 : Nat := 4983230072969 + 3 ^ 40 * 2676860 * 2
def baseEnd_2676860 : Nat := 1374515824794502006639351

theorem tailTrace_2676860 : CollatzResearch.WordTrace tailWord_2676860 prefixEnd_2676860 1374515824794502006639351 := by
  unfold tailWord_2676860
  simp only [CollatzResearch.WordTrace]
  refine ⟨48816552541100433067922017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65088736721467244090562689 48816552541100433067922017)
  ·
    refine ⟨36612414405825324800941513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48816552541100433067922017 36612414405825324800941513)
    ·
      refine ⟨27459310804368993600706135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36612414405825324800941513 27459310804368993600706135)
      ·
        refine ⟨41188966206553490401059203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27459310804368993600706135 41188966206553490401059203)
        ·
          refine ⟨61783449309830235601588805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41188966206553490401059203 61783449309830235601588805)
          ·
            refine ⟨11584396745593169175297901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61783449309830235601588805 11584396745593169175297901)
            ·
              refine ⟨4344148779597438440736713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11584396745593169175297901 4344148779597438440736713)
              ·
                refine ⟨3258111584698078830552535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4344148779597438440736713 3258111584698078830552535)
                ·
                  refine ⟨4887167377047118245828803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3258111584698078830552535 4887167377047118245828803)
                  ·
                    refine ⟨7330751065570677368743205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4887167377047118245828803 7330751065570677368743205)
                    ·
                      refine ⟨1374515824794502006639351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7330751065570677368743205 1374515824794502006639351)
                      ·
                        rfl

theorem cell23_2676860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 2, 1, 1, 4].length) (baseStart_2676860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2676860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2676860 prefixEnd_2676860 := by exact prefixLift 2676860
  have htrace : WordTrace (prefixWord ++ tailWord_2676860) baseStart_2676860 baseEnd_2676860 := by
    simpa [prefixWord, tailWord_2676860, baseEnd_2676860] using wordTrace_append hprefix tailTrace_2676860
  have hstable : (prefixWord ++ tailWord_2676860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676860).length < 2 ^ (prefixWord ++ tailWord_2676860).sum := by decide
  have hdescent : baseEnd_2676860 < baseStart_2676860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676873 : List Nat := [1, 2, 1, 1, 4, 2, 3, 2, 1, 2, 4]
def baseStart_2676873 : Nat := 118140960795 + 2676873 * 2 ^ 59
def prefixEnd_2676873 : Nat := 4983230072969 + 3 ^ 40 * 2676873 * 2
def baseEnd_2676873 : Nat := 1374522500043010455776791

theorem tailTrace_2676873 : CollatzResearch.WordTrace tailWord_2676873 prefixEnd_2676873 1374522500043010455776791 := by
  unfold tailWord_2676873
  simp only [CollatzResearch.WordTrace]
  refine ⟨97633579231153769356067273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65089052820769179570711515 97633579231153769356067273)
  ·
    refine ⟨73225184423365327017050455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97633579231153769356067273 73225184423365327017050455)
    ·
      refine ⟨109837776635047990525575683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73225184423365327017050455 109837776635047990525575683)
      ·
        refine ⟨164756664952571985788363525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109837776635047990525575683 164756664952571985788363525)
        ·
          refine ⟨30891874678607247335318161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 164756664952571985788363525 30891874678607247335318161)
          ·
            refine ⟨23168906008955435501488621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30891874678607247335318161 23168906008955435501488621)
            ·
              refine ⟨8688339753358288313058233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23168906008955435501488621 8688339753358288313058233)
              ·
                refine ⟨6516254815018716234793675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8688339753358288313058233 6516254815018716234793675)
                ·
                  refine ⟨9774382222528074352190513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6516254815018716234793675 9774382222528074352190513)
                  ·
                    refine ⟨7330786666896055764142885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9774382222528074352190513 7330786666896055764142885)
                    ·
                      refine ⟨1374522500043010455776791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7330786666896055764142885 1374522500043010455776791)
                      ·
                        rfl

theorem cell23_2676873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 2, 4].length) (baseStart_2676873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2676873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2676873 prefixEnd_2676873 := by exact prefixLift 2676873
  have htrace : WordTrace (prefixWord ++ tailWord_2676873) baseStart_2676873 baseEnd_2676873 := by
    simpa [prefixWord, tailWord_2676873, baseEnd_2676873] using wordTrace_append hprefix tailTrace_2676873
  have hstable : (prefixWord ++ tailWord_2676873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676873).length < 2 ^ (prefixWord ++ tailWord_2676873).sum := by decide
  have hdescent : baseEnd_2676873 < baseStart_2676873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676887 : List Nat := [1, 1, 3, 3, 4, 1, 2, 2, 2, 4]
def baseStart_2676887 : Nat := 118140960795 + 2676887 * 2 ^ 59
def prefixEnd_2676887 : Nat := 4983230072969 + 3 ^ 40 * 2676887 * 2
def baseEnd_2676887 : Nat := 458176562924057800333909

theorem tailTrace_2676887 : CollatzResearch.WordTrace tailWord_2676887 prefixEnd_2676887 458176562924057800333909 := by
  unfold tailWord_2676887
  simp only [CollatzResearch.WordTrace]
  refine ⟨97634089853103049747076915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65089393235402033164717943 97634089853103049747076915)
  ·
    refine ⟨146451134779654574620615373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97634089853103049747076915 146451134779654574620615373)
    ·
      refine ⟨54919175542370465482730765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146451134779654574620615373 54919175542370465482730765)
      ·
        refine ⟨20594690828388924556024037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54919175542370465482730765 20594690828388924556024037)
        ·
          refine ⟨3861504530322923354254507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20594690828388924556024037 3861504530322923354254507)
          ·
            refine ⟨5792256795484385031381761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3861504530322923354254507 5792256795484385031381761)
            ·
              refine ⟨4344192596613288773536321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5792256795484385031381761 4344192596613288773536321)
              ·
                refine ⟨3258144447459966580152241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4344192596613288773536321 3258144447459966580152241)
                ·
                  refine ⟨2443608335594974935114181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3258144447459966580152241 2443608335594974935114181)
                  ·
                    refine ⟨458176562924057800333909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2443608335594974935114181 458176562924057800333909)
                    ·
                      rfl

theorem cell23_2676887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 2, 2, 4].length) (baseStart_2676887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2676887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2676887 prefixEnd_2676887 := by exact prefixLift 2676887
  have htrace : WordTrace (prefixWord ++ tailWord_2676887) baseStart_2676887 baseEnd_2676887 := by
    simpa [prefixWord, tailWord_2676887, baseEnd_2676887] using wordTrace_append hprefix tailTrace_2676887
  have hstable : (prefixWord ++ tailWord_2676887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676887).length < 2 ^ (prefixWord ++ tailWord_2676887).sum := by decide
  have hdescent : baseEnd_2676887 < baseStart_2676887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676888 : List Nat := [2, 1, 2, 4, 4, 1, 2, 2, 1, 1, 3]
def baseStart_2676888 : Nat := 118140960795 + 2676888 * 2 ^ 59
def prefixEnd_2676888 : Nat := 4983230072969 + 3 ^ 40 * 2676888 * 2
def baseEnd_2676888 : Nat := 1374530202252827897089223

theorem tailTrace_2676888 : CollatzResearch.WordTrace tailWord_2676888 prefixEnd_2676888 1374530202252827897089223 := by
  unfold tailWord_2676888
  simp only [CollatzResearch.WordTrace]
  refine ⟨48817063163049713458931659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65089417550732951278575545 48817063163049713458931659)
  ·
    refine ⟨73225594744574570188397489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48817063163049713458931659 73225594744574570188397489)
    ·
      refine ⟨54919196058430927641298117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73225594744574570188397489 54919196058430927641298117)
      ·
        refine ⟨10297349260955798932743397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54919196058430927641298117 10297349260955798932743397)
        ·
          refine ⟨1930752986429212299889387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10297349260955798932743397 1930752986429212299889387)
          ·
            refine ⟨2896129479643818449834081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1930752986429212299889387 2896129479643818449834081)
            ·
              refine ⟨2172097109732863837375561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2896129479643818449834081 2172097109732863837375561)
              ·
                refine ⟨1629072832299647878031671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2172097109732863837375561 1629072832299647878031671)
                ·
                  refine ⟨2443609248449471817047507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1629072832299647878031671 2443609248449471817047507)
                  ·
                    refine ⟨3665413872674207725571261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2443609248449471817047507 3665413872674207725571261)
                    ·
                      refine ⟨1374530202252827897089223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3665413872674207725571261 1374530202252827897089223)
                      ·
                        rfl

theorem cell23_2676888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_2676888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2676888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2676888 prefixEnd_2676888 := by exact prefixLift 2676888
  have htrace : WordTrace (prefixWord ++ tailWord_2676888) baseStart_2676888 baseEnd_2676888 := by
    simpa [prefixWord, tailWord_2676888, baseEnd_2676888] using wordTrace_append hprefix tailTrace_2676888
  have hstable : (prefixWord ++ tailWord_2676888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676888).length < 2 ^ (prefixWord ++ tailWord_2676888).sum := by decide
  have hdescent : baseEnd_2676888 < baseStart_2676888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676900 : List Nat := [2, 3, 1, 2, 4, 2, 1, 8]
def baseStart_2676900 : Nat := 118140960795 + 2676900 * 2 ^ 59
def prefixEnd_2676900 : Nat := 4983230072969 + 3 ^ 40 * 2676900 * 2
def baseEnd_2676900 : Nat := 50908754222988216671821

theorem tailTrace_2676900 : CollatzResearch.WordTrace tailWord_2676900 prefixEnd_2676900 50908754222988216671821 := by
  unfold tailWord_2676900
  simp only [CollatzResearch.WordTrace]
  refine ⟨48817282001027976483650077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65089709334703968644866769 48817282001027976483650077)
  ·
    refine ⟨18306480750385491181368779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48817282001027976483650077 18306480750385491181368779)
    ·
      refine ⟨27459721125578236772053169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18306480750385491181368779 27459721125578236772053169)
      ·
        refine ⟨20594790844183677579039877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27459721125578236772053169 20594790844183677579039877)
        ·
          refine ⟨3861523283284439546069977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20594790844183677579039877 3861523283284439546069977)
          ·
            refine ⟨2896142462463329659552483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3861523283284439546069977 2896142462463329659552483)
            ·
              refine ⟨4344213693694994489328725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2896142462463329659552483 4344213693694994489328725)
              ·
                refine ⟨50908754222988216671821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4344213693694994489328725 50908754222988216671821)
                ·
                  rfl

theorem cell23_2676900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 8].length) (baseStart_2676900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2676900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2676900 prefixEnd_2676900 := by exact prefixLift 2676900
  have htrace : WordTrace (prefixWord ++ tailWord_2676900) baseStart_2676900 baseEnd_2676900 := by
    simpa [prefixWord, tailWord_2676900, baseEnd_2676900] using wordTrace_append hprefix tailTrace_2676900
  have hstable : (prefixWord ++ tailWord_2676900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676900).length < 2 ^ (prefixWord ++ tailWord_2676900).sum := by decide
  have hdescent : baseEnd_2676900 < baseStart_2676900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676917 : List Nat := [1, 3, 3, 4, 1, 1, 3, 7]
def baseStart_2676917 : Nat := 118140960795 + 2676917 * 2 ^ 59
def prefixEnd_2676917 : Nat := 4983230072969 + 3 ^ 40 * 2676917 * 2
def baseEnd_2676917 : Nat := 50909077525622529023207

theorem tailTrace_2676917 : CollatzResearch.WordTrace tailWord_2676917 prefixEnd_2676917 50909077525622529023207 := by
  unfold tailWord_2676917
  simp only [CollatzResearch.WordTrace]
  refine ⟨97635184042994364870669005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65090122695329576580446003 97635184042994364870669005)
  ·
    refine ⟨36613194016122886826500877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97635184042994364870669005 36613194016122886826500877)
    ·
      refine ⟨13729947756046082559937829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36613194016122886826500877 13729947756046082559937829)
      ·
        refine ⟨2574365204258640479988343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13729947756046082559937829 2574365204258640479988343)
        ·
          refine ⟨3861547806387960719982515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2574365204258640479988343 3861547806387960719982515)
          ·
            refine ⟨5792321709581941079973773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3861547806387960719982515 5792321709581941079973773)
            ·
              refine ⟨2172120641093227904990165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5792321709581941079973773 2172120641093227904990165)
              ·
                refine ⟨50909077525622529023207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2172120641093227904990165 50909077525622529023207)
                ·
                  rfl

theorem cell23_2676917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 7].length) (baseStart_2676917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2676917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2676917 prefixEnd_2676917 := by exact prefixLift 2676917
  have htrace : WordTrace (prefixWord ++ tailWord_2676917) baseStart_2676917 baseEnd_2676917 := by
    simpa [prefixWord, tailWord_2676917, baseEnd_2676917] using wordTrace_append hprefix tailTrace_2676917
  have hstable : (prefixWord ++ tailWord_2676917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676917).length < 2 ^ (prefixWord ++ tailWord_2676917).sum := by decide
  have hdescent : baseEnd_2676917 < baseStart_2676917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676920 : List Nat := [2, 1, 2, 1, 2, 1, 3, 3, 3, 3, 2]
def baseStart_2676920 : Nat := 118140960795 + 2676920 * 2 ^ 59
def prefixEnd_2676920 : Nat := 4983230072969 + 3 ^ 40 * 2676920 * 2
def baseEnd_2676920 : Nat := 1374546633633771771889075

theorem tailTrace_2676920 : CollatzResearch.WordTrace tailWord_2676920 prefixEnd_2676920 1374546633633771771889075 := by
  unfold tailWord_2676920
  simp only [CollatzResearch.WordTrace]
  refine ⟨48817646730991748191514107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65090195641322330922018809 48817646730991748191514107)
  ·
    refine ⟨73226470096487622287271161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48817646730991748191514107 73226470096487622287271161)
    ·
      refine ⟨54919852572365716715453371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73226470096487622287271161 54919852572365716715453371)
      ·
        refine ⟨82379778858548575073180057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54919852572365716715453371 82379778858548575073180057)
        ·
          refine ⟨61784834143911431304885043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82379778858548575073180057 61784834143911431304885043)
          ·
            refine ⟨92677251215867146957327565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61784834143911431304885043 92677251215867146957327565)
            ·
              refine ⟨34753969205950180108997837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92677251215867146957327565 34753969205950180108997837)
              ·
                refine ⟨13032738452231317540874189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34753969205950180108997837 13032738452231317540874189)
                ·
                  refine ⟨4887276919586744077827821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13032738452231317540874189 4887276919586744077827821)
                  ·
                    refine ⟨1832728844845029029185433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4887276919586744077827821 1832728844845029029185433)
                    ·
                      refine ⟨1374546633633771771889075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1832728844845029029185433 1374546633633771771889075)
                      ·
                        rfl

theorem cell23_2676920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 3, 3, 2].length) (baseStart_2676920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2676920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2676920 prefixEnd_2676920 := by exact prefixLift 2676920
  have htrace : WordTrace (prefixWord ++ tailWord_2676920) baseStart_2676920 baseEnd_2676920 := by
    simpa [prefixWord, tailWord_2676920, baseEnd_2676920] using wordTrace_append hprefix tailTrace_2676920
  have hstable : (prefixWord ++ tailWord_2676920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676920).length < 2 ^ (prefixWord ++ tailWord_2676920).sum := by decide
  have hdescent : baseEnd_2676920 < baseStart_2676920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676953 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 1, 6, 3]
def baseStart_2676953 : Nat := 118140960795 + 2676953 * 2 ^ 59
def prefixEnd_2676953 : Nat := 4983230072969 + 3 ^ 40 * 2676953 * 2
def baseEnd_2676953 : Nat := 1374563578495370142776423

theorem tailTrace_2676953 : CollatzResearch.WordTrace tailWord_2676953 prefixEnd_2676953 1374563578495370142776423 := by
  unfold tailWord_2676953
  simp only [CollatzResearch.WordTrace]
  refine ⟨97636497070863943018979513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65090998047242628679319675 97636497070863943018979513)
  ·
    refine ⟨73227372803147957264234635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97636497070863943018979513 73227372803147957264234635)
    ·
      refine ⟨109841059204721935896351953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73227372803147957264234635 109841059204721935896351953)
      ·
        refine ⟨82380794403541451922263965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109841059204721935896351953 82380794403541451922263965)
        ·
          refine ⟨30892797901328044470848987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82380794403541451922263965 30892797901328044470848987)
          ·
            refine ⟨46339196851992066706273481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30892797901328044470848987 46339196851992066706273481)
            ·
              refine ⟨34754397638994050029705111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46339196851992066706273481 34754397638994050029705111)
              ·
                refine ⟨52131596458491075044557667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34754397638994050029705111 52131596458491075044557667)
                ·
                  refine ⟨78197394687736612566836501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52131596458491075044557667 78197394687736612566836501)
                  ·
                    refine ⟨3665502875987653714070461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 78197394687736612566836501 3665502875987653714070461)
                    ·
                      refine ⟨1374563578495370142776423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3665502875987653714070461 1374563578495370142776423)
                      ·
                        rfl

theorem cell23_2676953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 6, 3].length) (baseStart_2676953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2676953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2676953 prefixEnd_2676953 := by exact prefixLift 2676953
  have htrace : WordTrace (prefixWord ++ tailWord_2676953) baseStart_2676953 baseEnd_2676953 := by
    simpa [prefixWord, tailWord_2676953, baseEnd_2676953] using wordTrace_append hprefix tailTrace_2676953
  have hstable : (prefixWord ++ tailWord_2676953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676953).length < 2 ^ (prefixWord ++ tailWord_2676953).sum := by decide
  have hdescent : baseEnd_2676953 < baseStart_2676953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677013 : List Nat := [1, 3, 2, 1, 2, 1, 3, 1, 1, 1, 7]
def baseStart_2677013 : Nat := 118140960795 + 2677013 * 2 ^ 59
def prefixEnd_2677013 : Nat := 4983230072969 + 3 ^ 40 * 2677013 * 2
def baseEnd_2677013 : Nat := 1374594387334639908026147

theorem tailTrace_2677013 : CollatzResearch.WordTrace tailWord_2677013 prefixEnd_2677013 1374594387334639908026147 := by
  unfold tailWord_2677013
  simp only [CollatzResearch.WordTrace]
  refine ⟨97638685450646573266163693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65092456967097715510775795 97638685450646573266163693)
  ·
    refine ⟨36614507043992464974811385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97638685450646573266163693 36614507043992464974811385)
    ·
      refine ⟨27460880282994348731108539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36614507043992464974811385 27460880282994348731108539)
      ·
        refine ⟨41191320424491523096662809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27460880282994348731108539 41191320424491523096662809)
        ·
          refine ⟨30893490318368642322497107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41191320424491523096662809 30893490318368642322497107)
          ·
            refine ⟨46340235477552963483745661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30893490318368642322497107 46340235477552963483745661)
            ·
              refine ⟨17377588304082361306404623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46340235477552963483745661 17377588304082361306404623)
              ·
                refine ⟨26066382456123541959606935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17377588304082361306404623 26066382456123541959606935)
                ·
                  refine ⟨39099573684185312939410403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26066382456123541959606935 39099573684185312939410403)
                  ·
                    refine ⟨58649360526277969409115605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39099573684185312939410403 58649360526277969409115605)
                    ·
                      refine ⟨1374594387334639908026147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 58649360526277969409115605 1374594387334639908026147)
                      ·
                        rfl

theorem cell23_2677013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_2677013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677013 prefixEnd_2677013 := by exact prefixLift 2677013
  have htrace : WordTrace (prefixWord ++ tailWord_2677013) baseStart_2677013 baseEnd_2677013 := by
    simpa [prefixWord, tailWord_2677013, baseEnd_2677013] using wordTrace_append hprefix tailTrace_2677013
  have hstable : (prefixWord ++ tailWord_2677013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677013).length < 2 ^ (prefixWord ++ tailWord_2677013).sum := by decide
  have hdescent : baseEnd_2677013 < baseStart_2677013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677018 : List Nat := [3, 1, 1, 3, 4, 2, 2, 1, 2, 2, 2]
def baseStart_2677018 : Nat := 118140960795 + 2677018 * 2 ^ 59
def prefixEnd_2677018 : Nat := 4983230072969 + 3 ^ 40 * 2677018 * 2
def baseEnd_2677018 : Nat := 1374596954737912388463625

theorem tailTrace_2677018 : CollatzResearch.WordTrace tailWord_2677018 prefixEnd_2677018 1374596954737912388463625 := by
  unfold tailWord_2677018
  simp only [CollatzResearch.WordTrace]
  refine ⟨24409716953907114780023927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65092578543752306080063805 24409716953907114780023927)
  ·
    refine ⟨36614575430860672170035891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24409716953907114780023927 36614575430860672170035891)
    ·
      refine ⟨54921863146291008255053837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36614575430860672170035891 54921863146291008255053837)
      ·
        refine ⟨20595698679859128095645189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54921863146291008255053837 20595698679859128095645189)
        ·
          refine ⟨3861693502473586517933473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20595698679859128095645189 3861693502473586517933473)
          ·
            refine ⟨2896270126855189888450105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3861693502473586517933473 2896270126855189888450105)
            ·
              refine ⟨2172202595141392416337579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2896270126855189888450105 2172202595141392416337579)
              ·
                refine ⟨3258303892712088624506369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2172202595141392416337579 3258303892712088624506369)
                ·
                  refine ⟨2443727919534066468379777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3258303892712088624506369 2443727919534066468379777)
                  ·
                    refine ⟨1832795939650549851284833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2443727919534066468379777 1832795939650549851284833)
                    ·
                      refine ⟨1374596954737912388463625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1832795939650549851284833 1374596954737912388463625)
                      ·
                        rfl

theorem cell23_2677018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 1, 2, 2, 2].length) (baseStart_2677018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677018 prefixEnd_2677018 := by exact prefixLift 2677018
  have htrace : WordTrace (prefixWord ++ tailWord_2677018) baseStart_2677018 baseEnd_2677018 := by
    simpa [prefixWord, tailWord_2677018, baseEnd_2677018] using wordTrace_append hprefix tailTrace_2677018
  have hstable : (prefixWord ++ tailWord_2677018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677018).length < 2 ^ (prefixWord ++ tailWord_2677018).sum := by decide
  have hdescent : baseEnd_2677018 < baseStart_2677018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677040 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 3, 6, 2]
def baseStart_2677040 : Nat := 118140960795 + 2677040 * 2 ^ 59
def prefixEnd_2677040 : Nat := 4983230072969 + 3 ^ 40 * 2677040 * 2
def baseEnd_2677040 : Nat := 1374608251312311302388523

theorem tailTrace_2677040 : CollatzResearch.WordTrace tailWord_2677040 prefixEnd_2677040 1374608251312311302388523 := by
  unfold tailWord_2677040
  simp only [CollatzResearch.WordTrace]
  refine ⟨48819835110774378438698287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65093113481032504584931049 48819835110774378438698287)
  ·
    refine ⟨73229752666161567658047431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48819835110774378438698287 73229752666161567658047431)
    ·
      refine ⟨109844628999242351487071147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73229752666161567658047431 109844628999242351487071147)
      ·
        refine ⟨164766943498863527230606721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109844628999242351487071147 164766943498863527230606721)
        ·
          refine ⟨123575207624147645422955041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164766943498863527230606721 123575207624147645422955041)
          ·
            refine ⟨92681405718110734067216281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123575207624147645422955041 92681405718110734067216281)
            ·
              refine ⟨69511054288583050550412211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92681405718110734067216281 69511054288583050550412211)
              ·
                refine ⟨104266581432874575825618317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69511054288583050550412211 104266581432874575825618317)
                ·
                  refine ⟨39099968037327965934606869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104266581432874575825618317 39099968037327965934606869)
                  ·
                    refine ⟨1832811001749748403184697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 39099968037327965934606869 1832811001749748403184697)
                    ·
                      refine ⟨1374608251312311302388523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1832811001749748403184697 1374608251312311302388523)
                      ·
                        rfl

theorem cell23_2677040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 3, 6, 2].length) (baseStart_2677040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677040 prefixEnd_2677040 := by exact prefixLift 2677040
  have htrace : WordTrace (prefixWord ++ tailWord_2677040) baseStart_2677040 baseEnd_2677040 := by
    simpa [prefixWord, tailWord_2677040, baseEnd_2677040] using wordTrace_append hprefix tailTrace_2677040
  have hstable : (prefixWord ++ tailWord_2677040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677040).length < 2 ^ (prefixWord ++ tailWord_2677040).sum := by decide
  have hdescent : baseEnd_2677040 < baseStart_2677040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677124 : List Nat := [2, 3, 2, 1, 1, 2, 4, 1, 3, 1, 3]
def baseStart_2677124 : Nat := 118140960795 + 2677124 * 2 ^ 59
def prefixEnd_2677124 : Nat := 4983230072969 + 3 ^ 40 * 2677124 * 2
def baseEnd_2677124 : Nat := 1374651383687288973738137

theorem tailTrace_2677124 : CollatzResearch.WordTrace tailWord_2677124 prefixEnd_2677124 1374651383687288973738137 := by
  unfold tailWord_2677124
  simp only [CollatzResearch.WordTrace]
  refine ⟨48821366976622219611727213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65095155968829626148969617 48821366976622219611727213)
  ·
    refine ⟨18308012616233332354397705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48821366976622219611727213 18308012616233332354397705)
    ·
      refine ⟨13731009462174999265798279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18308012616233332354397705 13731009462174999265798279)
      ·
        refine ⟨20596514193262498898697419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13731009462174999265798279 20596514193262498898697419)
        ·
          refine ⟨30894771289893748348046129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20596514193262498898697419 30894771289893748348046129)
          ·
            refine ⟨23171078467420311261034597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30894771289893748348046129 23171078467420311261034597)
            ·
              refine ⟨4344577212641308361443987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23171078467420311261034597 4344577212641308361443987)
              ·
                refine ⟨6516865818961962542165981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4344577212641308361443987 6516865818961962542165981)
                ·
                  refine ⟨2443824682110735953312243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6516865818961962542165981 2443824682110735953312243)
                  ·
                    refine ⟨3665737023166103929968365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2443824682110735953312243 3665737023166103929968365)
                    ·
                      refine ⟨1374651383687288973738137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3665737023166103929968365 1374651383687288973738137)
                      ·
                        rfl

theorem cell23_2677124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_2677124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677124 prefixEnd_2677124 := by exact prefixLift 2677124
  have htrace : WordTrace (prefixWord ++ tailWord_2677124) baseStart_2677124 baseEnd_2677124 := by
    simpa [prefixWord, tailWord_2677124, baseEnd_2677124] using wordTrace_append hprefix tailTrace_2677124
  have hstable : (prefixWord ++ tailWord_2677124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677124).length < 2 ^ (prefixWord ++ tailWord_2677124).sum := by decide
  have hdescent : baseEnd_2677124 < baseStart_2677124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677134 : List Nat := [4, 1, 1, 4, 1, 1, 1, 2, 1, 5, 2]
def baseStart_2677134 : Nat := 118140960795 + 2677134 * 2 ^ 59
def prefixEnd_2677134 : Nat := 4983230072969 + 3 ^ 40 * 2677134 * 2
def baseEnd_2677134 : Nat := 1374656518493833934613091

theorem tailTrace_2677134 : CollatzResearch.WordTrace tailWord_2677134 prefixEnd_2677134 1374656518493833934613091 := by
  unfold tailWord_2677134
  simp only [CollatzResearch.WordTrace]
  refine ⟨12205387335401026366414807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65095399122138807287545637 12205387335401026366414807)
  ·
    refine ⟨18308081003101539549622211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12205387335401026366414807 18308081003101539549622211)
    ·
      refine ⟨27462121504652309324433317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18308081003101539549622211 27462121504652309324433317)
      ·
        refine ⟨5149147782122307998331247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27462121504652309324433317 5149147782122307998331247)
        ·
          refine ⟨7723721673183461997496871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5149147782122307998331247 7723721673183461997496871)
          ·
            refine ⟨11585582509775192996245307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7723721673183461997496871 11585582509775192996245307)
            ·
              refine ⟨17378373764662789494367961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11585582509775192996245307 17378373764662789494367961)
              ·
                refine ⟨13033780323497092120775971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17378373764662789494367961 13033780323497092120775971)
                ·
                  refine ⟨19550670485245638181163957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13033780323497092120775971 19550670485245638181163957)
                  ·
                    refine ⟨1832875357991778579484121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19550670485245638181163957 1832875357991778579484121)
                    ·
                      refine ⟨1374656518493833934613091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1832875357991778579484121 1374656518493833934613091)
                      ·
                        rfl

theorem cell23_2677134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_2677134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677134 prefixEnd_2677134 := by exact prefixLift 2677134
  have htrace : WordTrace (prefixWord ++ tailWord_2677134) baseStart_2677134 baseEnd_2677134 := by
    simpa [prefixWord, tailWord_2677134, baseEnd_2677134] using wordTrace_append hprefix tailTrace_2677134
  have hstable : (prefixWord ++ tailWord_2677134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677134).length < 2 ^ (prefixWord ++ tailWord_2677134).sum := by decide
  have hdescent : baseEnd_2677134 < baseStart_2677134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677144 : List Nat := [2, 1, 2, 5, 1, 2, 2, 2, 1, 5]
def baseStart_2677144 : Nat := 118140960795 + 2677144 * 2 ^ 59
def prefixEnd_2677144 : Nat := 4983230072969 + 3 ^ 40 * 2677144 * 2
def baseEnd_2677144 : Nat := 458220551100126298496015

theorem tailTrace_2677144 : CollatzResearch.WordTrace tailWord_2677144 prefixEnd_2677144 458220551100126298496015 := by
  unfold tailWord_2677144
  simp only [CollatzResearch.WordTrace]
  refine ⟨48821731706585991319591243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65095642275447988426121657 48821731706585991319591243)
  ·
    refine ⟨73232597559878986979386865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48821731706585991319591243 73232597559878986979386865)
    ·
      refine ⟨54924448169909240234540149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73232597559878986979386865 54924448169909240234540149)
      ·
        refine ⟨5149167015928991271988139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54924448169909240234540149 5149167015928991271988139)
        ·
          refine ⟨7723750523893486907982209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5149167015928991271988139 7723750523893486907982209)
          ·
            refine ⟨5792812892920115180986657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7723750523893486907982209 5792812892920115180986657)
            ·
              refine ⟨4344609669690086385739993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5792812892920115180986657 4344609669690086385739993)
              ·
                refine ⟨3258457252267564789304995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4344609669690086385739993 3258457252267564789304995)
                ·
                  refine ⟨4887685878401347183957493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3258457252267564789304995 4887685878401347183957493)
                  ·
                    refine ⟨458220551100126298496015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4887685878401347183957493 458220551100126298496015)
                    ·
                      rfl

theorem cell23_2677144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 2, 1, 5].length) (baseStart_2677144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677144 prefixEnd_2677144 := by exact prefixLift 2677144
  have htrace : WordTrace (prefixWord ++ tailWord_2677144) baseStart_2677144 baseEnd_2677144 := by
    simpa [prefixWord, tailWord_2677144, baseEnd_2677144] using wordTrace_append hprefix tailTrace_2677144
  have hstable : (prefixWord ++ tailWord_2677144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677144).length < 2 ^ (prefixWord ++ tailWord_2677144).sum := by decide
  have hdescent : baseEnd_2677144 < baseStart_2677144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677181 : List Nat := [1, 4, 1, 2, 2, 2, 3, 1, 3, 2, 2]
def baseStart_2677181 : Nat := 118140960795 + 2677181 * 2 ^ 59
def prefixEnd_2677181 : Nat := 4983230072969 + 3 ^ 40 * 2677181 * 2
def baseEnd_2677181 : Nat := 1374680652084595250725375

theorem tailTrace_2677181 : CollatzResearch.WordTrace tailWord_2677181 prefixEnd_2677181 1374680652084595250725375 := by
  unfold tailWord_2677181
  simp only [CollatzResearch.WordTrace]
  refine ⟨97644812914037937958279397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65096541942691958638852931 97644812914037937958279397)
  ·
    refine ⟨18308402421382113367177387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97644812914037937958279397 18308402421382113367177387)
    ·
      refine ⟨27462603632073170050766081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18308402421382113367177387 27462603632073170050766081)
      ·
        refine ⟨20596952724054877538074561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27462603632073170050766081 20596952724054877538074561)
        ·
          refine ⟨15447714543041158153555921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20596952724054877538074561 15447714543041158153555921)
          ·
            refine ⟨11585785907280868615166941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15447714543041158153555921 11585785907280868615166941)
            ·
              refine ⟨4344669715230325730687603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11585785907280868615166941 4344669715230325730687603)
              ·
                refine ⟨6517004572845488596031405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4344669715230325730687603 6517004572845488596031405)
                ·
                  refine ⟨2443876714817058223511777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6517004572845488596031405 2443876714817058223511777)
                  ·
                    refine ⟨1832907536112793667633833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2443876714817058223511777 1832907536112793667633833)
                    ·
                      refine ⟨1374680652084595250725375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1832907536112793667633833 1374680652084595250725375)
                      ·
                        rfl

theorem cell23_2677181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 3, 2, 2].length) (baseStart_2677181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677181 prefixEnd_2677181 := by exact prefixLift 2677181
  have htrace : WordTrace (prefixWord ++ tailWord_2677181) baseStart_2677181 baseEnd_2677181 := by
    simpa [prefixWord, tailWord_2677181, baseEnd_2677181] using wordTrace_append hprefix tailTrace_2677181
  have hstable : (prefixWord ++ tailWord_2677181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677181).length < 2 ^ (prefixWord ++ tailWord_2677181).sum := by decide
  have hdescent : baseEnd_2677181 < baseStart_2677181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677191 : List Nat := [1, 1, 4, 1, 1, 6, 2, 1, 2, 4]
def baseStart_2677191 : Nat := 118140960795 + 2677191 * 2 ^ 59
def prefixEnd_2677191 : Nat := 4983230072969 + 3 ^ 40 * 2677191 * 2
def baseEnd_2677191 : Nat := 458228595630380070533443

theorem tailTrace_2677191 : CollatzResearch.WordTrace tailWord_2677191 prefixEnd_2677191 458228595630380070533443 := by
  unfold tailWord_2677191
  simp only [CollatzResearch.WordTrace]
  refine ⟨97645177644001709666143427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65096785096001139777428951 97645177644001709666143427)
  ·
    refine ⟨146467766466002564499215141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97645177644001709666143427 146467766466002564499215141)
    ·
      refine ⟨27462706212375480843602839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146467766466002564499215141 27462706212375480843602839)
      ·
        refine ⟨41194059318563221265404259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27462706212375480843602839 41194059318563221265404259)
        ·
          refine ⟨61791088977844831898106389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41194059318563221265404259 61791088977844831898106389)
          ·
            refine ⟨2896457295836476495223737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 61791088977844831898106389 2896457295836476495223737)
            ·
              refine ⟨2172342971877357371417803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2896457295836476495223737 2172342971877357371417803)
              ·
                refine ⟨3258514457816036057126705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2172342971877357371417803 3258514457816036057126705)
                ·
                  refine ⟨2443885843362027042845029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3258514457816036057126705 2443885843362027042845029)
                  ·
                    refine ⟨458228595630380070533443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2443885843362027042845029 458228595630380070533443)
                    ·
                      rfl

theorem cell23_2677191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 1, 2, 4].length) (baseStart_2677191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677191 prefixEnd_2677191 := by exact prefixLift 2677191
  have htrace : WordTrace (prefixWord ++ tailWord_2677191) baseStart_2677191 baseEnd_2677191 := by
    simpa [prefixWord, tailWord_2677191, baseEnd_2677191] using wordTrace_append hprefix tailTrace_2677191
  have hstable : (prefixWord ++ tailWord_2677191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677191).length < 2 ^ (prefixWord ++ tailWord_2677191).sum := by decide
  have hdescent : baseEnd_2677191 < baseStart_2677191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677218 : List Nat := [3, 3, 3, 2, 1, 2, 1, 1, 1, 1, 5]
def baseStart_2677218 : Nat := 118140960795 + 2677218 * 2 ^ 59
def prefixEnd_2677218 : Nat := 4983230072969 + 3 ^ 40 * 2677218 * 2
def baseEnd_2677218 : Nat := 1374699650868811605962705

theorem tailTrace_2677218 : CollatzResearch.WordTrace tailWord_2677218 prefixEnd_2677218 1374699650868811605962705 := by
  unfold tailWord_2677218
  simp only [CollatzResearch.WordTrace]
  refine ⟨24411540603725973319344077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65097441609935928851584205 24411540603725973319344077)
  ·
    refine ⟨9154327726397239994754029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24411540603725973319344077 9154327726397239994754029)
    ·
      refine ⟨3432872897398964998032761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9154327726397239994754029 3432872897398964998032761)
      ·
        refine ⟨2574654673049223748524571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3432872897398964998032761 2574654673049223748524571)
        ·
          refine ⟨3861982009573835622786857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2574654673049223748524571 3861982009573835622786857)
          ·
            refine ⟨2896486507180376717090143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3861982009573835622786857 2896486507180376717090143)
            ·
              refine ⟨4344729760770565075635215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2896486507180376717090143 4344729760770565075635215)
              ·
                refine ⟨6517094641155847613452823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4344729760770565075635215 6517094641155847613452823)
                ·
                  refine ⟨9775641961733771420179235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6517094641155847613452823 9775641961733771420179235)
                  ·
                    refine ⟨14663462942600657130268853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9775641961733771420179235 14663462942600657130268853)
                    ·
                      refine ⟨1374699650868811605962705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14663462942600657130268853 1374699650868811605962705)
                      ·
                        rfl

theorem cell23_2677218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_2677218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677218 prefixEnd_2677218 := by exact prefixLift 2677218
  have htrace : WordTrace (prefixWord ++ tailWord_2677218) baseStart_2677218 baseEnd_2677218 := by
    simpa [prefixWord, tailWord_2677218, baseEnd_2677218] using wordTrace_append hprefix tailTrace_2677218
  have hstable : (prefixWord ++ tailWord_2677218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677218).length < 2 ^ (prefixWord ++ tailWord_2677218).sum := by decide
  have hdescent : baseEnd_2677218 < baseStart_2677218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677288 : List Nat := [2, 1, 5, 2, 1, 2, 1, 1, 4, 2, 2]
def baseStart_2677288 : Nat := 118140960795 + 2677288 * 2 ^ 59
def prefixEnd_2677288 : Nat := 4983230072969 + 3 ^ 40 * 2677288 * 2
def baseEnd_2677288 : Nat := 1374735594514626332087383

theorem tailTrace_2677288 : CollatzResearch.WordTrace tailWord_2677288 prefixEnd_2677288 1374735594514626332087383 := by
  unfold tailWord_2677288
  simp only [CollatzResearch.WordTrace]
  refine ⟨48824357762325147616212259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65099143683100196821616345 48824357762325147616212259)
  ·
    refine ⟨73236536643487721424318389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48824357762325147616212259 73236536643487721424318389)
    ·
      refine ⟨6865925310326973883529849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73236536643487721424318389 6865925310326973883529849)
      ·
        refine ⟨5149443982745230412647387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6865925310326973883529849 5149443982745230412647387)
        ·
          refine ⟨7724165974117845618971081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5149443982745230412647387 7724165974117845618971081)
          ·
            refine ⟨5793124480588384214228311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7724165974117845618971081 5793124480588384214228311)
            ·
              refine ⟨8689686720882576321342467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5793124480588384214228311 8689686720882576321342467)
              ·
                refine ⟨13034530081323864482013701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8689686720882576321342467 13034530081323864482013701)
                ·
                  refine ⟨2443974390248224590377569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13034530081323864482013701 2443974390248224590377569)
                  ·
                    refine ⟨1832980792686168442783177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2443974390248224590377569 1832980792686168442783177)
                    ·
                      refine ⟨1374735594514626332087383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1832980792686168442783177 1374735594514626332087383)
                      ·
                        rfl

theorem cell23_2677288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_2677288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677288 prefixEnd_2677288 := by exact prefixLift 2677288
  have htrace : WordTrace (prefixWord ++ tailWord_2677288) baseStart_2677288 baseEnd_2677288 := by
    simpa [prefixWord, tailWord_2677288, baseEnd_2677288] using wordTrace_append hprefix tailTrace_2677288
  have hstable : (prefixWord ++ tailWord_2677288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677288).length < 2 ^ (prefixWord ++ tailWord_2677288).sum := by decide
  have hdescent : baseEnd_2677288 < baseStart_2677288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677327 : List Nat := [1, 1, 2, 1, 1, 2, 6, 1, 1, 3, 4]
def baseStart_2677327 : Nat := 118140960795 + 2677327 * 2 ^ 59
def prefixEnd_2677327 : Nat := 4983230072969 + 3 ^ 40 * 2677327 * 2
def baseEnd_2677327 : Nat := 1374755620260151679499703

theorem tailTrace_2677327 : CollatzResearch.WordTrace tailWord_2677327 prefixEnd_2677327 1374755620260151679499703 := by
  unfold tailWord_2677327
  simp only [CollatzResearch.WordTrace]
  refine ⟨97650137971509004893094235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65100091981006003262062823 97650137971509004893094235)
  ·
    refine ⟨146475206957263507339641353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97650137971509004893094235 146475206957263507339641353)
    ·
      refine ⟨109856405217947630504731015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146475206957263507339641353 109856405217947630504731015)
      ·
        refine ⟨164784607826921445757096523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109856405217947630504731015 164784607826921445757096523)
        ·
          refine ⟨247176911740382168635644785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164784607826921445757096523 247176911740382168635644785)
          ·
            refine ⟨185382683805286626476733589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247176911740382168635644785 185382683805286626476733589)
            ·
              refine ⟨8689813303372810616096887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 185382683805286626476733589 8689813303372810616096887)
              ·
                refine ⟨13034719955059215924145331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8689813303372810616096887 13034719955059215924145331)
                ·
                  refine ⟨19552079932588823886217997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13034719955059215924145331 19552079932588823886217997)
                  ·
                    refine ⟨7332029974720808957331749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19552079932588823886217997 7332029974720808957331749)
                    ·
                      refine ⟨1374755620260151679499703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7332029974720808957331749 1374755620260151679499703)
                      ·
                        rfl

theorem cell23_2677327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 3, 4].length) (baseStart_2677327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677327 prefixEnd_2677327 := by exact prefixLift 2677327
  have htrace : WordTrace (prefixWord ++ tailWord_2677327) baseStart_2677327 baseEnd_2677327 := by
    simpa [prefixWord, tailWord_2677327, baseEnd_2677327] using wordTrace_append hprefix tailTrace_2677327
  have hstable : (prefixWord ++ tailWord_2677327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677327).length < 2 ^ (prefixWord ++ tailWord_2677327).sum := by decide
  have hdescent : baseEnd_2677327 < baseStart_2677327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677344 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 4, 4, 2]
def baseStart_2677344 : Nat := 118140960795 + 2677344 * 2 ^ 59
def prefixEnd_2677344 : Nat := 4983230072969 + 3 ^ 40 * 2677344 * 2
def baseEnd_2677344 : Nat := 1374764349431278112987125

theorem tailTrace_2677344 : CollatzResearch.WordTrace tailWord_2677344 prefixEnd_2677344 1374764349431278112987125 := by
  unfold tailWord_2677344
  simp only [CollatzResearch.WordTrace]
  refine ⟨48825379006223708398231543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65100505341631611197642057 48825379006223708398231543)
  ·
    refine ⟨73238068509335562597347315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48825379006223708398231543 73238068509335562597347315)
    ·
      refine ⟨109857102764003343896020973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73238068509335562597347315 109857102764003343896020973)
      ·
        refine ⟨41196413536501253961007865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109857102764003343896020973 41196413536501253961007865)
        ·
          refine ⟨30897310152375940470755899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41196413536501253961007865 30897310152375940470755899)
          ·
            refine ⟨46345965228563910706133849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30897310152375940470755899 46345965228563910706133849)
            ·
              refine ⟨34759473921422933029600387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46345965228563910706133849 34759473921422933029600387)
              ·
                refine ⟨52139210882134399544400581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34759473921422933029600387 52139210882134399544400581)
                ·
                  refine ⟨9776102040400199914575109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52139210882134399544400581 9776102040400199914575109)
                  ·
                    refine ⟨1833019132575037483982833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9776102040400199914575109 1833019132575037483982833)
                    ·
                      refine ⟨1374764349431278112987125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1833019132575037483982833 1374764349431278112987125)
                      ·
                        rfl

theorem cell23_2677344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 4, 4, 2].length) (baseStart_2677344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677344 prefixEnd_2677344 := by exact prefixLift 2677344
  have htrace : WordTrace (prefixWord ++ tailWord_2677344) baseStart_2677344 baseEnd_2677344 := by
    simpa [prefixWord, tailWord_2677344, baseEnd_2677344] using wordTrace_append hprefix tailTrace_2677344
  have hstable : (prefixWord ++ tailWord_2677344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677344).length < 2 ^ (prefixWord ++ tailWord_2677344).sum := by decide
  have hdescent : baseEnd_2677344 < baseStart_2677344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677381 : List Nat := [1, 3, 1, 1, 4, 3, 2, 1, 2, 2, 3]
def baseStart_2677381 : Nat := 118140960795 + 2677381 * 2 ^ 59
def prefixEnd_2677381 : Nat := 4983230072969 + 3 ^ 40 * 2677381 * 2
def baseEnd_2677381 : Nat := 1374783348215494468224455

theorem tailTrace_2677381 : CollatzResearch.WordTrace tailWord_2677381 prefixEnd_2677381 1374783348215494468224455 := by
  unfold tailWord_2677381
  simp only [CollatzResearch.WordTrace]
  refine ⟨97652107513313372115559997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65101405008875581410373331 97652107513313372115559997)
  ·
    refine ⟨36619540317492514543334999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97652107513313372115559997 36619540317492514543334999)
    ·
      refine ⟨54929310476238771815002499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36619540317492514543334999 54929310476238771815002499)
      ·
        refine ⟨82393965714358157722503749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54929310476238771815002499 82393965714358157722503749)
        ·
          refine ⟨15448868571442154572969453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82393965714358157722503749 15448868571442154572969453)
          ·
            refine ⟨5793325714290807964863545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15448868571442154572969453 5793325714290807964863545)
            ·
              refine ⟨4344994285718105973647659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5793325714290807964863545 4344994285718105973647659)
              ·
                refine ⟨6517491428577158960471489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4344994285718105973647659 6517491428577158960471489)
                ·
                  refine ⟨4888118571432869220353617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6517491428577158960471489 4888118571432869220353617)
                  ·
                    refine ⟨3666088928574651915265213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4888118571432869220353617 3666088928574651915265213)
                    ·
                      refine ⟨1374783348215494468224455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3666088928574651915265213 1374783348215494468224455)
                      ·
                        rfl

theorem cell23_2677381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 2, 2, 3].length) (baseStart_2677381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677381 prefixEnd_2677381 := by exact prefixLift 2677381
  have htrace : WordTrace (prefixWord ++ tailWord_2677381) baseStart_2677381 baseEnd_2677381 := by
    simpa [prefixWord, tailWord_2677381, baseEnd_2677381] using wordTrace_append hprefix tailTrace_2677381
  have hstable : (prefixWord ++ tailWord_2677381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677381).length < 2 ^ (prefixWord ++ tailWord_2677381).sum := by decide
  have hdescent : baseEnd_2677381 < baseStart_2677381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677417 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 2, 5, 4]
def baseStart_2677417 : Nat := 118140960795 + 2677417 * 2 ^ 59
def prefixEnd_2677417 : Nat := 4983230072969 + 3 ^ 40 * 2677417 * 2
def baseEnd_2677417 : Nat := 1374801833519056327374289

theorem tailTrace_2677417 : CollatzResearch.WordTrace tailWord_2677417 prefixEnd_2677417 1374801833519056327374289 := by
  unfold tailWord_2677417
  simp only [CollatzResearch.WordTrace]
  refine ⟨97653420541182950263870505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65102280360788633509247003 97653420541182950263870505)
  ·
    refine ⟨73240065405887212697902879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97653420541182950263870505 73240065405887212697902879)
    ·
      refine ⟨109860098108830819046854319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73240065405887212697902879 109860098108830819046854319)
      ·
        refine ⟨164790147163246228570281479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109860098108830819046854319 164790147163246228570281479)
        ·
          refine ⟨247185220744869342855422219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164790147163246228570281479 247185220744869342855422219)
          ·
            refine ⟨370777831117304014283133329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247185220744869342855422219 370777831117304014283133329)
            ·
              refine ⟨278083373337978010712349997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 370777831117304014283133329 278083373337978010712349997)
              ·
                refine ⟨104281265001741754017131249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 278083373337978010712349997 104281265001741754017131249)
                ·
                  refine ⟨78210948751306315512848437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104281265001741754017131249 78210948751306315512848437)
                  ·
                    refine ⟨7332276445434967079329541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 78210948751306315512848437 7332276445434967079329541)
                    ·
                      refine ⟨1374801833519056327374289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7332276445434967079329541 1374801833519056327374289)
                      ·
                        rfl

theorem cell23_2677417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 5, 4].length) (baseStart_2677417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677417 prefixEnd_2677417 := by exact prefixLift 2677417
  have htrace : WordTrace (prefixWord ++ tailWord_2677417) baseStart_2677417 baseEnd_2677417 := by
    simpa [prefixWord, tailWord_2677417, baseEnd_2677417] using wordTrace_append hprefix tailTrace_2677417
  have hstable : (prefixWord ++ tailWord_2677417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677417).length < 2 ^ (prefixWord ++ tailWord_2677417).sum := by decide
  have hdescent : baseEnd_2677417 < baseStart_2677417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677434 : List Nat := [3, 1, 1, 1, 2, 3, 1, 3, 3, 1, 4]
def baseStart_2677434 : Nat := 118140960795 + 2677434 * 2 ^ 59
def prefixEnd_2677434 : Nat := 4983230072969 + 3 ^ 40 * 2677434 * 2
def baseEnd_2677434 : Nat := 1374810562690182760861711

theorem tailTrace_2677434 : CollatzResearch.WordTrace tailWord_2677434 prefixEnd_2677434 1374810562690182760861711 := by
  unfold tailWord_2677434
  simp only [CollatzResearch.WordTrace]
  refine ⟨24413510145530340541809839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65102693721414241444826237 24413510145530340541809839)
  ·
    refine ⟨36620265218295510812714759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24413510145530340541809839 36620265218295510812714759)
    ·
      refine ⟨54930397827443266219072139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36620265218295510812714759 54930397827443266219072139)
      ·
        refine ⟨82395596741164899328608209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54930397827443266219072139 82395596741164899328608209)
        ·
          refine ⟨61796697555873674496456157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82395596741164899328608209 61796697555873674496456157)
          ·
            refine ⟨23173761583452627936171059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61796697555873674496456157 23173761583452627936171059)
            ·
              refine ⟨34760642375178941904256589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23173761583452627936171059 34760642375178941904256589)
              ·
                refine ⟨13035240890692103214096221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34760642375178941904256589 13035240890692103214096221)
                ·
                  refine ⟨4888215334009538705286083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13035240890692103214096221 4888215334009538705286083)
                  ·
                    refine ⟨7332323001014308057929125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4888215334009538705286083 7332323001014308057929125)
                    ·
                      refine ⟨1374810562690182760861711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7332323001014308057929125 1374810562690182760861711)
                      ·
                        rfl

theorem cell23_2677434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 3, 1, 4].length) (baseStart_2677434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677434 prefixEnd_2677434 := by exact prefixLift 2677434
  have htrace : WordTrace (prefixWord ++ tailWord_2677434) baseStart_2677434 baseEnd_2677434 := by
    simpa [prefixWord, tailWord_2677434, baseEnd_2677434] using wordTrace_append hprefix tailTrace_2677434
  have hstable : (prefixWord ++ tailWord_2677434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677434).length < 2 ^ (prefixWord ++ tailWord_2677434).sum := by decide
  have hdescent : baseEnd_2677434 < baseStart_2677434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677448 : List Nat := [2, 1, 3, 1, 2, 5, 2, 1, 1, 5]
def baseStart_2677448 : Nat := 118140960795 + 2677448 * 2 ^ 59
def prefixEnd_2677448 : Nat := 4983230072969 + 3 ^ 40 * 2677448 * 2
def baseEnd_2677448 : Nat := 458272583806448568695549

theorem tailTrace_2677448 : CollatzResearch.WordTrace tailWord_2677448 prefixEnd_2677448 458272583806448568695549 := by
  unfold tailWord_2677448
  simp only [CollatzResearch.WordTrace]
  refine ⟨48827275602035321279124499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65103034136047095038832665 48827275602035321279124499)
  ·
    refine ⟨73240913403052981918686749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48827275602035321279124499 73240913403052981918686749)
    ·
      refine ⟨27465342526144868219507531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73240913403052981918686749 27465342526144868219507531)
      ·
        refine ⟨41198013789217302329261297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27465342526144868219507531 41198013789217302329261297)
        ·
          refine ⟨30898510341912976746945973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41198013789217302329261297 30898510341912976746945973)
          ·
            refine ⟨2896735344554341570026185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30898510341912976746945973 2896735344554341570026185)
            ·
              refine ⟨2172551508415756177519639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2896735344554341570026185 2172551508415756177519639)
              ·
                refine ⟨3258827262623634266279459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2172551508415756177519639 3258827262623634266279459)
                ·
                  refine ⟨4888240893935451399419189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3258827262623634266279459 4888240893935451399419189)
                  ·
                    refine ⟨458272583806448568695549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4888240893935451399419189 458272583806448568695549)
                    ·
                      rfl

theorem cell23_2677448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 1, 1, 5].length) (baseStart_2677448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677448 prefixEnd_2677448 := by exact prefixLift 2677448
  have htrace : WordTrace (prefixWord ++ tailWord_2677448) baseStart_2677448 baseEnd_2677448 := by
    simpa [prefixWord, tailWord_2677448, baseEnd_2677448] using wordTrace_append hprefix tailTrace_2677448
  have hstable : (prefixWord ++ tailWord_2677448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677448).length < 2 ^ (prefixWord ++ tailWord_2677448).sum := by decide
  have hdescent : baseEnd_2677448 < baseStart_2677448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677457 : List Nat := [1, 2, 2, 1, 2, 3, 12]
def baseStart_2677457 : Nat := 118140960795 + 2677457 * 2 ^ 59
def prefixEnd_2677457 : Nat := 4983230072969 + 3 ^ 40 * 2677457 * 2
def baseEnd_2677457 : Nat := 16973115712904150257705

theorem tailTrace_2677457 : CollatzResearch.WordTrace tailWord_2677457 prefixEnd_2677457 16973115712904150257705 := by
  unfold tailWord_2677457
  simp only [CollatzResearch.WordTrace]
  refine ⟨97654879461038037095326625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65103252974025358063551083 97654879461038037095326625)
  ·
    refine ⟨73241159595778527821494969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97654879461038037095326625 73241159595778527821494969)
    ·
      refine ⟨54930869696833895866121227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73241159595778527821494969 54930869696833895866121227)
      ·
        refine ⟨82396304545250843799181841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54930869696833895866121227 82396304545250843799181841)
        ·
          refine ⟨61797228408938132849386381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82396304545250843799181841 61797228408938132849386381)
          ·
            refine ⟨23173960653351799818519893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61797228408938132849386381 23173960653351799818519893)
            ·
              refine ⟨16973115712904150257705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 23173960653351799818519893 16973115712904150257705)
              ·
                rfl

theorem cell23_2677457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 12].length) (baseStart_2677457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677457 prefixEnd_2677457 := by exact prefixLift 2677457
  have htrace : WordTrace (prefixWord ++ tailWord_2677457) baseStart_2677457 baseEnd_2677457 := by
    simpa [prefixWord, tailWord_2677457, baseEnd_2677457] using wordTrace_append hprefix tailTrace_2677457
  have hstable : (prefixWord ++ tailWord_2677457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677457).length < 2 ^ (prefixWord ++ tailWord_2677457).sum := by decide
  have hdescent : baseEnd_2677457 < baseStart_2677457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677501 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 6, 1, 3]
def baseStart_2677501 : Nat := 118140960795 + 2677501 * 2 ^ 59
def prefixEnd_2677501 : Nat := 4983230072969 + 3 ^ 40 * 2677501 * 2
def baseEnd_2677501 : Nat := 1374844965894033998723903

theorem tailTrace_2677501 : CollatzResearch.WordTrace tailWord_2677501 prefixEnd_2677501 1374844965894033998723903 := by
  unfold tailWord_2677501
  simp only [CollatzResearch.WordTrace]
  refine ⟨97656484272878632609928357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65104322848585755073285571 97656484272878632609928357)
  ·
    refine ⟨18310590801164743614361567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97656484272878632609928357 18310590801164743614361567)
    ·
      refine ⟨27465886201747115421542351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18310590801164743614361567 27465886201747115421542351)
      ·
        refine ⟨41198829302620673132313527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27465886201747115421542351 41198829302620673132313527)
        ·
          refine ⟨61798243953931009698470291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41198829302620673132313527 61798243953931009698470291)
          ·
            refine ⟨92697365930896514547705437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61798243953931009698470291 92697365930896514547705437)
            ·
              refine ⟨34761512224086192955389539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92697365930896514547705437 34761512224086192955389539)
              ·
                refine ⟨52142268336129289433084309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34761512224086192955389539 52142268336129289433084309)
                ·
                  refine ⟨2444168828256060442175827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 52142268336129289433084309 2444168828256060442175827)
                  ·
                    refine ⟨3666253242384090663263741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2444168828256060442175827 3666253242384090663263741)
                    ·
                      refine ⟨1374844965894033998723903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3666253242384090663263741 1374844965894033998723903)
                      ·
                        rfl

theorem cell23_2677501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 6, 1, 3].length) (baseStart_2677501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677501 prefixEnd_2677501 := by exact prefixLift 2677501
  have htrace : WordTrace (prefixWord ++ tailWord_2677501) baseStart_2677501 baseEnd_2677501 := by
    simpa [prefixWord, tailWord_2677501, baseEnd_2677501] using wordTrace_append hprefix tailTrace_2677501
  have hstable : (prefixWord ++ tailWord_2677501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677501).length < 2 ^ (prefixWord ++ tailWord_2677501).sum := by decide
  have hdescent : baseEnd_2677501 < baseStart_2677501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677514 : List Nat := [3, 1, 2, 2, 1, 2, 1, 2, 2, 2, 5]
def baseStart_2677514 : Nat := 118140960795 + 2677514 * 2 ^ 59
def prefixEnd_2677514 : Nat := 4983230072969 + 3 ^ 40 * 2677514 * 2
def baseEnd_2677514 : Nat := 1374851641142542447861343

theorem tailTrace_2677514 : CollatzResearch.WordTrace tailWord_2677514 prefixEnd_2677514 1374851641142542447861343 := by
  unfold tailWord_2677514
  simp only [CollatzResearch.WordTrace]
  refine ⟨24414239605457883957537899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65104638947887690553434397 24414239605457883957537899)
  ·
    refine ⟨36621359408186825936306849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24414239605457883957537899 36621359408186825936306849)
    ·
      refine ⟨27466019556140119452230137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36621359408186825936306849 27466019556140119452230137)
      ·
        refine ⟨20599514667105089589172603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27466019556140119452230137 20599514667105089589172603)
        ·
          refine ⟨30899272000657634383758905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20599514667105089589172603 30899272000657634383758905)
          ·
            refine ⟨23174454000493225787819179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30899272000657634383758905 23174454000493225787819179)
            ·
              refine ⟨34761681000739838681728769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23174454000493225787819179 34761681000739838681728769)
              ·
                refine ⟨26071260750554879011296577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34761681000739838681728769 26071260750554879011296577)
                ·
                  refine ⟨19553445562916159258472433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26071260750554879011296577 19553445562916159258472433)
                  ·
                    refine ⟨14665084172187119443854325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19553445562916159258472433 14665084172187119443854325)
                    ·
                      refine ⟨1374851641142542447861343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14665084172187119443854325 1374851641142542447861343)
                      ·
                        rfl

theorem cell23_2677514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_2677514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677514 prefixEnd_2677514 := by exact prefixLift 2677514
  have htrace : WordTrace (prefixWord ++ tailWord_2677514) baseStart_2677514 baseEnd_2677514 := by
    simpa [prefixWord, tailWord_2677514, baseEnd_2677514] using wordTrace_append hprefix tailTrace_2677514
  have hstable : (prefixWord ++ tailWord_2677514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677514).length < 2 ^ (prefixWord ++ tailWord_2677514).sum := by decide
  have hdescent : baseEnd_2677514 < baseStart_2677514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677518 : List Nat := [4, 1, 1, 2, 1, 1, 1, 6, 2, 1, 3]
def baseStart_2677518 : Nat := 118140960795 + 2677518 * 2 ^ 59
def prefixEnd_2677518 : Nat := 4983230072969 + 3 ^ 40 * 2677518 * 2
def baseEnd_2677518 : Nat := 1374853695065160432211325

theorem tailTrace_2677518 : CollatzResearch.WordTrace tailWord_2677518 prefixEnd_2677518 1374853695065160432211325 := by
  unfold tailWord_2677518
  simp only [CollatzResearch.WordTrace]
  refine ⟨12207138039227130564162151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65104736209211363008864805 12207138039227130564162151)
  ·
    refine ⟨18310707058840695846243227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12207138039227130564162151 18310707058840695846243227)
    ·
      refine ⟨27466060588261043769364841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18310707058840695846243227 27466060588261043769364841)
      ·
        refine ⟨20599545441195782827023631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27466060588261043769364841 20599545441195782827023631)
        ·
          refine ⟨30899318161793674240535447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20599545441195782827023631 30899318161793674240535447)
          ·
            refine ⟨46348977242690511360803171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30899318161793674240535447 46348977242690511360803171)
            ·
              refine ⟨69523465864035767041204757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46348977242690511360803171 69523465864035767041204757)
              ·
                refine ⟨3258912462376676580056473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 69523465864035767041204757 3258912462376676580056473)
                ·
                  refine ⟨2444184346782507435042355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3258912462376676580056473 2444184346782507435042355)
                  ·
                    refine ⟨3666276520173761152563533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2444184346782507435042355 3666276520173761152563533)
                    ·
                      refine ⟨1374853695065160432211325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3666276520173761152563533 1374853695065160432211325)
                      ·
                        rfl

theorem cell23_2677518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_2677518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677518 prefixEnd_2677518 := by exact prefixLift 2677518
  have htrace : WordTrace (prefixWord ++ tailWord_2677518) baseStart_2677518 baseEnd_2677518 := by
    simpa [prefixWord, tailWord_2677518, baseEnd_2677518] using wordTrace_append hprefix tailTrace_2677518
  have hstable : (prefixWord ++ tailWord_2677518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677518).length < 2 ^ (prefixWord ++ tailWord_2677518).sum := by decide
  have hdescent : baseEnd_2677518 < baseStart_2677518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677535 : List Nat := [1, 1, 2, 4, 2, 2, 4, 1, 2, 1, 3]
def baseStart_2677535 : Nat := 118140960795 + 2677535 * 2 ^ 59
def prefixEnd_2677535 : Nat := 4983230072969 + 3 ^ 40 * 2677535 * 2
def baseEnd_2677535 : Nat := 1374862424236286865698747

theorem tailTrace_2677535 : CollatzResearch.WordTrace tailWord_2677535 prefixEnd_2677535 1374862424236286865698747 := by
  unfold tailWord_2677535
  simp only [CollatzResearch.WordTrace]
  refine ⟨97657724354755456416666059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65105149569836970944444039 97657724354755456416666059)
  ·
    refine ⟨146486586532133184624999089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97657724354755456416666059 146486586532133184624999089)
    ·
      refine ⟨109864939899099888468749317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146486586532133184624999089 109864939899099888468749317)
      ·
        refine ⟨20599676231081229087890497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109864939899099888468749317 20599676231081229087890497)
        ·
          refine ⟨15449757173310921815917873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20599676231081229087890497 15449757173310921815917873)
          ·
            refine ⟨11587317879983191361938405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15449757173310921815917873 11587317879983191361938405)
            ·
              refine ⟨2172622102496848380363451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11587317879983191361938405 2172622102496848380363451)
              ·
                refine ⟨3258933153745272570545177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2172622102496848380363451 3258933153745272570545177)
                ·
                  refine ⟨2444199865308954427908883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3258933153745272570545177 2444199865308954427908883)
                  ·
                    refine ⟨3666299797963431641863325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2444199865308954427908883 3666299797963431641863325)
                    ·
                      refine ⟨1374862424236286865698747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3666299797963431641863325 1374862424236286865698747)
                      ·
                        rfl

theorem cell23_2677535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 1, 2, 1, 3].length) (baseStart_2677535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677535 prefixEnd_2677535 := by exact prefixLift 2677535
  have htrace : WordTrace (prefixWord ++ tailWord_2677535) baseStart_2677535 baseEnd_2677535 := by
    simpa [prefixWord, tailWord_2677535, baseEnd_2677535] using wordTrace_append hprefix tailTrace_2677535
  have hstable : (prefixWord ++ tailWord_2677535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677535).length < 2 ^ (prefixWord ++ tailWord_2677535).sum := by decide
  have hdescent : baseEnd_2677535 < baseStart_2677535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677562 : List Nat := [3, 1, 1, 1, 6, 1, 3, 1, 1, 3, 2]
def baseStart_2677562 : Nat := 118140960795 + 2677562 * 2 ^ 59
def prefixEnd_2677562 : Nat := 4983230072969 + 3 ^ 40 * 2677562 * 2
def baseEnd_2677562 : Nat := 1374876288213958260061123

theorem tailTrace_2677562 : CollatzResearch.WordTrace tailWord_2677562 prefixEnd_2677562 1374876288213958260061123 := by
  unfold tailWord_2677562
  simp only [CollatzResearch.WordTrace]
  refine ⟨24414677281414410006974735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65105806083771760018599293 24414677281414410006974735)
  ·
    refine ⟨36622015922121615010462103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24414677281414410006974735 36622015922121615010462103)
    ·
      refine ⟨54933023883182422515693155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36622015922121615010462103 54933023883182422515693155)
      ·
        refine ⟨82399535824773633773539733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54933023883182422515693155 82399535824773633773539733)
        ·
          refine ⟨3862478241786264083134675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 82399535824773633773539733 3862478241786264083134675)
          ·
            refine ⟨5793717362679396124702013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3862478241786264083134675 5793717362679396124702013)
            ·
              refine ⟨2172644011004773546763255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5793717362679396124702013 2172644011004773546763255)
              ·
                refine ⟨3258966016507160320144883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2172644011004773546763255 3258966016507160320144883)
                ·
                  refine ⟨4888449024760740480217325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3258966016507160320144883 4888449024760740480217325)
                  ·
                    refine ⟨1833168384285277680081497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4888449024760740480217325 1833168384285277680081497)
                    ·
                      refine ⟨1374876288213958260061123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1833168384285277680081497 1374876288213958260061123)
                      ·
                        rfl

theorem cell23_2677562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 1, 1, 3, 2].length) (baseStart_2677562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677562 prefixEnd_2677562 := by exact prefixLift 2677562
  have htrace : WordTrace (prefixWord ++ tailWord_2677562) baseStart_2677562 baseEnd_2677562 := by
    simpa [prefixWord, tailWord_2677562, baseEnd_2677562] using wordTrace_append hprefix tailTrace_2677562
  have hstable : (prefixWord ++ tailWord_2677562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677562).length < 2 ^ (prefixWord ++ tailWord_2677562).sum := by decide
  have hdescent : baseEnd_2677562 < baseStart_2677562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677588 : List Nat := [2, 4, 1, 1, 4, 1, 1, 1, 2, 2, 4]
def baseStart_2677588 : Nat := 118140960795 + 2677588 * 2 ^ 59
def prefixEnd_2677588 : Nat := 4983230072969 + 3 ^ 40 * 2677588 * 2
def baseEnd_2677588 : Nat := 1374889638710975158336003

theorem tailTrace_2677588 : CollatzResearch.WordTrace tailWord_2677588 prefixEnd_2677588 1374889638710975158336003 := by
  unfold tailWord_2677588
  simp only [CollatzResearch.WordTrace]
  refine ⟨48829828711781723234172709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65106438282375630978896945 48829828711781723234172709)
  ·
    refine ⟨9155592883459073106407383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48829828711781723234172709 9155592883459073106407383)
    ·
      refine ⟨13733389325188609659611075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9155592883459073106407383 13733389325188609659611075)
      ·
        refine ⟨20600083987782914489416613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13733389325188609659611075 20600083987782914489416613)
        ·
          refine ⟨3862515747709296466765615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20600083987782914489416613 3862515747709296466765615)
          ·
            refine ⟨5793773621563944700148423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3862515747709296466765615 5793773621563944700148423)
            ·
              refine ⟨8690660432345917050222635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5793773621563944700148423 8690660432345917050222635)
              ·
                refine ⟨13035990648518875575333953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8690660432345917050222635 13035990648518875575333953)
                ·
                  refine ⟨9776992986389156681500465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13035990648518875575333953 9776992986389156681500465)
                  ·
                    refine ⟨7332744739791867511125349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9776992986389156681500465 7332744739791867511125349)
                    ·
                      refine ⟨1374889638710975158336003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7332744739791867511125349 1374889638710975158336003)
                      ·
                        rfl

theorem cell23_2677588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_2677588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677588 prefixEnd_2677588 := by exact prefixLift 2677588
  have htrace : WordTrace (prefixWord ++ tailWord_2677588) baseStart_2677588 baseEnd_2677588 := by
    simpa [prefixWord, tailWord_2677588, baseEnd_2677588] using wordTrace_append hprefix tailTrace_2677588
  have hstable : (prefixWord ++ tailWord_2677588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677588).length < 2 ^ (prefixWord ++ tailWord_2677588).sum := by decide
  have hdescent : baseEnd_2677588 < baseStart_2677588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677591 : List Nat := [1, 1, 3, 2, 4, 1, 1, 1, 1, 5, 3]
def baseStart_2677591 : Nat := 118140960795 + 2677591 * 2 ^ 59
def prefixEnd_2677591 : Nat := 4983230072969 + 3 ^ 40 * 2677591 * 2
def baseEnd_2677591 : Nat := 1374891179152938646598489

theorem tailTrace_2677591 : CollatzResearch.WordTrace tailWord_2677591 prefixEnd_2677591 1374891179152938646598489 := by
  unfold tailWord_2677591
  simp only [CollatzResearch.WordTrace]
  refine ⟨97659766842552577980704627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65106511228368385320469751 97659766842552577980704627)
  ·
    refine ⟨146489650263828866971056941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97659766842552577980704627 146489650263828866971056941)
    ·
      refine ⟨54933618848935825114146353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146489650263828866971056941 54933618848935825114146353)
      ·
        refine ⟨41200214136701868835609765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54933618848935825114146353 41200214136701868835609765)
        ·
          refine ⟨7725040150631600406676831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41200214136701868835609765 7725040150631600406676831)
          ·
            refine ⟨11587560225947400610015247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7725040150631600406676831 11587560225947400610015247)
            ·
              refine ⟨17381340338921100915022871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11587560225947400610015247 17381340338921100915022871)
              ·
                refine ⟨26072010508381651372534307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17381340338921100915022871 26072010508381651372534307)
                ·
                  refine ⟨39108015762572477058801461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26072010508381651372534307 39108015762572477058801461)
                  ·
                    refine ⟨3666376477741169724262637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39108015762572477058801461 3666376477741169724262637)
                    ·
                      refine ⟨1374891179152938646598489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3666376477741169724262637 1374891179152938646598489)
                      ·
                        rfl

theorem cell23_2677591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 5, 3].length) (baseStart_2677591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677591 prefixEnd_2677591 := by exact prefixLift 2677591
  have htrace : WordTrace (prefixWord ++ tailWord_2677591) baseStart_2677591 baseEnd_2677591 := by
    simpa [prefixWord, tailWord_2677591, baseEnd_2677591] using wordTrace_append hprefix tailTrace_2677591
  have hstable : (prefixWord ++ tailWord_2677591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677591).length < 2 ^ (prefixWord ++ tailWord_2677591).sum := by decide
  have hdescent : baseEnd_2677591 < baseStart_2677591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677611 : List Nat := [1, 1, 1, 1, 2, 2, 7, 1, 2, 5]
def baseStart_2677611 : Nat := 118140960795 + 2677611 * 2 ^ 59
def prefixEnd_2677611 : Nat := 4983230072969 + 3 ^ 40 * 2677611 * 2
def baseEnd_2677611 : Nat := 458300482922009522782799

theorem tailTrace_2677611 : CollatzResearch.WordTrace tailWord_2677611 prefixEnd_2677611 458300482922009522782799 := by
  unfold tailWord_2677611
  simp only [CollatzResearch.WordTrace]
  refine ⟨97660496302480121396432687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65106997534986747597621791 97660496302480121396432687)
  ·
    refine ⟨146490744453720182094649031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97660496302480121396432687 146490744453720182094649031)
    ·
      refine ⟨219736116680580273141973547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146490744453720182094649031 219736116680580273141973547)
      ·
        refine ⟨329604175020870409712960321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219736116680580273141973547 329604175020870409712960321)
        ·
          refine ⟨247203131265652807284720241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 329604175020870409712960321 247203131265652807284720241)
          ·
            refine ⟨185402348449239605463540181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247203131265652807284720241 185402348449239605463540181)
            ·
              refine ⟨4345367541779053253051723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 185402348449239605463540181 4345367541779053253051723)
              ·
                refine ⟨6518051312668579879577585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4345367541779053253051723 6518051312668579879577585)
                ·
                  refine ⟨4888538484501434909683189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6518051312668579879577585 4888538484501434909683189)
                  ·
                    refine ⟨458300482922009522782799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4888538484501434909683189 458300482922009522782799)
                    ·
                      rfl

theorem cell23_2677611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 2, 5].length) (baseStart_2677611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677611 prefixEnd_2677611 := by exact prefixLift 2677611
  have htrace : WordTrace (prefixWord ++ tailWord_2677611) baseStart_2677611 baseEnd_2677611 := by
    simpa [prefixWord, tailWord_2677611, baseEnd_2677611] using wordTrace_append hprefix tailTrace_2677611
  have hstable : (prefixWord ++ tailWord_2677611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677611).length < 2 ^ (prefixWord ++ tailWord_2677611).sum := by decide
  have hdescent : baseEnd_2677611 < baseStart_2677611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677631 : List Nat := [1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 4]
def baseStart_2677631 : Nat := 118140960795 + 2677631 * 2 ^ 59
def prefixEnd_2677631 : Nat := 4983230072969 + 3 ^ 40 * 2677631 * 2
def baseEnd_2677631 : Nat := 1374911718379118490098305

theorem tailTrace_2677631 : CollatzResearch.WordTrace tailWord_2677631 prefixEnd_2677631 1374911718379118490098305 := by
  unfold tailWord_2677631
  simp only [CollatzResearch.WordTrace]
  refine ⟨97661225762407664812160747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65107483841605109874773831 97661225762407664812160747)
  ·
    refine ⟨146491838643611497218241121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97661225762407664812160747 146491838643611497218241121)
    ·
      refine ⟨109868878982708622913680841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146491838643611497218241121 109868878982708622913680841)
      ·
        refine ⟨82401659237031467185260631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109868878982708622913680841 82401659237031467185260631)
        ·
          refine ⟨123602488855547200777890947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82401659237031467185260631 123602488855547200777890947)
          ·
            refine ⟨185403733283320801166836421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123602488855547200777890947 185403733283320801166836421)
            ·
              refine ⟨34763199990622650218781829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 185403733283320801166836421 34763199990622650218781829)
              ·
                refine ⟨6518099998241746916021593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34763199990622650218781829 6518099998241746916021593)
                ·
                  refine ⟨4888574998681310187016195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6518099998241746916021593 4888574998681310187016195)
                  ·
                    refine ⟨7332862498021965280524293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4888574998681310187016195 7332862498021965280524293)
                    ·
                      refine ⟨1374911718379118490098305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7332862498021965280524293 1374911718379118490098305)
                      ·
                        rfl

theorem cell23_2677631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 4].length) (baseStart_2677631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677631 prefixEnd_2677631 := by exact prefixLift 2677631
  have htrace : WordTrace (prefixWord ++ tailWord_2677631) baseStart_2677631 baseEnd_2677631 := by
    simpa [prefixWord, tailWord_2677631, baseEnd_2677631] using wordTrace_append hprefix tailTrace_2677631
  have hstable : (prefixWord ++ tailWord_2677631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677631).length < 2 ^ (prefixWord ++ tailWord_2677631).sum := by decide
  have hdescent : baseEnd_2677631 < baseStart_2677631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677651 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 6, 2, 3]
def baseStart_2677651 : Nat := 118140960795 + 2677651 * 2 ^ 59
def prefixEnd_2677651 : Nat := 4983230072969 + 3 ^ 40 * 2677651 * 2
def baseEnd_2677651 : Nat := 1374921987992208411848213

theorem tailTrace_2677651 : CollatzResearch.WordTrace tailWord_2677651 prefixEnd_2677651 1374921987992208411848213 := by
  unfold tailWord_2677651
  simp only [CollatzResearch.WordTrace]
  refine ⟨97661955222335208227888807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65107970148223472151925871 97661955222335208227888807)
  ·
    refine ⟨146492932833502812341833211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97661955222335208227888807 146492932833502812341833211)
    ·
      refine ⟨219739399250254218512749817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146492932833502812341833211 219739399250254218512749817)
      ·
        refine ⟨164804549437690663884562363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219739399250254218512749817 164804549437690663884562363)
        ·
          refine ⟨247206824156535995826843545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164804549437690663884562363 247206824156535995826843545)
          ·
            refine ⟨185405118117401996870132659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247206824156535995826843545 185405118117401996870132659)
            ·
              refine ⟨278107677176102995305198989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185405118117401996870132659 278107677176102995305198989)
              ·
                refine ⟨104290378941038623239449621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 278107677176102995305198989 104290378941038623239449621)
                ·
                  refine ⟨4888611512861185464349201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 104290378941038623239449621 4888611512861185464349201)
                  ·
                    refine ⟨3666458634645889098261901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4888611512861185464349201 3666458634645889098261901)
                    ·
                      refine ⟨1374921987992208411848213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3666458634645889098261901 1374921987992208411848213)
                      ·
                        rfl

theorem cell23_2677651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 6, 2, 3].length) (baseStart_2677651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677651 prefixEnd_2677651 := by exact prefixLift 2677651
  have htrace : WordTrace (prefixWord ++ tailWord_2677651) baseStart_2677651 baseEnd_2677651 := by
    simpa [prefixWord, tailWord_2677651, baseEnd_2677651] using wordTrace_append hprefix tailTrace_2677651
  have hstable : (prefixWord ++ tailWord_2677651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677651).length < 2 ^ (prefixWord ++ tailWord_2677651).sum := by decide
  have hdescent : baseEnd_2677651 < baseStart_2677651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677661 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 2, 4, 4]
def baseStart_2677661 : Nat := 118140960795 + 2677661 * 2 ^ 59
def prefixEnd_2677661 : Nat := 4983230072969 + 3 ^ 40 * 2677661 * 2
def baseEnd_2677661 : Nat := 1374927122798753372723167

theorem tailTrace_2677661 : CollatzResearch.WordTrace tailWord_2677661 prefixEnd_2677661 1374927122798753372723167 := by
  unfold tailWord_2677661
  simp only [CollatzResearch.WordTrace]
  refine ⟨97662319952298979935752837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65108213301532653290501891 97662319952298979935752837)
  ·
    refine ⟨18311684991056058737953657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97662319952298979935752837 18311684991056058737953657)
    ·
      refine ⟨13733763743292044053465243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18311684991056058737953657 13733763743292044053465243)
      ·
        refine ⟨20600645614938066080197865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13733763743292044053465243 20600645614938066080197865)
        ·
          refine ⟨15450484211203549560148399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20600645614938066080197865 15450484211203549560148399)
          ·
            refine ⟨23175726316805324340222599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15450484211203549560148399 23175726316805324340222599)
            ·
              refine ⟨34763589475207986510333899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23175726316805324340222599 34763589475207986510333899)
              ·
                refine ⟨52145384212811979765500849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34763589475207986510333899 52145384212811979765500849)
                ·
                  refine ⟨39109038159608984824125637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52145384212811979765500849 39109038159608984824125637)
                  ·
                    refine ⟨7332944654926684654523557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39109038159608984824125637 7332944654926684654523557)
                    ·
                      refine ⟨1374927122798753372723167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7332944654926684654523557 1374927122798753372723167)
                      ·
                        rfl

theorem cell23_2677661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_2677661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677661 prefixEnd_2677661 := by exact prefixLift 2677661
  have htrace : WordTrace (prefixWord ++ tailWord_2677661) baseStart_2677661 baseEnd_2677661 := by
    simpa [prefixWord, tailWord_2677661, baseEnd_2677661] using wordTrace_append hprefix tailTrace_2677661
  have hstable : (prefixWord ++ tailWord_2677661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677661).length < 2 ^ (prefixWord ++ tailWord_2677661).sum := by decide
  have hdescent : baseEnd_2677661 < baseStart_2677661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677668 : List Nat := [2, 3, 1, 2, 1, 2, 2, 3, 2, 2, 3]
def baseStart_2677668 : Nat := 118140960795 + 2677668 * 2 ^ 59
def prefixEnd_2677668 : Nat := 4983230072969 + 3 ^ 40 * 2677668 * 2
def baseEnd_2677668 : Nat := 1374930717163334845335635

theorem tailTrace_2677668 : CollatzResearch.WordTrace tailWord_2677668 prefixEnd_2677668 1374930717163334845335635 := by
  unfold tailWord_2677668
  simp only [CollatzResearch.WordTrace]
  refine ⟨48831287631636810065628829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65108383508849080087505105 48831287631636810065628829)
  ·
    refine ⟨18311732861863803774610811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48831287631636810065628829 18311732861863803774610811)
    ·
      refine ⟨27467599292795705661916217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18311732861863803774610811 27467599292795705661916217)
      ·
        refine ⟨20600699469596779246437163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27467599292795705661916217 20600699469596779246437163)
        ·
          refine ⟨30901049204395168869655745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20600699469596779246437163 30901049204395168869655745)
          ·
            refine ⟨23175786903296376652241809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30901049204395168869655745 23175786903296376652241809)
            ·
              refine ⟨17381840177472282489181357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23175786903296376652241809 17381840177472282489181357)
              ·
                refine ⟨6518190066552105933443009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17381840177472282489181357 6518190066552105933443009)
                ·
                  refine ⟨4888642549914079450082257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6518190066552105933443009 4888642549914079450082257)
                  ·
                    refine ⟨3666481912435559587561693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4888642549914079450082257 3666481912435559587561693)
                    ·
                      refine ⟨1374930717163334845335635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3666481912435559587561693 1374930717163334845335635)
                      ·
                        rfl

theorem cell23_2677668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_2677668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677668 prefixEnd_2677668 := by exact prefixLift 2677668
  have htrace : WordTrace (prefixWord ++ tailWord_2677668) baseStart_2677668 baseEnd_2677668 := by
    simpa [prefixWord, tailWord_2677668, baseEnd_2677668] using wordTrace_append hprefix tailTrace_2677668
  have hstable : (prefixWord ++ tailWord_2677668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677668).length < 2 ^ (prefixWord ++ tailWord_2677668).sum := by decide
  have hdescent : baseEnd_2677668 < baseStart_2677668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677755 : List Nat := [1, 1, 1, 1, 1, 3, 3, 5, 3, 2, 2]
def baseStart_2677755 : Nat := 118140960795 + 2677755 * 2 ^ 59
def prefixEnd_2677755 : Nat := 4983230072969 + 3 ^ 40 * 2677755 * 2
def baseEnd_2677755 : Nat := 1374975389980276004947735

theorem tailTrace_2677755 : CollatzResearch.WordTrace tailWord_2677755 prefixEnd_2677755 1374975389980276004947735 := by
  unfold tailWord_2677755
  simp only [CollatzResearch.WordTrace]
  refine ⟨97665748413958433989674719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65110498942638955993116479 97665748413958433989674719)
  ·
    refine ⟨146498622620937650984512079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97665748413958433989674719 146498622620937650984512079)
    ·
      refine ⟨219747933931406476476768119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146498622620937650984512079 219747933931406476476768119)
      ·
        refine ⟨329621900897109714715152179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219747933931406476476768119 329621900897109714715152179)
        ·
          refine ⟨494432851345664572072728269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329621900897109714715152179 494432851345664572072728269)
          ·
            refine ⟨185412319254624214527273101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 494432851345664572072728269 185412319254624214527273101)
            ·
              refine ⟨69529619720484080447727413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 185412319254624214527273101 69529619720484080447727413)
              ·
                refine ⟨6518401848795382541974445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69529619720484080447727413 6518401848795382541974445)
                ·
                  refine ⟨2444400693298268453240417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6518401848795382541974445 2444400693298268453240417)
                  ·
                    refine ⟨1833300519973701339930313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2444400693298268453240417 1833300519973701339930313)
                    ·
                      refine ⟨1374975389980276004947735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1833300519973701339930313 1374975389980276004947735)
                      ·
                        rfl

theorem cell23_2677755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 3, 2, 2].length) (baseStart_2677755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677755 prefixEnd_2677755 := by exact prefixLift 2677755
  have htrace : WordTrace (prefixWord ++ tailWord_2677755) baseStart_2677755 baseEnd_2677755 := by
    simpa [prefixWord, tailWord_2677755, baseEnd_2677755] using wordTrace_append hprefix tailTrace_2677755
  have hstable : (prefixWord ++ tailWord_2677755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677755).length < 2 ^ (prefixWord ++ tailWord_2677755).sum := by decide
  have hdescent : baseEnd_2677755 < baseStart_2677755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677768 : List Nat := [2, 1, 3, 2, 1, 3, 1, 3, 1, 2, 4]
def baseStart_2677768 : Nat := 118140960795 + 2677768 * 2 ^ 59
def prefixEnd_2677768 : Nat := 4983230072969 + 3 ^ 40 * 2677768 * 2
def baseEnd_2677768 : Nat := 1374982065228784454085175

theorem tailTrace_2677768 : CollatzResearch.WordTrace tailWord_2677768 prefixEnd_2677768 1374982065228784454085175 := by
  unfold tailWord_2677768
  simp only [CollatzResearch.WordTrace]
  refine ⟨48833111281455668604948979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65110815041940891473265305 48833111281455668604948979)
  ·
    refine ⟨73249666922183502907423469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48833111281455668604948979 73249666922183502907423469)
    ·
      refine ⟨27468625095818813590283801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73249666922183502907423469 27468625095818813590283801)
      ·
        refine ⟨20601468821864110192712851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27468625095818813590283801 20601468821864110192712851)
        ·
          refine ⟨30902203232796165289069277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20601468821864110192712851 30902203232796165289069277)
          ·
            refine ⟨11588326212298561983400979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30902203232796165289069277 11588326212298561983400979)
            ·
              refine ⟨17382489318447842975101469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11588326212298561983400979 17382489318447842975101469)
              ·
                refine ⟨6518433494417941115663051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17382489318447842975101469 6518433494417941115663051)
                ·
                  refine ⟨9777650241626911673494577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6518433494417941115663051 9777650241626911673494577)
                  ·
                    refine ⟨7333237681220183755120933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9777650241626911673494577 7333237681220183755120933)
                    ·
                      refine ⟨1374982065228784454085175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7333237681220183755120933 1374982065228784454085175)
                      ·
                        rfl

theorem cell23_2677768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_2677768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677768 prefixEnd_2677768 := by exact prefixLift 2677768
  have htrace : WordTrace (prefixWord ++ tailWord_2677768) baseStart_2677768 baseEnd_2677768 := by
    simpa [prefixWord, tailWord_2677768, baseEnd_2677768] using wordTrace_append hprefix tailTrace_2677768
  have hstable : (prefixWord ++ tailWord_2677768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677768).length < 2 ^ (prefixWord ++ tailWord_2677768).sum := by decide
  have hdescent : baseEnd_2677768 < baseStart_2677768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677772 : List Nat := [2, 2, 1, 2, 3, 3, 1, 2, 3, 2, 2]
def baseStart_2677772 : Nat := 118140960795 + 2677772 * 2 ^ 59
def prefixEnd_2677772 : Nat := 4983230072969 + 3 ^ 40 * 2677772 * 2
def baseEnd_2677772 : Nat := 1374984119151402438435157

theorem tailTrace_2677772 : CollatzResearch.WordTrace tailWord_2677772 prefixEnd_2677772 1374984119151402438435157 := by
  unfold tailWord_2677772
  simp only [CollatzResearch.WordTrace]
  refine ⟨48833184227448422946521785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65110912303264563928695713 48833184227448422946521785)
  ·
    refine ⟨36624888170586317209891339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48833184227448422946521785 36624888170586317209891339)
    ·
      refine ⟨54937332255879475814837009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36624888170586317209891339 54937332255879475814837009)
      ·
        refine ⟨41202999191909606861127757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54937332255879475814837009 41202999191909606861127757)
        ·
          refine ⟨15451124696966102572922909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41202999191909606861127757 15451124696966102572922909)
          ·
            refine ⟨5794171761362288464846091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15451124696966102572922909 5794171761362288464846091)
            ·
              refine ⟨8691257642043432697269137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5794171761362288464846091 8691257642043432697269137)
              ·
                refine ⟨6518443231532574522951853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8691257642043432697269137 6518443231532574522951853)
                ·
                  refine ⟨2444416211824715446106945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6518443231532574522951853 2444416211824715446106945)
                  ·
                    refine ⟨1833312158868536584580209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2444416211824715446106945 1833312158868536584580209)
                    ·
                      refine ⟨1374984119151402438435157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1833312158868536584580209 1374984119151402438435157)
                      ·
                        rfl

theorem cell23_2677772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 3, 2, 2].length) (baseStart_2677772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677772 prefixEnd_2677772 := by exact prefixLift 2677772
  have htrace : WordTrace (prefixWord ++ tailWord_2677772) baseStart_2677772 baseEnd_2677772 := by
    simpa [prefixWord, tailWord_2677772, baseEnd_2677772] using wordTrace_append hprefix tailTrace_2677772
  have hstable : (prefixWord ++ tailWord_2677772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677772).length < 2 ^ (prefixWord ++ tailWord_2677772).sum := by decide
  have hdescent : baseEnd_2677772 < baseStart_2677772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677789 : List Nat := [1, 4, 2, 2, 3, 2, 2, 1, 1, 1, 4]
def baseStart_2677789 : Nat := 118140960795 + 2677789 * 2 ^ 59
def prefixEnd_2677789 : Nat := 4983230072969 + 3 ^ 40 * 2677789 * 2
def baseEnd_2677789 : Nat := 1374992848322528871922579

theorem tailTrace_2677789 : CollatzResearch.WordTrace tailWord_2677789 prefixEnd_2677789 1374992848322528871922579 := by
  unfold tailWord_2677789
  simp only [CollatzResearch.WordTrace]
  refine ⟨97666988495835257796412421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65111325663890171864274947 97666988495835257796412421)
  ·
    refine ⟨18312560342969110836827329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97666988495835257796412421 18312560342969110836827329)
    ·
      refine ⟨13734420257226833127620497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18312560342969110836827329 13734420257226833127620497)
      ·
        refine ⟨10300815192920124845715373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13734420257226833127620497 10300815192920124845715373)
        ·
          refine ⟨3862805697345046817143265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10300815192920124845715373 3862805697345046817143265)
          ·
            refine ⟨2897104273008785112857449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3862805697345046817143265 2897104273008785112857449)
            ·
              refine ⟨2172828204756588834643087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2897104273008785112857449 2172828204756588834643087)
              ·
                refine ⟨3259242307134883251964631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2172828204756588834643087 3259242307134883251964631)
                ·
                  refine ⟨4888863460702324877946947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3259242307134883251964631 4888863460702324877946947)
                  ·
                    refine ⟨7333295191053487316920421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4888863460702324877946947 7333295191053487316920421)
                    ·
                      refine ⟨1374992848322528871922579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7333295191053487316920421 1374992848322528871922579)
                      ·
                        rfl

theorem cell23_2677789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_2677789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677789 prefixEnd_2677789 := by exact prefixLift 2677789
  have htrace : WordTrace (prefixWord ++ tailWord_2677789) baseStart_2677789 baseEnd_2677789 := by
    simpa [prefixWord, tailWord_2677789, baseEnd_2677789] using wordTrace_append hprefix tailTrace_2677789
  have hstable : (prefixWord ++ tailWord_2677789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677789).length < 2 ^ (prefixWord ++ tailWord_2677789).sum := by decide
  have hdescent : baseEnd_2677789 < baseStart_2677789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677799 : List Nat := [1, 1, 7, 1, 1, 3, 1, 2, 2, 4]
def baseStart_2677799 : Nat := 118140960795 + 2677799 * 2 ^ 59
def prefixEnd_2677799 : Nat := 4983230072969 + 3 ^ 40 * 2677799 * 2
def baseEnd_2677799 : Nat := 458332661043024610932511

theorem tailTrace_2677799 : CollatzResearch.WordTrace tailWord_2677799 prefixEnd_2677799 458332661043024610932511 := by
  unfold tailWord_2677799
  simp only [CollatzResearch.WordTrace]
  refine ⟨97667353225799029504276451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65111568817199353002850967 97667353225799029504276451)
  ·
    refine ⟨146501029838698544256414677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97667353225799029504276451 146501029838698544256414677)
    ·
      refine ⟨3433617886844497131009719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 146501029838698544256414677 3433617886844497131009719)
      ·
        refine ⟨5150426830266745696514579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3433617886844497131009719 5150426830266745696514579)
        ·
          refine ⟨7725640245400118544771869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5150426830266745696514579 7725640245400118544771869)
          ·
            refine ⟨2897115092025044454289451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7725640245400118544771869 2897115092025044454289451)
            ·
              refine ⟨4345672638037566681434177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2897115092025044454289451 4345672638037566681434177)
              ·
                refine ⟨3259254478528175011075633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4345672638037566681434177 3259254478528175011075633)
                ·
                  refine ⟨2444440858896131258306725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3259254478528175011075633 2444440858896131258306725)
                  ·
                    refine ⟨458332661043024610932511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2444440858896131258306725 458332661043024610932511)
                    ·
                      rfl

theorem cell23_2677799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_2677799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677799 prefixEnd_2677799 := by exact prefixLift 2677799
  have htrace : WordTrace (prefixWord ++ tailWord_2677799) baseStart_2677799 baseEnd_2677799 := by
    simpa [prefixWord, tailWord_2677799, baseEnd_2677799] using wordTrace_append hprefix tailTrace_2677799
  have hstable : (prefixWord ++ tailWord_2677799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677799).length < 2 ^ (prefixWord ++ tailWord_2677799).sum := by decide
  have hdescent : baseEnd_2677799 < baseStart_2677799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677822 : List Nat := [4, 2, 1, 3, 1, 1, 3, 1, 1, 3, 3]
def baseStart_2677822 : Nat := 118140960795 + 2677822 * 2 ^ 59
def prefixEnd_2677822 : Nat := 4983230072969 + 3 ^ 40 * 2677822 * 2
def baseEnd_2677822 : Nat := 1375009793184127242809927

theorem tailTrace_2677822 : CollatzResearch.WordTrace tailWord_2677822 prefixEnd_2677822 1375009793184127242809927 := by
  unfold tailWord_2677822
  simp only [CollatzResearch.WordTrace]
  refine ⟨12208524013089463054045465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65112128069810469621575813 12208524013089463054045465)
  ·
    refine ⟨9156393009817097290534099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12208524013089463054045465 9156393009817097290534099)
    ·
      refine ⟨13734589514725645935801149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9156393009817097290534099 13734589514725645935801149)
      ·
        refine ⟨5150471068022117225925431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13734589514725645935801149 5150471068022117225925431)
        ·
          refine ⟨7725706602033175838888147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5150471068022117225925431 7725706602033175838888147)
          ·
            refine ⟨11588559903049763758332221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7725706602033175838888147 11588559903049763758332221)
            ·
              refine ⟨4345709963643661409374583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11588559903049763758332221 4345709963643661409374583)
              ·
                refine ⟨6518564945465492114061875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4345709963643661409374583 6518564945465492114061875)
                ·
                  refine ⟨9777847418198238171092813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6518564945465492114061875 9777847418198238171092813)
                  ·
                    refine ⟨3666692781824339314159805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9777847418198238171092813 3666692781824339314159805)
                    ·
                      refine ⟨1375009793184127242809927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3666692781824339314159805 1375009793184127242809927)
                      ·
                        rfl

theorem cell23_2677822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_2677822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677822 prefixEnd_2677822 := by exact prefixLift 2677822
  have htrace : WordTrace (prefixWord ++ tailWord_2677822) baseStart_2677822 baseEnd_2677822 := by
    simpa [prefixWord, tailWord_2677822, baseEnd_2677822] using wordTrace_append hprefix tailTrace_2677822
  have hstable : (prefixWord ++ tailWord_2677822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677822).length < 2 ^ (prefixWord ++ tailWord_2677822).sum := by decide
  have hdescent : baseEnd_2677822 < baseStart_2677822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677832 : List Nat := [2, 1, 3, 1, 1, 1, 6, 2, 1, 3, 2]
def baseStart_2677832 : Nat := 118140960795 + 2677832 * 2 ^ 59
def prefixEnd_2677832 : Nat := 4983230072969 + 3 ^ 40 * 2677832 * 2
def baseEnd_2677832 : Nat := 1375014927990672203684881

theorem tailTrace_2677832 : CollatzResearch.WordTrace tailWord_2677832 prefixEnd_2677832 1375014927990672203684881 := by
  unfold tailWord_2677832
  simp only [CollatzResearch.WordTrace]
  refine ⟨48834278417339738070113875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65112371223119650760151833 48834278417339738070113875)
  ·
    refine ⟨73251417626009607105170813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48834278417339738070113875 73251417626009607105170813)
    ·
      refine ⟨27469281609753602664439055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73251417626009607105170813 27469281609753602664439055)
      ·
        refine ⟨41203922414630403996658583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27469281609753602664439055 41203922414630403996658583)
        ·
          refine ⟨61805883621945605994987875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41203922414630403996658583 61805883621945605994987875)
          ·
            refine ⟨92708825432918408992481813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61805883621945605994987875 92708825432918408992481813)
            ·
              refine ⟨4345726192168050421522585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 92708825432918408992481813 4345726192168050421522585)
              ·
                refine ⟨3259294644126037816141939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4345726192168050421522585 3259294644126037816141939)
                ·
                  refine ⟨4888941966189056724212909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3259294644126037816141939 4888941966189056724212909)
                  ·
                    refine ⟨1833353237320896271579841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4888941966189056724212909 1833353237320896271579841)
                    ·
                      refine ⟨1375014927990672203684881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1833353237320896271579841 1375014927990672203684881)
                      ·
                        rfl

theorem cell23_2677832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 2, 1, 3, 2].length) (baseStart_2677832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677832 prefixEnd_2677832 := by exact prefixLift 2677832
  have htrace : WordTrace (prefixWord ++ tailWord_2677832) baseStart_2677832 baseEnd_2677832 := by
    simpa [prefixWord, tailWord_2677832, baseEnd_2677832] using wordTrace_append hprefix tailTrace_2677832
  have hstable : (prefixWord ++ tailWord_2677832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677832).length < 2 ^ (prefixWord ++ tailWord_2677832).sum := by decide
  have hdescent : baseEnd_2677832 < baseStart_2677832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677845 : List Nat := [1, 3, 2, 2, 1, 2, 2, 1, 3, 4, 2]
def baseStart_2677845 : Nat := 118140960795 + 2677845 * 2 ^ 59
def prefixEnd_2677845 : Nat := 4983230072969 + 3 ^ 40 * 2677845 * 2
def baseEnd_2677845 : Nat := 1375021603239180652822321

theorem tailTrace_2677845 : CollatzResearch.WordTrace tailWord_2677845 prefixEnd_2677845 1375021603239180652822321 := by
  unfold tailWord_2677845
  simp only [CollatzResearch.WordTrace]
  refine ⟨97669030983632379360450989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65112687322421586240300659 97669030983632379360450989)
  ·
    refine ⟨36625886618862142260169121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97669030983632379360450989 36625886618862142260169121)
    ·
      refine ⟨27469414964146606695126841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36625886618862142260169121 27469414964146606695126841)
      ·
        refine ⟨20602061223109955021345131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27469414964146606695126841 20602061223109955021345131)
        ·
          refine ⟨30903091834664932532017697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20602061223109955021345131 30903091834664932532017697)
          ·
            refine ⟨23177318875998699399013273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30903091834664932532017697 23177318875998699399013273)
            ·
              refine ⟨17382989156999024549259955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23177318875998699399013273 17382989156999024549259955)
              ·
                refine ⟨26074483735498536823889933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17382989156999024549259955 26074483735498536823889933)
                ·
                  refine ⟨9777931400811951308958725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26074483735498536823889933 9777931400811951308958725)
                  ·
                    refine ⟨1833362137652240870429761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9777931400811951308958725 1833362137652240870429761)
                    ·
                      refine ⟨1375021603239180652822321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1833362137652240870429761 1375021603239180652822321)
                      ·
                        rfl

theorem cell23_2677845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 4, 2].length) (baseStart_2677845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677845 prefixEnd_2677845 := by exact prefixLift 2677845
  have htrace : WordTrace (prefixWord ++ tailWord_2677845) baseStart_2677845 baseEnd_2677845 := by
    simpa [prefixWord, tailWord_2677845, baseEnd_2677845] using wordTrace_append hprefix tailTrace_2677845
  have hstable : (prefixWord ++ tailWord_2677845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677845).length < 2 ^ (prefixWord ++ tailWord_2677845).sum := by decide
  have hdescent : baseEnd_2677845 < baseStart_2677845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677848 : List Nat := [2, 1, 2, 2, 1, 3, 3, 1, 2, 1, 5]
def baseStart_2677848 : Nat := 118140960795 + 2677848 * 2 ^ 59
def prefixEnd_2677848 : Nat := 4983230072969 + 3 ^ 40 * 2677848 * 2
def baseEnd_2677848 : Nat := 1375023143681144141084807

theorem tailTrace_2677848 : CollatzResearch.WordTrace tailWord_2677848 prefixEnd_2677848 1375023143681144141084807 := by
  unfold tailWord_2677848
  simp only [CollatzResearch.WordTrace]
  refine ⟨48834570201310755436405099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65112760268414340581873465 48834570201310755436405099)
  ·
    refine ⟨73251855301966133154607649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48834570201310755436405099 73251855301966133154607649)
    ·
      refine ⟨54938891476474599865955737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73251855301966133154607649 54938891476474599865955737)
      ·
        refine ⟨41204168607355949899466803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54938891476474599865955737 41204168607355949899466803)
        ·
          refine ⟨61806252911033924849200205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41204168607355949899466803 61806252911033924849200205)
          ·
            refine ⟨23177344841637721818450077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61806252911033924849200205 23177344841637721818450077)
            ·
              refine ⟨8691504315614145681918779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23177344841637721818450077 8691504315614145681918779)
              ·
                refine ⟨13037256473421218522878169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8691504315614145681918779 13037256473421218522878169)
                ·
                  refine ⟨9777942355065913892158627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13037256473421218522878169 9777942355065913892158627)
                  ·
                    refine ⟨14666913532598870838237941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9777942355065913892158627 14666913532598870838237941)
                    ·
                      refine ⟨1375023143681144141084807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14666913532598870838237941 1375023143681144141084807)
                      ·
                        rfl

theorem cell23_2677848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_2677848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677848 prefixEnd_2677848 := by exact prefixLift 2677848
  have htrace : WordTrace (prefixWord ++ tailWord_2677848) baseStart_2677848 baseEnd_2677848 := by
    simpa [prefixWord, tailWord_2677848, baseEnd_2677848] using wordTrace_append hprefix tailTrace_2677848
  have hstable : (prefixWord ++ tailWord_2677848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677848).length < 2 ^ (prefixWord ++ tailWord_2677848).sum := by decide
  have hdescent : baseEnd_2677848 < baseStart_2677848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677935 : List Nat := [1, 1, 2, 1, 2, 3, 3, 1, 1, 6, 2]
def baseStart_2677935 : Nat := 118140960795 + 2677935 * 2 ^ 59
def prefixEnd_2677935 : Nat := 4983230072969 + 3 ^ 40 * 2677935 * 2
def baseEnd_2677935 : Nat := 1375067816498085300696907

theorem tailTrace_2677935 : CollatzResearch.WordTrace tailWord_2677935 prefixEnd_2677935 1375067816498085300696907 := by
  unfold tailWord_2677935
  simp only [CollatzResearch.WordTrace]
  refine ⟨97672313553306324731227259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65114875702204216487484839 97672313553306324731227259)
  ·
    refine ⟨146508470329959487096840889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97672313553306324731227259 146508470329959487096840889)
    ·
      refine ⟨109881352747469615322630667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146508470329959487096840889 109881352747469615322630667)
      ·
        refine ⟨164822029121204422983946001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109881352747469615322630667 164822029121204422983946001)
        ·
          refine ⟨123616521840903317237959501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164822029121204422983946001 123616521840903317237959501)
          ·
            refine ⟨46356195690338743964234813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123616521840903317237959501 46356195690338743964234813)
            ·
              refine ⟨17383573383877028986588055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46356195690338743964234813 17383573383877028986588055)
              ·
                refine ⟨26075360075815543479882083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17383573383877028986588055 26075360075815543479882083)
                ·
                  refine ⟨39113040113723315219823125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26075360075815543479882083 39113040113723315219823125)
                  ·
                    refine ⟨1833423755330780400929209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 39113040113723315219823125 1833423755330780400929209)
                    ·
                      refine ⟨1375067816498085300696907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1833423755330780400929209 1375067816498085300696907)
                      ·
                        rfl

theorem cell23_2677935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 6, 2].length) (baseStart_2677935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677935 prefixEnd_2677935 := by exact prefixLift 2677935
  have htrace : WordTrace (prefixWord ++ tailWord_2677935) baseStart_2677935 baseEnd_2677935 := by
    simpa [prefixWord, tailWord_2677935, baseEnd_2677935] using wordTrace_append hprefix tailTrace_2677935
  have hstable : (prefixWord ++ tailWord_2677935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677935).length < 2 ^ (prefixWord ++ tailWord_2677935).sum := by decide
  have hdescent : baseEnd_2677935 < baseStart_2677935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677945 : List Nat := [1, 2, 1, 4, 1, 3, 1, 1, 5, 4]
def baseStart_2677945 : Nat := 118140960795 + 2677945 * 2 ^ 59
def prefixEnd_2677945 : Nat := 4983230072969 + 3 ^ 40 * 2677945 * 2
def baseEnd_2677945 : Nat := 458357650434876753857287

theorem tailTrace_2677945 : CollatzResearch.WordTrace tailWord_2677945 prefixEnd_2677945 458357650434876753857287 := by
  unfold tailWord_2677945
  simp only [CollatzResearch.WordTrace]
  refine ⟨97672678283270096439091289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65115118855513397626060859 97672678283270096439091289)
  ·
    refine ⟨73254508712452572329318467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97672678283270096439091289 73254508712452572329318467)
    ·
      refine ⟨109881763068678858493977701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73254508712452572329318467 109881763068678858493977701)
      ·
        refine ⟨20602830575377285967620819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109881763068678858493977701 20602830575377285967620819)
        ·
          refine ⟨30904245863065928951431229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20602830575377285967620819 30904245863065928951431229)
          ·
            refine ⟨11589092198649723356786711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30904245863065928951431229 11589092198649723356786711)
            ·
              refine ⟨17383638297974585035180067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11589092198649723356786711 17383638297974585035180067)
              ·
                refine ⟨26075457446961877552770101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17383638297974585035180067 26075457446961877552770101)
                ·
                  refine ⟨2444574135652676020572197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26075457446961877552770101 2444574135652676020572197)
                  ·
                    refine ⟨458357650434876753857287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2444574135652676020572197 458357650434876753857287)
                    ·
                      rfl

theorem cell23_2677945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 5, 4].length) (baseStart_2677945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677945 prefixEnd_2677945 := by exact prefixLift 2677945
  have htrace : WordTrace (prefixWord ++ tailWord_2677945) baseStart_2677945 baseEnd_2677945 := by
    simpa [prefixWord, tailWord_2677945, baseEnd_2677945] using wordTrace_append hprefix tailTrace_2677945
  have hstable : (prefixWord ++ tailWord_2677945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677945).length < 2 ^ (prefixWord ++ tailWord_2677945).sum := by decide
  have hdescent : baseEnd_2677945 < baseStart_2677945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677955 : List Nat := [1, 1, 1, 3, 1, 1, 1, 7, 2, 2, 3]
def baseStart_2677955 : Nat := 118140960795 + 2677955 * 2 ^ 59
def prefixEnd_2677955 : Nat := 4983230072969 + 3 ^ 40 * 2677955 * 2
def baseEnd_2677955 : Nat := 1375078086111175222446815

theorem tailTrace_2677955 : CollatzResearch.WordTrace tailWord_2677955 prefixEnd_2677955 1375078086111175222446815 := by
  unfold tailWord_2677955
  simp only [CollatzResearch.WordTrace]
  refine ⟨97673043013233868146955319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65115362008822578764636879 97673043013233868146955319)
  ·
    refine ⟨146509564519850802220432979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97673043013233868146955319 146509564519850802220432979)
    ·
      refine ⟨219764346779776203330649469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146509564519850802220432979 219764346779776203330649469)
      ·
        refine ⟨82411630042416076248993551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 219764346779776203330649469 82411630042416076248993551)
        ·
          refine ⟨123617445063624114373490327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82411630042416076248993551 123617445063624114373490327)
          ·
            refine ⟨185426167595436171560235491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123617445063624114373490327 185426167595436171560235491)
            ·
              refine ⟨278139251393154257340353237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185426167595436171560235491 278139251393154257340353237)
              ·
                refine ⟨6518888704527052906414529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 278139251393154257340353237 6518888704527052906414529)
                ·
                  refine ⟨4889166528395289679810897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6518888704527052906414529 4889166528395289679810897)
                  ·
                    refine ⟨3666874896296467259858173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4889166528395289679810897 3666874896296467259858173)
                    ·
                      refine ⟨1375078086111175222446815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3666874896296467259858173 1375078086111175222446815)
                      ·
                        rfl

theorem cell23_2677955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 2, 2, 3].length) (baseStart_2677955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677955 prefixEnd_2677955 := by exact prefixLift 2677955
  have htrace : WordTrace (prefixWord ++ tailWord_2677955) baseStart_2677955 baseEnd_2677955 := by
    simpa [prefixWord, tailWord_2677955, baseEnd_2677955] using wordTrace_append hprefix tailTrace_2677955
  have hstable : (prefixWord ++ tailWord_2677955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677955).length < 2 ^ (prefixWord ++ tailWord_2677955).sum := by decide
  have hdescent : baseEnd_2677955 < baseStart_2677955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677975 : List Nat := [1, 1, 3, 2, 1, 2, 5, 2, 6]
def baseStart_2677975 : Nat := 118140960795 + 2677975 * 2 ^ 59
def prefixEnd_2677975 : Nat := 4983230072969 + 3 ^ 40 * 2677975 * 2
def baseEnd_2677975 : Nat := 152787595080473904910747

theorem tailTrace_2677975 : CollatzResearch.WordTrace tailWord_2677975 prefixEnd_2677975 152787595080473904910747 := by
  unfold tailWord_2677975
  simp only [CollatzResearch.WordTrace]
  refine ⟨97673772473161411562683379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65115848315440941041788919 97673772473161411562683379)
  ·
    refine ⟨146510658709742117344025069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97673772473161411562683379 146510658709742117344025069)
    ·
      refine ⟨54941497016153294004009401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146510658709742117344025069 54941497016153294004009401)
      ·
        refine ⟨41206122762114970503007051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54941497016153294004009401 41206122762114970503007051)
        ·
          refine ⟨61809184143172455754510577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41206122762114970503007051 61809184143172455754510577)
          ·
            refine ⟨46356888107379341815882933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61809184143172455754510577 46356888107379341815882933)
            ·
              refine ⟨4345958260066813295239025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46356888107379341815882933 4345958260066813295239025)
              ·
                refine ⟨3259468695050109971429269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4345958260066813295239025 3259468695050109971429269)
                ·
                  refine ⟨152787595080473904910747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3259468695050109971429269 152787595080473904910747)
                  ·
                    rfl

theorem cell23_2677975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 2, 6].length) (baseStart_2677975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677975 prefixEnd_2677975 := by exact prefixLift 2677975
  have htrace : WordTrace (prefixWord ++ tailWord_2677975) baseStart_2677975 baseEnd_2677975 := by
    simpa [prefixWord, tailWord_2677975, baseEnd_2677975] using wordTrace_append hprefix tailTrace_2677975
  have hstable : (prefixWord ++ tailWord_2677975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677975).length < 2 ^ (prefixWord ++ tailWord_2677975).sum := by decide
  have hdescent : baseEnd_2677975 < baseStart_2677975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677992 : List Nat := [2, 1, 4, 1, 2, 1, 5, 1, 6]
def baseStart_2677992 : Nat := 118140960795 + 2677992 * 2 ^ 59
def prefixEnd_2677992 : Nat := 4983230072969 + 3 ^ 40 * 2677992 * 2
def baseEnd_2677992 : Nat := 152788564988376841964905

theorem tailTrace_2677992 : CollatzResearch.WordTrace tailWord_2677992 prefixEnd_2677992 152788564988376841964905 := by
  unfold tailWord_2677992
  simp only [CollatzResearch.WordTrace]
  refine ⟨48837196257049911733026115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65116261676066548977368153 48837196257049911733026115)
  ·
    refine ⟨73255794385574867599539173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48837196257049911733026115 73255794385574867599539173)
    ·
      refine ⟨13735461447295287674913595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73255794385574867599539173 13735461447295287674913595)
      ·
        refine ⟨20603192170942931512370393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13735461447295287674913595 20603192170942931512370393)
        ·
          refine ⟨15452394128207198634277795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20603192170942931512370393 15452394128207198634277795)
          ·
            refine ⟨23178591192310797951416693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15452394128207198634277795 23178591192310797951416693)
            ·
              refine ⟨2172992924279137307945315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23178591192310797951416693 2172992924279137307945315)
              ·
                refine ⟨3259489386418705961917973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2172992924279137307945315 3259489386418705961917973)
                ·
                  refine ⟨152788564988376841964905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3259489386418705961917973 152788564988376841964905)
                  ·
                    rfl

theorem cell23_2677992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 1, 6].length) (baseStart_2677992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677992 prefixEnd_2677992 := by exact prefixLift 2677992
  have htrace : WordTrace (prefixWord ++ tailWord_2677992) baseStart_2677992 baseEnd_2677992 := by
    simpa [prefixWord, tailWord_2677992, baseEnd_2677992] using wordTrace_append hprefix tailTrace_2677992
  have hstable : (prefixWord ++ tailWord_2677992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677992).length < 2 ^ (prefixWord ++ tailWord_2677992).sum := by decide
  have hdescent : baseEnd_2677992 < baseStart_2677992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678065 : List Nat := [1, 2, 2, 3, 3, 1, 2, 9]
def baseStart_2678065 : Nat := 118140960795 + 2678065 * 2 ^ 59
def prefixEnd_2678065 : Nat := 4983230072969 + 3 ^ 40 * 2678065 * 2
def baseEnd_2678065 : Nat := 50930909962339621928567

theorem tailTrace_2678065 : CollatzResearch.WordTrace tailWord_2678065 prefixEnd_2678065 50930909962339621928567 := by
  unfold tailWord_2678065
  simp only [CollatzResearch.WordTrace]
  refine ⟨97677055042835356933459649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65118036695223571288973099 97677055042835356933459649)
  ·
    refine ⟨73257791282126517700094737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97677055042835356933459649 73257791282126517700094737)
    ·
      refine ⟨54943343461594888275071053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73257791282126517700094737 54943343461594888275071053)
      ·
        refine ⟨20603753798098083103151645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54943343461594888275071053 20603753798098083103151645)
        ·
          refine ⟨7726407674286781163681867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20603753798098083103151645 7726407674286781163681867)
          ·
            refine ⟨11589611511430171745522801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7726407674286781163681867 11589611511430171745522801)
            ·
              refine ⟨8692208633572628809142101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11589611511430171745522801 8692208633572628809142101)
              ·
                refine ⟨50930909962339621928567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8692208633572628809142101 50930909962339621928567)
                ·
                  rfl

theorem cell23_2678065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 9].length) (baseStart_2678065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2678065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2678065 prefixEnd_2678065 := by exact prefixLift 2678065
  have htrace : WordTrace (prefixWord ++ tailWord_2678065) baseStart_2678065 baseEnd_2678065 := by
    simpa [prefixWord, tailWord_2678065, baseEnd_2678065] using wordTrace_append hprefix tailTrace_2678065
  have hstable : (prefixWord ++ tailWord_2678065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678065).length < 2 ^ (prefixWord ++ tailWord_2678065).sum := by decide
  have hdescent : baseEnd_2678065 < baseStart_2678065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678135 : List Nat := [1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 5]
def baseStart_2678135 : Nat := 118140960795 + 2678135 * 2 ^ 59
def prefixEnd_2678135 : Nat := 4983230072969 + 3 ^ 40 * 2678135 * 2
def baseEnd_2678135 : Nat := 1375170512628984518195987

theorem tailTrace_2678135 : CollatzResearch.WordTrace tailWord_2678135 prefixEnd_2678135 1375170512628984518195987 := by
  unfold tailWord_2678135
  simp only [CollatzResearch.WordTrace]
  refine ⟨97679608152581758888507859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65119738768387839259005239 97679608152581758888507859)
  ·
    refine ⟨146519412228872638332761789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97679608152581758888507859 146519412228872638332761789)
    ·
      refine ⟨54944779585827239374785671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146519412228872638332761789 54944779585827239374785671)
      ·
        refine ⟨82417169378740859062178507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54944779585827239374785671 82417169378740859062178507)
        ·
          refine ⟨123625754068111288593267761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82417169378740859062178507 123625754068111288593267761)
          ·
            refine ⟨92719315551083466444950821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123625754068111288593267761 92719315551083466444950821)
            ·
              refine ⟨17384871665828149958428279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92719315551083466444950821 17384871665828149958428279)
              ·
                refine ⟨26077307498742224937642419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17384871665828149958428279 26077307498742224937642419)
                ·
                  refine ⟨39115961248113337406463629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26077307498742224937642419 39115961248113337406463629)
                  ·
                    refine ⟨14668485468042501527423861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39115961248113337406463629 14668485468042501527423861)
                    ·
                      refine ⟨1375170512628984518195987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14668485468042501527423861 1375170512628984518195987)
                      ·
                        rfl

theorem cell23_2678135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_2678135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2678135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2678135 prefixEnd_2678135 := by exact prefixLift 2678135
  have htrace : WordTrace (prefixWord ++ tailWord_2678135) baseStart_2678135 baseEnd_2678135 := by
    simpa [prefixWord, tailWord_2678135, baseEnd_2678135] using wordTrace_append hprefix tailTrace_2678135
  have hstable : (prefixWord ++ tailWord_2678135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678135).length < 2 ^ (prefixWord ++ tailWord_2678135).sum := by decide
  have hdescent : baseEnd_2678135 < baseStart_2678135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678195 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 7]
def baseStart_2678195 : Nat := 118140960795 + 2678195 * 2 ^ 59
def prefixEnd_2678195 : Nat := 4983230072969 + 3 ^ 40 * 2678195 * 2
def baseEnd_2678195 : Nat := 1375201321468254283445711

theorem tailTrace_2678195 : CollatzResearch.WordTrace tailWord_2678195 prefixEnd_2678195 1375201321468254283445711 := by
  unfold tailWord_2678195
  simp only [CollatzResearch.WordTrace]
  refine ⟨97681796532364389135692039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65121197688242926090461359 97681796532364389135692039)
  ·
    refine ⟨146522694798546583703538059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97681796532364389135692039 146522694798546583703538059)
    ·
      refine ⟨219784042197819875555307089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146522694798546583703538059 219784042197819875555307089)
      ·
        refine ⟨164838031648364906666480317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219784042197819875555307089 164838031648364906666480317)
        ·
          refine ⟨61814261868136839999930119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164838031648364906666480317 61814261868136839999930119)
          ·
            refine ⟨92721392802205259999895179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61814261868136839999930119 92721392802205259999895179)
            ·
              refine ⟨139082089203307889999842769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92721392802205259999895179 139082089203307889999842769)
              ·
                refine ⟨104311566902480917499882077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139082089203307889999842769 104311566902480917499882077)
                ·
                  refine ⟨39116837588430344062455779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104311566902480917499882077 39116837588430344062455779)
                  ·
                    refine ⟨58675256382645516093683669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39116837588430344062455779 58675256382645516093683669)
                    ·
                      refine ⟨1375201321468254283445711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 58675256382645516093683669 1375201321468254283445711)
                      ·
                        rfl

theorem cell23_2678195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 7].length) (baseStart_2678195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2678195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2678195 prefixEnd_2678195 := by exact prefixLift 2678195
  have htrace : WordTrace (prefixWord ++ tailWord_2678195) baseStart_2678195 baseEnd_2678195 := by
    simpa [prefixWord, tailWord_2678195, baseEnd_2678195] using wordTrace_append hprefix tailTrace_2678195
  have hstable : (prefixWord ++ tailWord_2678195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678195).length < 2 ^ (prefixWord ++ tailWord_2678195).sum := by decide
  have hdescent : baseEnd_2678195 < baseStart_2678195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678222 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 3, 3, 4]
def baseStart_2678222 : Nat := 118140960795 + 2678222 * 2 ^ 59
def prefixEnd_2678222 : Nat := 4983230072969 + 3 ^ 40 * 2678222 * 2
def baseEnd_2678222 : Nat := 1375215185445925677808087

theorem tailTrace_2678222 : CollatzResearch.WordTrace tailWord_2678222 prefixEnd_2678222 1375215185445925677808087 := by
  unfold tailWord_2678222
  simp only [CollatzResearch.WordTrace]
  refine ⟨12210347662908321593365615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65121854202177715164616613 12210347662908321593365615)
  ·
    refine ⟨18315521494362482390048423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12210347662908321593365615 18315521494362482390048423)
    ·
      refine ⟨27473282241543723585072635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18315521494362482390048423 27473282241543723585072635)
      ·
        refine ⟨41209923362315585377608953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27473282241543723585072635 41209923362315585377608953)
        ·
          refine ⟨30907442521736689033206715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41209923362315585377608953 30907442521736689033206715)
          ·
            refine ⟨46361163782605033549810073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30907442521736689033206715 46361163782605033549810073)
            ·
              refine ⟨34770872836953775162357555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46361163782605033549810073 34770872836953775162357555)
              ·
                refine ⟨52156309255430662743536333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34770872836953775162357555 52156309255430662743536333)
                ·
                  refine ⟨19558615970786498528826125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52156309255430662743536333 19558615970786498528826125)
                  ·
                    refine ⟨7334480989044936948309797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19558615970786498528826125 7334480989044936948309797)
                    ·
                      refine ⟨1375215185445925677808087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7334480989044936948309797 1375215185445925677808087)
                      ·
                        rfl

theorem cell23_2678222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_2678222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2678222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2678222 prefixEnd_2678222 := by exact prefixLift 2678222
  have htrace : WordTrace (prefixWord ++ tailWord_2678222) baseStart_2678222 baseEnd_2678222 := by
    simpa [prefixWord, tailWord_2678222, baseEnd_2678222] using wordTrace_append hprefix tailTrace_2678222
  have hstable : (prefixWord ++ tailWord_2678222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678222).length < 2 ^ (prefixWord ++ tailWord_2678222).sum := by decide
  have hdescent : baseEnd_2678222 < baseStart_2678222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678239 : List Nat := [1, 1, 2, 3, 3, 1, 4, 1, 2, 1, 4]
def baseStart_2678239 : Nat := 118140960795 + 2678239 * 2 ^ 59
def prefixEnd_2678239 : Nat := 4983230072969 + 3 ^ 40 * 2678239 * 2
def baseEnd_2678239 : Nat := 1375223914617052111295509

theorem tailTrace_2678239 : CollatzResearch.WordTrace tailWord_2678239 prefixEnd_2678239 1375223914617052111295509 := by
  unfold tailWord_2678239
  simp only [CollatzResearch.WordTrace]
  refine ⟨97683401344204984650293771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65122267562803323100195847 97683401344204984650293771)
  ·
    refine ⟨146525102016307476975440657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97683401344204984650293771 146525102016307476975440657)
    ·
      refine ⟨109893826512230607731580493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146525102016307476975440657 109893826512230607731580493)
      ·
        refine ⟨41210184942086477899342685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109893826512230607731580493 41210184942086477899342685)
        ·
          refine ⟨15453819353282429212253507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41210184942086477899342685 15453819353282429212253507)
          ·
            refine ⟨23180729029923643818380261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15453819353282429212253507 23180729029923643818380261)
            ·
              refine ⟨4346386693110683215946299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23180729029923643818380261 4346386693110683215946299)
              ·
                refine ⟨6519580039666024823919449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4346386693110683215946299 6519580039666024823919449)
                ·
                  refine ⟨4889685029749518617939587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6519580039666024823919449 4889685029749518617939587)
                  ·
                    refine ⟨7334527544624277926909381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4889685029749518617939587 7334527544624277926909381)
                    ·
                      refine ⟨1375223914617052111295509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7334527544624277926909381 1375223914617052111295509)
                      ·
                        rfl

theorem cell23_2678239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 2, 1, 4].length) (baseStart_2678239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2678239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2678239 prefixEnd_2678239 := by exact prefixLift 2678239
  have htrace : WordTrace (prefixWord ++ tailWord_2678239) baseStart_2678239 baseEnd_2678239 := by
    simpa [prefixWord, tailWord_2678239, baseEnd_2678239] using wordTrace_append hprefix tailTrace_2678239
  have hstable : (prefixWord ++ tailWord_2678239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678239).length < 2 ^ (prefixWord ++ tailWord_2678239).sum := by decide
  have hdescent : baseEnd_2678239 < baseStart_2678239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678266 : List Nat := [3, 1, 1, 1, 1, 2, 5, 4, 1, 4]
def baseStart_2678266 : Nat := 118140960795 + 2678266 * 2 ^ 59
def prefixEnd_2678266 : Nat := 4983230072969 + 3 ^ 40 * 2678266 * 2
def baseEnd_2678266 : Nat := 458412592864907835219295

theorem tailTrace_2678266 : CollatzResearch.WordTrace tailWord_2678266 prefixEnd_2678266 458412592864907835219295 := by
  unfold tailWord_2678266
  simp only [CollatzResearch.WordTrace]
  refine ⟨24421096528776792065381663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65122924076738112174351101 24421096528776792065381663)
  ·
    refine ⟨36631644793165188098072495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24421096528776792065381663 36631644793165188098072495)
    ·
      refine ⟨54947467189747782147108743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36631644793165188098072495 54947467189747782147108743)
      ·
        refine ⟨82421200784621673220663115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54947467189747782147108743 82421200784621673220663115)
        ·
          refine ⟨123631801176932509830994673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82421200784621673220663115 123631801176932509830994673)
          ·
            refine ⟨92723850882699382373246005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123631801176932509830994673 92723850882699382373246005)
            ·
              refine ⟨8692861020253067097491813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92723850882699382373246005 8692861020253067097491813)
              ·
                refine ⟨1629911441297450080779715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8692861020253067097491813 1629911441297450080779715)
                ·
                  refine ⟨2444867161946175121169573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1629911441297450080779715 2444867161946175121169573)
                  ·
                    refine ⟨458412592864907835219295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2444867161946175121169573 458412592864907835219295)
                    ·
                      rfl

theorem cell23_2678266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 4, 1, 4].length) (baseStart_2678266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2678266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2678266 prefixEnd_2678266 := by exact prefixLift 2678266
  have htrace : WordTrace (prefixWord ++ tailWord_2678266) baseStart_2678266 baseEnd_2678266 := by
    simpa [prefixWord, tailWord_2678266, baseEnd_2678266] using wordTrace_append hprefix tailTrace_2678266
  have hstable : (prefixWord ++ tailWord_2678266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678266).length < 2 ^ (prefixWord ++ tailWord_2678266).sum := by decide
  have hdescent : baseEnd_2678266 < baseStart_2678266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678279 : List Nat := [1, 1, 4, 3, 2, 1, 2, 3, 6]
def baseStart_2678279 : Nat := 118140960795 + 2678279 * 2 ^ 59
def prefixEnd_2678279 : Nat := 4983230072969 + 3 ^ 40 * 2678279 * 2
def baseEnd_2678279 : Nat := 152804939315914661643925

theorem tailTrace_2678279 : CollatzResearch.WordTrace tailWord_2678279 prefixEnd_2678279 152804939315914661643925 := by
  unfold tailWord_2678279
  simp only [CollatzResearch.WordTrace]
  refine ⟨97684860264060071481749891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65123240176040047654499927 97684860264060071481749891)
  ·
    refine ⟨146527290396090107222624837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97684860264060071481749891 146527290396090107222624837)
    ·
      refine ⟨27473866949266895104242157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146527290396090107222624837 27473866949266895104242157)
      ·
        refine ⟨10302700105975085664090809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27473866949266895104242157 10302700105975085664090809)
        ·
          refine ⟨7727025079481314248068107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10302700105975085664090809 7727025079481314248068107)
          ·
            refine ⟨11590537619221971372102161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7727025079481314248068107 11590537619221971372102161)
            ·
              refine ⟨8692903214416478529076621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11590537619221971372102161 8692903214416478529076621)
              ·
                refine ⟨3259838705406179448403733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8692903214416478529076621 3259838705406179448403733)
                ·
                  refine ⟨152804939315914661643925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3259838705406179448403733 152804939315914661643925)
                  ·
                    rfl

theorem cell23_2678279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 3, 6].length) (baseStart_2678279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2678279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2678279 prefixEnd_2678279 := by exact prefixLift 2678279
  have htrace : WordTrace (prefixWord ++ tailWord_2678279) baseStart_2678279 baseEnd_2678279 := by
    simpa [prefixWord, tailWord_2678279, baseEnd_2678279] using wordTrace_append hprefix tailTrace_2678279
  have hstable : (prefixWord ++ tailWord_2678279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678279).length < 2 ^ (prefixWord ++ tailWord_2678279).sum := by decide
  have hdescent : baseEnd_2678279 < baseStart_2678279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678323 : List Nat := [1, 1, 1, 2, 4, 3, 2, 4, 1, 1, 3]
def baseStart_2678323 : Nat := 118140960795 + 2678323 * 2 ^ 59
def prefixEnd_2678323 : Nat := 4983230072969 + 3 ^ 40 * 2678323 * 2
def baseEnd_2678323 : Nat := 1375267046992029782645123

theorem tailTrace_2678323 : CollatzResearch.WordTrace tailWord_2678323 prefixEnd_2678323 1375267046992029782645123 := by
  unfold tailWord_2678323
  simp only [CollatzResearch.WordTrace]
  refine ⟨97686465075900666996351623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65124310050600444664234415 97686465075900666996351623)
  ·
    refine ⟨146529697613851000494527435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97686465075900666996351623 146529697613851000494527435)
    ·
      refine ⟨219794546420776500741791153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146529697613851000494527435 219794546420776500741791153)
      ·
        refine ⟨164845909815582375556343365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219794546420776500741791153 164845909815582375556343365)
        ·
          refine ⟨30908608090421695416814381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 164845909815582375556343365 30908608090421695416814381)
          ·
            refine ⟨11590728033908135781305393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30908608090421695416814381 11590728033908135781305393)
            ·
              refine ⟨8693046025431101835979045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11590728033908135781305393 8693046025431101835979045)
              ·
                refine ⟨1629946129768331594246071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8693046025431101835979045 1629946129768331594246071)
                ·
                  refine ⟨2444919194652497391369107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1629946129768331594246071 2444919194652497391369107)
                  ·
                    refine ⟨3667378791978746087053661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2444919194652497391369107 3667378791978746087053661)
                    ·
                      refine ⟨1375267046992029782645123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3667378791978746087053661 1375267046992029782645123)
                      ·
                        rfl

theorem cell23_2678323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 4, 1, 1, 3].length) (baseStart_2678323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2678323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2678323 prefixEnd_2678323 := by exact prefixLift 2678323
  have htrace : WordTrace (prefixWord ++ tailWord_2678323) baseStart_2678323 baseEnd_2678323 := by
    simpa [prefixWord, tailWord_2678323, baseEnd_2678323] using wordTrace_append hprefix tailTrace_2678323
  have hstable : (prefixWord ++ tailWord_2678323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678323).length < 2 ^ (prefixWord ++ tailWord_2678323).sum := by decide
  have hdescent : baseEnd_2678323 < baseStart_2678323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678346 : List Nat := [3, 1, 2, 1, 1, 3, 4, 2, 1, 1, 4]
def baseStart_2678346 : Nat := 118140960795 + 2678346 * 2 ^ 59
def prefixEnd_2678346 : Nat := 4983230072969 + 3 ^ 40 * 2678346 * 2
def baseEnd_2678346 : Nat := 1375278857047083192657517

theorem tailTrace_2678346 : CollatzResearch.WordTrace tailWord_2678346 prefixEnd_2678346 1375278857047083192657517 := by
  unfold tailWord_2678346
  simp only [CollatzResearch.WordTrace]
  refine ⟨24421825988704335481109723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65124869303211561282959261 24421825988704335481109723)
  ·
    refine ⟨36632738983056503221664585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24421825988704335481109723 36632738983056503221664585)
    ·
      refine ⟨27474554237292377416248439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36632738983056503221664585 27474554237292377416248439)
      ·
        refine ⟨41211831355938566124372659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27474554237292377416248439 41211831355938566124372659)
        ·
          refine ⟨61817747033907849186558989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41211831355938566124372659 61817747033907849186558989)
          ·
            refine ⟨23181655137715443444959621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61817747033907849186558989 23181655137715443444959621)
            ·
              refine ⟨4346560338321645645929929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23181655137715443444959621 4346560338321645645929929)
              ·
                refine ⟨3259920253741234234447447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4346560338321645645929929 3259920253741234234447447)
                ·
                  refine ⟨4889880380611851351671171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3259920253741234234447447 4889880380611851351671171)
                  ·
                    refine ⟨7334820570917777027506757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4889880380611851351671171 7334820570917777027506757)
                    ·
                      refine ⟨1375278857047083192657517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7334820570917777027506757 1375278857047083192657517)
                      ·
                        rfl

theorem cell23_2678346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 2, 1, 1, 4].length) (baseStart_2678346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2678346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2678346 prefixEnd_2678346 := by exact prefixLift 2678346
  have htrace : WordTrace (prefixWord ++ tailWord_2678346) baseStart_2678346 baseEnd_2678346 := by
    simpa [prefixWord, tailWord_2678346, baseEnd_2678346] using wordTrace_append hprefix tailTrace_2678346
  have hstable : (prefixWord ++ tailWord_2678346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678346).length < 2 ^ (prefixWord ++ tailWord_2678346).sum := by decide
  have hdescent : baseEnd_2678346 < baseStart_2678346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678352 : List Nat := [2, 1, 1, 1, 1, 3, 5, 9]
def baseStart_2678352 : Nat := 118140960795 + 2678352 * 2 ^ 59
def prefixEnd_2678352 : Nat := 4983230072969 + 3 ^ 40 * 2678352 * 2
def baseEnd_2678352 : Nat := 50936368071518895154907

theorem tailTrace_2678352 : CollatzResearch.WordTrace tailWord_2678352 prefixEnd_2678352 50936368071518895154907 := by
  unfold tailWord_2678352
  simp only [CollatzResearch.WordTrace]
  refine ⟨48843761396397802474578655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65125015195197069966104873 48843761396397802474578655)
  ·
    refine ⟨73265642094596703711867983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48843761396397802474578655 73265642094596703711867983)
    ·
      refine ⟨109898463141895055567801975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73265642094596703711867983 109898463141895055567801975)
      ·
        refine ⟨164847694712842583351702963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109898463141895055567801975 164847694712842583351702963)
        ·
          refine ⟨247271542069263875027554445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164847694712842583351702963 247271542069263875027554445)
          ·
            refine ⟨92726828275973953135332917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 247271542069263875027554445 92726828275973953135332917)
            ·
              refine ⟨8693140150872558106437461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92726828275973953135332917 8693140150872558106437461)
              ·
                refine ⟨50936368071518895154907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8693140150872558106437461 50936368071518895154907)
                ·
                  rfl

theorem cell23_2678352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 9].length) (baseStart_2678352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2678352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2678352 prefixEnd_2678352 := by exact prefixLift 2678352
  have htrace : WordTrace (prefixWord ++ tailWord_2678352) baseStart_2678352 baseEnd_2678352 := by
    simpa [prefixWord, tailWord_2678352, baseEnd_2678352] using wordTrace_append hprefix tailTrace_2678352
  have hstable : (prefixWord ++ tailWord_2678352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678352).length < 2 ^ (prefixWord ++ tailWord_2678352).sum := by decide
  have hdescent : baseEnd_2678352 < baseStart_2678352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678390 : List Nat := [5, 1, 1, 2, 2, 1, 4, 1, 2, 4]
def baseStart_2678390 : Nat := 118140960795 + 2678390 * 2 ^ 59
def prefixEnd_2678390 : Nat := 4983230072969 + 3 ^ 40 * 2678390 * 2
def baseEnd_2678390 : Nat := 458433816731960340169105

theorem tailTrace_2678390 : CollatzResearch.WordTrace tailWord_2678390 prefixEnd_2678390 458433816731960340169105 := by
  unfold tailWord_2678390
  simp only [CollatzResearch.WordTrace]
  refine ⟨6105556797916121089940039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65125939177771958292693749 6105556797916121089940039)
  ·
    refine ⟨9158335196874181634910059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6105556797916121089940039 9158335196874181634910059)
    ·
      refine ⟨13737502795311272452365089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9158335196874181634910059 13737502795311272452365089)
      ·
        refine ⟨10303127096483454339273817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13737502795311272452365089 10303127096483454339273817)
        ·
          refine ⟨7727345322362590754455363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10303127096483454339273817 7727345322362590754455363)
          ·
            refine ⟨11591017983543886131683045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7727345322362590754455363 11591017983543886131683045)
            ·
              refine ⟨2173315871914478649690571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11591017983543886131683045 2173315871914478649690571)
              ·
                refine ⟨3259973807871717974535857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2173315871914478649690571 3259973807871717974535857)
                ·
                  refine ⟨2444980355903788480901893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3259973807871717974535857 2444980355903788480901893)
                  ·
                    refine ⟨458433816731960340169105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2444980355903788480901893 458433816731960340169105)
                    ·
                      rfl

theorem cell23_2678390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_2678390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2678390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2678390 prefixEnd_2678390 := by exact prefixLift 2678390
  have htrace : WordTrace (prefixWord ++ tailWord_2678390) baseStart_2678390 baseEnd_2678390 := by
    simpa [prefixWord, tailWord_2678390, baseEnd_2678390] using wordTrace_append hprefix tailTrace_2678390
  have hstable : (prefixWord ++ tailWord_2678390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678390).length < 2 ^ (prefixWord ++ tailWord_2678390).sum := by decide
  have hdescent : baseEnd_2678390 < baseStart_2678390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678429 : List Nat := [1, 4, 2, 1, 1, 1, 1, 4, 2, 6]
def baseStart_2678429 : Nat := 118140960795 + 2678429 * 2 ^ 59
def prefixEnd_2678429 : Nat := 4983230072969 + 3 ^ 40 * 2678429 * 2
def baseEnd_2678429 : Nat := 458440491980468789306545

theorem tailTrace_2678429 : CollatzResearch.WordTrace tailWord_2678429 prefixEnd_2678429 458440491980468789306545 := by
  unfold tailWord_2678429
  simp only [CollatzResearch.WordTrace]
  refine ⟨97690331213516647099710341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65126887475677764733140227 97690331213516647099710341)
  ·
    refine ⟨18316937102534371331195689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97690331213516647099710341 18316937102534371331195689)
    ·
      refine ⟨13737702826900778498396767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18316937102534371331195689 13737702826900778498396767)
      ·
        refine ⟨20606554240351167747595151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13737702826900778498396767 20606554240351167747595151)
        ·
          refine ⟨30909831360526751621392727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20606554240351167747595151 30909831360526751621392727)
          ·
            refine ⟨46364747040790127432089091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30909831360526751621392727 46364747040790127432089091)
            ·
              refine ⟨69547120561185191148133637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46364747040790127432089091 69547120561185191148133637)
              ·
                refine ⟨13040085105222223340275057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69547120561185191148133637 13040085105222223340275057)
                ·
                  refine ⟨9780063828916667505206293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13040085105222223340275057 9780063828916667505206293)
                  ·
                    refine ⟨458440491980468789306545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9780063828916667505206293 458440491980468789306545)
                    ·
                      rfl

theorem cell23_2678429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_2678429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2678429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2678429 prefixEnd_2678429 := by exact prefixLift 2678429
  have htrace : WordTrace (prefixWord ++ tailWord_2678429) baseStart_2678429 baseEnd_2678429 := by
    simpa [prefixWord, tailWord_2678429, baseEnd_2678429] using wordTrace_append hprefix tailTrace_2678429
  have hstable : (prefixWord ++ tailWord_2678429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678429).length < 2 ^ (prefixWord ++ tailWord_2678429).sum := by decide
  have hdescent : baseEnd_2678429 < baseStart_2678429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678430 : List Nat := [4, 3, 1, 1, 1, 2, 1, 4, 2, 1, 3]
def baseStart_2678430 : Nat := 118140960795 + 2678430 * 2 ^ 59
def prefixEnd_2678430 : Nat := 4983230072969 + 3 ^ 40 * 2678430 * 2
def baseEnd_2678430 : Nat := 1375321989422060864007131

theorem tailTrace_2678430 : CollatzResearch.WordTrace tailWord_2678430 prefixEnd_2678430 1375321989422060864007131 := by
  unfold tailWord_2678430
  simp only [CollatzResearch.WordTrace]
  refine ⟨12211295960814128033812093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65126911791008682846997829 12211295960814128033812093)
  ·
    refine ⟨4579235985305298012679535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12211295960814128033812093 4579235985305298012679535)
    ·
      refine ⟨6868853977957947019019303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4579235985305298012679535 6868853977957947019019303)
      ·
        refine ⟨10303280966936920528528955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6868853977957947019019303 10303280966936920528528955)
        ·
          refine ⟨15454921450405380792793433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10303280966936920528528955 15454921450405380792793433)
          ·
            refine ⟨11591191087804035594595075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15454921450405380792793433 11591191087804035594595075)
            ·
              refine ⟨17386786631706053391892613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11591191087804035594595075 17386786631706053391892613)
              ·
                refine ⟨3260022493444885010979865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17386786631706053391892613 3260022493444885010979865)
                ·
                  refine ⟨2445016870083663758234899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3260022493444885010979865 2445016870083663758234899)
                  ·
                    refine ⟨3667525305125495637352349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2445016870083663758234899 3667525305125495637352349)
                    ·
                      refine ⟨1375321989422060864007131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3667525305125495637352349 1375321989422060864007131)
                      ·
                        rfl

theorem cell23_2678430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_2678430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2678430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2678430 prefixEnd_2678430 := by exact prefixLift 2678430
  have htrace : WordTrace (prefixWord ++ tailWord_2678430) baseStart_2678430 baseEnd_2678430 := by
    simpa [prefixWord, tailWord_2678430, baseEnd_2678430] using wordTrace_append hprefix tailTrace_2678430
  have hstable : (prefixWord ++ tailWord_2678430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678430).length < 2 ^ (prefixWord ++ tailWord_2678430).sum := by decide
  have hdescent : baseEnd_2678430 < baseStart_2678430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678431 : List Nat := [1, 1, 2, 7, 1, 2, 2, 2, 1, 2, 2]
def baseStart_2678431 : Nat := 118140960795 + 2678431 * 2 ^ 59
def prefixEnd_2678431 : Nat := 4983230072969 + 3 ^ 40 * 2678431 * 2
def baseEnd_2678431 : Nat := 1375322502902715360094627

theorem tailTrace_2678431 : CollatzResearch.WordTrace tailWord_2678431 prefixEnd_2678431 1375322502902715360094627 := by
  unfold tailWord_2678431
  simp only [CollatzResearch.WordTrace]
  refine ⟨97690404159509401441283147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65126936106339600960855431 97690404159509401441283147)
  ·
    refine ⟨146535606239264102161924721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97690404159509401441283147 146535606239264102161924721)
    ·
      refine ⟨109901704679448076621443541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146535606239264102161924721 109901704679448076621443541)
      ·
        refine ⟨2575821203424564295815083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 109901704679448076621443541 2575821203424564295815083)
        ·
          refine ⟨3863731805136846443722625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2575821203424564295815083 3863731805136846443722625)
          ·
            refine ⟨2897798853852634832791969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3863731805136846443722625 2897798853852634832791969)
            ·
              refine ⟨2173349140389476124593977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2897798853852634832791969 2173349140389476124593977)
              ·
                refine ⟨1630011855292107093445483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2173349140389476124593977 1630011855292107093445483)
                ·
                  refine ⟨2445017782938160640168225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1630011855292107093445483 2445017782938160640168225)
                  ·
                    refine ⟨1833763337203620480126169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2445017782938160640168225 1833763337203620480126169)
                    ·
                      refine ⟨1375322502902715360094627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1833763337203620480126169 1375322502902715360094627)
                      ·
                        rfl

theorem cell23_2678431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_2678431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2678431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2678431 prefixEnd_2678431 := by exact prefixLift 2678431
  have htrace : WordTrace (prefixWord ++ tailWord_2678431) baseStart_2678431 baseEnd_2678431 := by
    simpa [prefixWord, tailWord_2678431, baseEnd_2678431] using wordTrace_append hprefix tailTrace_2678431
  have hstable : (prefixWord ++ tailWord_2678431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678431).length < 2 ^ (prefixWord ++ tailWord_2678431).sum := by decide
  have hdescent : baseEnd_2678431 < baseStart_2678431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678474 : List Nat := [3, 1, 2, 1, 6, 1, 2, 1, 1, 3, 2]
def baseStart_2678474 : Nat := 118140960795 + 2678474 * 2 ^ 59
def prefixEnd_2678474 : Nat := 4983230072969 + 3 ^ 40 * 2678474 * 2
def baseEnd_2678474 : Nat := 1375344582570858691856929

theorem tailTrace_2678474 : CollatzResearch.WordTrace tailWord_2678474 prefixEnd_2678474 1375344582570858691856929 := by
  unfold tailWord_2678474
  simp only [CollatzResearch.WordTrace]
  refine ⟨24422993124588404946274619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65127981665569079856732317 24422993124588404946274619)
  ·
    refine ⟨36634489686882607419411929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24422993124588404946274619 36634489686882607419411929)
    ·
      refine ⟨27475867265161955564558947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36634489686882607419411929 27475867265161955564558947)
      ·
        refine ⟨41213800897742933346838421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27475867265161955564558947 41213800897742933346838421)
        ·
          refine ⟨1931896917081700000633051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 41213800897742933346838421 1931896917081700000633051)
          ·
            refine ⟨2897845375622550000949577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1931896917081700000633051 2897845375622550000949577)
            ·
              refine ⟨2173384031716912500712183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2897845375622550000949577 2173384031716912500712183)
              ·
                refine ⟨3260076047575368751068275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2173384031716912500712183 3260076047575368751068275)
                ·
                  refine ⟨4890114071363053126602413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3260076047575368751068275 4890114071363053126602413)
                  ·
                    refine ⟨1833792776761144922475905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4890114071363053126602413 1833792776761144922475905)
                    ·
                      refine ⟨1375344582570858691856929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1833792776761144922475905 1375344582570858691856929)
                      ·
                        rfl

theorem cell23_2678474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 1, 1, 3, 2].length) (baseStart_2678474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2678474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2678474 prefixEnd_2678474 := by exact prefixLift 2678474
  have htrace : WordTrace (prefixWord ++ tailWord_2678474) baseStart_2678474 baseEnd_2678474 := by
    simpa [prefixWord, tailWord_2678474, baseEnd_2678474] using wordTrace_append hprefix tailTrace_2678474
  have hstable : (prefixWord ++ tailWord_2678474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678474).length < 2 ^ (prefixWord ++ tailWord_2678474).sum := by decide
  have hdescent : baseEnd_2678474 < baseStart_2678474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678496 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 1, 7, 2]
def baseStart_2678496 : Nat := 118140960795 + 2678496 * 2 ^ 59
def prefixEnd_2678496 : Nat := 4983230072969 + 3 ^ 40 * 2678496 * 2
def baseEnd_2678496 : Nat := 1375355879145257605781827

theorem tailTrace_2678496 : CollatzResearch.WordTrace tailWord_2678496 prefixEnd_2678496 1375355879145257605781827 := by
  unfold tailWord_2678496
  simp only [CollatzResearch.WordTrace]
  refine ⟨48846387452136958771199671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65128516602849278361599561 48846387452136958771199671)
  ·
    refine ⟨73269581178205438156799507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48846387452136958771199671 73269581178205438156799507)
    ·
      refine ⟨109904371767308157235199261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73269581178205438156799507 109904371767308157235199261)
      ·
        refine ⟨41214139412740558963199723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109904371767308157235199261 41214139412740558963199723)
        ·
          refine ⟨61821209119110838444799585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41214139412740558963199723 61821209119110838444799585)
          ·
            refine ⟨46365906839333128833599689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61821209119110838444799585 46365906839333128833599689)
            ·
              refine ⟨34774430129499846625199767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46365906839333128833599689 34774430129499846625199767)
              ·
                refine ⟨52161645194249769937799651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34774430129499846625199767 52161645194249769937799651)
                ·
                  refine ⟨78242467791374654906699477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52161645194249769937799651 78242467791374654906699477)
                  ·
                    refine ⟨1833807838860343474375769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 78242467791374654906699477 1833807838860343474375769)
                    ·
                      refine ⟨1375355879145257605781827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1833807838860343474375769 1375355879145257605781827)
                      ·
                        rfl

theorem cell23_2678496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 1, 7, 2].length) (baseStart_2678496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2678496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2678496 prefixEnd_2678496 := by exact prefixLift 2678496
  have htrace : WordTrace (prefixWord ++ tailWord_2678496) baseStart_2678496 baseEnd_2678496 := by
    simpa [prefixWord, tailWord_2678496, baseEnd_2678496] using wordTrace_append hprefix tailTrace_2678496
  have hstable : (prefixWord ++ tailWord_2678496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678496).length < 2 ^ (prefixWord ++ tailWord_2678496).sum := by decide
  have hdescent : baseEnd_2678496 < baseStart_2678496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678539 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 6]
def baseStart_2678539 : Nat := 118140960795 + 2678539 * 2 ^ 59
def prefixEnd_2678539 : Nat := 4983230072969 + 3 ^ 40 * 2678539 * 2
def baseEnd_2678539 : Nat := 1375377958813400937544129

theorem tailTrace_2678539 : CollatzResearch.WordTrace tailWord_2678539 prefixEnd_2678539 1375377958813400937544129 := by
  unfold tailWord_2678539
  simp only [CollatzResearch.WordTrace]
  refine ⟨97694343243118135886214671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65129562162078757257476447 97694343243118135886214671)
  ·
    refine ⟨146541514864677203829322007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97694343243118135886214671 146541514864677203829322007)
    ·
      refine ⟨219812272297015805743983011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146541514864677203829322007 219812272297015805743983011)
      ·
        refine ⟨329718408445523708615974517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219812272297015805743983011 329718408445523708615974517)
        ·
          refine ⟨30911100791767847682747611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 329718408445523708615974517 30911100791767847682747611)
          ·
            refine ⟨46366651187651771524121417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30911100791767847682747611 46366651187651771524121417)
            ·
              refine ⟨34774988390738828643091063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46366651187651771524121417 34774988390738828643091063)
              ·
                refine ⟨52162482586108242964636595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34774988390738828643091063 52162482586108242964636595)
                ·
                  refine ⟨78243723879162364446954893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52162482586108242964636595 78243723879162364446954893)
                  ·
                    refine ⟨29341396454685886667608085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 78243723879162364446954893 29341396454685886667608085)
                    ·
                      refine ⟨1375377958813400937544129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29341396454685886667608085 1375377958813400937544129)
                      ·
                        rfl

theorem cell23_2678539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 6].length) (baseStart_2678539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2678539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2678539 prefixEnd_2678539 := by exact prefixLift 2678539
  have htrace : WordTrace (prefixWord ++ tailWord_2678539) baseStart_2678539 baseEnd_2678539 := by
    simpa [prefixWord, tailWord_2678539, baseEnd_2678539] using wordTrace_append hprefix tailTrace_2678539
  have hstable : (prefixWord ++ tailWord_2678539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678539).length < 2 ^ (prefixWord ++ tailWord_2678539).sum := by decide
  have hdescent : baseEnd_2678539 < baseStart_2678539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678580 : List Nat := [2, 5, 1, 1, 2, 1, 1, 3, 2, 2, 3]
def baseStart_2678580 : Nat := 118140960795 + 2678580 * 2 ^ 59
def prefixEnd_2678580 : Nat := 4983230072969 + 3 ^ 40 * 2678580 * 2
def baseEnd_2678580 : Nat := 1375399011520235277131441

theorem tailTrace_2678580 : CollatzResearch.WordTrace tailWord_2678580 prefixEnd_2678580 1375399011520235277131441 := by
  unfold tailWord_2678580
  simp only [CollatzResearch.WordTrace]
  refine ⟨48847919317984799944228597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65130559090646399925638129 48847919317984799944228597)
  ·
    refine ⟨4579492436061074994771431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48847919317984799944228597 4579492436061074994771431)
    ·
      refine ⟨6869238654091612492157147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4579492436061074994771431 6869238654091612492157147)
      ·
        refine ⟨10303857981137418738235721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6869238654091612492157147 10303857981137418738235721)
        ·
          refine ⟨7727893485853064053676791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10303857981137418738235721 7727893485853064053676791)
          ·
            refine ⟨11591840228779596080515187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7727893485853064053676791 11591840228779596080515187)
            ·
              refine ⟨17387760343169394120772781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11591840228779596080515187 17387760343169394120772781)
              ·
                refine ⟨6520410128688522795289793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17387760343169394120772781 6520410128688522795289793)
                ·
                  refine ⟨4890307596516392096467345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6520410128688522795289793 4890307596516392096467345)
                  ·
                    refine ⟨3667730697387294072350509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4890307596516392096467345 3667730697387294072350509)
                    ·
                      refine ⟨1375399011520235277131441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3667730697387294072350509 1375399011520235277131441)
                      ·
                        rfl

theorem cell23_2678580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_2678580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2678580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2678580 prefixEnd_2678580 := by exact prefixLift 2678580
  have htrace : WordTrace (prefixWord ++ tailWord_2678580) baseStart_2678580 baseEnd_2678580 := by
    simpa [prefixWord, tailWord_2678580, baseEnd_2678580] using wordTrace_append hprefix tailTrace_2678580
  have hstable : (prefixWord ++ tailWord_2678580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678580).length < 2 ^ (prefixWord ++ tailWord_2678580).sum := by decide
  have hdescent : baseEnd_2678580 < baseStart_2678580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678604 : List Nat := [2, 2, 1, 3, 4, 2, 2, 2, 1, 4]
def baseStart_2678604 : Nat := 118140960795 + 2678604 * 2 ^ 59
def prefixEnd_2678604 : Nat := 4983230072969 + 3 ^ 40 * 2678604 * 2
def baseEnd_2678604 : Nat := 458470445018647727743777

theorem tailTrace_2678604 : CollatzResearch.WordTrace tailWord_2678604 prefixEnd_2678604 458470445018647727743777 := by
  unfold tailWord_2678604
  simp only [CollatzResearch.WordTrace]
  refine ⟨48848356993941325993665433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65131142658588434658220577 48848356993941325993665433)
  ·
    refine ⟨36636267745455994495249075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48848356993941325993665433 36636267745455994495249075)
    ·
      refine ⟨54954401618183991742873613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36636267745455994495249075 54954401618183991742873613)
      ·
        refine ⟨20607900606818996903577605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54954401618183991742873613 20607900606818996903577605)
        ·
          refine ⟨3863981363778561919420801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20607900606818996903577605 3863981363778561919420801)
          ·
            refine ⟨2897986022833921439565601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3863981363778561919420801 2897986022833921439565601)
            ·
              refine ⟨2173489517125441079674201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2897986022833921439565601 2173489517125441079674201)
              ·
                refine ⟨1630117137844080809755651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2173489517125441079674201 1630117137844080809755651)
                ·
                  refine ⟨2445175706766121214633477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1630117137844080809755651 2445175706766121214633477)
                  ·
                    refine ⟨458470445018647727743777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2445175706766121214633477 458470445018647727743777)
                    ·
                      rfl

theorem cell23_2678604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 2, 1, 4].length) (baseStart_2678604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2678604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2678604 prefixEnd_2678604 := by exact prefixLift 2678604
  have htrace : WordTrace (prefixWord ++ tailWord_2678604) baseStart_2678604 baseEnd_2678604 := by
    simpa [prefixWord, tailWord_2678604, baseEnd_2678604] using wordTrace_append hprefix tailTrace_2678604
  have hstable : (prefixWord ++ tailWord_2678604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678604).length < 2 ^ (prefixWord ++ tailWord_2678604).sum := by decide
  have hdescent : baseEnd_2678604 < baseStart_2678604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678650 : List Nat := [3, 1, 1, 1, 1, 1, 8, 1, 1, 1, 4]
def baseStart_2678650 : Nat := 118140960795 + 2678650 * 2 ^ 59
def prefixEnd_2678650 : Nat := 4983230072969 + 3 ^ 40 * 2678650 * 2
def baseEnd_2678650 : Nat := 1375434955166050003256119

theorem tailTrace_2678650 : CollatzResearch.WordTrace tailWord_2678650 prefixEnd_2678650 1375434955166050003256119 := by
  unfold tailWord_2678650
  simp only [CollatzResearch.WordTrace]
  refine ⟨24424597936429000460876351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65132261163810667895670269 24424597936429000460876351)
  ·
    refine ⟨36636896904643500691314527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24424597936429000460876351 36636896904643500691314527)
    ·
      refine ⟨54955345356965251036971791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36636896904643500691314527 54955345356965251036971791)
      ·
        refine ⟨82433018035447876555457687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54955345356965251036971791 82433018035447876555457687)
        ·
          refine ⟨123649527053171814833186531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82433018035447876555457687 123649527053171814833186531)
          ·
            refine ⟨185474290579757722249779797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123649527053171814833186531 185474290579757722249779797)
            ·
              refine ⟨2173526842731535807614607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 185474290579757722249779797 2173526842731535807614607)
              ·
                refine ⟨3260290264097303711421911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2173526842731535807614607 3260290264097303711421911)
                ·
                  refine ⟨4890435396145955567132867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3260290264097303711421911 4890435396145955567132867)
                  ·
                    refine ⟨7335653094218933350699301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4890435396145955567132867 7335653094218933350699301)
                    ·
                      refine ⟨1375434955166050003256119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7335653094218933350699301 1375434955166050003256119)
                      ·
                        rfl

theorem cell23_2678650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 1, 1, 1, 4].length) (baseStart_2678650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2678650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2678650 prefixEnd_2678650 := by exact prefixLift 2678650
  have htrace : WordTrace (prefixWord ++ tailWord_2678650) baseStart_2678650 baseEnd_2678650 := by
    simpa [prefixWord, tailWord_2678650, baseEnd_2678650] using wordTrace_append hprefix tailTrace_2678650
  have hstable : (prefixWord ++ tailWord_2678650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678650).length < 2 ^ (prefixWord ++ tailWord_2678650).sum := by decide
  have hdescent : baseEnd_2678650 < baseStart_2678650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678660 : List Nat := [2, 3, 2, 1, 1, 1, 5, 2, 2, 4]
def baseStart_2678660 : Nat := 118140960795 + 2678660 * 2 ^ 59
def prefixEnd_2678660 : Nat := 4983230072969 + 3 ^ 40 * 2678660 * 2
def baseEnd_2678660 : Nat := 458480029990864988043691

theorem tailTrace_2678660 : CollatzResearch.WordTrace tailWord_2678660 prefixEnd_2678660 458480029990864988043691 := by
  unfold tailWord_2678660
  simp only [CollatzResearch.WordTrace]
  refine ⟨48849378237839886775684717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65132504317119849034246289 48849378237839886775684717)
  ·
    refine ⟨18318516839189957540881769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48849378237839886775684717 18318516839189957540881769)
    ·
      refine ⟨13738887629392468155661327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18318516839189957540881769 13738887629392468155661327)
      ·
        refine ⟨20608331444088702233491991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13738887629392468155661327 20608331444088702233491991)
        ·
          refine ⟨30912497166133053350237987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20608331444088702233491991 30912497166133053350237987)
          ·
            refine ⟨46368745749199580025356981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30912497166133053350237987 46368745749199580025356981)
            ·
              refine ⟨4347069913987460627377217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46368745749199580025356981 4347069913987460627377217)
              ·
                refine ⟨3260302435490595470532913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4347069913987460627377217 3260302435490595470532913)
                ·
                  refine ⟨2445226826617946602899685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3260302435490595470532913 2445226826617946602899685)
                  ·
                    refine ⟨458480029990864988043691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2445226826617946602899685 458480029990864988043691)
                    ·
                      rfl

theorem cell23_2678660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_2678660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2678660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2678660 prefixEnd_2678660 := by exact prefixLift 2678660
  have htrace : WordTrace (prefixWord ++ tailWord_2678660) baseStart_2678660 baseEnd_2678660 := by
    simpa [prefixWord, tailWord_2678660, baseEnd_2678660] using wordTrace_append hprefix tailTrace_2678660
  have hstable : (prefixWord ++ tailWord_2678660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678660).length < 2 ^ (prefixWord ++ tailWord_2678660).sum := by decide
  have hdescent : baseEnd_2678660 < baseStart_2678660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678680 : List Nat := [2, 1, 2, 6, 1, 1, 1, 1, 1, 1, 6]
def baseStart_2678680 : Nat := 118140960795 + 2678680 * 2 ^ 59
def prefixEnd_2678680 : Nat := 4983230072969 + 3 ^ 40 * 2678680 * 2
def baseEnd_2678680 : Nat := 1375450359585684885880981

theorem tailTrace_2678680 : CollatzResearch.WordTrace tailWord_2678680 prefixEnd_2678680 1375450359585684885880981 := by
  unfold tailWord_2678680
  simp only [CollatzResearch.WordTrace]
  refine ⟨48849742967803658483548747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65132990623738211311398329 48849742967803658483548747)
  ·
    refine ⟨73274614451705487725323121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48849742967803658483548747 73274614451705487725323121)
    ·
      refine ⟨54955960838779115793992341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73274614451705487725323121 54955960838779115793992341)
      ·
        refine ⟨2576060664317771052843391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 54955960838779115793992341 2576060664317771052843391)
        ·
          refine ⟨3864090996476656579265087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2576060664317771052843391 3864090996476656579265087)
          ·
            refine ⟨5796136494714984868897631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3864090996476656579265087 5796136494714984868897631)
            ·
              refine ⟨8694204742072477303346447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5796136494714984868897631 8694204742072477303346447)
              ·
                refine ⟨13041307113108715955019671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8694204742072477303346447 13041307113108715955019671)
                ·
                  refine ⟨19561960669663073932529507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13041307113108715955019671 19561960669663073932529507)
                  ·
                    refine ⟨29342941004494610898794261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19561960669663073932529507 29342941004494610898794261)
                    ·
                      refine ⟨1375450359585684885880981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29342941004494610898794261 1375450359585684885880981)
                      ·
                        rfl

theorem cell23_2678680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_2678680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2678680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2678680 prefixEnd_2678680 := by exact prefixLift 2678680
  have htrace : WordTrace (prefixWord ++ tailWord_2678680) baseStart_2678680 baseEnd_2678680 := by
    simpa [prefixWord, tailWord_2678680, baseEnd_2678680] using wordTrace_append hprefix tailTrace_2678680
  have hstable : (prefixWord ++ tailWord_2678680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678680).length < 2 ^ (prefixWord ++ tailWord_2678680).sum := by decide
  have hdescent : baseEnd_2678680 < baseStart_2678680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678687 : List Nat := [1, 1, 2, 5, 3, 1, 2, 2, 1, 2, 3]
def baseStart_2678687 : Nat := 118140960795 + 2678687 * 2 ^ 59
def prefixEnd_2678687 : Nat := 4983230072969 + 3 ^ 40 * 2678687 * 2
def baseEnd_2678687 : Nat := 1375453953950266358493449

theorem tailTrace_2678687 : CollatzResearch.WordTrace tailWord_2678687 prefixEnd_2678687 1375453953950266358493449 := by
  unfold tailWord_2678687
  simp only [CollatzResearch.WordTrace]
  refine ⟨97699741246581957162602315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65133160831054638108401543 97699741246581957162602315)
  ·
    refine ⟨146549611869872935743903473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97699741246581957162602315 146549611869872935743903473)
    ·
      refine ⟨109912208902404701807927605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146549611869872935743903473 109912208902404701807927605)
      ·
        refine ⟨10304269584600440794493213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 109912208902404701807927605 10304269584600440794493213)
        ·
          refine ⟨3864101094225165297934955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10304269584600440794493213 3864101094225165297934955)
          ·
            refine ⟨5796151641337747946902433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3864101094225165297934955 5796151641337747946902433)
            ·
              refine ⟨4347113731003310960176825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5796151641337747946902433 4347113731003310960176825)
              ·
                refine ⟨3260335298252483220132619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4347113731003310960176825 3260335298252483220132619)
                ·
                  refine ⟨4890502947378724830198929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3260335298252483220132619 4890502947378724830198929)
                  ·
                    refine ⟨3667877210534043622649197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4890502947378724830198929 3667877210534043622649197)
                    ·
                      refine ⟨1375453953950266358493449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3667877210534043622649197 1375453953950266358493449)
                      ·
                        rfl

theorem cell23_2678687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_2678687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2678687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2678687 prefixEnd_2678687 := by exact prefixLift 2678687
  have htrace : WordTrace (prefixWord ++ tailWord_2678687) baseStart_2678687 baseEnd_2678687 := by
    simpa [prefixWord, tailWord_2678687, baseEnd_2678687] using wordTrace_append hprefix tailTrace_2678687
  have hstable : (prefixWord ++ tailWord_2678687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678687).length < 2 ^ (prefixWord ++ tailWord_2678687).sum := by decide
  have hdescent : baseEnd_2678687 < baseStart_2678687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678693 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 2, 7, 2]
def baseStart_2678693 : Nat := 118140960795 + 2678693 * 2 ^ 59
def prefixEnd_2678693 : Nat := 4983230072969 + 3 ^ 40 * 2678693 * 2
def baseEnd_2678693 : Nat := 1375457034834193335018421

theorem tailTrace_2678693 : CollatzResearch.WordTrace tailWord_2678693 prefixEnd_2678693 1375457034834193335018421 := by
  unfold tailWord_2678693
  simp only [CollatzResearch.WordTrace]
  refine ⟨97699960084560220187320733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65133306723040146791547155 97699960084560220187320733)
  ·
    refine ⟨36637485031710082570245275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97699960084560220187320733 36637485031710082570245275)
    ·
      refine ⟨54956227547565123855367913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36637485031710082570245275 54956227547565123855367913)
      ·
        refine ⟨41217170660673842891525935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54956227547565123855367913 41217170660673842891525935)
        ·
          refine ⟨61825755991010764337288903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41217170660673842891525935 61825755991010764337288903)
          ·
            refine ⟨92738633986516146505933355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61825755991010764337288903 92738633986516146505933355)
            ·
              refine ⟨139107950979774219758900033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92738633986516146505933355 139107950979774219758900033)
              ·
                refine ⟨104330963234830664819175025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139107950979774219758900033 104330963234830664819175025)
                ·
                  refine ⟨78248222426122998614381269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104330963234830664819175025 78248222426122998614381269)
                  ·
                    refine ⟨1833942713112257780024561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 78248222426122998614381269 1833942713112257780024561)
                    ·
                      refine ⟨1375457034834193335018421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1833942713112257780024561 1375457034834193335018421)
                      ·
                        rfl

theorem cell23_2678693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 7, 2].length) (baseStart_2678693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2678693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2678693 prefixEnd_2678693 := by exact prefixLift 2678693
  have htrace : WordTrace (prefixWord ++ tailWord_2678693) baseStart_2678693 baseEnd_2678693 := by
    simpa [prefixWord, tailWord_2678693, baseEnd_2678693] using wordTrace_append hprefix tailTrace_2678693
  have hstable : (prefixWord ++ tailWord_2678693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678693).length < 2 ^ (prefixWord ++ tailWord_2678693).sum := by decide
  have hdescent : baseEnd_2678693 < baseStart_2678693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678706 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8]
def baseStart_2678706 : Nat := 118140960795 + 2678706 * 2 ^ 59
def prefixEnd_2678706 : Nat := 4983230072969 + 3 ^ 40 * 2678706 * 2
def baseEnd_2678706 : Nat := 1375463710082701784155861

theorem tailTrace_2678706 : CollatzResearch.WordTrace tailWord_2678706 prefixEnd_2678706 1375463710082701784155861 := by
  unfold tailWord_2678706
  simp only [CollatzResearch.WordTrace]
  refine ⟨24425108558378280851885993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65133622822342082271695981 24425108558378280851885993)
  ·
    refine ⟨18318831418783710638914495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24425108558378280851885993 18318831418783710638914495)
    ·
      refine ⟨27478247128175565958371743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18318831418783710638914495 27478247128175565958371743)
      ·
        refine ⟨41217370692263348937557615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27478247128175565958371743 41217370692263348937557615)
        ·
          refine ⟨61826056038395023406336423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41217370692263348937557615 61826056038395023406336423)
          ·
            refine ⟨92739084057592535109504635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61826056038395023406336423 92739084057592535109504635)
            ·
              refine ⟨139108626086388802664256953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92739084057592535109504635 139108626086388802664256953)
              ·
                refine ⟨104331469564791601998192715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139108626086388802664256953 104331469564791601998192715)
                ·
                  refine ⟨156497204347187402997289073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104331469564791601998192715 156497204347187402997289073)
                  ·
                    refine ⟨117372903260390552247966805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 156497204347187402997289073 117372903260390552247966805)
                    ·
                      refine ⟨1375463710082701784155861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 117372903260390552247966805 1375463710082701784155861)
                      ·
                        rfl

theorem cell23_2678706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_2678706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2678706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2678706 prefixEnd_2678706 := by exact prefixLift 2678706
  have htrace : WordTrace (prefixWord ++ tailWord_2678706) baseStart_2678706 baseEnd_2678706 := by
    simpa [prefixWord, tailWord_2678706, baseEnd_2678706] using wordTrace_append hprefix tailTrace_2678706
  have hstable : (prefixWord ++ tailWord_2678706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678706).length < 2 ^ (prefixWord ++ tailWord_2678706).sum := by decide
  have hdescent : baseEnd_2678706 < baseStart_2678706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678723 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 2, 8, 2]
def baseStart_2678723 : Nat := 118140960795 + 2678723 * 2 ^ 59
def prefixEnd_2678723 : Nat := 4983230072969 + 3 ^ 40 * 2678723 * 2
def baseEnd_2678723 : Nat := 1375472439253828217643283

theorem tailTrace_2678723 : CollatzResearch.WordTrace tailWord_2678723 prefixEnd_2678723 1375472439253828217643283 := by
  unfold tailWord_2678723
  simp only [CollatzResearch.WordTrace]
  refine ⟨97701054274451535310912823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65134036182967690207275215 97701054274451535310912823)
  ·
    refine ⟨146551581411677302966369235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97701054274451535310912823 146551581411677302966369235)
    ·
      refine ⟨219827372117515954449553853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146551581411677302966369235 219827372117515954449553853)
      ·
        refine ⟨82435264544068482918582695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 219827372117515954449553853 82435264544068482918582695)
        ·
          refine ⟨123652896816102724377874043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82435264544068482918582695 123652896816102724377874043)
          ·
            refine ⟨185479345224154086566811065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123652896816102724377874043 185479345224154086566811065)
            ·
              refine ⟨139109508918115564925108299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185479345224154086566811065 139109508918115564925108299)
              ·
                refine ⟨208664263377173347387662449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139109508918115564925108299 208664263377173347387662449)
                ·
                  refine ⟨156498197532880010540746837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 208664263377173347387662449 156498197532880010540746837)
                  ·
                    refine ⟨1833963252338437623524377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 156498197532880010540746837 1833963252338437623524377)
                    ·
                      refine ⟨1375472439253828217643283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1833963252338437623524377 1375472439253828217643283)
                      ·
                        rfl

theorem cell23_2678723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 8, 2].length) (baseStart_2678723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2678723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2678723 prefixEnd_2678723 := by exact prefixLift 2678723
  have htrace : WordTrace (prefixWord ++ tailWord_2678723) baseStart_2678723 baseEnd_2678723 := by
    simpa [prefixWord, tailWord_2678723, baseEnd_2678723] using wordTrace_append hprefix tailTrace_2678723
  have hstable : (prefixWord ++ tailWord_2678723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678723).length < 2 ^ (prefixWord ++ tailWord_2678723).sum := by decide
  have hdescent : baseEnd_2678723 < baseStart_2678723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678780 : List Nat := [2, 2, 2, 1, 2, 2, 3, 4, 5]
def baseStart_2678780 : Nat := 118140960795 + 2678780 * 2 ^ 59
def prefixEnd_2678780 : Nat := 4983230072969 + 3 ^ 40 * 2678780 * 2
def baseEnd_2678780 : Nat := 152833523072348277181169

theorem tailTrace_2678780 : CollatzResearch.WordTrace tailWord_2678780 prefixEnd_2678780 152833523072348277181169 := by
  unfold tailWord_2678780
  simp only [CollatzResearch.WordTrace]
  refine ⟨48851566617622517022868897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65135422156830022697158529 48851566617622517022868897)
  ·
    refine ⟨36638674963216887767151673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48851566617622517022868897 36638674963216887767151673)
    ·
      refine ⟨27479006222412665825363755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36638674963216887767151673 27479006222412665825363755)
      ·
        refine ⟨41218509333618998738045633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27479006222412665825363755 41218509333618998738045633)
        ·
          refine ⟨30913882000214249053534225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41218509333618998738045633 30913882000214249053534225)
          ·
            refine ⟨23185411500160686790150669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30913882000214249053534225 23185411500160686790150669)
            ·
              refine ⟨8694529312560257546306501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23185411500160686790150669 8694529312560257546306501)
              ·
                refine ⟨1630224246105048289932469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8694529312560257546306501 1630224246105048289932469)
                ·
                  refine ⟨152833523072348277181169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1630224246105048289932469 152833523072348277181169)
                  ·
                    rfl

theorem cell23_2678780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 4, 5].length) (baseStart_2678780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2678780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2678780 prefixEnd_2678780 := by exact prefixLift 2678780
  have htrace : WordTrace (prefixWord ++ tailWord_2678780) baseStart_2678780 baseEnd_2678780 := by
    simpa [prefixWord, tailWord_2678780, baseEnd_2678780] using wordTrace_append hprefix tailTrace_2678780
  have hstable : (prefixWord ++ tailWord_2678780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678780).length < 2 ^ (prefixWord ++ tailWord_2678780).sum := by decide
  have hdescent : baseEnd_2678780 < baseStart_2678780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678810 : List Nat := [3, 1, 1, 3, 1, 3, 3, 1, 2, 5]
def baseStart_2678810 : Nat := 118140960795 + 2678810 * 2 ^ 59
def prefixEnd_2678810 : Nat := 4983230072969 + 3 ^ 40 * 2678810 * 2
def baseEnd_2678810 : Nat := 458505704023589792418461

theorem tailTrace_2678810 : CollatzResearch.WordTrace tailWord_2678810 prefixEnd_2678810 458505704023589792418461 := by
  unfold tailWord_2678810
  simp only [CollatzResearch.WordTrace]
  refine ⟨24426056856284087292332471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65136151616757566112886589 24426056856284087292332471)
  ·
    refine ⟨36639085284426130938498707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24426056856284087292332471 36639085284426130938498707)
    ·
      refine ⟨54958627926639196407748061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36639085284426130938498707 54958627926639196407748061)
      ·
        refine ⟨20609485472489698652905523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54958627926639196407748061 20609485472489698652905523)
        ·
          refine ⟨30914228208734547979358285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20609485472489698652905523 30914228208734547979358285)
          ·
            refine ⟨11592835578275455492259357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30914228208734547979358285 11592835578275455492259357)
            ·
              refine ⟨4347313341853295809597259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11592835578275455492259357 4347313341853295809597259)
              ·
                refine ⟨6520970012779943714395889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4347313341853295809597259 6520970012779943714395889)
                ·
                  refine ⟨4890727509584957785796917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6520970012779943714395889 4890727509584957785796917)
                  ·
                    refine ⟨458505704023589792418461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4890727509584957785796917 458505704023589792418461)
                    ·
                      rfl

theorem cell23_2678810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 2, 5].length) (baseStart_2678810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2678810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2678810 prefixEnd_2678810 := by exact prefixLift 2678810
  have htrace : WordTrace (prefixWord ++ tailWord_2678810) baseStart_2678810 baseEnd_2678810 := by
    simpa [prefixWord, tailWord_2678810, baseEnd_2678810] using wordTrace_append hprefix tailTrace_2678810
  have hstable : (prefixWord ++ tailWord_2678810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678810).length < 2 ^ (prefixWord ++ tailWord_2678810).sum := by decide
  have hdescent : baseEnd_2678810 < baseStart_2678810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678917 : List Nat := [1, 3, 1, 1, 5, 1, 3, 2, 1, 5]
def baseStart_2678917 : Nat := 118140960795 + 2678917 * 2 ^ 59
def prefixEnd_2678917 : Nat := 4983230072969 + 3 ^ 40 * 2678917 * 2
def baseEnd_2678917 : Nat := 458524018166933486205797

theorem tailTrace_2678917 : CollatzResearch.WordTrace tailWord_2678917 prefixEnd_2678917 458524018166933486205797 := by
  unfold tailWord_2678917
  simp only [CollatzResearch.WordTrace]
  refine ⟨97708130035748706443475005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65138753357165804295650003 97708130035748706443475005)
  ·
    refine ⟨36640548763405764916303127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97708130035748706443475005 36640548763405764916303127)
    ·
      refine ⟨54960823145108647374454691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36640548763405764916303127 54960823145108647374454691)
      ·
        refine ⟨82441234717662971061682037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54960823145108647374454691 82441234717662971061682037)
        ·
          refine ⟨7728865754780903537032691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82441234717662971061682037 7728865754780903537032691)
          ·
            refine ⟨11593298632171355305549037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7728865754780903537032691 11593298632171355305549037)
            ·
              refine ⟨4347486987064258239580889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11593298632171355305549037 4347486987064258239580889)
              ·
                refine ⟨3260615240298193679685667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4347486987064258239580889 3260615240298193679685667)
                ·
                  refine ⟨4890922860447290519528501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3260615240298193679685667 4890922860447290519528501)
                  ·
                    refine ⟨458524018166933486205797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4890922860447290519528501 458524018166933486205797)
                    ·
                      rfl

theorem cell23_2678917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 2, 1, 5].length) (baseStart_2678917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2678917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2678917 prefixEnd_2678917 := by exact prefixLift 2678917
  have htrace : WordTrace (prefixWord ++ tailWord_2678917) baseStart_2678917 baseEnd_2678917 := by
    simpa [prefixWord, tailWord_2678917, baseEnd_2678917] using wordTrace_append hprefix tailTrace_2678917
  have hstable : (prefixWord ++ tailWord_2678917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678917).length < 2 ^ (prefixWord ++ tailWord_2678917).sum := by decide
  have hdescent : baseEnd_2678917 < baseStart_2678917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678923 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 5]
def baseStart_2678923 : Nat := 118140960795 + 2678923 * 2 ^ 59
def prefixEnd_2678923 : Nat := 4983230072969 + 3 ^ 40 * 2678923 * 2
def baseEnd_2678923 : Nat := 1375575135384727435142363

theorem tailTrace_2678923 : CollatzResearch.WordTrace tailWord_2678923 prefixEnd_2678923 1375575135384727435142363 := by
  unfold tailWord_2678923
  simp only [CollatzResearch.WordTrace]
  refine ⟨97708348873726969468193423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65138899249151312978795615 97708348873726969468193423)
  ·
    refine ⟨146562523310590454202290135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97708348873726969468193423 146562523310590454202290135)
    ·
      refine ⟨219843784965885681303435203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146562523310590454202290135 219843784965885681303435203)
      ·
        refine ⟨329765677448828521955152805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219843784965885681303435203 329765677448828521955152805)
        ·
          refine ⟨61831064521655347866591151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 329765677448828521955152805 61831064521655347866591151)
          ·
            refine ⟨92746596782483021799886727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61831064521655347866591151 92746596782483021799886727)
            ·
              refine ⟨139119895173724532699830091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92746596782483021799886727 139119895173724532699830091)
              ·
                refine ⟨208679842760586799049745137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139119895173724532699830091 208679842760586799049745137)
                ·
                  refine ⟨156509882070440099287308853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 208679842760586799049745137 156509882070440099287308853)
                  ·
                    refine ⟨14672801444103759308185205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 156509882070440099287308853 14672801444103759308185205)
                    ·
                      refine ⟨1375575135384727435142363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14672801444103759308185205 1375575135384727435142363)
                      ·
                        rfl

theorem cell23_2678923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 5].length) (baseStart_2678923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2678923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2678923 prefixEnd_2678923 := by exact prefixLift 2678923
  have htrace : WordTrace (prefixWord ++ tailWord_2678923) baseStart_2678923 baseEnd_2678923 := by
    simpa [prefixWord, tailWord_2678923, baseEnd_2678923] using wordTrace_append hprefix tailTrace_2678923
  have hstable : (prefixWord ++ tailWord_2678923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678923).length < 2 ^ (prefixWord ++ tailWord_2678923).sum := by decide
  have hdescent : baseEnd_2678923 < baseStart_2678923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678967 : List Nat := [1, 1, 3, 1, 4, 3, 2, 1, 1, 2, 4]
def baseStart_2678967 : Nat := 118140960795 + 2678967 * 2 ^ 59
def prefixEnd_2678967 : Nat := 4983230072969 + 3 ^ 40 * 2678967 * 2
def baseEnd_2678967 : Nat := 1375597728533525262992161

theorem tailTrace_2678967 : CollatzResearch.WordTrace tailWord_2678967 prefixEnd_2678967 1375597728533525262992161 := by
  unfold tailWord_2678967
  simp only [CollatzResearch.WordTrace]
  refine ⟨97709953685567564982795155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65139969123711709988530103 97709953685567564982795155)
  ·
    refine ⟨146564930528351347474192733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97709953685567564982795155 146564930528351347474192733)
    ·
      refine ⟨54961848948131755302822275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146564930528351347474192733 54961848948131755302822275)
      ·
        refine ⟨82442773422197632954233413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54961848948131755302822275 82442773422197632954233413)
        ·
          refine ⟨15458020016662056178918765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82442773422197632954233413 15458020016662056178918765)
          ·
            refine ⟨5796757506248271067094537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15458020016662056178918765 5796757506248271067094537)
            ·
              refine ⟨4347568129686203300320903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5796757506248271067094537 4347568129686203300320903)
              ·
                refine ⟨6521352194529304950481355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4347568129686203300320903 6521352194529304950481355)
                ·
                  refine ⟨9782028291793957425722033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6521352194529304950481355 9782028291793957425722033)
                  ·
                    refine ⟨7336521218845468069291525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9782028291793957425722033 7336521218845468069291525)
                    ·
                      refine ⟨1375597728533525262992161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7336521218845468069291525 1375597728533525262992161)
                      ·
                        rfl

theorem cell23_2678967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 2, 4].length) (baseStart_2678967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2678967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2678967 prefixEnd_2678967 := by exact prefixLift 2678967
  have htrace : WordTrace (prefixWord ++ tailWord_2678967) baseStart_2678967 baseEnd_2678967 := by
    simpa [prefixWord, tailWord_2678967, baseEnd_2678967] using wordTrace_append hprefix tailTrace_2678967
  have hstable : (prefixWord ++ tailWord_2678967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678967).length < 2 ^ (prefixWord ++ tailWord_2678967).sum := by decide
  have hdescent : baseEnd_2678967 < baseStart_2678967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678987 : List Nat := [1, 1, 1, 1, 3, 2, 4, 2, 4, 1, 3]
def baseStart_2678987 : Nat := 118140960795 + 2678987 * 2 ^ 59
def prefixEnd_2678987 : Nat := 4983230072969 + 3 ^ 40 * 2678987 * 2
def baseEnd_2678987 : Nat := 1375607998146615184742069

theorem tailTrace_2678987 : CollatzResearch.WordTrace tailWord_2678987 prefixEnd_2678987 1375607998146615184742069 := by
  unfold tailWord_2678987
  simp only [CollatzResearch.WordTrace]
  refine ⟨97710683145495108398523215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65140455430330072265682143 97710683145495108398523215)
  ·
    refine ⟨146566024718242662597784823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97710683145495108398523215 146566024718242662597784823)
    ·
      refine ⟨219849037077363993896677235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146566024718242662597784823 219849037077363993896677235)
      ·
        refine ⟨329773555616045990845015853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219849037077363993896677235 329773555616045990845015853)
        ·
          refine ⟨123665083356017246566880945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 329773555616045990845015853 123665083356017246566880945)
          ·
            refine ⟨92748812517012934925160709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123665083356017246566880945 92748812517012934925160709)
            ·
              refine ⟨17390402346939925298467633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92748812517012934925160709 17390402346939925298467633)
              ·
                refine ⟨13042801760204943973850725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17390402346939925298467633 13042801760204943973850725)
                ·
                  refine ⟨2445525330038426995097011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13042801760204943973850725 2445525330038426995097011)
                  ·
                    refine ⟨3668287995057640492645517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2445525330038426995097011 3668287995057640492645517)
                    ·
                      refine ⟨1375607998146615184742069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3668287995057640492645517 1375607998146615184742069)
                      ·
                        rfl

theorem cell23_2678987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 4, 1, 3].length) (baseStart_2678987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2678987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2678987 prefixEnd_2678987 := by exact prefixLift 2678987
  have htrace : WordTrace (prefixWord ++ tailWord_2678987) baseStart_2678987 baseEnd_2678987 := by
    simpa [prefixWord, tailWord_2678987, baseEnd_2678987] using wordTrace_append hprefix tailTrace_2678987
  have hstable : (prefixWord ++ tailWord_2678987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678987).length < 2 ^ (prefixWord ++ tailWord_2678987).sum := by decide
  have hdescent : baseEnd_2678987 < baseStart_2678987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678988 : List Nat := [2, 2, 1, 6, 1, 2, 2, 1, 1, 1, 4]
def baseStart_2678988 : Nat := 118140960795 + 2678988 * 2 ^ 59
def prefixEnd_2678988 : Nat := 4983230072969 + 3 ^ 40 * 2678988 * 2
def baseEnd_2678988 : Nat := 1375608511627269680829565

theorem tailTrace_2678988 : CollatzResearch.WordTrace tailWord_2678988 prefixEnd_2678988 1375608511627269680829565 := by
  unfold tailWord_2678988
  simp only [CollatzResearch.WordTrace]
  refine ⟨48855359809245742784654809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65140479745660990379539745 48855359809245742784654809)
  ·
    refine ⟨36641519856934307088491107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48855359809245742784654809 36641519856934307088491107)
    ·
      refine ⟨54962279785401460632736661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36641519856934307088491107 54962279785401460632736661)
      ·
        refine ⟨2576356864940693467159531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 54962279785401460632736661 2576356864940693467159531)
        ·
          refine ⟨3864535297411040200739297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2576356864940693467159531 3864535297411040200739297)
          ·
            refine ⟨2898401473058280150554473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3864535297411040200739297 2898401473058280150554473)
            ·
              refine ⟨2173801104793710112915855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2898401473058280150554473 2173801104793710112915855)
              ·
                refine ⟨3260701657190565169373783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2173801104793710112915855 3260701657190565169373783)
                ·
                  refine ⟨4891052485785847754060675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3260701657190565169373783 4891052485785847754060675)
                  ·
                    refine ⟨7336578728678771631091013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4891052485785847754060675 7336578728678771631091013)
                    ·
                      refine ⟨1375608511627269680829565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7336578728678771631091013 1375608511627269680829565)
                      ·
                        rfl

theorem cell23_2678988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_2678988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2678988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2678988 prefixEnd_2678988 := by exact prefixLift 2678988
  have htrace : WordTrace (prefixWord ++ tailWord_2678988) baseStart_2678988 baseEnd_2678988 := by
    simpa [prefixWord, tailWord_2678988, baseEnd_2678988] using wordTrace_append hprefix tailTrace_2678988
  have hstable : (prefixWord ++ tailWord_2678988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678988).length < 2 ^ (prefixWord ++ tailWord_2678988).sum := by decide
  have hdescent : baseEnd_2678988 < baseStart_2678988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678998 : List Nat := [5, 2, 1, 2, 1, 3, 1, 2, 2, 4]
def baseStart_2678998 : Nat := 118140960795 + 2678998 * 2 ^ 59
def prefixEnd_2678998 : Nat := 4983230072969 + 3 ^ 40 * 2678998 * 2
def baseEnd_2678998 : Nat := 458537882144604880568173

theorem tailTrace_2678998 : CollatzResearch.WordTrace tailWord_2678998 prefixEnd_2678998 458537882144604880568173 := by
  unfold tailWord_2678998
  simp only [CollatzResearch.WordTrace]
  refine ⟨6106942771778453579823353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65140722898970171518115765 6106942771778453579823353)
  ·
    refine ⟨4580207078833840184867515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6106942771778453579823353 4580207078833840184867515)
    ·
      refine ⟨6870310618250760277301273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4580207078833840184867515 6870310618250760277301273)
      ·
        refine ⟨5152732963688070207975955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6870310618250760277301273 5152732963688070207975955)
        ·
          refine ⟨7729099445532105311963933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5152732963688070207975955 7729099445532105311963933)
          ·
            refine ⟨2898412292074539491986475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7729099445532105311963933 2898412292074539491986475)
            ·
              refine ⟨4347618438111809237979713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2898412292074539491986475 4347618438111809237979713)
              ·
                refine ⟨3260713828583856928484785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4347618438111809237979713 3260713828583856928484785)
                ·
                  refine ⟨2445535371437892696363589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3260713828583856928484785 2445535371437892696363589)
                  ·
                    refine ⟨458537882144604880568173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2445535371437892696363589 458537882144604880568173)
                    ·
                      rfl

theorem cell23_2678998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_2678998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2678998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2678998 prefixEnd_2678998 := by exact prefixLift 2678998
  have htrace : WordTrace (prefixWord ++ tailWord_2678998) baseStart_2678998 baseEnd_2678998 := by
    simpa [prefixWord, tailWord_2678998, baseEnd_2678998] using wordTrace_append hprefix tailTrace_2678998
  have hstable : (prefixWord ++ tailWord_2678998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678998).length < 2 ^ (prefixWord ++ tailWord_2678998).sum := by decide
  have hdescent : baseEnd_2678998 < baseStart_2678998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679020 : List Nat := [2, 2, 1, 1, 2, 3, 1, 3, 2, 6]
def baseStart_2679020 : Nat := 118140960795 + 2679020 * 2 ^ 59
def prefixEnd_2679020 : Nat := 4983230072969 + 3 ^ 40 * 2679020 * 2
def baseEnd_2679020 : Nat := 458541647669404518543139

theorem tailTrace_2679020 : CollatzResearch.WordTrace tailWord_2679020 prefixEnd_2679020 458541647669404518543139 := by
  unfold tailWord_2679020
  simp only [CollatzResearch.WordTrace]
  refine ⟨48855943377187777517237257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65141257836250370022983009 48855943377187777517237257)
  ·
    refine ⟨36641957532890833137927943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48855943377187777517237257 36641957532890833137927943)
    ·
      refine ⟨54962936299336249706891915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36641957532890833137927943 54962936299336249706891915)
      ·
        refine ⟨82444404449004374560337873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54962936299336249706891915 82444404449004374560337873)
        ·
          refine ⟨61833303336753280920253405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82444404449004374560337873 61833303336753280920253405)
          ·
            refine ⟨23187488751282480345095027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61833303336753280920253405 23187488751282480345095027)
            ·
              refine ⟨34781233126923720517642541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23187488751282480345095027 34781233126923720517642541)
              ·
                refine ⟨13042962422596395194115953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34781233126923720517642541 13042962422596395194115953)
                ·
                  refine ⟨9782221816947296395586965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13042962422596395194115953 9782221816947296395586965)
                  ·
                    refine ⟨458541647669404518543139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9782221816947296395586965 458541647669404518543139)
                    ·
                      rfl

theorem cell23_2679020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 6].length) (baseStart_2679020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679020 prefixEnd_2679020 := by exact prefixLift 2679020
  have htrace : WordTrace (prefixWord ++ tailWord_2679020) baseStart_2679020 baseEnd_2679020 := by
    simpa [prefixWord, tailWord_2679020, baseEnd_2679020] using wordTrace_append hprefix tailTrace_2679020
  have hstable : (prefixWord ++ tailWord_2679020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679020).length < 2 ^ (prefixWord ++ tailWord_2679020).sum := by decide
  have hdescent : baseEnd_2679020 < baseStart_2679020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679021 : List Nat := [1, 5, 1, 2, 3, 2, 1, 1, 1, 3, 3]
def baseStart_2679021 : Nat := 118140960795 + 2679021 * 2 ^ 59
def prefixEnd_2679021 : Nat := 4983230072969 + 3 ^ 40 * 2679021 * 2
def baseEnd_2679021 : Nat := 1375625456488868051716913

theorem tailTrace_2679021 : CollatzResearch.WordTrace tailWord_2679021 prefixEnd_2679021 1375625456488868051716913 := by
  unfold tailWord_2679021
  simp only [CollatzResearch.WordTrace]
  refine ⟨97711923227371932205260917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65141282151581288136840611 97711923227371932205260917)
  ·
    refine ⟨9160492802566118644243211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97711923227371932205260917 9160492802566118644243211)
    ·
      refine ⟨13740739203849177966364817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9160492802566118644243211 13740739203849177966364817)
      ·
        refine ⟨10305554402886883474773613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13740739203849177966364817 10305554402886883474773613)
        ·
          refine ⟨3864582901082581303040105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10305554402886883474773613 3864582901082581303040105)
          ·
            refine ⟨2898437175811935977280079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3864582901082581303040105 2898437175811935977280079)
            ·
              refine ⟨4347655763717903965920119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2898437175811935977280079 4347655763717903965920119)
              ·
                refine ⟨6521483645576855948880179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4347655763717903965920119 6521483645576855948880179)
                ·
                  refine ⟨9782225468365283923320269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6521483645576855948880179 9782225468365283923320269)
                  ·
                    refine ⟨3668334550636981471245101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9782225468365283923320269 3668334550636981471245101)
                    ·
                      refine ⟨1375625456488868051716913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3668334550636981471245101 1375625456488868051716913)
                      ·
                        rfl

theorem cell23_2679021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_2679021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679021 prefixEnd_2679021 := by exact prefixLift 2679021
  have htrace : WordTrace (prefixWord ++ tailWord_2679021) baseStart_2679021 baseEnd_2679021 := by
    simpa [prefixWord, tailWord_2679021, baseEnd_2679021] using wordTrace_append hprefix tailTrace_2679021
  have hstable : (prefixWord ++ tailWord_2679021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679021).length < 2 ^ (prefixWord ++ tailWord_2679021).sum := by decide
  have hdescent : baseEnd_2679021 < baseStart_2679021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679040 : List Nat := [2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 4]
def baseStart_2679040 : Nat := 118140960795 + 2679040 * 2 ^ 59
def prefixEnd_2679040 : Nat := 4983230072969 + 3 ^ 40 * 2679040 * 2
def baseEnd_2679040 : Nat := 1375635212621303477379325

theorem tailTrace_2679040 : CollatzResearch.WordTrace tailWord_2679040 prefixEnd_2679040 1375635212621303477379325 := by
  unfold tailWord_2679040
  simp only [CollatzResearch.WordTrace]
  refine ⟨48856308107151549225101287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65141744142868732300135049 48856308107151549225101287)
  ·
    refine ⟨73284462160727323837651931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48856308107151549225101287 73284462160727323837651931)
    ·
      refine ⟨109926693241090985756477897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73284462160727323837651931 109926693241090985756477897)
      ·
        refine ⟨82445019930818239317358423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109926693241090985756477897 82445019930818239317358423)
        ·
          refine ⟨123667529896227358976037635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82445019930818239317358423 123667529896227358976037635)
          ·
            refine ⟨185501294844341038464056453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123667529896227358976037635 185501294844341038464056453)
            ·
              refine ⟨34781492783313944712010585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 185501294844341038464056453 34781492783313944712010585)
              ·
                refine ⟨26086119587485458534007939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34781492783313944712010585 26086119587485458534007939)
                ·
                  refine ⟨39129179381228187801011909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26086119587485458534007939 39129179381228187801011909)
                  ·
                    refine ⟨7336721133980285212689733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39129179381228187801011909 7336721133980285212689733)
                    ·
                      refine ⟨1375635212621303477379325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7336721133980285212689733 1375635212621303477379325)
                      ·
                        rfl

theorem cell23_2679040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 4].length) (baseStart_2679040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679040 prefixEnd_2679040 := by exact prefixLift 2679040
  have htrace : WordTrace (prefixWord ++ tailWord_2679040) baseStart_2679040 baseEnd_2679040 := by
    simpa [prefixWord, tailWord_2679040, baseEnd_2679040] using wordTrace_append hprefix tailTrace_2679040
  have hstable : (prefixWord ++ tailWord_2679040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679040).length < 2 ^ (prefixWord ++ tailWord_2679040).sum := by decide
  have hdescent : baseEnd_2679040 < baseStart_2679040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679050 : List Nat := [3, 1, 2, 2, 1, 1, 2, 2, 9]
def baseStart_2679050 : Nat := 118140960795 + 2679050 * 2 ^ 59
def prefixEnd_2679050 : Nat := 4983230072969 + 3 ^ 40 * 2679050 * 2
def baseEnd_2679050 : Nat := 152848927491983159806031

theorem tailTrace_2679050 : CollatzResearch.WordTrace tailWord_2679050 prefixEnd_2679050 152848927491983159806031 := by
  unfold tailWord_2679050
  simp only [CollatzResearch.WordTrace]
  refine ⟨24428245236066717539516651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65141987296177913438711069 24428245236066717539516651)
  ·
    refine ⟨36642367854100076309274977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24428245236066717539516651 36642367854100076309274977)
    ·
      refine ⟨27481775890575057231956233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36642367854100076309274977 27481775890575057231956233)
      ·
        refine ⟨20611331917931292923967175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27481775890575057231956233 20611331917931292923967175)
        ·
          refine ⟨30916997876896939385950763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20611331917931292923967175 30916997876896939385950763)
          ·
            refine ⟨46375496815345409078926145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30916997876896939385950763 46375496815345409078926145)
            ·
              refine ⟨34781622611509056809194609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46375496815345409078926145 34781622611509056809194609)
              ·
                refine ⟨26086216958631792606895957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34781622611509056809194609 26086216958631792606895957)
                ·
                  refine ⟨152848927491983159806031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 26086216958631792606895957 152848927491983159806031)
                  ·
                    rfl

theorem cell23_2679050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 9].length) (baseStart_2679050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679050 prefixEnd_2679050 := by exact prefixLift 2679050
  have htrace : WordTrace (prefixWord ++ tailWord_2679050) baseStart_2679050 baseEnd_2679050 := by
    simpa [prefixWord, tailWord_2679050, baseEnd_2679050] using wordTrace_append hprefix tailTrace_2679050
  have hstable : (prefixWord ++ tailWord_2679050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679050).length < 2 ^ (prefixWord ++ tailWord_2679050).sum := by decide
  have hdescent : baseEnd_2679050 < baseStart_2679050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679067 : List Nat := [1, 1, 1, 1, 1, 1, 6, 6, 5]
def baseStart_2679067 : Nat := 118140960795 + 2679067 * 2 ^ 59
def prefixEnd_2679067 : Nat := 4983230072969 + 3 ^ 40 * 2679067 * 2
def baseEnd_2679067 : Nat := 152849897399886096860189

theorem tailTrace_2679067 : CollatzResearch.WordTrace tailWord_2679067 prefixEnd_2679067 152849897399886096860189 := by
  unfold tailWord_2679067
  simp only [CollatzResearch.WordTrace]
  refine ⟨97713600985205282061435455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65142400656803521374290303 97713600985205282061435455)
  ·
    refine ⟨146570401477807923092153183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97713600985205282061435455 146570401477807923092153183)
    ·
      refine ⟨219855602216711884638229775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146570401477807923092153183 219855602216711884638229775)
      ·
        refine ⟨329783403325067826957344663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219855602216711884638229775 329783403325067826957344663)
        ·
          refine ⟨494675104987601740436016995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329783403325067826957344663 494675104987601740436016995)
          ·
            refine ⟨742012657481402610654025493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 494675104987601740436016995 742012657481402610654025493)
            ·
              refine ⟨34781843319440747374407445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 742012657481402610654025493 34781843319440747374407445)
              ·
                refine ⟨1630398905598785033175349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34781843319440747374407445 1630398905598785033175349)
                ·
                  refine ⟨152849897399886096860189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1630398905598785033175349 152849897399886096860189)
                  ·
                    rfl

theorem cell23_2679067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6, 5].length) (baseStart_2679067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679067 prefixEnd_2679067 := by exact prefixLift 2679067
  have htrace : WordTrace (prefixWord ++ tailWord_2679067) baseStart_2679067 baseEnd_2679067 := by
    simpa [prefixWord, tailWord_2679067, baseEnd_2679067] using wordTrace_append hprefix tailTrace_2679067
  have hstable : (prefixWord ++ tailWord_2679067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679067).length < 2 ^ (prefixWord ++ tailWord_2679067).sum := by decide
  have hdescent : baseEnd_2679067 < baseStart_2679067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679144 : List Nat := [2, 1, 4, 2, 2, 1, 1, 1, 5, 4]
def baseStart_2679144 : Nat := 118140960795 + 2679144 * 2 ^ 59
def prefixEnd_2679144 : Nat := 4983230072969 + 3 ^ 40 * 2679144 * 2
def baseEnd_2679144 : Nat := 458562871536457023492949

theorem tailTrace_2679144 : CollatzResearch.WordTrace tailWord_2679144 prefixEnd_2679144 458562871536457023492949 := by
  unfold tailWord_2679144
  simp only [CollatzResearch.WordTrace]
  refine ⟨48858204702963162105994243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65144272937284216141325657 48858204702963162105994243)
  ·
    refine ⟨73287307054444743158991365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48858204702963162105994243 73287307054444743158991365)
    ·
      refine ⟨13741370072708389342310881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73287307054444743158991365 13741370072708389342310881)
      ·
        refine ⟨10306027554531292006733161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13741370072708389342310881 10306027554531292006733161)
        ·
          refine ⟨7729520665898469005049871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10306027554531292006733161 7729520665898469005049871)
          ·
            refine ⟨11594280998847703507574807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7729520665898469005049871 11594280998847703507574807)
            ·
              refine ⟨17391421498271555261362211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11594280998847703507574807 17391421498271555261362211)
              ·
                refine ⟨26087132247407332892043317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17391421498271555261362211 26087132247407332892043317)
                ·
                  refine ⟨2445668648194437458629061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26087132247407332892043317 2445668648194437458629061)
                  ·
                    refine ⟨458562871536457023492949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2445668648194437458629061 458562871536457023492949)
                    ·
                      rfl

theorem cell23_2679144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_2679144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679144 prefixEnd_2679144 := by exact prefixLift 2679144
  have htrace : WordTrace (prefixWord ++ tailWord_2679144) baseStart_2679144 baseEnd_2679144 := by
    simpa [prefixWord, tailWord_2679144, baseEnd_2679144] using wordTrace_append hprefix tailTrace_2679144
  have hstable : (prefixWord ++ tailWord_2679144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679144).length < 2 ^ (prefixWord ++ tailWord_2679144).sum := by decide
  have hdescent : baseEnd_2679144 < baseStart_2679144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679154 : List Nat := [3, 2, 1, 2, 1, 4, 1, 1, 1, 4, 3]
def baseStart_2679154 : Nat := 118140960795 + 2679154 * 2 ^ 59
def prefixEnd_2679154 : Nat := 4983230072969 + 3 ^ 40 * 2679154 * 2
def baseEnd_2679154 : Nat := 1375693749415916031353801

theorem tailTrace_2679154 : CollatzResearch.WordTrace tailWord_2679154 prefixEnd_2679154 1375693749415916031353801 := by
  unfold tailWord_2679154
  simp only [CollatzResearch.WordTrace]
  refine ⟨24429193533972523979963129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65144516090593397279901677 24429193533972523979963129)
  ·
    refine ⟨18321895150479392984972347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24429193533972523979963129 18321895150479392984972347)
    ·
      refine ⟨27482842725719089477458521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18321895150479392984972347 27482842725719089477458521)
      ·
        refine ⟨20612132044289317108093891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27482842725719089477458521 20612132044289317108093891)
        ·
          refine ⟨30918198066433975662140837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20612132044289317108093891 30918198066433975662140837)
          ·
            refine ⟨5797162137456370436651407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30918198066433975662140837 5797162137456370436651407)
            ·
              refine ⟨8695743206184555654977111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5797162137456370436651407 8695743206184555654977111)
              ·
                refine ⟨13043614809276833482465667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8695743206184555654977111 13043614809276833482465667)
                ·
                  refine ⟨19565422213915250223698501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13043614809276833482465667 19565422213915250223698501)
                  ·
                    refine ⟨3668516665109109416943469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19565422213915250223698501 3668516665109109416943469)
                    ·
                      refine ⟨1375693749415916031353801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3668516665109109416943469 1375693749415916031353801)
                      ·
                        rfl

theorem cell23_2679154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_2679154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679154 prefixEnd_2679154 := by exact prefixLift 2679154
  have htrace : WordTrace (prefixWord ++ tailWord_2679154) baseStart_2679154 baseEnd_2679154 := by
    simpa [prefixWord, tailWord_2679154, baseEnd_2679154] using wordTrace_append hprefix tailTrace_2679154
  have hstable : (prefixWord ++ tailWord_2679154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679154).length < 2 ^ (prefixWord ++ tailWord_2679154).sum := by decide
  have hdescent : baseEnd_2679154 < baseStart_2679154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679177 : List Nat := [1, 2, 1, 1, 6, 1, 1, 1, 1, 2, 6]
def baseStart_2679177 : Nat := 118140960795 + 2679177 * 2 ^ 59
def prefixEnd_2679177 : Nat := 4983230072969 + 3 ^ 40 * 2679177 * 2
def baseEnd_2679177 : Nat := 1375705559470969441366195

theorem tailTrace_2679177 : CollatzResearch.WordTrace tailWord_2679177 prefixEnd_2679177 1375705559470969441366195 := by
  unfold tailWord_2679177
  simp only [CollatzResearch.WordTrace]
  refine ⟨97717613014806770847939785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65145075343204513898626523 97717613014806770847939785)
  ·
    refine ⟨73288209761105078135954839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97717613014806770847939785 73288209761105078135954839)
    ·
      refine ⟨109932314641657617203932259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73288209761105078135954839 109932314641657617203932259)
      ·
        refine ⟨164898471962486425805898389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109932314641657617203932259 164898471962486425805898389)
        ·
          refine ⟨7729615873241551209651487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 164898471962486425805898389 7729615873241551209651487)
          ·
            refine ⟨11594423809862326814477231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7729615873241551209651487 11594423809862326814477231)
            ·
              refine ⟨17391635714793490221715847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11594423809862326814477231 17391635714793490221715847)
              ·
                refine ⟨26087453572190235332573771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17391635714793490221715847 26087453572190235332573771)
                ·
                  refine ⟨39131180358285352998860657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26087453572190235332573771 39131180358285352998860657)
                  ·
                    refine ⟨29348385268714014749145493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39131180358285352998860657 29348385268714014749145493)
                    ·
                      refine ⟨1375705559470969441366195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29348385268714014749145493 1375705559470969441366195)
                      ·
                        rfl

theorem cell23_2679177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 2, 6].length) (baseStart_2679177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679177 prefixEnd_2679177 := by exact prefixLift 2679177
  have htrace : WordTrace (prefixWord ++ tailWord_2679177) baseStart_2679177 baseEnd_2679177 := by
    simpa [prefixWord, tailWord_2679177, baseEnd_2679177] using wordTrace_append hprefix tailTrace_2679177
  have hstable : (prefixWord ++ tailWord_2679177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679177).length < 2 ^ (prefixWord ++ tailWord_2679177).sum := by decide
  have hdescent : baseEnd_2679177 < baseStart_2679177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679178 : List Nat := [3, 1, 2, 5, 1, 1, 2, 1, 3, 4]
def baseStart_2679178 : Nat := 118140960795 + 2679178 * 2 ^ 59
def prefixEnd_2679178 : Nat := 4983230072969 + 3 ^ 40 * 2679178 * 2
def baseEnd_2679178 : Nat := 458568690983874645817897

theorem tailTrace_2679178 : CollatzResearch.WordTrace tailWord_2679178 prefixEnd_2679178 458568690983874645817897 := by
  unfold tailWord_2679178
  simp only [CollatzResearch.WordTrace]
  refine ⟨24429412371950787004681547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65145099658535432012484125 24429412371950787004681547)
  ·
    refine ⟨36644118557926180507022321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24429412371950787004681547 36644118557926180507022321)
    ·
      refine ⟨27483088918444635380266741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36644118557926180507022321 27483088918444635380266741)
      ·
        refine ⟨2576539586104184566900007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27483088918444635380266741 2576539586104184566900007)
        ·
          refine ⟨3864809379156276850350011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2576539586104184566900007 3864809379156276850350011)
          ·
            refine ⟨5797214068734415275525017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3864809379156276850350011 5797214068734415275525017)
            ·
              refine ⟨4347910551550811456643763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5797214068734415275525017 4347910551550811456643763)
              ·
                refine ⟨6521865827326217184965645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4347910551550811456643763 6521865827326217184965645)
                ·
                  refine ⟨2445699685247331444362117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6521865827326217184965645 2445699685247331444362117)
                  ·
                    refine ⟨458568690983874645817897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2445699685247331444362117 458568690983874645817897)
                    ·
                      rfl

theorem cell23_2679178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 3, 4].length) (baseStart_2679178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679178 prefixEnd_2679178 := by exact prefixLift 2679178
  have htrace : WordTrace (prefixWord ++ tailWord_2679178) baseStart_2679178 baseEnd_2679178 := by
    simpa [prefixWord, tailWord_2679178, baseEnd_2679178] using wordTrace_append hprefix tailTrace_2679178
  have hstable : (prefixWord ++ tailWord_2679178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679178).length < 2 ^ (prefixWord ++ tailWord_2679178).sum := by decide
  have hdescent : baseEnd_2679178 < baseStart_2679178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679204 : List Nat := [2, 3, 1, 2, 1, 1, 3, 4, 1, 5]
def baseStart_2679204 : Nat := 118140960795 + 2679204 * 2 ^ 59
def prefixEnd_2679204 : Nat := 4983230072969 + 3 ^ 40 * 2679204 * 2
def baseEnd_2679204 : Nat := 458573141149546945242857

theorem tailTrace_2679204 : CollatzResearch.WordTrace tailWord_2679204 prefixEnd_2679204 458573141149546945242857 := by
  unfold tailWord_2679204
  simp only [CollatzResearch.WordTrace]
  refine ⟨48859298892854477229586333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65145731857139302972781777 48859298892854477229586333)
  ·
    refine ⟨18322237084820428961094875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48859298892854477229586333 18322237084820428961094875)
    ·
      refine ⟨27483355627230643441642313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18322237084820428961094875 27483355627230643441642313)
      ·
        refine ⟨20612516720422982581231735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27483355627230643441642313 20612516720422982581231735)
        ·
          refine ⟨30918775080634473871847603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20612516720422982581231735 30918775080634473871847603)
          ·
            refine ⟨46378162620951710807771405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30918775080634473871847603 46378162620951710807771405)
            ·
              refine ⟨17391810982856891552914277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46378162620951710807771405 17391810982856891552914277)
              ·
                refine ⟨3260964559285667166171427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17391810982856891552914277 3260964559285667166171427)
                ·
                  refine ⟨4891446838928500749257141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3260964559285667166171427 4891446838928500749257141)
                  ·
                    refine ⟨458573141149546945242857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4891446838928500749257141 458573141149546945242857)
                    ·
                      rfl

theorem cell23_2679204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 4, 1, 5].length) (baseStart_2679204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679204 prefixEnd_2679204 := by exact prefixLift 2679204
  have htrace : WordTrace (prefixWord ++ tailWord_2679204) baseStart_2679204 baseEnd_2679204 := by
    simpa [prefixWord, tailWord_2679204, baseEnd_2679204] using wordTrace_append hprefix tailTrace_2679204
  have hstable : (prefixWord ++ tailWord_2679204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679204).length < 2 ^ (prefixWord ++ tailWord_2679204).sum := by decide
  have hdescent : baseEnd_2679204 < baseStart_2679204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679228 : List Nat := [2, 2, 2, 4, 1, 2, 1, 2, 2, 3, 2]
def baseStart_2679228 : Nat := 118140960795 + 2679228 * 2 ^ 59
def prefixEnd_2679228 : Nat := 4983230072969 + 3 ^ 40 * 2679228 * 2
def baseEnd_2679228 : Nat := 1375731746984348741828461

theorem tailTrace_2679228 : CollatzResearch.WordTrace tailWord_2679228 prefixEnd_2679228 1375731746984348741828461 := by
  unfold tailWord_2679228
  simp only [CollatzResearch.WordTrace]
  refine ⟨48859736568811003279023169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65146315425081337705364225 48859736568811003279023169)
  ·
    refine ⟨36644802426608252459267377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48859736568811003279023169 36644802426608252459267377)
    ·
      refine ⟨27483601819956189344450533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36644802426608252459267377 27483601819956189344450533)
      ·
        refine ⟨5153175341241785502084475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27483601819956189344450533 5153175341241785502084475)
        ·
          refine ⟨7729763011862678253126713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5153175341241785502084475 7729763011862678253126713)
          ·
            refine ⟨5797322258897008689845035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7729763011862678253126713 5797322258897008689845035)
            ·
              refine ⟨8695983388345513034767553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5797322258897008689845035 8695983388345513034767553)
              ·
                refine ⟨6521987541259134776075665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8695983388345513034767553 6521987541259134776075665)
                ·
                  refine ⟨4891490655944351082056749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6521987541259134776075665 4891490655944351082056749)
                  ·
                    refine ⟨1834308995979131655771281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4891490655944351082056749 1834308995979131655771281)
                    ·
                      refine ⟨1375731746984348741828461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1834308995979131655771281 1375731746984348741828461)
                      ·
                        rfl

theorem cell23_2679228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_2679228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679228 prefixEnd_2679228 := by exact prefixLift 2679228
  have htrace : WordTrace (prefixWord ++ tailWord_2679228) baseStart_2679228 baseEnd_2679228 := by
    simpa [prefixWord, tailWord_2679228, baseEnd_2679228] using wordTrace_append hprefix tailTrace_2679228
  have hstable : (prefixWord ++ tailWord_2679228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679228).length < 2 ^ (prefixWord ++ tailWord_2679228).sum := by decide
  have hdescent : baseEnd_2679228 < baseStart_2679228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679261 : List Nat := [1, 4, 3, 1, 1, 1, 3, 1, 3, 2, 3]
def baseStart_2679261 : Nat := 118140960795 + 2679261 * 2 ^ 59
def prefixEnd_2679261 : Nat := 4983230072969 + 3 ^ 40 * 2679261 * 2
def baseEnd_2679261 : Nat := 1375748691845947112715809

theorem tailTrace_2679261 : CollatzResearch.WordTrace tailWord_2679261 prefixEnd_2679261 1375748691845947112715809 := by
  unfold tailWord_2679261
  simp only [CollatzResearch.WordTrace]
  refine ⟨97720676746502453193997637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65147117831001635462665091 97720676746502453193997637)
  ·
    refine ⟨18322626889969209973874557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97720676746502453193997637 18322626889969209973874557)
    ·
      refine ⟨6870985083738453740202959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18322626889969209973874557 6870985083738453740202959)
      ·
        refine ⟨10306477625607680610304439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6870985083738453740202959 10306477625607680610304439)
        ·
          refine ⟨15459716438411520915456659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10306477625607680610304439 15459716438411520915456659)
          ·
            refine ⟨23189574657617281373184989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15459716438411520915456659 23189574657617281373184989)
            ·
              refine ⟨8696090496606480514944371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23189574657617281373184989 8696090496606480514944371)
              ·
                refine ⟨13044135744909720772416557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8696090496606480514944371 13044135744909720772416557)
                ·
                  refine ⟨4891550904341145289656209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13044135744909720772416557 4891550904341145289656209)
                  ·
                    refine ⟨3668663178255858967242157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4891550904341145289656209 3668663178255858967242157)
                    ·
                      refine ⟨1375748691845947112715809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3668663178255858967242157 1375748691845947112715809)
                      ·
                        rfl

theorem cell23_2679261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_2679261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679261 prefixEnd_2679261 := by exact prefixLift 2679261
  have htrace : WordTrace (prefixWord ++ tailWord_2679261) baseStart_2679261 baseEnd_2679261 := by
    simpa [prefixWord, tailWord_2679261, baseEnd_2679261] using wordTrace_append hprefix tailTrace_2679261
  have hstable : (prefixWord ++ tailWord_2679261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679261).length < 2 ^ (prefixWord ++ tailWord_2679261).sum := by decide
  have hdescent : baseEnd_2679261 < baseStart_2679261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679285 : List Nat := [1, 3, 5, 1, 2, 1, 2, 2, 2, 4]
def baseStart_2679285 : Nat := 118140960795 + 2679285 * 2 ^ 59
def prefixEnd_2679285 : Nat := 4983230072969 + 3 ^ 40 * 2679285 * 2
def baseEnd_2679285 : Nat := 458587005127218339605233

theorem tailTrace_2679285 : CollatzResearch.WordTrace tailWord_2679285 prefixEnd_2679285 458587005127218339605233 := by
  unfold tailWord_2679285
  simp only [CollatzResearch.WordTrace]
  refine ⟨97721552098415505292871309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65147701398943670195247539 97721552098415505292871309)
  ·
    refine ⟨36645582036905814484826741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97721552098415505292871309 36645582036905814484826741)
    ·
      refine ⟨3435523315959920107952507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36645582036905814484826741 3435523315959920107952507)
      ·
        refine ⟨5153284973939880161928761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3435523315959920107952507 5153284973939880161928761)
        ·
          refine ⟨3864963730454910121446571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5153284973939880161928761 3864963730454910121446571)
          ·
            refine ⟨5797445595682365182169857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3864963730454910121446571 5797445595682365182169857)
            ·
              refine ⟨4348084196761773886627393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5797445595682365182169857 4348084196761773886627393)
              ·
                refine ⟨3261063147571330414970545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4348084196761773886627393 3261063147571330414970545)
                ·
                  refine ⟨2445797360678497811227909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3261063147571330414970545 2445797360678497811227909)
                  ·
                    refine ⟨458587005127218339605233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2445797360678497811227909 458587005127218339605233)
                    ·
                      rfl

theorem cell23_2679285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_2679285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679285 prefixEnd_2679285 := by exact prefixLift 2679285
  have htrace : WordTrace (prefixWord ++ tailWord_2679285) baseStart_2679285 baseEnd_2679285 := by
    simpa [prefixWord, tailWord_2679285, baseEnd_2679285] using wordTrace_append hprefix tailTrace_2679285
  have hstable : (prefixWord ++ tailWord_2679285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679285).length < 2 ^ (prefixWord ++ tailWord_2679285).sum := by decide
  have hdescent : baseEnd_2679285 < baseStart_2679285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679287 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 5]
def baseStart_2679287 : Nat := 118140960795 + 2679287 * 2 ^ 59
def prefixEnd_2679287 : Nat := 4983230072969 + 3 ^ 40 * 2679287 * 2
def baseEnd_2679287 : Nat := 1375762042342964010990689

theorem tailTrace_2679287 : CollatzResearch.WordTrace tailWord_2679287 prefixEnd_2679287 1375762042342964010990689 := by
  unfold tailWord_2679287
  simp only [CollatzResearch.WordTrace]
  refine ⟨97721625044408259634444115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65147750029605506422962743 97721625044408259634444115)
  ·
    refine ⟨146582437566612389451666173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97721625044408259634444115 146582437566612389451666173)
    ·
      refine ⟨54968414087479646044374815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146582437566612389451666173 54968414087479646044374815)
      ·
        refine ⟨82452621131219469066562223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54968414087479646044374815 82452621131219469066562223)
        ·
          refine ⟨123678931696829203599843335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82452621131219469066562223 123678931696829203599843335)
          ·
            refine ⟨185518397545243805399765003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123678931696829203599843335 185518397545243805399765003)
            ·
              refine ⟨278277596317865708099647505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185518397545243805399765003 278277596317865708099647505)
              ·
                refine ⟨208708197238399281074735629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 278277596317865708099647505 208708197238399281074735629)
                ·
                  refine ⟨78265573964399730403025861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 208708197238399281074735629 78265573964399730403025861)
                  ·
                    refine ⟨14674795118324949450567349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 78265573964399730403025861 14674795118324949450567349)
                    ·
                      refine ⟨1375762042342964010990689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14674795118324949450567349 1375762042342964010990689)
                      ·
                        rfl

theorem cell23_2679287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_2679287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679287 prefixEnd_2679287 := by exact prefixLift 2679287
  have htrace : WordTrace (prefixWord ++ tailWord_2679287) baseStart_2679287 baseEnd_2679287 := by
    simpa [prefixWord, tailWord_2679287, baseEnd_2679287] using wordTrace_append hprefix tailTrace_2679287
  have hstable : (prefixWord ++ tailWord_2679287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679287).length < 2 ^ (prefixWord ++ tailWord_2679287).sum := by decide
  have hdescent : baseEnd_2679287 < baseStart_2679287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679298 : List Nat := [3, 4, 1, 2, 2, 2, 1, 8]
def baseStart_2679298 : Nat := 118140960795 + 2679298 * 2 ^ 59
def prefixEnd_2679298 : Nat := 4983230072969 + 3 ^ 40 * 2679298 * 2
def baseEnd_2679298 : Nat := 50954358912228276590857

theorem tailTrace_2679298 : CollatzResearch.WordTrace tailWord_2679298 prefixEnd_2679298 50954358912228276590857 := by
  unfold tailWord_2679298
  simp only [CollatzResearch.WordTrace]
  refine ⟨24430506561842102128273637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65148017498245605675396365 24430506561842102128273637)
  ·
    refine ⟨4580719980345394149051307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24430506561842102128273637 4580719980345394149051307)
    ·
      refine ⟨6871079970518091223576961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4580719980345394149051307 6871079970518091223576961)
      ·
        refine ⟨5153309977888568417682721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6871079970518091223576961 5153309977888568417682721)
        ·
          refine ⟨3864982483416426313262041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5153309977888568417682721 3864982483416426313262041)
          ·
            refine ⟨2898736862562319734946531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3864982483416426313262041 2898736862562319734946531)
            ·
              refine ⟨4348105293843479602419797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2898736862562319734946531 4348105293843479602419797)
              ·
                refine ⟨50954358912228276590857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4348105293843479602419797 50954358912228276590857)
                ·
                  rfl

theorem cell23_2679298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 8].length) (baseStart_2679298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679298 prefixEnd_2679298 := by exact prefixLift 2679298
  have htrace : WordTrace (prefixWord ++ tailWord_2679298) baseStart_2679298 baseEnd_2679298 := by
    simpa [prefixWord, tailWord_2679298, baseEnd_2679298] using wordTrace_append hprefix tailTrace_2679298
  have hstable : (prefixWord ++ tailWord_2679298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679298).length < 2 ^ (prefixWord ++ tailWord_2679298).sum := by decide
  have hdescent : baseEnd_2679298 < baseStart_2679298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679301 : List Nat := [1, 3, 1, 1, 2, 2, 3, 2, 3, 3, 2]
def baseStart_2679301 : Nat := 118140960795 + 2679301 * 2 ^ 59
def prefixEnd_2679301 : Nat := 4983230072969 + 3 ^ 40 * 2679301 * 2
def baseEnd_2679301 : Nat := 1375769231072126956215625

theorem tailTrace_2679301 : CollatzResearch.WordTrace tailWord_2679301 prefixEnd_2679301 1375769231072126956215625 := by
  unfold tailWord_2679301
  simp only [CollatzResearch.WordTrace]
  refine ⟨97722135666357540025453757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65148090444238360016969171 97722135666357540025453757)
  ·
    refine ⟨36645800874884077509545159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97722135666357540025453757 36645800874884077509545159)
    ·
      refine ⟨54968701312326116264317739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36645800874884077509545159 54968701312326116264317739)
      ·
        refine ⟨82453051968489174396476609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54968701312326116264317739 82453051968489174396476609)
        ·
          refine ⟨61839788976366880797357457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82453051968489174396476609 61839788976366880797357457)
          ·
            refine ⟨46379841732275160598018093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61839788976366880797357457 46379841732275160598018093)
            ·
              refine ⟨17392440649603185224256785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46379841732275160598018093 17392440649603185224256785)
              ·
                refine ⟨13044330487202388918192589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17392440649603185224256785 13044330487202388918192589)
                ·
                  refine ⟨4891623932700895844322221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13044330487202388918192589 4891623932700895844322221)
                  ·
                    refine ⟨1834358974762835941620833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4891623932700895844322221 1834358974762835941620833)
                    ·
                      refine ⟨1375769231072126956215625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1834358974762835941620833 1375769231072126956215625)
                      ·
                        rfl

theorem cell23_2679301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 3, 3, 2].length) (baseStart_2679301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679301 prefixEnd_2679301 := by exact prefixLift 2679301
  have htrace : WordTrace (prefixWord ++ tailWord_2679301) baseStart_2679301 baseEnd_2679301 := by
    simpa [prefixWord, tailWord_2679301, baseEnd_2679301] using wordTrace_append hprefix tailTrace_2679301
  have hstable : (prefixWord ++ tailWord_2679301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679301).length < 2 ^ (prefixWord ++ tailWord_2679301).sum := by decide
  have hdescent : baseEnd_2679301 < baseStart_2679301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679302 : List Nat := [6, 2, 1, 1, 1, 1, 2, 3, 2, 4]
def baseStart_2679302 : Nat := 118140960795 + 2679302 * 2 ^ 59
def prefixEnd_2679302 : Nat := 4983230072969 + 3 ^ 40 * 2679302 * 2
def baseEnd_2679302 : Nat := 458589914850927150767707

theorem tailTrace_2679302 : CollatzResearch.WordTrace tailWord_2679302 prefixEnd_2679302 458589914850927150767707 := by
  unfold tailWord_2679302
  simp only [CollatzResearch.WordTrace]
  refine ⟨3053817879354809912382505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 65148114759569278130826773 3053817879354809912382505)
  ·
    refine ⟨2290363409516107434286879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3053817879354809912382505 2290363409516107434286879)
    ·
      refine ⟨3435545114274161151430319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2290363409516107434286879 3435545114274161151430319)
      ·
        refine ⟨5153317671411241727145479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3435545114274161151430319 5153317671411241727145479)
        ·
          refine ⟨7729976507116862590718219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5153317671411241727145479 7729976507116862590718219)
          ·
            refine ⟨11594964760675293886077329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7729976507116862590718219 11594964760675293886077329)
            ·
              refine ⟨8696223570506470414557997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11594964760675293886077329 8696223570506470414557997)
              ·
                refine ⟨3261083838939926405459249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8696223570506470414557997 3261083838939926405459249)
                ·
                  refine ⟨2445812879204944804094437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3261083838939926405459249 2445812879204944804094437)
                  ·
                    refine ⟨458589914850927150767707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2445812879204944804094437 458589914850927150767707)
                    ·
                      rfl

theorem cell23_2679302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_2679302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679302 prefixEnd_2679302 := by exact prefixLift 2679302
  have htrace : WordTrace (prefixWord ++ tailWord_2679302) baseStart_2679302 baseEnd_2679302 := by
    simpa [prefixWord, tailWord_2679302, baseEnd_2679302] using wordTrace_append hprefix tailTrace_2679302
  have hstable : (prefixWord ++ tailWord_2679302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679302).length < 2 ^ (prefixWord ++ tailWord_2679302).sum := by decide
  have hdescent : baseEnd_2679302 < baseStart_2679302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679308 : List Nat := [2, 2, 1, 2, 4, 1, 2, 3, 2, 1, 3]
def baseStart_2679308 : Nat := 118140960795 + 2679308 * 2 ^ 59
def prefixEnd_2679308 : Nat := 4983230072969 + 3 ^ 40 * 2679308 * 2
def baseEnd_2679308 : Nat := 1375772825436708428828093

theorem tailTrace_2679308 : CollatzResearch.WordTrace tailWord_2679308 prefixEnd_2679308 1375772825436708428828093 := by
  unfold tailWord_2679308
  simp only [CollatzResearch.WordTrace]
  refine ⟨48861195488666090110479289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65148260651554786813972385 48861195488666090110479289)
  ·
    refine ⟨36645896616499567582859467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48861195488666090110479289 36645896616499567582859467)
    ·
      refine ⟨54968844924749351374289201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36645896616499567582859467 54968844924749351374289201)
      ·
        refine ⟨41226633693562013530716901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54968844924749351374289201 41226633693562013530716901)
        ·
          refine ⟨7729993817542877537009419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41226633693562013530716901 7729993817542877537009419)
          ·
            refine ⟨11594990726314316305514129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7729993817542877537009419 11594990726314316305514129)
            ·
              refine ⟨8696243044735737229135597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11594990726314316305514129 8696243044735737229135597)
              ·
                refine ⟨3261091141775901460925849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8696243044735737229135597 3261091141775901460925849)
                ·
                  refine ⟨2445818356331926095694387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3261091141775901460925849 2445818356331926095694387)
                  ·
                    refine ⟨3668727534497889143541581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2445818356331926095694387 3668727534497889143541581)
                    ·
                      refine ⟨1375772825436708428828093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3668727534497889143541581 1375772825436708428828093)
                      ·
                        rfl

theorem cell23_2679308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 3, 2, 1, 3].length) (baseStart_2679308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679308 prefixEnd_2679308 := by exact prefixLift 2679308
  have htrace : WordTrace (prefixWord ++ tailWord_2679308) baseStart_2679308 baseEnd_2679308 := by
    simpa [prefixWord, tailWord_2679308, baseEnd_2679308] using wordTrace_append hprefix tailTrace_2679308
  have hstable : (prefixWord ++ tailWord_2679308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679308).length < 2 ^ (prefixWord ++ tailWord_2679308).sum := by decide
  have hdescent : baseEnd_2679308 < baseStart_2679308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679342 : List Nat := [4, 1, 3, 1, 3, 2, 1, 2, 2, 1, 3]
def baseStart_2679342 : Nat := 118140960795 + 2679342 * 2 ^ 59
def prefixEnd_2679342 : Nat := 4983230072969 + 3 ^ 40 * 2679342 * 2
def baseEnd_2679342 : Nat := 1375790283778961295802937

theorem tailTrace_2679342 : CollatzResearch.WordTrace tailWord_2679342 prefixEnd_2679342 1375790283778961295802937 := by
  unfold tailWord_2679342
  simp only [CollatzResearch.WordTrace]
  refine ⟨12215453882401125503462035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65149087372806002685130853 12215453882401125503462035)
  ·
    refine ⟨18323180823601688255193053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12215453882401125503462035 18323180823601688255193053)
    ·
      refine ⟨6871192808850633095697395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18323180823601688255193053 6871192808850633095697395)
      ·
        refine ⟨10306789213275949643546093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6871192808850633095697395 10306789213275949643546093)
        ·
          refine ⟨3865045954978481116329785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10306789213275949643546093 3865045954978481116329785)
          ·
            refine ⟨2898784466233860837247339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3865045954978481116329785 2898784466233860837247339)
            ·
              refine ⟨4348176699350791255871009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2898784466233860837247339 4348176699350791255871009)
              ·
                refine ⟨3261132524513093441903257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4348176699350791255871009 3261132524513093441903257)
                ·
                  refine ⟨2445849393384820081427443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3261132524513093441903257 2445849393384820081427443)
                  ·
                    refine ⟨3668774090077230122141165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2445849393384820081427443 3668774090077230122141165)
                    ·
                      refine ⟨1375790283778961295802937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3668774090077230122141165 1375790283778961295802937)
                      ·
                        rfl

theorem cell23_2679342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_2679342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679342 prefixEnd_2679342 := by exact prefixLift 2679342
  have htrace : WordTrace (prefixWord ++ tailWord_2679342) baseStart_2679342 baseEnd_2679342 := by
    simpa [prefixWord, tailWord_2679342, baseEnd_2679342] using wordTrace_append hprefix tailTrace_2679342
  have hstable : (prefixWord ++ tailWord_2679342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679342).length < 2 ^ (prefixWord ++ tailWord_2679342).sum := by decide
  have hdescent : baseEnd_2679342 < baseStart_2679342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679344 : List Nat := [2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 4]
def baseStart_2679344 : Nat := 118140960795 + 2679344 * 2 ^ 59
def prefixEnd_2679344 : Nat := 4983230072969 + 3 ^ 40 * 2679344 * 2
def baseEnd_2679344 : Nat := 1375791310740270287977927

theorem tailTrace_2679344 : CollatzResearch.WordTrace tailWord_2679344 prefixEnd_2679344 1375791310740270287977927 := by
  unfold tailWord_2679344
  simp only [CollatzResearch.WordTrace]
  refine ⟨48861852002600879184634543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65149136003467838912846057 48861852002600879184634543)
  ·
    refine ⟨73292778003901318776951815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48861852002600879184634543 73292778003901318776951815)
    ·
      refine ⟨109939167005851978165427723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73292778003901318776951815 109939167005851978165427723)
      ·
        refine ⟨164908750508777967248141585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109939167005851978165427723 164908750508777967248141585)
        ·
          refine ⟨123681562881583475436106189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164908750508777967248141585 123681562881583475436106189)
          ·
            refine ⟨46380586080593803288539821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123681562881583475436106189 46380586080593803288539821)
            ·
              refine ⟨17392719780222676233202433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46380586080593803288539821 17392719780222676233202433)
              ·
                refine ⟨13044539835167007174901825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17392719780222676233202433 13044539835167007174901825)
                ·
                  refine ⟨9783404876375255381176369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13044539835167007174901825 9783404876375255381176369)
                  ·
                    refine ⟨7337553657281441535882277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9783404876375255381176369 7337553657281441535882277)
                    ·
                      refine ⟨1375791310740270287977927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7337553657281441535882277 1375791310740270287977927)
                      ·
                        rfl

theorem cell23_2679344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 4].length) (baseStart_2679344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679344 prefixEnd_2679344 := by exact prefixLift 2679344
  have htrace : WordTrace (prefixWord ++ tailWord_2679344) baseStart_2679344 baseEnd_2679344 := by
    simpa [prefixWord, tailWord_2679344, baseEnd_2679344] using wordTrace_append hprefix tailTrace_2679344
  have hstable : (prefixWord ++ tailWord_2679344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679344).length < 2 ^ (prefixWord ++ tailWord_2679344).sum := by decide
  have hdescent : baseEnd_2679344 < baseStart_2679344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679354 : List Nat := [3, 1, 1, 1, 3, 3, 1, 3, 7]
def baseStart_2679354 : Nat := 118140960795 + 2679354 * 2 ^ 59
def prefixEnd_2679354 : Nat := 4983230072969 + 3 ^ 40 * 2679354 * 2
def baseEnd_2679354 : Nat := 152866271727423916539209

theorem tailTrace_2679354 : CollatzResearch.WordTrace tailWord_2679354 prefixEnd_2679354 152866271727423916539209 := by
  unfold tailWord_2679354
  simp only [CollatzResearch.WordTrace]
  refine ⟨24431017183791382519283279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65149379156777020051422077 24431017183791382519283279)
  ·
    refine ⟨36646525775687073778924919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24431017183791382519283279 36646525775687073778924919)
    ·
      refine ⟨54969788663530610668387379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36646525775687073778924919 54969788663530610668387379)
      ·
        refine ⟨82454682995295916002581069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54969788663530610668387379 82454682995295916002581069)
        ·
          refine ⟨30920506123235968500967901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82454682995295916002581069 30920506123235968500967901)
          ·
            refine ⟨11595189796213488187862963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30920506123235968500967901 11595189796213488187862963)
            ·
              refine ⟨17392784694320232281794445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11595189796213488187862963 17392784694320232281794445)
              ·
                refine ⟨6522294260370087105672917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17392784694320232281794445 6522294260370087105672917)
                ·
                  refine ⟨152866271727423916539209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6522294260370087105672917 152866271727423916539209)
                  ·
                    rfl

theorem cell23_2679354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 7].length) (baseStart_2679354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679354 prefixEnd_2679354 := by exact prefixLift 2679354
  have htrace : WordTrace (prefixWord ++ tailWord_2679354) baseStart_2679354 baseEnd_2679354 := by
    simpa [prefixWord, tailWord_2679354, baseEnd_2679354] using wordTrace_append hprefix tailTrace_2679354
  have hstable : (prefixWord ++ tailWord_2679354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679354).length < 2 ^ (prefixWord ++ tailWord_2679354).sum := by decide
  have hdescent : baseEnd_2679354 < baseStart_2679354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679361 : List Nat := [1, 2, 5, 1, 1, 2, 2, 1, 2, 2, 4]
def baseStart_2679361 : Nat := 118140960795 + 2679361 * 2 ^ 59
def prefixEnd_2679361 : Nat := 4983230072969 + 3 ^ 40 * 2679361 * 2
def baseEnd_2679361 : Nat := 1375800039911396721465349

theorem tailTrace_2679361 : CollatzResearch.WordTrace tailWord_2679361 prefixEnd_2679361 1375800039911396721465349 := by
  unfold tailWord_2679361
  simp only [CollatzResearch.WordTrace]
  refine ⟨97724324046140170272637937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65149549364093446848425291 97724324046140170272637937)
  ·
    refine ⟨73293243034605127704478453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97724324046140170272637937 73293243034605127704478453)
    ·
      refine ⟨6871241534494230722294855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73293243034605127704478453 6871241534494230722294855)
      ·
        refine ⟨10306862301741346083442283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6871241534494230722294855 10306862301741346083442283)
        ·
          refine ⟨15460293452612019125163425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10306862301741346083442283 15460293452612019125163425)
          ·
            refine ⟨11595220089459014343872569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15460293452612019125163425 11595220089459014343872569)
            ·
              refine ⟨8696415067094260757904427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11595220089459014343872569 8696415067094260757904427)
              ·
                refine ⟨13044622600641391136856641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8696415067094260757904427 13044622600641391136856641)
                ·
                  refine ⟨9783466950481043352642481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13044622600641391136856641 9783466950481043352642481)
                  ·
                    refine ⟨7337600212860782514481861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9783466950481043352642481 7337600212860782514481861)
                    ·
                      refine ⟨1375800039911396721465349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7337600212860782514481861 1375800039911396721465349)
                      ·
                        rfl

theorem cell23_2679361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_2679361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679361 prefixEnd_2679361 := by exact prefixLift 2679361
  have htrace : WordTrace (prefixWord ++ tailWord_2679361) baseStart_2679361 baseEnd_2679361 := by
    simpa [prefixWord, tailWord_2679361, baseEnd_2679361] using wordTrace_append hprefix tailTrace_2679361
  have hstable : (prefixWord ++ tailWord_2679361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679361).length < 2 ^ (prefixWord ++ tailWord_2679361).sum := by decide
  have hdescent : baseEnd_2679361 < baseStart_2679361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679384 : List Nat := [2, 1, 2, 2, 1, 2, 4, 1, 1, 7]
def baseStart_2679384 : Nat := 118140960795 + 2679384 * 2 ^ 59
def prefixEnd_2679384 : Nat := 4983230072969 + 3 ^ 40 * 2679384 * 2
def baseEnd_2679384 : Nat := 458603949988816710492581

theorem tailTrace_2679384 : CollatzResearch.WordTrace tailWord_2679384 prefixEnd_2679384 458603949988816710492581 := by
  unfold tailWord_2679384
  simp only [CollatzResearch.WordTrace]
  refine ⟨48862581462528422600362603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65150108616704563467150137 48862581462528422600362603)
  ·
    refine ⟨73293872193792633900543905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48862581462528422600362603 73293872193792633900543905)
    ·
      refine ⟨54970404145344475425407929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73293872193792633900543905 54970404145344475425407929)
      ·
        refine ⟨41227803109008356569055947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54970404145344475425407929 41227803109008356569055947)
        ·
          refine ⟨61841704663512534853583921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41227803109008356569055947 61841704663512534853583921)
          ·
            refine ⟨46381278497634401140187941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61841704663512534853583921 46381278497634401140187941)
            ·
              refine ⟨8696489718306450213785239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46381278497634401140187941 8696489718306450213785239)
              ·
                refine ⟨13044734577459675320677859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8696489718306450213785239 13044734577459675320677859)
                ·
                  refine ⟨19567101866189512981016789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13044734577459675320677859 19567101866189512981016789)
                  ·
                    refine ⟨458603949988816710492581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19567101866189512981016789 458603949988816710492581)
                    ·
                      rfl

theorem cell23_2679384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 1, 7].length) (baseStart_2679384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679384 prefixEnd_2679384 := by exact prefixLift 2679384
  have htrace : WordTrace (prefixWord ++ tailWord_2679384) baseStart_2679384 baseEnd_2679384 := by
    simpa [prefixWord, tailWord_2679384, baseEnd_2679384] using wordTrace_append hprefix tailTrace_2679384
  have hstable : (prefixWord ++ tailWord_2679384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679384).length < 2 ^ (prefixWord ++ tailWord_2679384).sum := by decide
  have hdescent : baseEnd_2679384 < baseStart_2679384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679405 : List Nat := [1, 5, 1, 1, 3, 2, 3, 2, 5]
def baseStart_2679405 : Nat := 118140960795 + 2679405 * 2 ^ 59
def prefixEnd_2679405 : Nat := 4983230072969 + 3 ^ 40 * 2679405 * 2
def baseEnd_2679405 : Nat := 152869181451132727701683

theorem tailTrace_2679405 : CollatzResearch.WordTrace tailWord_2679405 prefixEnd_2679405 152869181451132727701683 := by
  unfold tailWord_2679405
  simp only [CollatzResearch.WordTrace]
  refine ⟨97725928857980765787239669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65150619238653843858159779 97725928857980765787239669)
  ·
    refine ⟨9161805830435696792553719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97725928857980765787239669 9161805830435696792553719)
    ·
      refine ⟨13742708745653545188830579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9161805830435696792553719 13742708745653545188830579)
      ·
        refine ⟨20614063118480317783245869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13742708745653545188830579 20614063118480317783245869)
        ·
          refine ⟨7730273669430119168717201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20614063118480317783245869 7730273669430119168717201)
          ·
            refine ⟨5797705252072589376537901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7730273669430119168717201 5797705252072589376537901)
            ·
              refine ⟨2174139469527221016201713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5797705252072589376537901 2174139469527221016201713)
              ·
                refine ⟨1630604602145415762151285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2174139469527221016201713 1630604602145415762151285)
                ·
                  refine ⟨152869181451132727701683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1630604602145415762151285 152869181451132727701683)
                  ·
                    rfl

theorem cell23_2679405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_2679405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679405 prefixEnd_2679405 := by exact prefixLift 2679405
  have htrace : WordTrace (prefixWord ++ tailWord_2679405) baseStart_2679405 baseEnd_2679405 := by
    simpa [prefixWord, tailWord_2679405, baseEnd_2679405] using wordTrace_append hprefix tailTrace_2679405
  have hstable : (prefixWord ++ tailWord_2679405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679405).length < 2 ^ (prefixWord ++ tailWord_2679405).sum := by decide
  have hdescent : baseEnd_2679405 < baseStart_2679405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679431 : List Nat := [1, 1, 4, 2, 1, 2, 2, 1, 5, 4]
def baseStart_2679431 : Nat := 118140960795 + 2679431 * 2 ^ 59
def prefixEnd_2679431 : Nat := 4983230072969 + 3 ^ 40 * 2679431 * 2
def baseEnd_2679431 : Nat := 458611994519070482530009

theorem tailTrace_2679431 : CollatzResearch.WordTrace tailWord_2679431 prefixEnd_2679431 458611994519070482530009 := by
  unfold tailWord_2679431
  simp only [CollatzResearch.WordTrace]
  refine ⟨97726877155886572227686147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65151251437257714818457431 97726877155886572227686147)
  ·
    refine ⟨146590315733829858341529221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97726877155886572227686147 146590315733829858341529221)
    ·
      refine ⟨27485684200093098439036729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146590315733829858341529221 27485684200093098439036729)
      ·
        refine ⟨20614263150069823829277547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27485684200093098439036729 20614263150069823829277547)
        ·
          refine ⟨30921394725104735743916321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20614263150069823829277547 30921394725104735743916321)
          ·
            refine ⟨23191046043828551807937241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30921394725104735743916321 23191046043828551807937241)
            ·
              refine ⟨17393284532871413855952931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23191046043828551807937241 17393284532871413855952931)
              ·
                refine ⟨26089926799307120783929397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17393284532871413855952931 26089926799307120783929397)
                ·
                  refine ⟨2445930637435042573493381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26089926799307120783929397 2445930637435042573493381)
                  ·
                    refine ⟨458611994519070482530009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2445930637435042573493381 458611994519070482530009)
                    ·
                      rfl

theorem cell23_2679431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 5, 4].length) (baseStart_2679431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679431 prefixEnd_2679431 := by exact prefixLift 2679431
  have htrace : WordTrace (prefixWord ++ tailWord_2679431) baseStart_2679431 baseEnd_2679431 := by
    simpa [prefixWord, tailWord_2679431, baseEnd_2679431] using wordTrace_append hprefix tailTrace_2679431
  have hstable : (prefixWord ++ tailWord_2679431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679431).length < 2 ^ (prefixWord ++ tailWord_2679431).sum := by decide
  have hdescent : baseEnd_2679431 < baseStart_2679431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679438 : List Nat := [4, 1, 1, 3, 1, 1, 4, 1, 2, 1, 4]
def baseStart_2679438 : Nat := 118140960795 + 2679438 * 2 ^ 59
def prefixEnd_2679438 : Nat := 4983230072969 + 3 ^ 40 * 2679438 * 2
def baseEnd_2679438 : Nat := 1375839577921792920202495

theorem tailTrace_2679438 : CollatzResearch.WordTrace tailWord_2679438 prefixEnd_2679438 1375839577921792920202495 := by
  unfold tailWord_2679438
  simp only [CollatzResearch.WordTrace]
  refine ⟨12215891558357651552898871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65151421644574141615460645 12215891558357651552898871)
  ·
    refine ⟨18323837337536477329348307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12215891558357651552898871 18323837337536477329348307)
    ·
      refine ⟨27485756006304715994022461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18323837337536477329348307 27485756006304715994022461)
      ·
        refine ⟨10307158502364268497758423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27485756006304715994022461 10307158502364268497758423)
        ·
          refine ⟨15460737753546402746637635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10307158502364268497758423 15460737753546402746637635)
          ·
            refine ⟨23191106630319604119956453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15460737753546402746637635 23191106630319604119956453)
            ·
              refine ⟨4348332493184925772491835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23191106630319604119956453 4348332493184925772491835)
              ·
                refine ⟨6522498739777388658737753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4348332493184925772491835 6522498739777388658737753)
                ·
                  refine ⟨4891874054833041494053315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6522498739777388658737753 4891874054833041494053315)
                  ·
                    refine ⟨7337811082249562241079973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4891874054833041494053315 7337811082249562241079973)
                    ·
                      refine ⟨1375839577921792920202495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7337811082249562241079973 1375839577921792920202495)
                      ·
                        rfl

theorem cell23_2679438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_2679438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679438 prefixEnd_2679438 := by exact prefixLift 2679438
  have htrace : WordTrace (prefixWord ++ tailWord_2679438) baseStart_2679438 baseEnd_2679438 := by
    simpa [prefixWord, tailWord_2679438, baseEnd_2679438] using wordTrace_append hprefix tailTrace_2679438
  have hstable : (prefixWord ++ tailWord_2679438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679438).length < 2 ^ (prefixWord ++ tailWord_2679438).sum := by decide
  have hdescent : baseEnd_2679438 < baseStart_2679438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679488 : List Nat := [2, 1, 1, 2, 4, 2, 1, 1, 5, 1, 3]
def baseStart_2679488 : Nat := 118140960795 + 2679488 * 2 ^ 59
def prefixEnd_2679488 : Nat := 4983230072969 + 3 ^ 40 * 2679488 * 2
def baseEnd_2679488 : Nat := 1375865251954517724577265

theorem tailTrace_2679488 : CollatzResearch.WordTrace tailWord_2679488 prefixEnd_2679488 1375865251954517724577265 := by
  unfold tailWord_2679488
  simp only [CollatzResearch.WordTrace]
  refine ⟨48864478058340035481255559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65152637411120047308340745 48864478058340035481255559)
  ·
    refine ⟨73296717087510053221883339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48864478058340035481255559 73296717087510053221883339)
    ·
      refine ⟨109945075631265079832825009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73296717087510053221883339 109945075631265079832825009)
      ·
        refine ⟨82458806723448809874618757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109945075631265079832825009 82458806723448809874618757)
        ·
          refine ⟨15461026260646651851491017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82458806723448809874618757 15461026260646651851491017)
          ·
            refine ⟨11595769695484988888618263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15461026260646651851491017 11595769695484988888618263)
            ·
              refine ⟨17393654543227483332927395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11595769695484988888618263 17393654543227483332927395)
              ·
                refine ⟨26090481814841224999391093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17393654543227483332927395 26090481814841224999391093)
                ·
                  refine ⟨2445982670141364843692915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26090481814841224999391093 2445982670141364843692915)
                  ·
                    refine ⟨3668974005212047265539373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2445982670141364843692915 3668974005212047265539373)
                    ·
                      refine ⟨1375865251954517724577265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3668974005212047265539373 1375865251954517724577265)
                      ·
                        rfl

theorem cell23_2679488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 5, 1, 3].length) (baseStart_2679488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679488 prefixEnd_2679488 := by exact prefixLift 2679488
  have htrace : WordTrace (prefixWord ++ tailWord_2679488) baseStart_2679488 baseEnd_2679488 := by
    simpa [prefixWord, tailWord_2679488, baseEnd_2679488] using wordTrace_append hprefix tailTrace_2679488
  have hstable : (prefixWord ++ tailWord_2679488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679488).length < 2 ^ (prefixWord ++ tailWord_2679488).sum := by decide
  have hdescent : baseEnd_2679488 < baseStart_2679488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679489 : List Nat := [1, 2, 6, 2, 2, 1, 1, 1, 2, 1, 4]
def baseStart_2679489 : Nat := 118140960795 + 2679489 * 2 ^ 59
def prefixEnd_2679489 : Nat := 4983230072969 + 3 ^ 40 * 2679489 * 2
def baseEnd_2679489 : Nat := 1375865765435172220664761

theorem tailTrace_2679489 : CollatzResearch.WordTrace tailWord_2679489 prefixEnd_2679489 1375865765435172220664761 := by
  unfold tailWord_2679489
  simp only [CollatzResearch.WordTrace]
  refine ⟨97728992589676448133297521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65152661726450965422198347 97728992589676448133297521)
  ·
    refine ⟨73296744442257336099973141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97728992589676448133297521 73296744442257336099973141)
    ·
      refine ⟨3435784895730812629686241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 73296744442257336099973141 3435784895730812629686241)
      ·
        refine ⟨2576838671798109472264681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3435784895730812629686241 2576838671798109472264681)
        ·
          refine ⟨1932629003848582104198511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2576838671798109472264681 1932629003848582104198511)
          ·
            refine ⟨2898943505772873156297767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1932629003848582104198511 2898943505772873156297767)
            ·
              refine ⟨4348415258659309734446651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2898943505772873156297767 4348415258659309734446651)
              ·
                refine ⟨6522622887988964601669977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4348415258659309734446651 6522622887988964601669977)
                ·
                  refine ⟨4891967165991723451252483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6522622887988964601669977 4891967165991723451252483)
                  ·
                    refine ⟨7337950748987585176878725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4891967165991723451252483 7337950748987585176878725)
                    ·
                      refine ⟨1375865765435172220664761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7337950748987585176878725 1375865765435172220664761)
                      ·
                        rfl

theorem cell23_2679489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_2679489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679489 prefixEnd_2679489 := by exact prefixLift 2679489
  have htrace : WordTrace (prefixWord ++ tailWord_2679489) baseStart_2679489 baseEnd_2679489 := by
    simpa [prefixWord, tailWord_2679489, baseEnd_2679489] using wordTrace_append hprefix tailTrace_2679489
  have hstable : (prefixWord ++ tailWord_2679489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679489).length < 2 ^ (prefixWord ++ tailWord_2679489).sum := by decide
  have hdescent : baseEnd_2679489 < baseStart_2679489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679504 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 2, 10]
def baseStart_2679504 : Nat := 118140960795 + 2679504 * 2 ^ 59
def prefixEnd_2679504 : Nat := 4983230072969 + 3 ^ 40 * 2679504 * 2
def baseEnd_2679504 : Nat := 458624489214996553992397

theorem tailTrace_2679504 : CollatzResearch.WordTrace tailWord_2679504 prefixEnd_2679504 458624489214996553992397 := by
  unfold tailWord_2679504
  simp only [CollatzResearch.WordTrace]
  refine ⟨48864769842311052847546783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65153026456414737130062377 48864769842311052847546783)
  ·
    refine ⟨73297154763466579271320175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48864769842311052847546783 73297154763466579271320175)
    ·
      refine ⟨109945732145199868906980263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73297154763466579271320175 109945732145199868906980263)
      ·
        refine ⟨164918598217799803360470395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109945732145199868906980263 164918598217799803360470395)
        ·
          refine ⟨247377897326699705040705593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164918598217799803360470395 247377897326699705040705593)
          ·
            refine ⟨185533422995024778780529195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247377897326699705040705593 185533422995024778780529195)
            ·
              refine ⟨278300134492537168170793793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185533422995024778780529195 278300134492537168170793793)
              ·
                refine ⟨208725100869402876128095345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 278300134492537168170793793 208725100869402876128095345)
                ·
                  refine ⟨156543825652052157096071509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 208725100869402876128095345 156543825652052157096071509)
                  ·
                    refine ⟨458624489214996553992397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 156543825652052157096071509 458624489214996553992397)
                    ·
                      rfl

theorem cell23_2679504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 10].length) (baseStart_2679504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679504 prefixEnd_2679504 := by exact prefixLift 2679504
  have htrace : WordTrace (prefixWord ++ tailWord_2679504) baseStart_2679504 baseEnd_2679504 := by
    simpa [prefixWord, tailWord_2679504, baseEnd_2679504] using wordTrace_append hprefix tailTrace_2679504
  have hstable : (prefixWord ++ tailWord_2679504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679504).length < 2 ^ (prefixWord ++ tailWord_2679504).sum := by decide
  have hdescent : baseEnd_2679504 < baseStart_2679504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679538 : List Nat := [3, 2, 1, 3, 1, 2, 3, 1, 1, 6]
def baseStart_2679538 : Nat := 118140960795 + 2679538 * 2 ^ 59
def prefixEnd_2679538 : Nat := 4983230072969 + 3 ^ 40 * 2679538 * 2
def baseEnd_2679538 : Nat := 458630308662414176317345

theorem tailTrace_2679538 : CollatzResearch.WordTrace tailWord_2679538 prefixEnd_2679538 458630308662414176317345 := by
  unfold tailWord_2679538
  simp only [CollatzResearch.WordTrace]
  refine ⟨24432694941624732375457817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65153853177665953001220845 24432694941624732375457817)
  ·
    refine ⟨18324521206218549281593363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24432694941624732375457817 18324521206218549281593363)
    ·
      refine ⟨27486781809327823922390045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18324521206218549281593363 27486781809327823922390045)
      ·
        refine ⟨10307543178497933970896267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27486781809327823922390045 10307543178497933970896267)
        ·
          refine ⟨15461314767746900956344401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10307543178497933970896267 15461314767746900956344401)
          ·
            refine ⟨11595986075810175717258301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15461314767746900956344401 11595986075810175717258301)
            ·
              refine ⟨4348494778428815893971863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11595986075810175717258301 4348494778428815893971863)
              ·
                refine ⟨6522742167643223840957795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4348494778428815893971863 6522742167643223840957795)
                ·
                  refine ⟨9784113251464835761436693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6522742167643223840957795 9784113251464835761436693)
                  ·
                    refine ⟨458630308662414176317345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9784113251464835761436693 458630308662414176317345)
                    ·
                      rfl

theorem cell23_2679538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 1, 6].length) (baseStart_2679538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679538 prefixEnd_2679538 := by exact prefixLift 2679538
  have htrace : WordTrace (prefixWord ++ tailWord_2679538) baseStart_2679538 baseEnd_2679538 := by
    simpa [prefixWord, tailWord_2679538, baseEnd_2679538] using wordTrace_append hprefix tailTrace_2679538
  have hstable : (prefixWord ++ tailWord_2679538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679538).length < 2 ^ (prefixWord ++ tailWord_2679538).sum := by decide
  have hdescent : baseEnd_2679538 < baseStart_2679538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679621 : List Nat := [1, 3, 1, 1, 1, 2, 2, 3, 1, 3, 5]
def baseStart_2679621 : Nat := 118140960795 + 2679621 * 2 ^ 59
def prefixEnd_2679621 : Nat := 4983230072969 + 3 ^ 40 * 2679621 * 2
def baseEnd_2679621 : Nat := 1375933544881565704214153

theorem tailTrace_2679621 : CollatzResearch.WordTrace tailWord_2679621 prefixEnd_2679621 1375933544881565704214153 := by
  unfold tailWord_2679621
  simp only [CollatzResearch.WordTrace]
  refine ⟨97733807025198234677102717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65155871350132156451401811 97733807025198234677102717)
  ·
    refine ⟨36650177634449338003913519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97733807025198234677102717 36650177634449338003913519)
    ·
      refine ⟨54975266451674007005870279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36650177634449338003913519 54975266451674007005870279)
      ·
        refine ⟨82462899677511010508805419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54975266451674007005870279 82462899677511010508805419)
        ·
          refine ⟨123694349516266515763208129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82462899677511010508805419 123694349516266515763208129)
          ·
            refine ⟨92770762137199886822406097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123694349516266515763208129 92770762137199886822406097)
            ·
              refine ⟨69578071602899915116804573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92770762137199886822406097 69578071602899915116804573)
              ·
                refine ⟨26091776851087468168801715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69578071602899915116804573 26091776851087468168801715)
                ·
                  refine ⟨39137665276631202253202573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26091776851087468168801715 39137665276631202253202573)
                  ·
                    refine ⟨14676624478736700844950965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39137665276631202253202573 14676624478736700844950965)
                    ·
                      refine ⟨1375933544881565704214153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14676624478736700844950965 1375933544881565704214153)
                      ·
                        rfl

theorem cell23_2679621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_2679621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679621 prefixEnd_2679621 := by exact prefixLift 2679621
  have htrace : WordTrace (prefixWord ++ tailWord_2679621) baseStart_2679621 baseEnd_2679621 := by
    simpa [prefixWord, tailWord_2679621, baseEnd_2679621] using wordTrace_append hprefix tailTrace_2679621
  have hstable : (prefixWord ++ tailWord_2679621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679621).length < 2 ^ (prefixWord ++ tailWord_2679621).sum := by decide
  have hdescent : baseEnd_2679621 < baseStart_2679621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679631 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 5, 4, 4]
def baseStart_2679631 : Nat := 118140960795 + 2679631 * 2 ^ 59
def prefixEnd_2679631 : Nat := 4983230072969 + 3 ^ 40 * 2679631 * 2
def baseEnd_2679631 : Nat := 1375938679688110665089107

theorem tailTrace_2679631 : CollatzResearch.WordTrace tailWord_2679631 prefixEnd_2679631 1375938679688110665089107 := by
  unfold tailWord_2679631
  simp only [CollatzResearch.WordTrace]
  refine ⟨97734171755162006384966747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65156114503441337589977831 97734171755162006384966747)
  ·
    refine ⟨146601257632743009577450121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97734171755162006384966747 146601257632743009577450121)
    ·
      refine ⟨109950943224557257183087591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146601257632743009577450121 109950943224557257183087591)
      ·
        refine ⟨164926414836835885774631387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109950943224557257183087591 164926414836835885774631387)
        ·
          refine ⟨247389622255253828661947081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164926414836835885774631387 247389622255253828661947081)
          ·
            refine ⟨185542216691440371496460311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247389622255253828661947081 185542216691440371496460311)
            ·
              refine ⟨278313325037160557244690467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185542216691440371496460311 278313325037160557244690467)
              ·
                refine ⟨417469987555740835867035701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 278313325037160557244690467 417469987555740835867035701)
                ·
                  refine ⟨39137811333350703362534597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 417469987555740835867035701 39137811333350703362534597)
                  ·
                    refine ⟨7338339625003256880475237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39137811333350703362534597 7338339625003256880475237)
                    ·
                      refine ⟨1375938679688110665089107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7338339625003256880475237 1375938679688110665089107)
                      ·
                        rfl

theorem cell23_2679631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 4, 4].length) (baseStart_2679631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679631 prefixEnd_2679631 := by exact prefixLift 2679631
  have htrace : WordTrace (prefixWord ++ tailWord_2679631) baseStart_2679631 baseEnd_2679631 := by
    simpa [prefixWord, tailWord_2679631, baseEnd_2679631] using wordTrace_append hprefix tailTrace_2679631
  have hstable : (prefixWord ++ tailWord_2679631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679631).length < 2 ^ (prefixWord ++ tailWord_2679631).sum := by decide
  have hdescent : baseEnd_2679631 < baseStart_2679631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679635 : List Nat := [1, 1, 1, 2, 1, 1, 3, 5, 4, 2, 2]
def baseStart_2679635 : Nat := 118140960795 + 2679635 * 2 ^ 59
def prefixEnd_2679635 : Nat := 4983230072969 + 3 ^ 40 * 2679635 * 2
def baseEnd_2679635 : Nat := 1375940733610728649439089

theorem tailTrace_2679635 : CollatzResearch.WordTrace tailWord_2679635 prefixEnd_2679635 1375940733610728649439089 := by
  unfold tailWord_2679635
  simp only [CollatzResearch.WordTrace]
  refine ⟨97734317647147515068112359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65156211764765010045408239 97734317647147515068112359)
  ·
    refine ⟨146601476470721272602168539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97734317647147515068112359 146601476470721272602168539)
    ·
      refine ⟨219902214706081908903252809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146601476470721272602168539 219902214706081908903252809)
      ·
        refine ⟨164926661029561431677439607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219902214706081908903252809 164926661029561431677439607)
        ·
          refine ⟨247389991544342147516159411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164926661029561431677439607 247389991544342147516159411)
          ·
            refine ⟨371084987316513221274239117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247389991544342147516159411 371084987316513221274239117)
            ·
              refine ⟨139156870243692457977839669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 371084987316513221274239117 139156870243692457977839669)
              ·
                refine ⟨13045956585346167935422469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 139156870243692457977839669 13045956585346167935422469)
                ·
                  refine ⟨2446116859752406487891713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13045956585346167935422469 2446116859752406487891713)
                  ·
                    refine ⟨1834587644814304865918785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2446116859752406487891713 1834587644814304865918785)
                    ·
                      refine ⟨1375940733610728649439089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1834587644814304865918785 1375940733610728649439089)
                      ·
                        rfl

theorem cell23_2679635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 4, 2, 2].length) (baseStart_2679635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679635 prefixEnd_2679635 := by exact prefixLift 2679635
  have htrace : WordTrace (prefixWord ++ tailWord_2679635) baseStart_2679635 baseEnd_2679635 := by
    simpa [prefixWord, tailWord_2679635, baseEnd_2679635] using wordTrace_append hprefix tailTrace_2679635
  have hstable : (prefixWord ++ tailWord_2679635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679635).length < 2 ^ (prefixWord ++ tailWord_2679635).sum := by decide
  have hdescent : baseEnd_2679635 < baseStart_2679635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679648 : List Nat := [2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 4]
def baseStart_2679648 : Nat := 118140960795 + 2679648 * 2 ^ 59
def prefixEnd_2679648 : Nat := 4983230072969 + 3 ^ 40 * 2679648 * 2
def baseEnd_2679648 : Nat := 1375947408859237098576529

theorem tailTrace_2679648 : CollatzResearch.WordTrace tailWord_2679648 prefixEnd_2679648 1375947408859237098576529 := by
  unfold tailWord_2679648
  simp only [CollatzResearch.WordTrace]
  refine ⟨48867395898050209144167799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65156527864066945525557065 48867395898050209144167799)
  ·
    refine ⟨73301093847075313716251699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48867395898050209144167799 73301093847075313716251699)
    ·
      refine ⟨109951640770612970574377549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73301093847075313716251699 109951640770612970574377549)
      ·
        refine ⟨41231865288979863965391581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109951640770612970574377549 41231865288979863965391581)
        ·
          refine ⟨15461949483367448987021843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41231865288979863965391581 15461949483367448987021843)
          ·
            refine ⟨23192924225051173480532765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15461949483367448987021843 23192924225051173480532765)
            ·
              refine ⟨8697346584394190055199787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23192924225051173480532765 8697346584394190055199787)
              ·
                refine ⟨13046019876591285082799681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8697346584394190055199787 13046019876591285082799681)
                ·
                  refine ⟨9784514907443463812099761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13046019876591285082799681 9784514907443463812099761)
                  ·
                    refine ⟨7338386180582597859074821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9784514907443463812099761 7338386180582597859074821)
                    ·
                      refine ⟨1375947408859237098576529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7338386180582597859074821 1375947408859237098576529)
                      ·
                        rfl

theorem cell23_2679648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_2679648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679648 prefixEnd_2679648 := by exact prefixLift 2679648
  have htrace : WordTrace (prefixWord ++ tailWord_2679648) baseStart_2679648 baseEnd_2679648 := by
    simpa [prefixWord, tailWord_2679648, baseEnd_2679648] using wordTrace_append hprefix tailTrace_2679648
  have hstable : (prefixWord ++ tailWord_2679648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679648).length < 2 ^ (prefixWord ++ tailWord_2679648).sum := by decide
  have hdescent : baseEnd_2679648 < baseStart_2679648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679652 : List Nat := [2, 3, 1, 1, 4, 2, 2, 1, 1, 4, 2]
def baseStart_2679652 : Nat := 118140960795 + 2679652 * 2 ^ 59
def prefixEnd_2679652 : Nat := 4983230072969 + 3 ^ 40 * 2679652 * 2
def baseEnd_2679652 : Nat := 1375949462781855082926511

theorem tailTrace_2679652 : CollatzResearch.WordTrace tailWord_2679652 prefixEnd_2679652 1375949462781855082926511 := by
  unfold tailWord_2679652
  simp only [CollatzResearch.WordTrace]
  refine ⟨48867468844042963485740605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65156625125390617980987473 48867468844042963485740605)
  ·
    refine ⟨18325300816516111307152727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48867468844042963485740605 18325300816516111307152727)
    ·
      refine ⟨27487951224774166960729091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18325300816516111307152727 27487951224774166960729091)
      ·
        refine ⟨41231926837161250441093637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27487951224774166960729091 41231926837161250441093637)
        ·
          refine ⟨7730986281967734457705057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41231926837161250441093637 7730986281967734457705057)
          ·
            refine ⟨5798239711475800843278793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7730986281967734457705057 5798239711475800843278793)
            ·
              refine ⟨4348679783606850632459095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5798239711475800843278793 4348679783606850632459095)
              ·
                refine ⟨6523019675410275948688643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4348679783606850632459095 6523019675410275948688643)
                ·
                  refine ⟨9784529513115413923032965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6523019675410275948688643 9784529513115413923032965)
                  ·
                    refine ⟨1834599283709140110568681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9784529513115413923032965 1834599283709140110568681)
                    ·
                      refine ⟨1375949462781855082926511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1834599283709140110568681 1375949462781855082926511)
                      ·
                        rfl

theorem cell23_2679652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 1, 4, 2].length) (baseStart_2679652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679652 prefixEnd_2679652 := by exact prefixLift 2679652
  have htrace : WordTrace (prefixWord ++ tailWord_2679652) baseStart_2679652 baseEnd_2679652 := by
    simpa [prefixWord, tailWord_2679652, baseEnd_2679652] using wordTrace_append hprefix tailTrace_2679652
  have hstable : (prefixWord ++ tailWord_2679652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679652).length < 2 ^ (prefixWord ++ tailWord_2679652).sum := by decide
  have hdescent : baseEnd_2679652 < baseStart_2679652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679815 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 5, 1, 4]
def baseStart_2679815 : Nat := 118140960795 + 2679815 * 2 ^ 59
def prefixEnd_2679815 : Nat := 4983230072969 + 3 ^ 40 * 2679815 * 2
def baseEnd_2679815 : Nat := 1376033160128537945188261

theorem tailTrace_2679815 : CollatzResearch.WordTrace tailWord_2679815 prefixEnd_2679815 1376033160128537945188261 := by
  unfold tailWord_2679815
  simp only [CollatzResearch.WordTrace]
  refine ⟨97740882786495405809664899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65160588524330270539776599 97740882786495405809664899)
  ·
    refine ⟨146611324179743108714497349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97740882786495405809664899 146611324179743108714497349)
    ·
      refine ⟨27489623283701832883968253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146611324179743108714497349 27489623283701832883968253)
      ·
        refine ⟨10308608731388187331488095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27489623283701832883968253 10308608731388187331488095)
        ·
          refine ⟨15462913097082280997232143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10308608731388187331488095 15462913097082280997232143)
          ·
            refine ⟨23194369645623421495848215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15462913097082280997232143 23194369645623421495848215)
            ·
              refine ⟨34791554468435132243772323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23194369645623421495848215 34791554468435132243772323)
              ·
                refine ⟨52187331702652698365658485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34791554468435132243772323 52187331702652698365658485)
                ·
                  refine ⟨4892562347123690471780483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52187331702652698365658485 4892562347123690471780483)
                  ·
                    refine ⟨7338843520685535707670725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4892562347123690471780483 7338843520685535707670725)
                    ·
                      refine ⟨1376033160128537945188261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7338843520685535707670725 1376033160128537945188261)
                      ·
                        rfl

theorem cell23_2679815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_2679815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679815 prefixEnd_2679815 := by exact prefixLift 2679815
  have htrace : WordTrace (prefixWord ++ tailWord_2679815) baseStart_2679815 baseEnd_2679815 := by
    simpa [prefixWord, tailWord_2679815, baseEnd_2679815] using wordTrace_append hprefix tailTrace_2679815
  have hstable : (prefixWord ++ tailWord_2679815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679815).length < 2 ^ (prefixWord ++ tailWord_2679815).sum := by decide
  have hdescent : baseEnd_2679815 < baseStart_2679815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679836 : List Nat := [2, 2, 3, 1, 4, 2, 1, 1, 2, 3, 2]
def baseStart_2679836 : Nat := 118140960795 + 2679836 * 2 ^ 59
def prefixEnd_2679836 : Nat := 4983230072969 + 3 ^ 40 * 2679836 * 2
def baseEnd_2679836 : Nat := 1376043943222282363025665

theorem tailTrace_2679836 : CollatzResearch.WordTrace tailWord_2679836 prefixEnd_2679836 1376043943222282363025665 := by
  unfold tailWord_2679836
  simp only [CollatzResearch.WordTrace]
  refine ⟨48870824359709663198089681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65161099146279550930786241 48870824359709663198089681)
  ·
    refine ⟨36653118269782247398567261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48870824359709663198089681 36653118269782247398567261)
    ·
      refine ⟨13744919351168342774462723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36653118269782247398567261 13744919351168342774462723)
      ·
        refine ⟨20617379026752514161694085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13744919351168342774462723 20617379026752514161694085)
        ·
          refine ⟨3865758567516096405317641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20617379026752514161694085 3865758567516096405317641)
          ·
            refine ⟨2899318925637072303988231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3865758567516096405317641 2899318925637072303988231)
            ·
              refine ⟨4348978388455608455982347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2899318925637072303988231 4348978388455608455982347)
              ·
                refine ⟨6523467582683412683973521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4348978388455608455982347 6523467582683412683973521)
                ·
                  refine ⟨4892600687012559512980141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6523467582683412683973521 4892600687012559512980141)
                  ·
                    refine ⟨1834725257629709817367553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4892600687012559512980141 1834725257629709817367553)
                    ·
                      refine ⟨1376043943222282363025665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1834725257629709817367553 1376043943222282363025665)
                      ·
                        rfl

theorem cell23_2679836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 2, 3, 2].length) (baseStart_2679836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679836 prefixEnd_2679836 := by exact prefixLift 2679836
  have htrace : WordTrace (prefixWord ++ tailWord_2679836) baseStart_2679836 baseEnd_2679836 := by
    simpa [prefixWord, tailWord_2679836, baseEnd_2679836] using wordTrace_append hprefix tailTrace_2679836
  have hstable : (prefixWord ++ tailWord_2679836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679836).length < 2 ^ (prefixWord ++ tailWord_2679836).sum := by decide
  have hdescent : baseEnd_2679836 < baseStart_2679836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679845 : List Nat := [1, 3, 1, 2, 2, 2, 1, 4, 1, 2, 4]
def baseStart_2679845 : Nat := 118140960795 + 2679845 * 2 ^ 59
def prefixEnd_2679845 : Nat := 4983230072969 + 3 ^ 40 * 2679845 * 2
def baseEnd_2679845 : Nat := 1376048564548172827813123

theorem tailTrace_2679845 : CollatzResearch.WordTrace tailWord_2679845 prefixEnd_2679845 1376048564548172827813123 := by
  unfold tailWord_2679845
  simp only [CollatzResearch.WordTrace]
  refine ⟨97741976976386720933256989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65161317984257813955504659 97741976976386720933256989)
  ·
    refine ⟨36653241366145020349971371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97741976976386720933256989 36653241366145020349971371)
    ·
      refine ⟨54979862049217530524957057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36653241366145020349971371 54979862049217530524957057)
      ·
        refine ⟨41234896536913147893717793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54979862049217530524957057 41234896536913147893717793)
        ·
          refine ⟨30926172402684860920288345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41234896536913147893717793 30926172402684860920288345)
          ·
            refine ⟨23194629302013645690216259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30926172402684860920288345 23194629302013645690216259)
            ·
              refine ⟨34791943953020468535324389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23194629302013645690216259 34791943953020468535324389)
              ·
                refine ⟨6523489491191337850373323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34791943953020468535324389 6523489491191337850373323)
                ·
                  refine ⟨9785234236787006775559985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6523489491191337850373323 9785234236787006775559985)
                  ·
                    refine ⟨7338925677590255081669989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9785234236787006775559985 7338925677590255081669989)
                    ·
                      refine ⟨1376048564548172827813123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7338925677590255081669989 1376048564548172827813123)
                      ·
                        rfl

theorem cell23_2679845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_2679845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679845 prefixEnd_2679845 := by exact prefixLift 2679845
  have htrace : WordTrace (prefixWord ++ tailWord_2679845) baseStart_2679845 baseEnd_2679845 := by
    simpa [prefixWord, tailWord_2679845, baseEnd_2679845] using wordTrace_append hprefix tailTrace_2679845
  have hstable : (prefixWord ++ tailWord_2679845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679845).length < 2 ^ (prefixWord ++ tailWord_2679845).sum := by decide
  have hdescent : baseEnd_2679845 < baseStart_2679845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679852 : List Nat := [2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 3]
def baseStart_2679852 : Nat := 118140960795 + 2679852 * 2 ^ 59
def prefixEnd_2679852 : Nat := 4983230072969 + 3 ^ 40 * 2679852 * 2
def baseEnd_2679852 : Nat := 1376052158912754300425591

theorem tailTrace_2679852 : CollatzResearch.WordTrace tailWord_2679852 prefixEnd_2679852 1376052158912754300425591 := by
  unfold tailWord_2679852
  simp only [CollatzResearch.WordTrace]
  refine ⟨48871116143680680564380905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65161488191574240752507873 48871116143680680564380905)
  ·
    refine ⟨36653337107760510423285679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48871116143680680564380905 36653337107760510423285679)
    ·
      refine ⟨54980005661640765634928519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36653337107760510423285679 54980005661640765634928519)
      ·
        refine ⟨82470008492461148452392779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54980005661640765634928519 82470008492461148452392779)
        ·
          refine ⟨123705012738691722678589169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82470008492461148452392779 123705012738691722678589169)
          ·
            refine ⟨92778759554018792008941877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123705012738691722678589169 92778759554018792008941877)
            ·
              refine ⟨8698008708189261750838301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92778759554018792008941877 8698008708189261750838301)
              ·
                refine ⟨3261753265570973156564363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8698008708189261750838301 3261753265570973156564363)
                ·
                  refine ⟨4892629898356459734846545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3261753265570973156564363 4892629898356459734846545)
                  ·
                    refine ⟨3669472423767344801134909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4892629898356459734846545 3669472423767344801134909)
                    ·
                      refine ⟨1376052158912754300425591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3669472423767344801134909 1376052158912754300425591)
                      ·
                        rfl

theorem cell23_2679852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 3].length) (baseStart_2679852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679852 prefixEnd_2679852 := by exact prefixLift 2679852
  have htrace : WordTrace (prefixWord ++ tailWord_2679852) baseStart_2679852 baseEnd_2679852 := by
    simpa [prefixWord, tailWord_2679852, baseEnd_2679852] using wordTrace_append hprefix tailTrace_2679852
  have hstable : (prefixWord ++ tailWord_2679852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679852).length < 2 ^ (prefixWord ++ tailWord_2679852).sum := by decide
  have hdescent : baseEnd_2679852 < baseStart_2679852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679866 : List Nat := [3, 1, 1, 1, 3, 1, 4, 4, 1, 2, 2]
def baseStart_2679866 : Nat := 118140960795 + 2679866 * 2 ^ 59
def prefixEnd_2679866 : Nat := 4983230072969 + 3 ^ 40 * 2679866 * 2
def baseEnd_2679866 : Nat := 1376059347641917245650527

theorem tailTrace_2679866 : CollatzResearch.WordTrace tailWord_2679866 prefixEnd_2679866 1376059347641917245650527 := by
  unfold tailWord_2679866
  simp only [CollatzResearch.WordTrace]
  refine ⟨24435685727327660379942863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65161828606207094346514301 24435685727327660379942863)
  ·
    refine ⟨36653528590991490569914295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24435685727327660379942863 36653528590991490569914295)
    ·
      refine ⟨54980292886487235854871443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36653528590991490569914295 54980292886487235854871443)
      ·
        refine ⟨82470439329730853782307165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54980292886487235854871443 82470439329730853782307165)
        ·
          refine ⟨30926414748649070168365187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82470439329730853782307165 30926414748649070168365187)
          ·
            refine ⟨46389622122973605252547781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30926414748649070168365187 46389622122973605252547781)
            ·
              refine ⟨8698054148057550984852709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46389622122973605252547781 8698054148057550984852709)
              ·
                refine ⟨1630885152760790809659883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8698054148057550984852709 1630885152760790809659883)
                ·
                  refine ⟨2446327729141186214489825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1630885152760790809659883 2446327729141186214489825)
                  ·
                    refine ⟨1834745796855889660867369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2446327729141186214489825 1834745796855889660867369)
                    ·
                      refine ⟨1376059347641917245650527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1834745796855889660867369 1376059347641917245650527)
                      ·
                        rfl

theorem cell23_2679866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 4, 1, 2, 2].length) (baseStart_2679866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679866 prefixEnd_2679866 := by exact prefixLift 2679866
  have htrace : WordTrace (prefixWord ++ tailWord_2679866) baseStart_2679866 baseEnd_2679866 := by
    simpa [prefixWord, tailWord_2679866, baseEnd_2679866] using wordTrace_append hprefix tailTrace_2679866
  have hstable : (prefixWord ++ tailWord_2679866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679866).length < 2 ^ (prefixWord ++ tailWord_2679866).sum := by decide
  have hdescent : baseEnd_2679866 < baseStart_2679866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679882 : List Nat := [3, 1, 2, 1, 1, 2, 5, 1, 1, 3, 3]
def baseStart_2679882 : Nat := 118140960795 + 2679882 * 2 ^ 59
def prefixEnd_2679882 : Nat := 4983230072969 + 3 ^ 40 * 2679882 * 2
def baseEnd_2679882 : Nat := 1376067563332389183050453

theorem tailTrace_2679882 : CollatzResearch.WordTrace tailWord_2679882 prefixEnd_2679882 1376067563332389183050453 := by
  unfold tailWord_2679882
  simp only [CollatzResearch.WordTrace]
  refine ⟨24435831619313169063088475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65162217651501784168235933 24435831619313169063088475)
  ·
    refine ⟨36653747428969753594632713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24435831619313169063088475 36653747428969753594632713)
    ·
      refine ⟨27490310571727315195974535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36653747428969753594632713 27490310571727315195974535)
      ·
        refine ⟨41235465857590972793961803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27490310571727315195974535 41235465857590972793961803)
        ·
          refine ⟨61853198786386459190942705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41235465857590972793961803 61853198786386459190942705)
          ·
            refine ⟨46389899089789844393207029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61853198786386459190942705 46389899089789844393207029)
            ·
              refine ⟨4349053039667797911863159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46389899089789844393207029 4349053039667797911863159)
              ·
                refine ⟨6523579559501696867794739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4349053039667797911863159 6523579559501696867794739)
                ·
                  refine ⟨9785369339252545301692109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6523579559501696867794739 9785369339252545301692109)
                  ·
                    refine ⟨3669513502219704488134541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9785369339252545301692109 3669513502219704488134541)
                    ·
                      refine ⟨1376067563332389183050453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3669513502219704488134541 1376067563332389183050453)
                      ·
                        rfl

theorem cell23_2679882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 1, 3, 3].length) (baseStart_2679882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679882 prefixEnd_2679882 := by exact prefixLift 2679882
  have htrace : WordTrace (prefixWord ++ tailWord_2679882) baseStart_2679882 baseEnd_2679882 := by
    simpa [prefixWord, tailWord_2679882, baseEnd_2679882] using wordTrace_append hprefix tailTrace_2679882
  have hstable : (prefixWord ++ tailWord_2679882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679882).length < 2 ^ (prefixWord ++ tailWord_2679882).sum := by decide
  have hdescent : baseEnd_2679882 < baseStart_2679882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679909 : List Nat := [1, 3, 1, 3, 2, 1, 1, 5, 1, 3, 2]
def baseStart_2679909 : Nat := 118140960795 + 2679909 * 2 ^ 59
def prefixEnd_2679909 : Nat := 4983230072969 + 3 ^ 40 * 2679909 * 2
def baseEnd_2679909 : Nat := 1376081427310060577412829

theorem tailTrace_2679909 : CollatzResearch.WordTrace tailWord_2679909 prefixEnd_2679909 1376081427310060577412829 := by
  unfold tailWord_2679909
  simp only [CollatzResearch.WordTrace]
  refine ⟨97744311248154859863586781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65162874165436573242391187 97744311248154859863586781)
  ·
    refine ⟨36654116718058072448845043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97744311248154859863586781 36654116718058072448845043)
    ·
      refine ⟨54981175077087108673267565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36654116718058072448845043 54981175077087108673267565)
      ·
        refine ⟨20617940653907665752475337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54981175077087108673267565 20617940653907665752475337)
        ·
          refine ⟨15463455490430749314356503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20617940653907665752475337 15463455490430749314356503)
          ·
            refine ⟨23195183235646123971534755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15463455490430749314356503 23195183235646123971534755)
            ·
              refine ⟨34792774853469185957302133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23195183235646123971534755 34792774853469185957302133)
              ·
                refine ⟨3261822642512736183497075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34792774853469185957302133 3261822642512736183497075)
                ·
                  refine ⟨4892733963769104275245613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3261822642512736183497075 4892733963769104275245613)
                  ·
                    refine ⟨1834775236413414103217105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4892733963769104275245613 1834775236413414103217105)
                    ·
                      refine ⟨1376081427310060577412829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1834775236413414103217105 1376081427310060577412829)
                      ·
                        rfl

theorem cell23_2679909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 5, 1, 3, 2].length) (baseStart_2679909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679909 prefixEnd_2679909 := by exact prefixLift 2679909
  have htrace : WordTrace (prefixWord ++ tailWord_2679909) baseStart_2679909 baseEnd_2679909 := by
    simpa [prefixWord, tailWord_2679909, baseEnd_2679909] using wordTrace_append hprefix tailTrace_2679909
  have hstable : (prefixWord ++ tailWord_2679909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679909).length < 2 ^ (prefixWord ++ tailWord_2679909).sum := by decide
  have hdescent : baseEnd_2679909 < baseStart_2679909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679990 : List Nat := [5, 1, 3, 2, 1, 1, 2, 1, 1, 4, 2]
def baseStart_2679990 : Nat := 118140960795 + 2679990 * 2 ^ 59
def prefixEnd_2679990 : Nat := 4983230072969 + 3 ^ 40 * 2679990 * 2
def baseEnd_2679990 : Nat := 1376123019243074760499957

theorem tailTrace_2679990 : CollatzResearch.WordTrace tailWord_2679990 prefixEnd_2679990 1376123019243074760499957 := by
  unfold tailWord_2679990
  simp only [CollatzResearch.WordTrace]
  refine ⟨6109204097553838168580339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65164843707240940464856949 6109204097553838168580339)
  ·
    refine ⟨9163806146330757252870509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6109204097553838168580339 9163806146330757252870509)
    ·
      refine ⟨3436427304874033969826441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9163806146330757252870509 3436427304874033969826441)
      ·
        refine ⟨2577320478655525477369831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3436427304874033969826441 2577320478655525477369831)
        ·
          refine ⟨3865980717983288216054747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2577320478655525477369831 3865980717983288216054747)
          ·
            refine ⟨5798971076974932324082121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3865980717983288216054747 5798971076974932324082121)
            ·
              refine ⟨4349228307731199243061591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5798971076974932324082121 4349228307731199243061591)
              ·
                refine ⟨6523842461596798864592387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4349228307731199243061591 6523842461596798864592387)
                ·
                  refine ⟨9785763692395198296888581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6523842461596798864592387 9785763692395198296888581)
                  ·
                    refine ⟨1834830692324099680666609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9785763692395198296888581 1834830692324099680666609)
                    ·
                      refine ⟨1376123019243074760499957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1834830692324099680666609 1376123019243074760499957)
                      ·
                        rfl

theorem cell23_2679990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_2679990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2679990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2679990 prefixEnd_2679990 := by exact prefixLift 2679990
  have htrace : WordTrace (prefixWord ++ tailWord_2679990) baseStart_2679990 baseEnd_2679990 := by
    simpa [prefixWord, tailWord_2679990, baseEnd_2679990] using wordTrace_append hprefix tailTrace_2679990
  have hstable : (prefixWord ++ tailWord_2679990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679990).length < 2 ^ (prefixWord ++ tailWord_2679990).sum := by decide
  have hdescent : baseEnd_2679990 < baseStart_2679990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680015 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 5]
def baseStart_2680015 : Nat := 118140960795 + 2680015 * 2 ^ 59
def prefixEnd_2680015 : Nat := 4983230072969 + 3 ^ 40 * 2680015 * 2
def baseEnd_2680015 : Nat := 1376135856259437162687341

theorem tailTrace_2680015 : CollatzResearch.WordTrace tailWord_2680015 prefixEnd_2680015 1376135856259437162687341 := by
  unfold tailWord_2680015
  simp only [CollatzResearch.WordTrace]
  refine ⟨97748177385770839966945499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65165451590513893311296999 97748177385770839966945499)
  ·
    refine ⟨146622266078656259950418249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97748177385770839966945499 146622266078656259950418249)
    ·
      refine ⟨109966699558992194962813687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146622266078656259950418249 109966699558992194962813687)
      ·
        refine ⟨164950049338488292444220531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109966699558992194962813687 164950049338488292444220531)
        ·
          refine ⟨247425074007732438666330797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164950049338488292444220531 247425074007732438666330797)
          ·
            refine ⟨92784402752899664499874049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 247425074007732438666330797 92784402752899664499874049)
            ·
              refine ⟨69588302064674748374905537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92784402752899664499874049 69588302064674748374905537)
              ·
                refine ⟨52191226548506061281179153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69588302064674748374905537 52191226548506061281179153)
                ·
                  refine ⟨39143419911379545960884365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52191226548506061281179153 39143419911379545960884365)
                  ·
                    refine ⟨14678782466767329735331637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39143419911379545960884365 14678782466767329735331637)
                    ·
                      refine ⟨1376135856259437162687341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14678782466767329735331637 1376135856259437162687341)
                      ·
                        rfl

theorem cell23_2680015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 5].length) (baseStart_2680015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2680015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2680015 prefixEnd_2680015 := by exact prefixLift 2680015
  have htrace : WordTrace (prefixWord ++ tailWord_2680015) baseStart_2680015 baseEnd_2680015 := by
    simpa [prefixWord, tailWord_2680015, baseEnd_2680015] using wordTrace_append hprefix tailTrace_2680015
  have hstable : (prefixWord ++ tailWord_2680015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680015).length < 2 ^ (prefixWord ++ tailWord_2680015).sum := by decide
  have hdescent : baseEnd_2680015 < baseStart_2680015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680112 : List Nat := [2, 1, 1, 1, 2, 2, 4, 3, 1, 6]
def baseStart_2680112 : Nat := 118140960795 + 2680112 * 2 ^ 59
def prefixEnd_2680112 : Nat := 4983230072969 + 3 ^ 40 * 2680112 * 2
def baseEnd_2680112 : Nat := 458728554627641094391465

theorem tailTrace_2680112 : CollatzResearch.WordTrace tailWord_2680112 prefixEnd_2680112 458728554627641094391465 := by
  unfold tailWord_2680112
  simp only [CollatzResearch.WordTrace]
  refine ⟨48875857633209712766613295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65167810177612950355484393 48875857633209712766613295)
  ·
    refine ⟨73313786449814569149919943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48875857633209712766613295 73313786449814569149919943)
    ·
      refine ⟨109970679674721853724879915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73313786449814569149919943 109970679674721853724879915)
      ·
        refine ⟨164956019512082780587319873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109970679674721853724879915 164956019512082780587319873)
        ·
          refine ⟨123717014634062085440489905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164956019512082780587319873 123717014634062085440489905)
          ·
            refine ⟨92787760975546564080367429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123717014634062085440489905 92787760975546564080367429)
            ·
              refine ⟨17397705182914980765068893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92787760975546564080367429 17397705182914980765068893)
              ·
                refine ⟨6524139443593117786900835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17397705182914980765068893 6524139443593117786900835)
                ·
                  refine ⟨9786209165389676680351253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6524139443593117786900835 9786209165389676680351253)
                  ·
                    refine ⟨458728554627641094391465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9786209165389676680351253 458728554627641094391465)
                    ·
                      rfl

theorem cell23_2680112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 1, 6].length) (baseStart_2680112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2680112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2680112 prefixEnd_2680112 := by exact prefixLift 2680112
  have htrace : WordTrace (prefixWord ++ tailWord_2680112) baseStart_2680112 baseEnd_2680112 := by
    simpa [prefixWord, tailWord_2680112, baseEnd_2680112] using wordTrace_append hprefix tailTrace_2680112
  have hstable : (prefixWord ++ tailWord_2680112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680112).length < 2 ^ (prefixWord ++ tailWord_2680112).sum := by decide
  have hdescent : baseEnd_2680112 < baseStart_2680112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680129 : List Nat := [1, 2, 5, 2, 1, 1, 1, 1, 3, 6]
def baseStart_2680129 : Nat := 118140960795 + 2680129 * 2 ^ 59
def prefixEnd_2680129 : Nat := 4983230072969 + 3 ^ 40 * 2680129 * 2
def baseEnd_2680129 : Nat := 458731464351349905553939

theorem tailTrace_2680129 : CollatzResearch.WordTrace tailWord_2680129 prefixEnd_2680129 458731464351349905553939 := by
  unfold tailWord_2680129
  simp only [CollatzResearch.WordTrace]
  refine ⟨97752335307357837436595441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65168223538238558291063627 97752335307357837436595441)
  ·
    refine ⟨73314251480518378077446581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97752335307357837436595441 73314251480518378077446581)
    ·
      refine ⟨6873211076298597944760617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73314251480518378077446581 6873211076298597944760617)
      ·
        refine ⟨5154908307223948458570463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6873211076298597944760617 5154908307223948458570463)
        ·
          refine ⟨7732362460835922687855695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5154908307223948458570463 7732362460835922687855695)
          ·
            refine ⟨11598543691253884031783543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7732362460835922687855695 11598543691253884031783543)
            ·
              refine ⟨17397815536880826047675315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11598543691253884031783543 17397815536880826047675315)
              ·
                refine ⟨26096723305321239071512973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17397815536880826047675315 26096723305321239071512973)
                ·
                  refine ⟨9786271239495464651817365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26096723305321239071512973 9786271239495464651817365)
                  ·
                    refine ⟨458731464351349905553939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9786271239495464651817365 458731464351349905553939)
                    ·
                      rfl

theorem cell23_2680129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_2680129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2680129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2680129 prefixEnd_2680129 := by exact prefixLift 2680129
  have htrace : WordTrace (prefixWord ++ tailWord_2680129) baseStart_2680129 baseEnd_2680129 := by
    simpa [prefixWord, tailWord_2680129, baseEnd_2680129] using wordTrace_append hprefix tailTrace_2680129
  have hstable : (prefixWord ++ tailWord_2680129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680129).length < 2 ^ (prefixWord ++ tailWord_2680129).sum := by decide
  have hdescent : baseEnd_2680129 < baseStart_2680129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680170 : List Nat := [3, 1, 3, 3, 2, 1, 1, 2, 3, 2, 2]
def baseStart_2680170 : Nat := 118140960795 + 2680170 * 2 ^ 59
def prefixEnd_2680170 : Nat := 4983230072969 + 3 ^ 40 * 2680170 * 2
def baseEnd_2680170 : Nat := 1376215445760884056249129

theorem tailTrace_2680170 : CollatzResearch.WordTrace tailWord_2680170 prefixEnd_2680170 1376215445760884056249129 := by
  unfold tailWord_2680170
  simp only [CollatzResearch.WordTrace]
  refine ⟨24438457675052325359709491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65169220466806200959225309 24438457675052325359709491)
  ·
    refine ⟨36657686512578488039564237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24438457675052325359709491 36657686512578488039564237)
    ·
      refine ⟨13746632442216933014836589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36657686512578488039564237 13746632442216933014836589)
      ·
        refine ⟨5154987165831349880563721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13746632442216933014836589 5154987165831349880563721)
        ·
          refine ⟨3866240374373512410422791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5154987165831349880563721 3866240374373512410422791)
          ·
            refine ⟨5799360561560268615634187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3866240374373512410422791 5799360561560268615634187)
            ·
              refine ⟨8699040842340402923451281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5799360561560268615634187 8699040842340402923451281)
              ·
                refine ⟨6524280631755302192588461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8699040842340402923451281 6524280631755302192588461)
                ·
                  refine ⟨2446605236908238322220673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6524280631755302192588461 2446605236908238322220673)
                  ·
                    refine ⟨1834953927681178741665505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2446605236908238322220673 1834953927681178741665505)
                    ·
                      refine ⟨1376215445760884056249129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1834953927681178741665505 1376215445760884056249129)
                      ·
                        rfl

theorem cell23_2680170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_2680170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2680170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2680170 prefixEnd_2680170 := by exact prefixLift 2680170
  have htrace : WordTrace (prefixWord ++ tailWord_2680170) baseStart_2680170 baseEnd_2680170 := by
    simpa [prefixWord, tailWord_2680170, baseEnd_2680170] using wordTrace_append hprefix tailTrace_2680170
  have hstable : (prefixWord ++ tailWord_2680170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680170).length < 2 ^ (prefixWord ++ tailWord_2680170).sum := by decide
  have hdescent : baseEnd_2680170 < baseStart_2680170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680220 : List Nat := [2, 2, 3, 4, 1, 2, 1, 1, 1, 3, 3]
def baseStart_2680220 : Nat := 118140960795 + 2680220 * 2 ^ 59
def prefixEnd_2680220 : Nat := 4983230072969 + 3 ^ 40 * 2680220 * 2
def baseEnd_2680220 : Nat := 1376241119793608860623899

theorem tailTrace_2680220 : CollatzResearch.WordTrace tailWord_2680220 prefixEnd_2680220 1376241119793608860623899 := by
  unfold tailWord_2680220
  simp only [CollatzResearch.WordTrace]
  refine ⟨48877827175014079989079057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65170436233352106652105409 48877827175014079989079057)
  ·
    refine ⟨36658370381260559991809293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48877827175014079989079057 36658370381260559991809293)
    ·
      refine ⟨13746888892972709996928485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36658370381260559991809293 13746888892972709996928485)
      ·
        refine ⟨2577541667432383124424091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13746888892972709996928485 2577541667432383124424091)
        ·
          refine ⟨3866312501148574686636137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2577541667432383124424091 3866312501148574686636137)
          ·
            refine ⟨2899734375861431014977103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3866312501148574686636137 2899734375861431014977103)
            ·
              refine ⟨4349601563792146522465655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2899734375861431014977103 4349601563792146522465655)
              ·
                refine ⟨6524402345688219783698483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4349601563792146522465655 6524402345688219783698483)
                ·
                  refine ⟨9786603518532329675547725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6524402345688219783698483 9786603518532329675547725)
                  ·
                    refine ⟨3669976319449623628330397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9786603518532329675547725 3669976319449623628330397)
                    ·
                      refine ⟨1376241119793608860623899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3669976319449623628330397 1376241119793608860623899)
                      ·
                        rfl

theorem cell23_2680220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_2680220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2680220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2680220 prefixEnd_2680220 := by exact prefixLift 2680220
  have htrace : WordTrace (prefixWord ++ tailWord_2680220) baseStart_2680220 baseEnd_2680220 := by
    simpa [prefixWord, tailWord_2680220, baseEnd_2680220] using wordTrace_append hprefix tailTrace_2680220
  have hstable : (prefixWord ++ tailWord_2680220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680220).length < 2 ^ (prefixWord ++ tailWord_2680220).sum := by decide
  have hdescent : baseEnd_2680220 < baseStart_2680220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680259 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 4, 3, 3]
def baseStart_2680259 : Nat := 118140960795 + 2680259 * 2 ^ 59
def prefixEnd_2680259 : Nat := 4983230072969 + 3 ^ 40 * 2680259 * 2
def baseEnd_2680259 : Nat := 1376261145539134208036219

theorem tailTrace_2680259 : CollatzResearch.WordTrace tailWord_2680259 prefixEnd_2680259 1376261145539134208036219 := by
  unfold tailWord_2680259
  simp only [CollatzResearch.WordTrace]
  refine ⟨97757076796886869638827831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65171384531257913092551887 97757076796886869638827831)
  ·
    refine ⟨146635615195330304458241747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97757076796886869638827831 146635615195330304458241747)
    ·
      refine ⟨219953422792995456687362621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146635615195330304458241747 219953422792995456687362621)
      ·
        refine ⟨82482533547373296257760983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 219953422792995456687362621 82482533547373296257760983)
        ·
          refine ⟨123723800321059944386641475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82482533547373296257760983 123723800321059944386641475)
          ·
            refine ⟨185585700481589916579962213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123723800321059944386641475 185585700481589916579962213)
            ·
              refine ⟨34797318840298109358742915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 185585700481589916579962213 34797318840298109358742915)
              ·
                refine ⟨52195978260447164038114373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34797318840298109358742915 52195978260447164038114373)
                ·
                  refine ⟨9786745923833843257146445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52195978260447164038114373 9786745923833843257146445)
                  ·
                    refine ⟨3670029721437691221429917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9786745923833843257146445 3670029721437691221429917)
                    ·
                      refine ⟨1376261145539134208036219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3670029721437691221429917 1376261145539134208036219)
                      ·
                        rfl

theorem cell23_2680259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 3, 3].length) (baseStart_2680259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2680259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2680259 prefixEnd_2680259 := by exact prefixLift 2680259
  have htrace : WordTrace (prefixWord ++ tailWord_2680259) baseStart_2680259 baseEnd_2680259 := by
    simpa [prefixWord, tailWord_2680259, baseEnd_2680259] using wordTrace_append hprefix tailTrace_2680259
  have hstable : (prefixWord ++ tailWord_2680259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680259).length < 2 ^ (prefixWord ++ tailWord_2680259).sum := by decide
  have hdescent : baseEnd_2680259 < baseStart_2680259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
