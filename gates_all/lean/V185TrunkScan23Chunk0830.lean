import V185TrunkScan23Chunk0829

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4910801 : List Nat := [1, 2, 2, 1, 2, 4, 2, 1, 8]
def baseStart_4910801 : Nat := 118140960795 + 4910801 * 2 ^ 59
def prefixEnd_4910801 : Nat := 4983230072969 + 3 ^ 40 * 4910801 * 2
def baseEnd_4910801 : Nat := 280177923508905133578127

theorem tailTrace_4910801 : CollatzResearch.WordTrace tailWord_4910801 prefixEnd_4910801 280177923508905133578127 := by
  unfold tailWord_4910801
  simp only [CollatzResearch.WordTrace]
  refine ⟨179111627082014149883748257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119407751388009433255832171 179111627082014149883748257)
  ·
    refine ⟨134333720311510612412811193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179111627082014149883748257 134333720311510612412811193)
    ·
      refine ⟨100750290233632959309608395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134333720311510612412811193 100750290233632959309608395)
      ·
        refine ⟨151125435350449438964412593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100750290233632959309608395 151125435350449438964412593)
        ·
          refine ⟨113344076512837079223309445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151125435350449438964412593 113344076512837079223309445)
          ·
            refine ⟨21252014346156952354370521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113344076512837079223309445 21252014346156952354370521)
            ·
              refine ⟨15939010759617714265777891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21252014346156952354370521 15939010759617714265777891)
              ·
                refine ⟨23908516139426571398666837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15939010759617714265777891 23908516139426571398666837)
                ·
                  refine ⟨280177923508905133578127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23908516139426571398666837 280177923508905133578127)
                  ·
                    rfl

theorem cell23_4910801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 8].length) (baseStart_4910801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4910801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4910801 prefixEnd_4910801 := by exact prefixLift 4910801
  have htrace : WordTrace (prefixWord ++ tailWord_4910801) baseStart_4910801 baseEnd_4910801 := by
    simpa [prefixWord, tailWord_4910801, baseEnd_4910801] using wordTrace_append hprefix tailTrace_4910801
  have hstable : (prefixWord ++ tailWord_4910801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4910801).length < 2 ^ (prefixWord ++ tailWord_4910801).sum := by decide
  have hdescent : baseEnd_4910801 < baseStart_4910801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4910801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4910899 : List Nat := [1, 1, 1, 2, 8, 1, 2, 1, 1, 5]
def baseStart_4910899 : Nat := 118140960795 + 4910899 * 2 ^ 59
def prefixEnd_4910899 : Nat := 4983230072969 + 3 ^ 40 * 4910899 * 2
def baseEnd_4910899 : Nat := 840550544228095606259231

theorem tailTrace_4910899 : CollatzResearch.WordTrace tailWord_4910899 prefixEnd_4910899 840550544228095606259231 := by
  unfold tailWord_4910899
  simp only [CollatzResearch.WordTrace]
  refine ⟨179115201435659112620815751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119410134290439408413877167 179115201435659112620815751)
  ·
    refine ⟨268672802153488668931223627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179115201435659112620815751 268672802153488668931223627)
    ·
      refine ⟨403009203230233003396835441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268672802153488668931223627 403009203230233003396835441)
      ·
        refine ⟨302256902422674752547626581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 403009203230233003396835441 302256902422674752547626581)
        ·
          refine ⟨3542073075265719756417499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 302256902422674752547626581 3542073075265719756417499)
          ·
            refine ⟨5313109612898579634626249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3542073075265719756417499 5313109612898579634626249)
            ·
              refine ⟨3984832209673934725969687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5313109612898579634626249 3984832209673934725969687)
              ·
                refine ⟨5977248314510902088954531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3984832209673934725969687 5977248314510902088954531)
                ·
                  refine ⟨8965872471766353133431797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5977248314510902088954531 8965872471766353133431797)
                  ·
                    refine ⟨840550544228095606259231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8965872471766353133431797 840550544228095606259231)
                    ·
                      rfl

theorem cell23_4910899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 1, 1, 5].length) (baseStart_4910899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4910899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4910899 prefixEnd_4910899 := by exact prefixLift 4910899
  have htrace : WordTrace (prefixWord ++ tailWord_4910899) baseStart_4910899 baseEnd_4910899 := by
    simpa [prefixWord, tailWord_4910899, baseEnd_4910899] using wordTrace_append hprefix tailTrace_4910899
  have hstable : (prefixWord ++ tailWord_4910899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4910899).length < 2 ^ (prefixWord ++ tailWord_4910899).sum := by decide
  have hdescent : baseEnd_4910899 < baseStart_4910899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4910899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4910919 : List Nat := [1, 1, 4, 1, 2, 1, 4, 4, 1, 2, 2]
def baseStart_4910919 : Nat := 118140960795 + 4910919 * 2 ^ 59
def prefixEnd_4910919 : Nat := 4983230072969 + 3 ^ 40 * 4910919 * 2
def baseEnd_4910919 : Nat := 2521661902297376740527601

theorem tailTrace_4910919 : CollatzResearch.WordTrace tailWord_4910919 prefixEnd_4910919 2521661902297376740527601 := by
  unfold tailWord_4910919
  simp only [CollatzResearch.WordTrace]
  refine ⟨179115930895586656036543811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119410620597057770691029207 179115930895586656036543811)
  ·
    refine ⟨268673896343379984054815717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179115930895586656036543811 268673896343379984054815717)
    ·
      refine ⟨50376355564383747010277947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 268673896343379984054815717 50376355564383747010277947)
      ·
        refine ⟨75564533346575620515416921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50376355564383747010277947 75564533346575620515416921)
        ·
          refine ⟨56673400009931715386562691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75564533346575620515416921 56673400009931715386562691)
          ·
            refine ⟨85010100014897573079844037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56673400009931715386562691 85010100014897573079844037)
            ·
              refine ⟨15939393752793294952470757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85010100014897573079844037 15939393752793294952470757)
              ·
                refine ⟨2988636328648742803588267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15939393752793294952470757 2988636328648742803588267)
                ·
                  refine ⟨4482954492973114205382401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2988636328648742803588267 4482954492973114205382401)
                  ·
                    refine ⟨3362215869729835654036801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4482954492973114205382401 3362215869729835654036801)
                    ·
                      refine ⟨2521661902297376740527601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3362215869729835654036801 2521661902297376740527601)
                      ·
                        rfl

theorem cell23_4910919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 4, 1, 2, 2].length) (baseStart_4910919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4910919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4910919 prefixEnd_4910919 := by exact prefixLift 4910919
  have htrace : WordTrace (prefixWord ++ tailWord_4910919) baseStart_4910919 baseEnd_4910919 := by
    simpa [prefixWord, tailWord_4910919, baseEnd_4910919] using wordTrace_append hprefix tailTrace_4910919
  have hstable : (prefixWord ++ tailWord_4910919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4910919).length < 2 ^ (prefixWord ++ tailWord_4910919).sum := by decide
  have hdescent : baseEnd_4910919 < baseStart_4910919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4910919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4910932 : List Nat := [2, 4, 1, 1, 3, 3, 1, 1, 1, 2, 4]
def baseStart_4910932 : Nat := 118140960795 + 4910932 * 2 ^ 59
def prefixEnd_4910932 : Nat := 4983230072969 + 3 ^ 40 * 4910932 * 2
def baseEnd_4910932 : Nat := 2521668577545885189665041

theorem tailTrace_4910932 : CollatzResearch.WordTrace tailWord_4910932 prefixEnd_4910932 2521668577545885189665041 := by
  unfold tailWord_4910932
  simp only [CollatzResearch.WordTrace]
  refine ⟨89558202522269779628383525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119410936696359706171178033 89558202522269779628383525)
  ·
    refine ⟨16792162972925583680321911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89558202522269779628383525 16792162972925583680321911)
    ·
      refine ⟨25188244459388375520482867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16792162972925583680321911 25188244459388375520482867)
      ·
        refine ⟨37782366689082563280724301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25188244459388375520482867 37782366689082563280724301)
        ·
          refine ⟨14168387508405961230271613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37782366689082563280724301 14168387508405961230271613)
          ·
            refine ⟨5313145315652235461351855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14168387508405961230271613 5313145315652235461351855)
            ·
              refine ⟨7969717973478353192027783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5313145315652235461351855 7969717973478353192027783)
              ·
                refine ⟨11954576960217529788041675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7969717973478353192027783 11954576960217529788041675)
                ·
                  refine ⟨17931865440326294682062513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11954576960217529788041675 17931865440326294682062513)
                  ·
                    refine ⟨13448899080244721011546885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17931865440326294682062513 13448899080244721011546885)
                    ·
                      refine ⟨2521668577545885189665041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13448899080244721011546885 2521668577545885189665041)
                      ·
                        rfl

theorem cell23_4910932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_4910932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4910932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4910932 prefixEnd_4910932 := by exact prefixLift 4910932
  have htrace : WordTrace (prefixWord ++ tailWord_4910932) baseStart_4910932 baseEnd_4910932 := by
    simpa [prefixWord, tailWord_4910932, baseEnd_4910932] using wordTrace_append hprefix tailTrace_4910932
  have hstable : (prefixWord ++ tailWord_4910932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4910932).length < 2 ^ (prefixWord ++ tailWord_4910932).sum := by decide
  have hdescent : baseEnd_4910932 < baseStart_4910932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4910932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4910988 : List Nat := [2, 2, 1, 2, 1, 2, 1, 3, 1, 4, 4]
def baseStart_4910988 : Nat := 118140960795 + 4910988 * 2 ^ 59
def prefixEnd_4910988 : Nat := 4983230072969 + 3 ^ 40 * 4910988 * 2
def baseEnd_4910988 : Nat := 2521697332462536970564783

theorem tailTrace_4910988 : CollatzResearch.WordTrace tailWord_4910988 prefixEnd_4910988 2521697332462536970564783 := by
  unfold tailWord_4910988
  simp only [CollatzResearch.WordTrace]
  refine ⟨89559223766168340410402809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119412298354891120547203745 89559223766168340410402809)
  ·
    refine ⟨67169417824626255307802107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89559223766168340410402809 67169417824626255307802107)
    ·
      refine ⟨100754126736939382961703161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67169417824626255307802107 100754126736939382961703161)
      ·
        refine ⟨75565595052704537221277371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100754126736939382961703161 75565595052704537221277371)
        ·
          refine ⟨113348392579056805831916057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75565595052704537221277371 113348392579056805831916057)
          ·
            refine ⟨85011294434292604373937043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113348392579056805831916057 85011294434292604373937043)
            ·
              refine ⟨127516941651438906560905565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85011294434292604373937043 127516941651438906560905565)
              ·
                refine ⟨47818853119289589960339587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127516941651438906560905565 47818853119289589960339587)
                ·
                  refine ⟨71728279678934384940509381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47818853119289589960339587 71728279678934384940509381)
                  ·
                    refine ⟨13449052439800197176345509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 71728279678934384940509381 13449052439800197176345509)
                    ·
                      refine ⟨2521697332462536970564783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13449052439800197176345509 2521697332462536970564783)
                      ·
                        rfl

theorem cell23_4910988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_4910988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4910988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4910988 prefixEnd_4910988 := by exact prefixLift 4910988
  have htrace : WordTrace (prefixWord ++ tailWord_4910988) baseStart_4910988 baseEnd_4910988 := by
    simpa [prefixWord, tailWord_4910988, baseEnd_4910988] using wordTrace_append hprefix tailTrace_4910988
  have hstable : (prefixWord ++ tailWord_4910988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4910988).length < 2 ^ (prefixWord ++ tailWord_4910988).sum := by decide
  have hdescent : baseEnd_4910988 < baseStart_4910988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4910988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4910996 : List Nat := [2, 4, 2, 1, 1, 4, 1, 2, 1, 3, 2]
def baseStart_4910996 : Nat := 118140960795 + 4910996 * 2 ^ 59
def prefixEnd_4910996 : Nat := 4983230072969 + 3 ^ 40 * 4910996 * 2
def baseEnd_4910996 : Nat := 2521701440307772939264747

theorem tailTrace_4910996 : CollatzResearch.WordTrace tailWord_4910996 prefixEnd_4910996 2521701440307772939264747 := by
  unfold tailWord_4910996
  simp only [CollatzResearch.WordTrace]
  refine ⟨89559369658153849093548421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119412492877538465458064561 89559369658153849093548421)
  ·
    refine ⟨16792381810903846705040329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89559369658153849093548421 16792381810903846705040329)
    ·
      refine ⟨12594286358177885028780247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16792381810903846705040329 12594286358177885028780247)
      ·
        refine ⟨18891429537266827543170371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12594286358177885028780247 18891429537266827543170371)
        ·
          refine ⟨28337144305900241314755557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18891429537266827543170371 28337144305900241314755557)
          ·
            refine ⟨5313214557356295246516667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28337144305900241314755557 5313214557356295246516667)
            ·
              refine ⟨7969821836034442869775001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5313214557356295246516667 7969821836034442869775001)
              ·
                refine ⟨5977366377025832152331251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7969821836034442869775001 5977366377025832152331251)
                ·
                  refine ⟨8966049565538748228496877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5977366377025832152331251 8966049565538748228496877)
                  ·
                    refine ⟨3362268587077030585686329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8966049565538748228496877 3362268587077030585686329)
                    ·
                      refine ⟨2521701440307772939264747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3362268587077030585686329 2521701440307772939264747)
                      ·
                        rfl

theorem cell23_4910996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_4910996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4910996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4910996 prefixEnd_4910996 := by exact prefixLift 4910996
  have htrace : WordTrace (prefixWord ++ tailWord_4910996) baseStart_4910996 baseEnd_4910996 := by
    simpa [prefixWord, tailWord_4910996, baseEnd_4910996] using wordTrace_append hprefix tailTrace_4910996
  have hstable : (prefixWord ++ tailWord_4910996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4910996).length < 2 ^ (prefixWord ++ tailWord_4910996).sum := by decide
  have hdescent : baseEnd_4910996 < baseStart_4910996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4910996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911009 : List Nat := [1, 2, 3, 4, 2, 1, 1, 2, 1, 4, 2]
def baseStart_4911009 : Nat := 118140960795 + 4911009 * 2 ^ 59
def prefixEnd_4911009 : Nat := 4983230072969 + 3 ^ 40 * 4911009 * 2
def baseEnd_4911009 : Nat := 2521708115556281388402187

theorem tailTrace_4911009 : CollatzResearch.WordTrace tailWord_4911009 prefixEnd_4911009 2521708115556281388402187 := by
  unfold tailWord_4911009
  simp only [CollatzResearch.WordTrace]
  refine ⟨179119213465260601407320081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119412808976840400938213387 179119213465260601407320081)
  ·
    refine ⟨134339410098945451055490061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179119213465260601407320081 134339410098945451055490061)
    ·
      refine ⟨50377278787104544145808773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134339410098945451055490061 50377278787104544145808773)
      ·
        refine ⟨9445739772582102027339145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50377278787104544145808773 9445739772582102027339145)
        ·
          refine ⟨7084304829436576520504359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9445739772582102027339145 7084304829436576520504359)
          ·
            refine ⟨10626457244154864780756539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7084304829436576520504359 10626457244154864780756539)
            ·
              refine ⟨15939685866232297171134809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10626457244154864780756539 15939685866232297171134809)
              ·
                refine ⟨11954764399674222878351107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15939685866232297171134809 11954764399674222878351107)
                ·
                  refine ⟨17932146599511334317526661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11954764399674222878351107 17932146599511334317526661)
                  ·
                    refine ⟨3362277487408375184536249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17932146599511334317526661 3362277487408375184536249)
                    ·
                      refine ⟨2521708115556281388402187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3362277487408375184536249 2521708115556281388402187)
                      ·
                        rfl

theorem cell23_4911009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_4911009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911009 prefixEnd_4911009 := by exact prefixLift 4911009
  have htrace : WordTrace (prefixWord ++ tailWord_4911009) baseStart_4911009 baseEnd_4911009 := by
    simpa [prefixWord, tailWord_4911009, baseEnd_4911009] using wordTrace_append hprefix tailTrace_4911009
  have hstable : (prefixWord ++ tailWord_4911009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911009).length < 2 ^ (prefixWord ++ tailWord_4911009).sum := by decide
  have hdescent : baseEnd_4911009 < baseStart_4911009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911035 : List Nat := [1, 1, 1, 1, 1, 2, 2, 5, 2, 5, 2]
def baseStart_4911035 : Nat := 118140960795 + 4911035 * 2 ^ 59
def prefixEnd_4911035 : Nat := 4983230072969 + 3 ^ 40 * 4911035 * 2
def baseEnd_4911035 : Nat := 2521721466053298286677067

theorem tailTrace_4911035 : CollatzResearch.WordTrace tailWord_4911035 prefixEnd_4911035 2521721466053298286677067 := by
  unfold tailWord_4911035
  simp only [CollatzResearch.WordTrace]
  refine ⟨179120161763166407847766559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119413441175444271898511039 179120161763166407847766559)
  ·
    refine ⟨268680242644749611771649839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179120161763166407847766559 268680242644749611771649839)
    ·
      refine ⟨403020363967124417657474759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268680242644749611771649839 403020363967124417657474759)
      ·
        refine ⟨604530545950686626486212139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 403020363967124417657474759 604530545950686626486212139)
        ·
          refine ⟨906795818926029939729318209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 604530545950686626486212139 906795818926029939729318209)
          ·
            refine ⟨680096864194522454796988657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 906795818926029939729318209 680096864194522454796988657)
            ·
              refine ⟨510072648145891841097741493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 680096864194522454796988657 510072648145891841097741493)
              ·
                refine ⟨47819310763677360102913265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 510072648145891841097741493 47819310763677360102913265)
                ·
                  refine ⟨35864483072758020077184949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47819310763677360102913265 35864483072758020077184949)
                  ·
                    refine ⟨3362295288071064382236089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35864483072758020077184949 3362295288071064382236089)
                    ·
                      refine ⟨2521721466053298286677067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3362295288071064382236089 2521721466053298286677067)
                      ·
                        rfl

theorem cell23_4911035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 5, 2].length) (baseStart_4911035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911035 prefixEnd_4911035 := by exact prefixLift 4911035
  have htrace : WordTrace (prefixWord ++ tailWord_4911035) baseStart_4911035 baseEnd_4911035 := by
    simpa [prefixWord, tailWord_4911035, baseEnd_4911035] using wordTrace_append hprefix tailTrace_4911035
  have hstable : (prefixWord ++ tailWord_4911035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911035).length < 2 ^ (prefixWord ++ tailWord_4911035).sum := by decide
  have hdescent : baseEnd_4911035 < baseStart_4911035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911082 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 4, 4, 2]
def baseStart_4911082 : Nat := 118140960795 + 4911082 * 2 ^ 59
def prefixEnd_4911082 : Nat := 4983230072969 + 3 ^ 40 * 4911082 * 2
def baseEnd_4911082 : Nat := 2521745599644059602789351

theorem tailTrace_4911082 : CollatzResearch.WordTrace tailWord_4911082 prefixEnd_4911082 2521745599644059602789351 := by
  unfold tailWord_4911082
  simp only [CollatzResearch.WordTrace]
  refine ⟨44780468998499033718681875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119414583995997423249818333 44780468998499033718681875)
  ·
    refine ⟨67170703497748550578022813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44780468998499033718681875 67170703497748550578022813)
    ·
      refine ⟨25189013811655706466758555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67170703497748550578022813 25189013811655706466758555)
      ·
        refine ⟨37783520717483559700137833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25189013811655706466758555 37783520717483559700137833)
        ·
          refine ⟨28337640538112669775103375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37783520717483559700137833 28337640538112669775103375)
          ·
            refine ⟨42506460807169004662655063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28337640538112669775103375 42506460807169004662655063)
            ·
              refine ⟨63759691210753506993982595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42506460807169004662655063 63759691210753506993982595)
              ·
                refine ⟨95639536816130260490973893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63759691210753506993982595 95639536816130260490973893)
                ·
                  refine ⟨17932413153024423842057605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95639536816130260490973893 17932413153024423842057605)
                  ·
                    refine ⟨3362327466192079470385801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17932413153024423842057605 3362327466192079470385801)
                    ·
                      refine ⟨2521745599644059602789351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3362327466192079470385801 2521745599644059602789351)
                      ·
                        rfl

theorem cell23_4911082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 4, 4, 2].length) (baseStart_4911082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911082 prefixEnd_4911082 := by exact prefixLift 4911082
  have htrace : WordTrace (prefixWord ++ tailWord_4911082) baseStart_4911082 baseEnd_4911082 := by
    simpa [prefixWord, tailWord_4911082, baseEnd_4911082] using wordTrace_append hprefix tailTrace_4911082
  have hstable : (prefixWord ++ tailWord_4911082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911082).length < 2 ^ (prefixWord ++ tailWord_4911082).sum := by decide
  have hdescent : baseEnd_4911082 < baseStart_4911082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911115 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 2, 5, 3]
def baseStart_4911115 : Nat := 118140960795 + 4911115 * 2 ^ 59
def prefixEnd_4911115 : Nat := 4983230072969 + 3 ^ 40 * 4911115 * 2
def baseEnd_4911115 : Nat := 2521762544505657973676699

theorem tailTrace_4911115 : CollatzResearch.WordTrace tailWord_4911115 prefixEnd_4911115 2521762544505657973676699 := by
  unfold tailWord_4911115
  simp only [CollatzResearch.WordTrace]
  refine ⟨179123079602876581510678799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119415386401917721007119199 179123079602876581510678799)
  ·
    refine ⟨268684619404314872266018199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179123079602876581510678799 268684619404314872266018199)
    ·
      refine ⟨403026929106472308399027299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268684619404314872266018199 403026929106472308399027299)
      ·
        refine ⟨604540393659708462598540949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 403026929106472308399027299 604540393659708462598540949)
        ·
          refine ⟨28337830952798834184306607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 604540393659708462598540949 28337830952798834184306607)
          ·
            refine ⟨42506746429198251276459911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28337830952798834184306607 42506746429198251276459911)
            ·
              refine ⟨63760119643797376914689867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42506746429198251276459911 63760119643797376914689867)
              ·
                refine ⟨95640179465696065372034801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63760119643797376914689867 95640179465696065372034801)
                ·
                  refine ⟨71730134599272049029026101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95640179465696065372034801 71730134599272049029026101)
                  ·
                    refine ⟨6724700118681754596471197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 71730134599272049029026101 6724700118681754596471197)
                    ·
                      refine ⟨2521762544505657973676699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6724700118681754596471197 2521762544505657973676699)
                      ·
                        rfl

theorem cell23_4911115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 5, 3].length) (baseStart_4911115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911115 prefixEnd_4911115 := by exact prefixLift 4911115
  have htrace : WordTrace (prefixWord ++ tailWord_4911115) baseStart_4911115 baseEnd_4911115 := by
    simpa [prefixWord, tailWord_4911115, baseEnd_4911115] using wordTrace_append hprefix tailTrace_4911115
  have hstable : (prefixWord ++ tailWord_4911115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911115).length < 2 ^ (prefixWord ++ tailWord_4911115).sum := by decide
  have hdescent : baseEnd_4911115 < baseStart_4911115 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911143 : List Nat := [1, 1, 7, 1, 3, 1, 1, 1, 3, 4]
def baseStart_4911143 : Nat := 118140960795 + 4911143 * 2 ^ 59
def prefixEnd_4911143 : Nat := 4983230072969 + 3 ^ 40 * 4911143 * 2
def baseEnd_4911143 : Nat := 840592307321327954708857

theorem tailTrace_4911143 : CollatzResearch.WordTrace tailWord_4911143 prefixEnd_4911143 840592307321327954708857 := by
  unfold tailWord_4911143
  simp only [CollatzResearch.WordTrace]
  refine ⟨179124100846775142292698083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119416067231183428195132055 179124100846775142292698083)
  ·
    refine ⟨268686151270162713439047125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179124100846775142292698083 268686151270162713439047125)
    ·
      refine ⟨6297331670394438596227667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 268686151270162713439047125 6297331670394438596227667)
      ·
        refine ⟨9445997505591657894341501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6297331670394438596227667 9445997505591657894341501)
        ·
          refine ⟨3542249064596871710378063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9445997505591657894341501 3542249064596871710378063)
          ·
            refine ⟨5313373596895307565567095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3542249064596871710378063 5313373596895307565567095)
            ·
              refine ⟨7970060395342961348350643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5313373596895307565567095 7970060395342961348350643)
              ·
                refine ⟨11955090593014442022525965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7970060395342961348350643 11955090593014442022525965)
                ·
                  refine ⟨4483158972380415758447237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11955090593014442022525965 4483158972380415758447237)
                  ·
                    refine ⟨840592307321327954708857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4483158972380415758447237 840592307321327954708857)
                    ·
                      rfl

theorem cell23_4911143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_4911143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911143 prefixEnd_4911143 := by exact prefixLift 4911143
  have htrace : WordTrace (prefixWord ++ tailWord_4911143) baseStart_4911143 baseEnd_4911143 := by
    simpa [prefixWord, tailWord_4911143, baseEnd_4911143] using wordTrace_append hprefix tailTrace_4911143
  have hstable : (prefixWord ++ tailWord_4911143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911143).length < 2 ^ (prefixWord ++ tailWord_4911143).sum := by decide
  have hdescent : baseEnd_4911143 < baseStart_4911143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911169 : List Nat := [1, 2, 5, 1, 2, 1, 3, 2, 1, 5]
def baseStart_4911169 : Nat := 118140960795 + 4911169 * 2 ^ 59
def prefixEnd_4911169 : Nat := 4983230072969 + 3 ^ 40 * 4911169 * 2
def baseEnd_4911169 : Nat := 840596757487000254133817

theorem tailTrace_4911169 : CollatzResearch.WordTrace tailWord_4911169 prefixEnd_4911169 840596757487000254133817 := by
  unfold tailWord_4911169
  simp only [CollatzResearch.WordTrace]
  refine ⟨179125049144680948733144561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119416699429787299155429707 179125049144680948733144561)
  ·
    refine ⟨134343786858510711549858421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179125049144680948733144561 134343786858510711549858421)
    ·
      refine ⟨12594730017985379207799227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 134343786858510711549858421 12594730017985379207799227)
      ·
        refine ⟨18892095026978068811698841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12594730017985379207799227 18892095026978068811698841)
        ·
          refine ⟨14169071270233551608774131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18892095026978068811698841 14169071270233551608774131)
          ·
            refine ⟨21253606905350327413161197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14169071270233551608774131 21253606905350327413161197)
            ·
              refine ⟨7970102589506372779935449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21253606905350327413161197 7970102589506372779935449)
              ·
                refine ⟨5977576942129779584951587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7970102589506372779935449 5977576942129779584951587)
                ·
                  refine ⟨8966365413194669377427381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5977576942129779584951587 8966365413194669377427381)
                  ·
                    refine ⟨840596757487000254133817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8966365413194669377427381 840596757487000254133817)
                    ·
                      rfl

theorem cell23_4911169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_4911169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911169 prefixEnd_4911169 := by exact prefixLift 4911169
  have htrace : WordTrace (prefixWord ++ tailWord_4911169) baseStart_4911169 baseEnd_4911169 := by
    simpa [prefixWord, tailWord_4911169, baseEnd_4911169] using wordTrace_append hprefix tailTrace_4911169
  have hstable : (prefixWord ++ tailWord_4911169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911169).length < 2 ^ (prefixWord ++ tailWord_4911169).sum := by decide
  have hdescent : baseEnd_4911169 < baseStart_4911169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911182 : List Nat := [4, 1, 1, 1, 1, 5, 1, 2, 1, 6]
def baseStart_4911182 : Nat := 118140960795 + 4911182 * 2 ^ 59
def prefixEnd_4911182 : Nat := 4983230072969 + 3 ^ 40 * 4911182 * 2
def baseEnd_4911182 : Nat := 840598982569836403846297

theorem tailTrace_4911182 : CollatzResearch.WordTrace tailWord_4911182 prefixEnd_4911182 840598982569836403846297 := by
  unfold tailWord_4911182
  simp only [CollatzResearch.WordTrace]
  refine ⟨22390690411704231494170975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119417015529089234635578533 22390690411704231494170975)
  ·
    refine ⟨33586035617556347241256463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22390690411704231494170975 33586035617556347241256463)
    ·
      refine ⟨50379053426334520861884695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33586035617556347241256463 50379053426334520861884695)
      ·
        refine ⟨75568580139501781292827043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50379053426334520861884695 75568580139501781292827043)
        ·
          refine ⟨113352870209252671939240565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75568580139501781292827043 113352870209252671939240565)
          ·
            refine ⟨10626831582117437994303803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 113352870209252671939240565 10626831582117437994303803)
            ·
              refine ⟨15940247373176156991455705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10626831582117437994303803 15940247373176156991455705)
              ·
                refine ⟨11955185529882117743591779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15940247373176156991455705 11955185529882117743591779)
                ·
                  refine ⟨17932778294823176615387669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11955185529882117743591779 17932778294823176615387669)
                  ·
                    refine ⟨840598982569836403846297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17932778294823176615387669 840598982569836403846297)
                    ·
                      rfl

theorem cell23_4911182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_4911182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911182 prefixEnd_4911182 := by exact prefixLift 4911182
  have htrace : WordTrace (prefixWord ++ tailWord_4911182) baseStart_4911182 baseEnd_4911182 := by
    simpa [prefixWord, tailWord_4911182, baseEnd_4911182] using wordTrace_append hprefix tailTrace_4911182
  have hstable : (prefixWord ++ tailWord_4911182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911182).length < 2 ^ (prefixWord ++ tailWord_4911182).sum := by decide
  have hdescent : baseEnd_4911182 < baseStart_4911182 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911186 : List Nat := [3, 2, 2, 1, 4, 1, 3, 1, 1, 5]
def baseStart_4911186 : Nat := 118140960795 + 4911186 * 2 ^ 59
def prefixEnd_4911186 : Nat := 4983230072969 + 3 ^ 40 * 4911186 * 2
def baseEnd_4911186 : Nat := 840599667210709065296291

theorem tailTrace_4911186 : CollatzResearch.WordTrace tailWord_4911186 prefixEnd_4911186 840599667210709065296291 := by
  unfold tailWord_4911186
  simp only [CollatzResearch.WordTrace]
  refine ⟨44781417296404840159128353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119417112790412907091008941 44781417296404840159128353)
  ·
    refine ⟨33586062972303630119346265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44781417296404840159128353 33586062972303630119346265)
    ·
      refine ⟨25189547229227722589509699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33586062972303630119346265 25189547229227722589509699)
      ·
        refine ⟨37784320843841583884264549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25189547229227722589509699 37784320843841583884264549)
        ·
          refine ⟨7084560158220296978299603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37784320843841583884264549 7084560158220296978299603)
          ·
            refine ⟨10626840237330445467449405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7084560158220296978299603 10626840237330445467449405)
            ·
              refine ⟨3985065088998917050293527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10626840237330445467449405 3985065088998917050293527)
              ·
                refine ⟨5977597633498375575440291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3985065088998917050293527 5977597633498375575440291)
                ·
                  refine ⟨8966396450247563363160437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5977597633498375575440291 8966396450247563363160437)
                  ·
                    refine ⟨840599667210709065296291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8966396450247563363160437 840599667210709065296291)
                    ·
                      rfl

theorem cell23_4911186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_4911186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911186 prefixEnd_4911186 := by exact prefixLift 4911186
  have htrace : WordTrace (prefixWord ++ tailWord_4911186) baseStart_4911186 baseEnd_4911186 := by
    simpa [prefixWord, tailWord_4911186, baseEnd_4911186] using wordTrace_append hprefix tailTrace_4911186
  have hstable : (prefixWord ++ tailWord_4911186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911186).length < 2 ^ (prefixWord ++ tailWord_4911186).sum := by decide
  have hdescent : baseEnd_4911186 < baseStart_4911186 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911192 : List Nat := [2, 1, 2, 2, 1, 4, 3, 1, 1, 1, 5]
def baseStart_4911192 : Nat := 118140960795 + 4911192 * 2 ^ 59
def prefixEnd_4911192 : Nat := 4983230072969 + 3 ^ 40 * 4911192 * 2
def baseEnd_4911192 : Nat := 2521802082516054172413845

theorem tailTrace_4911192 : CollatzResearch.WordTrace tailWord_4911192 prefixEnd_4911192 2521802082516054172413845 := by
  unfold tailWord_4911192
  simp only [CollatzResearch.WordTrace]
  refine ⟨89562944011798811830615915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119417258682398415774154553 89562944011798811830615915)
  ·
    refine ⟨134344416017698217745923873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89562944011798811830615915 134344416017698217745923873)
    ·
      refine ⟨100758312013273663309442905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134344416017698217745923873 100758312013273663309442905)
      ·
        refine ⟨75568734009955247482082179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100758312013273663309442905 75568734009955247482082179)
        ·
          refine ⟨113353101014932871223123269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75568734009955247482082179 113353101014932871223123269)
          ·
            refine ⟨21253706440299913354335613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113353101014932871223123269 21253706440299913354335613)
            ·
              refine ⟨7970139915112467507875855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21253706440299913354335613 7970139915112467507875855)
              ·
                refine ⟨11955209872668701261813783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7970139915112467507875855 11955209872668701261813783)
                ·
                  refine ⟨17932814809003051892720675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11955209872668701261813783 17932814809003051892720675)
                  ·
                    refine ⟨26899222213504577839081013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17932814809003051892720675 26899222213504577839081013)
                    ·
                      refine ⟨2521802082516054172413845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26899222213504577839081013 2521802082516054172413845)
                      ·
                        rfl

theorem cell23_4911192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 1, 1, 5].length) (baseStart_4911192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911192 prefixEnd_4911192 := by exact prefixLift 4911192
  have htrace : WordTrace (prefixWord ++ tailWord_4911192) baseStart_4911192 baseEnd_4911192 := by
    simpa [prefixWord, tailWord_4911192, baseEnd_4911192] using wordTrace_append hprefix tailTrace_4911192
  have hstable : (prefixWord ++ tailWord_4911192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911192).length < 2 ^ (prefixWord ++ tailWord_4911192).sum := by decide
  have hdescent : baseEnd_4911192 < baseStart_4911192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911212 : List Nat := [2, 2, 1, 1, 3, 5, 1, 8]
def baseStart_4911212 : Nat := 118140960795 + 4911212 * 2 ^ 59
def prefixEnd_4911212 : Nat := 4983230072969 + 3 ^ 40 * 4911212 * 2
def baseEnd_4911212 : Nat := 93400457486264596080139

theorem tailTrace_4911212 : CollatzResearch.WordTrace tailWord_4911212 prefixEnd_4911212 93400457486264596080139 := by
  unfold tailWord_4911212
  simp only [CollatzResearch.WordTrace]
  refine ⟨89563308741762583538479945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119417744989016778051306593 89563308741762583538479945)
  ·
    refine ⟨67172481556321937653859959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89563308741762583538479945 67172481556321937653859959)
    ·
      refine ⟨100758722334482906480789939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67172481556321937653859959 100758722334482906480789939)
      ·
        refine ⟨151138083501724359721184909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100758722334482906480789939 151138083501724359721184909)
        ·
          refine ⟨56676781313146634895444341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151138083501724359721184909 56676781313146634895444341)
          ·
            refine ⟨5313448248107497021447907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56676781313146634895444341 5313448248107497021447907)
            ·
              refine ⟨7970172372161245532171861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5313448248107497021447907 7970172372161245532171861)
              ·
                refine ⟨93400457486264596080139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7970172372161245532171861 93400457486264596080139)
                ·
                  rfl

theorem cell23_4911212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 8].length) (baseStart_4911212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911212 prefixEnd_4911212 := by exact prefixLift 4911212
  have htrace : WordTrace (prefixWord ++ tailWord_4911212) baseStart_4911212 baseEnd_4911212 := by
    simpa [prefixWord, tailWord_4911212, baseEnd_4911212] using wordTrace_append hprefix tailTrace_4911212
  have hstable : (prefixWord ++ tailWord_4911212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911212).length < 2 ^ (prefixWord ++ tailWord_4911212).sum := by decide
  have hdescent : baseEnd_4911212 < baseStart_4911212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911240 : List Nat := [2, 1, 3, 4, 1, 2, 2, 3, 1, 2, 2]
def baseStart_4911240 : Nat := 118140960795 + 4911240 * 2 ^ 59
def prefixEnd_4911240 : Nat := 4983230072969 + 3 ^ 40 * 4911240 * 2
def baseEnd_4911240 : Nat := 2521826729587469984613625

theorem tailTrace_4911240 : CollatzResearch.WordTrace tailWord_4911240 prefixEnd_4911240 2521826729587469984613625 := by
  unfold tailWord_4911240
  simp only [CollatzResearch.WordTrace]
  refine ⟨89563819363711863929489587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119418425818282485239319449 89563819363711863929489587)
  ·
    refine ⟨134345729045567795894234381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89563819363711863929489587 134345729045567795894234381)
    ·
      refine ⟨50379648392087923460337893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134345729045567795894234381 50379648392087923460337893)
      ·
        refine ⟨9446184073516485648813355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50379648392087923460337893 9446184073516485648813355)
        ·
          refine ⟨14169276110274728473220033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9446184073516485648813355 14169276110274728473220033)
          ·
            refine ⟨10626957082706046354915025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14169276110274728473220033 10626957082706046354915025)
            ·
              refine ⟨7970217812029534766186269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10626957082706046354915025 7970217812029534766186269)
              ·
                refine ⟨2988831679511075537319851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7970217812029534766186269 2988831679511075537319851)
                ·
                  refine ⟨4483247519266613305979777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2988831679511075537319851 4483247519266613305979777)
                  ·
                    refine ⟨3362435639449959979484833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4483247519266613305979777 3362435639449959979484833)
                    ·
                      refine ⟨2521826729587469984613625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3362435639449959979484833 2521826729587469984613625)
                      ·
                        rfl

theorem cell23_4911240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_4911240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911240 prefixEnd_4911240 := by exact prefixLift 4911240
  have htrace : WordTrace (prefixWord ++ tailWord_4911240) baseStart_4911240 baseEnd_4911240 := by
    simpa [prefixWord, tailWord_4911240, baseEnd_4911240] using wordTrace_append hprefix tailTrace_4911240
  have hstable : (prefixWord ++ tailWord_4911240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911240).length < 2 ^ (prefixWord ++ tailWord_4911240).sum := by decide
  have hdescent : baseEnd_4911240 < baseStart_4911240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911256 : List Nat := [2, 1, 2, 4, 3, 1, 1, 1, 4, 1, 3]
def baseStart_4911256 : Nat := 118140960795 + 4911256 * 2 ^ 59
def prefixEnd_4911256 : Nat := 4983230072969 + 3 ^ 40 * 4911256 * 2
def baseEnd_4911256 : Nat := 2521834945277941922013551

theorem tailTrace_4911256 : CollatzResearch.WordTrace tailWord_4911256 prefixEnd_4911256 2521834945277941922013551 := by
  unfold tailWord_4911256
  simp only [CollatzResearch.WordTrace]
  refine ⟨89564111147682881295780811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119418814863577175061041081 89564111147682881295780811)
  ·
    refine ⟨134346166721524321943671217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89564111147682881295780811 134346166721524321943671217)
    ·
      refine ⟨100759625041143241457753413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134346166721524321943671217 100759625041143241457753413)
      ·
        refine ⟨18892429695214357773328765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100759625041143241457753413 18892429695214357773328765)
        ·
          refine ⟨7084661135705384164998287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18892429695214357773328765 7084661135705384164998287)
          ·
            refine ⟨10626991703558076247497431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7084661135705384164998287 10626991703558076247497431)
            ·
              refine ⟨15940487555337114371246147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10626991703558076247497431 15940487555337114371246147)
              ·
                refine ⟨23910731333005671556869221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15940487555337114371246147 23910731333005671556869221)
                ·
                  refine ⟨4483262124938563416912979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23910731333005671556869221 4483262124938563416912979)
                  ·
                    refine ⟨6724893187407845125369469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4483262124938563416912979 6724893187407845125369469)
                    ·
                      refine ⟨2521834945277941922013551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6724893187407845125369469 2521834945277941922013551)
                      ·
                        rfl

theorem cell23_4911256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_4911256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911256 prefixEnd_4911256 := by exact prefixLift 4911256
  have htrace : WordTrace (prefixWord ++ tailWord_4911256) baseStart_4911256 baseEnd_4911256 := by
    simpa [prefixWord, tailWord_4911256, baseEnd_4911256] using wordTrace_append hprefix tailTrace_4911256
  have hstable : (prefixWord ++ tailWord_4911256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911256).length < 2 ^ (prefixWord ++ tailWord_4911256).sum := by decide
  have hdescent : baseEnd_4911256 < baseStart_4911256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911282 : List Nat := [3, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5]
def baseStart_4911282 : Nat := 118140960795 + 4911282 * 2 ^ 59
def prefixEnd_4911282 : Nat := 4983230072969 + 3 ^ 40 * 4911282 * 2
def baseEnd_4911282 : Nat := 2521848295774958820288431

theorem tailTrace_4911282 : CollatzResearch.WordTrace tailWord_4911282 prefixEnd_4911282 2521848295774958820288431 := by
  unfold tailWord_4911282
  simp only [CollatzResearch.WordTrace]
  refine ⟨44782292648317892258002025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119419447062181046021338733 44782292648317892258002025)
  ·
    refine ⟨33586719486238419193501519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44782292648317892258002025 33586719486238419193501519)
    ·
      refine ⟨50380079229357628790252279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33586719486238419193501519 50380079229357628790252279)
      ·
        refine ⟨75570118844036443185378419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50380079229357628790252279 75570118844036443185378419)
        ·
          refine ⟨113355178266054664778067629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75570118844036443185378419 113355178266054664778067629)
          ·
            refine ⟨42508191849770499291775361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113355178266054664778067629 42508191849770499291775361)
            ·
              refine ⟨31881143887327874468831521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42508191849770499291775361 31881143887327874468831521)
              ·
                refine ⟨23910857915495905851623641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31881143887327874468831521 23910857915495905851623641)
                ·
                  refine ⟨17933143436621929388717731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23910857915495905851623641 17933143436621929388717731)
                  ·
                    refine ⟨26899715154932894083076597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17933143436621929388717731 26899715154932894083076597)
                    ·
                      refine ⟨2521848295774958820288431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26899715154932894083076597 2521848295774958820288431)
                      ·
                        rfl

theorem cell23_4911282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_4911282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911282 prefixEnd_4911282 := by exact prefixLift 4911282
  have htrace : WordTrace (prefixWord ++ tailWord_4911282) baseStart_4911282 baseEnd_4911282 := by
    simpa [prefixWord, tailWord_4911282, baseEnd_4911282] using wordTrace_append hprefix tailTrace_4911282
  have hstable : (prefixWord ++ tailWord_4911282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911282).length < 2 ^ (prefixWord ++ tailWord_4911282).sum := by decide
  have hdescent : baseEnd_4911282 < baseStart_4911282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911296 : List Nat := [2, 1, 1, 2, 5, 1, 1, 2, 4, 2, 2]
def baseStart_4911296 : Nat := 118140960795 + 4911296 * 2 ^ 59
def prefixEnd_4911296 : Nat := 4983230072969 + 3 ^ 40 * 4911296 * 2
def baseEnd_4911296 : Nat := 2521855484504121765513367

theorem tailTrace_4911296 : CollatzResearch.WordTrace tailWord_4911296 prefixEnd_4911296 2521855484504121765513367 := by
  unfold tailWord_4911296
  simp only [CollatzResearch.WordTrace]
  refine ⟨89564840607610424711508871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119419787476813899615345161 89564840607610424711508871)
  ·
    refine ⟨134347260911415637067263307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89564840607610424711508871 134347260911415637067263307)
    ·
      refine ⟨201520891367123455600894961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134347260911415637067263307 201520891367123455600894961)
      ·
        refine ⟨151140668525342591700671221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201520891367123455600894961 151140668525342591700671221)
        ·
          refine ⟨14169437674250867971937927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 151140668525342591700671221 14169437674250867971937927)
          ·
            refine ⟨21254156511376301957906891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14169437674250867971937927 21254156511376301957906891)
            ·
              refine ⟨31881234767064452936860337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21254156511376301957906891 31881234767064452936860337)
              ·
                refine ⟨23910926075298339702645253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31881234767064452936860337 23910926075298339702645253)
                ·
                  refine ⟨4483298639118438694245985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23910926075298339702645253 4483298639118438694245985)
                  ·
                    refine ⟨3362473979338829020684489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4483298639118438694245985 3362473979338829020684489)
                    ·
                      refine ⟨2521855484504121765513367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3362473979338829020684489 2521855484504121765513367)
                      ·
                        rfl

theorem cell23_4911296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 4, 2, 2].length) (baseStart_4911296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911296 prefixEnd_4911296 := by exact prefixLift 4911296
  have htrace : WordTrace (prefixWord ++ tailWord_4911296) baseStart_4911296 baseEnd_4911296 := by
    simpa [prefixWord, tailWord_4911296, baseEnd_4911296] using wordTrace_append hprefix tailTrace_4911296
  have hstable : (prefixWord ++ tailWord_4911296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911296).length < 2 ^ (prefixWord ++ tailWord_4911296).sum := by decide
  have hdescent : baseEnd_4911296 < baseStart_4911296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911324 : List Nat := [2, 2, 5, 2, 2, 1, 2, 1, 2, 1, 3]
def baseStart_4911324 : Nat := 118140960795 + 4911324 * 2 ^ 59
def prefixEnd_4911324 : Nat := 4983230072969 + 3 ^ 40 * 4911324 * 2
def baseEnd_4911324 : Nat := 2521869861962447655963239

theorem tailTrace_4911324 : CollatzResearch.WordTrace tailWord_4911324 prefixEnd_4911324 2521869861962447655963239 := by
  unfold tailWord_4911324
  simp only [CollatzResearch.WordTrace]
  refine ⟨89565351229559705102518513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119420468306079606803358017 89565351229559705102518513)
  ·
    refine ⟨67174013422169778826888885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89565351229559705102518513 67174013422169778826888885)
    ·
      refine ⟨6297563758328416765020833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67174013422169778826888885 6297563758328416765020833)
      ·
        refine ⟨4723172818746312573765625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6297563758328416765020833 4723172818746312573765625)
        ·
          refine ⟨3542379614059734430324219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4723172818746312573765625 3542379614059734430324219)
          ·
            refine ⟨5313569421089601645486329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3542379614059734430324219 5313569421089601645486329)
            ·
              refine ⟨3985177065817201234114747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5313569421089601645486329 3985177065817201234114747)
              ·
                refine ⟨5977765598725801851172121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3985177065817201234114747 5977765598725801851172121)
                ·
                  refine ⟨4483324199044351388379091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5977765598725801851172121 4483324199044351388379091)
                  ·
                    refine ⟨6724986298566527082568637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4483324199044351388379091 6724986298566527082568637)
                    ·
                      refine ⟨2521869861962447655963239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6724986298566527082568637 2521869861962447655963239)
                      ·
                        rfl

theorem cell23_4911324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_4911324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911324 prefixEnd_4911324 := by exact prefixLift 4911324
  have htrace : WordTrace (prefixWord ++ tailWord_4911324) baseStart_4911324 baseEnd_4911324 := by
    simpa [prefixWord, tailWord_4911324, baseEnd_4911324] using wordTrace_append hprefix tailTrace_4911324
  have hstable : (prefixWord ++ tailWord_4911324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911324).length < 2 ^ (prefixWord ++ tailWord_4911324).sum := by decide
  have hdescent : baseEnd_4911324 < baseStart_4911324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911332 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 6, 5]
def baseStart_4911332 : Nat := 118140960795 + 4911332 * 2 ^ 59
def prefixEnd_4911332 : Nat := 4983230072969 + 3 ^ 40 * 4911332 * 2
def baseEnd_4911332 : Nat := 840624656602561208221067

theorem tailTrace_4911332 : CollatzResearch.WordTrace tailWord_4911332 prefixEnd_4911332 840624656602561208221067 := by
  unfold tailWord_4911332
  simp only [CollatzResearch.WordTrace]
  refine ⟨89565497121545213785664125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119420662828726951714218833 89565497121545213785664125)
  ·
    refine ⟨33587061420579455169624047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89565497121545213785664125 33587061420579455169624047)
    ·
      refine ⟨50380592130869182754436071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33587061420579455169624047 50380592130869182754436071)
      ·
        refine ⟨75570888196303774131654107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50380592130869182754436071 75570888196303774131654107)
        ·
          refine ⟨113356332294455661197481161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75570888196303774131654107 113356332294455661197481161)
          ·
            refine ⟨85017249220841745898110871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113356332294455661197481161 85017249220841745898110871)
            ·
              refine ⟨127525873831262618847166307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85017249220841745898110871 127525873831262618847166307)
              ·
                refine ⟨191288810746893928270749461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127525873831262618847166307 191288810746893928270749461)
                ·
                  refine ⟨8966663003760652887691381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 191288810746893928270749461 8966663003760652887691381)
                  ·
                    refine ⟨840624656602561208221067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8966663003760652887691381 840624656602561208221067)
                    ·
                      rfl

theorem cell23_4911332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_4911332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911332 prefixEnd_4911332 := by exact prefixLift 4911332
  have htrace : WordTrace (prefixWord ++ tailWord_4911332) baseStart_4911332 baseEnd_4911332 := by
    simpa [prefixWord, tailWord_4911332, baseEnd_4911332] using wordTrace_append hprefix tailTrace_4911332
  have hstable : (prefixWord ++ tailWord_4911332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911332).length < 2 ^ (prefixWord ++ tailWord_4911332).sum := by decide
  have hdescent : baseEnd_4911332 < baseStart_4911332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911342 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 3, 1, 7]
def baseStart_4911342 : Nat := 118140960795 + 4911342 * 2 ^ 59
def prefixEnd_4911342 : Nat := 4983230072969 + 3 ^ 40 * 4911342 * 2
def baseEnd_4911342 : Nat := 2521879104614228585538155

theorem tailTrace_4911342 : CollatzResearch.WordTrace tailWord_4911342 prefixEnd_4911342 2521879104614228585538155 := by
  unfold tailWord_4911342
  simp only [CollatzResearch.WordTrace]
  refine ⟨22391419871631774909899035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119420905982036132852794853 22391419871631774909899035)
  ·
    refine ⟨33587129807447662364848553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22391419871631774909899035 33587129807447662364848553)
    ·
      refine ⟨25190347355585746773636415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33587129807447662364848553 25190347355585746773636415)
      ·
        refine ⟨37785521033378620160454623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25190347355585746773636415 37785521033378620160454623)
        ·
          refine ⟨56678281550067930240681935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37785521033378620160454623 56678281550067930240681935)
          ·
            refine ⟨85017422325101895361022903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56678281550067930240681935 85017422325101895361022903)
            ·
              refine ⟨127526133487652843041534355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85017422325101895361022903 127526133487652843041534355)
              ·
                refine ⟨191289200231479264562301533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127526133487652843041534355 191289200231479264562301533)
                ·
                  refine ⟨71733450086804724210863075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 191289200231479264562301533 71733450086804724210863075)
                  ·
                    refine ⟨107600175130207086316294613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 71733450086804724210863075 107600175130207086316294613)
                    ·
                      refine ⟨2521879104614228585538155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 107600175130207086316294613 2521879104614228585538155)
                      ·
                        rfl

theorem cell23_4911342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_4911342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911342 prefixEnd_4911342 := by exact prefixLift 4911342
  have htrace : WordTrace (prefixWord ++ tailWord_4911342) baseStart_4911342 baseEnd_4911342 := by
    simpa [prefixWord, tailWord_4911342, baseEnd_4911342] using wordTrace_append hprefix tailTrace_4911342
  have hstable : (prefixWord ++ tailWord_4911342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911342).length < 2 ^ (prefixWord ++ tailWord_4911342).sum := by decide
  have hdescent : baseEnd_4911342 < baseStart_4911342 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911352 : List Nat := [2, 1, 2, 1, 1, 2, 1, 5, 1, 3, 4]
def baseStart_4911352 : Nat := 118140960795 + 4911352 * 2 ^ 59
def prefixEnd_4911352 : Nat := 4983230072969 + 3 ^ 40 * 4911352 * 2
def baseEnd_4911352 : Nat := 2521884239420773546413109

theorem tailTrace_4911352 : CollatzResearch.WordTrace tailWord_4911352 prefixEnd_4911352 2521884239420773546413109 := by
  unfold tailWord_4911352
  simp only [CollatzResearch.WordTrace]
  refine ⟨89565861851508985493528155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119421149135345313991370873 89565861851508985493528155)
  ·
    refine ⟨134348792777263478240292233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89565861851508985493528155 134348792777263478240292233)
    ·
      refine ⟨100761594582947608680219175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134348792777263478240292233 100761594582947608680219175)
      ·
        refine ⟨151142391874421413020328763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100761594582947608680219175 151142391874421413020328763)
        ·
          refine ⟨226713587811632119530493145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151142391874421413020328763 226713587811632119530493145)
          ·
            refine ⟨170035190858724089647869859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226713587811632119530493145 170035190858724089647869859)
            ·
              refine ⟨255052786288086134471804789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170035190858724089647869859 255052786288086134471804789)
              ·
                refine ⟨23911198714508075106731699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 255052786288086134471804789 23911198714508075106731699)
                ·
                  refine ⟨35866798071762112660097549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23911198714508075106731699 35866798071762112660097549)
                  ·
                    refine ⟨13450049276910792247536581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35866798071762112660097549 13450049276910792247536581)
                    ·
                      refine ⟨2521884239420773546413109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13450049276910792247536581 2521884239420773546413109)
                      ·
                        rfl

theorem cell23_4911352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 1, 3, 4].length) (baseStart_4911352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911352 prefixEnd_4911352 := by exact prefixLift 4911352
  have htrace : WordTrace (prefixWord ++ tailWord_4911352) baseStart_4911352 baseEnd_4911352 := by
    simpa [prefixWord, tailWord_4911352, baseEnd_4911352] using wordTrace_append hprefix tailTrace_4911352
  have hstable : (prefixWord ++ tailWord_4911352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911352).length < 2 ^ (prefixWord ++ tailWord_4911352).sum := by decide
  have hdescent : baseEnd_4911352 < baseStart_4911352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911369 : List Nat := [1, 2, 1, 1, 3, 4, 2, 2, 2, 1, 4]
def baseStart_4911369 : Nat := 118140960795 + 4911369 * 2 ^ 59
def prefixEnd_4911369 : Nat := 4983230072969 + 3 ^ 40 * 4911369 * 2
def baseEnd_4911369 : Nat := 2521892968591899979900531

theorem tailTrace_4911369 : CollatzResearch.WordTrace tailWord_4911369 prefixEnd_4911369 2521892968591899979900531 := by
  unfold tailWord_4911369
  simp only [CollatzResearch.WordTrace]
  refine ⟨179132343743956382890425161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119421562495970921926950107 179132343743956382890425161)
  ·
    refine ⟨134349257807967287167818871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179132343743956382890425161 134349257807967287167818871)
    ·
      refine ⟨201523886711950930751728307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134349257807967287167818871 201523886711950930751728307)
      ·
        refine ⟨302285830067926396127592461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201523886711950930751728307 302285830067926396127592461)
        ·
          refine ⟨113357186275472398547847173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 302285830067926396127592461 113357186275472398547847173)
          ·
            refine ⟨21254472426651074727721345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113357186275472398547847173 21254472426651074727721345)
            ·
              refine ⟨15940854319988306045791009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21254472426651074727721345 15940854319988306045791009)
              ·
                refine ⟨11955640739991229534343257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15940854319988306045791009 11955640739991229534343257)
                ·
                  refine ⟨8966730554993422150757443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11955640739991229534343257 8966730554993422150757443)
                  ·
                    refine ⟨13450095832490133226136165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8966730554993422150757443 13450095832490133226136165)
                    ·
                      refine ⟨2521892968591899979900531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13450095832490133226136165 2521892968591899979900531)
                      ·
                        rfl

theorem cell23_4911369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 2, 1, 4].length) (baseStart_4911369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911369 prefixEnd_4911369 := by exact prefixLift 4911369
  have htrace : WordTrace (prefixWord ++ tailWord_4911369) baseStart_4911369 baseEnd_4911369 := by
    simpa [prefixWord, tailWord_4911369, baseEnd_4911369] using wordTrace_append hprefix tailTrace_4911369
  have hstable : (prefixWord ++ tailWord_4911369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911369).length < 2 ^ (prefixWord ++ tailWord_4911369).sum := by decide
  have hdescent : baseEnd_4911369 < baseStart_4911369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911372 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 2, 3, 5]
def baseStart_4911372 : Nat := 118140960795 + 4911372 * 2 ^ 59
def prefixEnd_4911372 : Nat := 4983230072969 + 3 ^ 40 * 4911372 * 2
def baseEnd_4911372 : Nat := 2521894509033863468163017

theorem tailTrace_4911372 : CollatzResearch.WordTrace tailWord_4911372 prefixEnd_4911372 2521894509033863468163017 := by
  unfold tailWord_4911372
  simp only [CollatzResearch.WordTrace]
  refine ⟨89566226581472757201392185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119421635441963676268522913 89566226581472757201392185)
  ·
    refine ⟨67174669936104567901044139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89566226581472757201392185 67174669936104567901044139)
    ·
      refine ⟨100762004904156851851566209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67174669936104567901044139 100762004904156851851566209)
      ·
        refine ⟨75571503678117638888674657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100762004904156851851566209 75571503678117638888674657)
        ·
          refine ⟨56678627758588229166505993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75571503678117638888674657 56678627758588229166505993)
          ·
            refine ⟨42508970818941171874879495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56678627758588229166505993 42508970818941171874879495)
            ·
              refine ⟨63763456228411757812319243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42508970818941171874879495 63763456228411757812319243)
              ·
                refine ⟨95645184342617636718478865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63763456228411757812319243 95645184342617636718478865)
                ·
                  refine ⟨71733888256963227538859149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95645184342617636718478865 71733888256963227538859149)
                  ·
                    refine ⟨26900208096361210327072181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71733888256963227538859149 26900208096361210327072181)
                    ·
                      refine ⟨2521894509033863468163017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26900208096361210327072181 2521894509033863468163017)
                      ·
                        rfl

theorem cell23_4911372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_4911372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911372 prefixEnd_4911372 := by exact prefixLift 4911372
  have htrace : WordTrace (prefixWord ++ tailWord_4911372) baseStart_4911372 baseEnd_4911372 := by
    simpa [prefixWord, tailWord_4911372, baseEnd_4911372] using wordTrace_append hprefix tailTrace_4911372
  have hstable : (prefixWord ++ tailWord_4911372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911372).length < 2 ^ (prefixWord ++ tailWord_4911372).sum := by decide
  have hdescent : baseEnd_4911372 < baseStart_4911372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911396 : List Nat := [2, 3, 1, 3, 1, 3, 1, 2, 3, 4]
def baseStart_4911396 : Nat := 118140960795 + 4911396 * 2 ^ 59
def prefixEnd_4911396 : Nat := 4983230072969 + 3 ^ 40 * 4911396 * 2
def baseEnd_4911396 : Nat := 840635610856523791420969

theorem tailTrace_4911396 : CollatzResearch.WordTrace tailWord_4911396 prefixEnd_4911396 840635610856523791420969 := by
  unfold tailWord_4911396
  simp only [CollatzResearch.WordTrace]
  refine ⟨89566664257429283250829021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119422219009905711001105361 89566664257429283250829021)
  ·
    refine ⟨33587499096535981219060883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89566664257429283250829021 33587499096535981219060883)
    ·
      refine ⟨50381248644803971828591325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33587499096535981219060883 50381248644803971828591325)
      ·
        refine ⟨18892968241801489435721747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50381248644803971828591325 18892968241801489435721747)
        ·
          refine ⟨28339452362702234153582621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18892968241801489435721747 28339452362702234153582621)
          ·
            refine ⟨10627294636013337807593483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28339452362702234153582621 10627294636013337807593483)
            ·
              refine ⟨15940941954020006711390225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10627294636013337807593483 15940941954020006711390225)
              ·
                refine ⟨11955706465515005033542669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15940941954020006711390225 11955706465515005033542669)
                ·
                  refine ⟨4483389924568126887578501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11955706465515005033542669 4483389924568126887578501)
                  ·
                    refine ⟨840635610856523791420969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4483389924568126887578501 840635610856523791420969)
                    ·
                      rfl

theorem cell23_4911396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 3, 4].length) (baseStart_4911396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911396 prefixEnd_4911396 := by exact prefixLift 4911396
  have htrace : WordTrace (prefixWord ++ tailWord_4911396) baseStart_4911396 baseEnd_4911396 := by
    simpa [prefixWord, tailWord_4911396, baseEnd_4911396] using wordTrace_append hprefix tailTrace_4911396
  have hstable : (prefixWord ++ tailWord_4911396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911396).length < 2 ^ (prefixWord ++ tailWord_4911396).sum := by decide
  have hdescent : baseEnd_4911396 < baseStart_4911396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911413 : List Nat := [1, 3, 3, 1, 2, 1, 4, 3, 1, 4]
def baseStart_4911413 : Nat := 118140960795 + 4911413 * 2 ^ 59
def prefixEnd_4911413 : Nat := 4983230072969 + 3 ^ 40 * 4911413 * 2
def baseEnd_4911413 : Nat := 840638520580232602583443

theorem tailTrace_4911413 : CollatzResearch.WordTrace tailWord_4911413 prefixEnd_4911413 840638520580232602583443 := by
  unfold tailWord_4911413
  simp only [CollatzResearch.WordTrace]
  refine ⟨179133948555796978405026893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119422632370531318936684595 179133948555796978405026893)
  ·
    refine ⟨67175230708423866901885085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179133948555796978405026893 67175230708423866901885085)
    ·
      refine ⟨25190711515658950088206907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67175230708423866901885085 25190711515658950088206907)
      ·
        refine ⟨37786067273488425132310361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25190711515658950088206907 37786067273488425132310361)
        ·
          refine ⟨28339550455116318849232771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37786067273488425132310361 28339550455116318849232771)
          ·
            refine ⟨42509325682674478273849157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28339550455116318849232771 42509325682674478273849157)
            ·
              refine ⟨7970498565501464676346717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42509325682674478273849157 7970498565501464676346717)
              ·
                refine ⟨2988936962063049253630019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7970498565501464676346717 2988936962063049253630019)
                ·
                  refine ⟨4483405443094573880445029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2988936962063049253630019 4483405443094573880445029)
                  ·
                    refine ⟨840638520580232602583443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4483405443094573880445029 840638520580232602583443)
                    ·
                      rfl

theorem cell23_4911413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_4911413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911413 prefixEnd_4911413 := by exact prefixLift 4911413
  have htrace : WordTrace (prefixWord ++ tailWord_4911413) baseStart_4911413 baseEnd_4911413 := by
    simpa [prefixWord, tailWord_4911413, baseEnd_4911413] using wordTrace_append hprefix tailTrace_4911413
  have hstable : (prefixWord ++ tailWord_4911413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911413).length < 2 ^ (prefixWord ++ tailWord_4911413).sum := by decide
  have hdescent : baseEnd_4911413 < baseStart_4911413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911469 : List Nat := [1, 5, 1, 1, 1, 2, 2, 1, 3, 6]
def baseStart_4911469 : Nat := 118140960795 + 4911469 * 2 ^ 59
def prefixEnd_4911469 : Nat := 4983230072969 + 3 ^ 40 * 4911469 * 2
def baseEnd_4911469 : Nat := 840648105552449862883357

theorem tailTrace_4911469 : CollatzResearch.WordTrace tailWord_4911469 prefixEnd_4911469 840648105552449862883357 := by
  unfold tailWord_4911469
  simp only [CollatzResearch.WordTrace]
  refine ⟨179135991043594099969065461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119423994029062733312710307 179135991043594099969065461)
  ·
    refine ⟨16793999160336946872099887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 179135991043594099969065461 16793999160336946872099887)
    ·
      refine ⟨25190998740505420308149831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16793999160336946872099887 25190998740505420308149831)
      ·
        refine ⟨37786498110758130462224747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25190998740505420308149831 37786498110758130462224747)
        ·
          refine ⟨56679747166137195693337121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37786498110758130462224747 56679747166137195693337121)
          ·
            refine ⟨42509810374602896770002841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56679747166137195693337121 42509810374602896770002841)
            ·
              refine ⟨31882357780952172577502131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42509810374602896770002841 31882357780952172577502131)
              ·
                refine ⟨47823536671428258866253197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31882357780952172577502131 47823536671428258866253197)
                ·
                  refine ⟨17933826251785597074844949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47823536671428258866253197 17933826251785597074844949)
                  ·
                    refine ⟨840648105552449862883357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17933826251785597074844949 840648105552449862883357)
                    ·
                      rfl

theorem cell23_4911469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_4911469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911469 prefixEnd_4911469 := by exact prefixLift 4911469
  have htrace : WordTrace (prefixWord ++ tailWord_4911469) baseStart_4911469 baseEnd_4911469 := by
    simpa [prefixWord, tailWord_4911469, baseEnd_4911469] using wordTrace_append hprefix tailTrace_4911469
  have hstable : (prefixWord ++ tailWord_4911469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911469).length < 2 ^ (prefixWord ++ tailWord_4911469).sum := by decide
  have hdescent : baseEnd_4911469 < baseStart_4911469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911496 : List Nat := [2, 1, 3, 3, 1, 1, 2, 2, 3, 2, 3]
def baseStart_4911496 : Nat := 118140960795 + 4911496 * 2 ^ 59
def prefixEnd_4911496 : Nat := 4983230072969 + 3 ^ 40 * 4911496 * 2
def baseEnd_4911496 : Nat := 2521958180635020983012447

theorem tailTrace_4911496 : CollatzResearch.WordTrace tailWord_4911496 prefixEnd_4911496 2521958180635020983012447 := by
  unfold tailWord_4911496
  simp only [CollatzResearch.WordTrace]
  refine ⟨89568487907248141790149171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119424650542997522386865561 89568487907248141790149171)
  ·
    refine ⟨134352731860872212685223757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89568487907248141790149171 134352731860872212685223757)
    ·
      refine ⟨50382274447827079756958909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134352731860872212685223757 50382274447827079756958909)
      ·
        refine ⟨18893352917935154908859591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50382274447827079756958909 18893352917935154908859591)
        ·
          refine ⟨28340029376902732363289387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18893352917935154908859591 28340029376902732363289387)
          ·
            refine ⟨42510044065354098544934081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28340029376902732363289387 42510044065354098544934081)
            ·
              refine ⟨31882533049015573908700561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42510044065354098544934081 31882533049015573908700561)
              ·
                refine ⟨23911899786761680431525421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31882533049015573908700561 23911899786761680431525421)
                ·
                  refine ⟨8966962420035630161822033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23911899786761680431525421 8966962420035630161822033)
                  ·
                    refine ⟨6725221815026722621366525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8966962420035630161822033 6725221815026722621366525)
                    ·
                      refine ⟨2521958180635020983012447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6725221815026722621366525 2521958180635020983012447)
                      ·
                        rfl

theorem cell23_4911496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_4911496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911496 prefixEnd_4911496 := by exact prefixLift 4911496
  have htrace : WordTrace (prefixWord ++ tailWord_4911496) baseStart_4911496 baseEnd_4911496 := by
    simpa [prefixWord, tailWord_4911496, baseEnd_4911496] using wordTrace_append hprefix tailTrace_4911496
  have hstable : (prefixWord ++ tailWord_4911496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911496).length < 2 ^ (prefixWord ++ tailWord_4911496).sum := by decide
  have hdescent : baseEnd_4911496 < baseStart_4911496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911499 : List Nat := [1, 1, 1, 1, 4, 5, 2, 8]
def baseStart_4911499 : Nat := 118140960795 + 4911499 * 2 ^ 59
def prefixEnd_4911499 : Nat := 4983230072969 + 3 ^ 40 * 4911499 * 2
def baseEnd_4911499 : Nat := 93405915595443869306479

theorem tailTrace_4911499 : CollatzResearch.WordTrace tailWord_4911499 prefixEnd_4911499 93405915595443869306479 := by
  unfold tailWord_4911499
  simp only [CollatzResearch.WordTrace]
  refine ⟨179137085233485415092657551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119424723488990276728438367 179137085233485415092657551)
  ·
    refine ⟨268705627850228122638986327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179137085233485415092657551 268705627850228122638986327)
    ·
      refine ⟨403058441775342183958479491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268705627850228122638986327 403058441775342183958479491)
      ·
        refine ⟨604587662663013275937719237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 403058441775342183958479491 604587662663013275937719237)
        ·
          refine ⟨113360186749314989238322357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 604587662663013275937719237 113360186749314989238322357)
          ·
            refine ⟨10627517507748280241092721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 113360186749314989238322357 10627517507748280241092721)
            ·
              refine ⟨7970638130811210180819541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10627517507748280241092721 7970638130811210180819541)
              ·
                refine ⟨93405915595443869306479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7970638130811210180819541 93405915595443869306479)
                ·
                  rfl

theorem cell23_4911499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 8].length) (baseStart_4911499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911499 prefixEnd_4911499 := by exact prefixLift 4911499
  have htrace : WordTrace (prefixWord ++ tailWord_4911499) baseStart_4911499 baseEnd_4911499 := by
    simpa [prefixWord, tailWord_4911499, baseEnd_4911499] using wordTrace_append hprefix tailTrace_4911499
  have hstable : (prefixWord ++ tailWord_4911499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911499).length < 2 ^ (prefixWord ++ tailWord_4911499).sum := by decide
  have hdescent : baseEnd_4911499 < baseStart_4911499 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911543 : List Nat := [1, 1, 3, 1, 3, 3, 1, 4, 2, 1, 3]
def baseStart_4911543 : Nat := 118140960795 + 4911543 * 2 ^ 59
def prefixEnd_4911543 : Nat := 4983230072969 + 3 ^ 40 * 4911543 * 2
def baseEnd_4911543 : Nat := 2521982314225782299124731

theorem tailTrace_4911543 : CollatzResearch.WordTrace tailWord_4911543 prefixEnd_4911543 2521982314225782299124731 := by
  unfold tailWord_4911543
  simp only [CollatzResearch.WordTrace]
  refine ⟨179138690045326010607259283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119425793363550673738172855 179138690045326010607259283)
  ·
    refine ⟨268708035067989015910888925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179138690045326010607259283 268708035067989015910888925)
    ·
      refine ⟨100765513150495880966583347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 268708035067989015910888925 100765513150495880966583347)
      ·
        refine ⟨151148269725743821449875021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100765513150495880966583347 151148269725743821449875021)
        ·
          refine ⟨56680601147153933043703133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151148269725743821449875021 56680601147153933043703133)
          ·
            refine ⟨21255225430182724891388675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56680601147153933043703133 21255225430182724891388675)
            ·
              refine ⟨31882838145274087337083013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21255225430182724891388675 31882838145274087337083013)
              ·
                refine ⟨5978032152238891375703065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31882838145274087337083013 5978032152238891375703065)
                ·
                  refine ⟨4483524114179168531777299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5978032152238891375703065 4483524114179168531777299)
                  ·
                    refine ⟨6725286171268752797665949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4483524114179168531777299 6725286171268752797665949)
                    ·
                      refine ⟨2521982314225782299124731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6725286171268752797665949 2521982314225782299124731)
                      ·
                        rfl

theorem cell23_4911543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 4, 2, 1, 3].length) (baseStart_4911543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911543 prefixEnd_4911543 := by exact prefixLift 4911543
  have htrace : WordTrace (prefixWord ++ tailWord_4911543) baseStart_4911543 baseEnd_4911543 := by
    simpa [prefixWord, tailWord_4911543, baseEnd_4911543] using wordTrace_append hprefix tailTrace_4911543
  have hstable : (prefixWord ++ tailWord_4911543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911543).length < 2 ^ (prefixWord ++ tailWord_4911543).sum := by decide
  have hdescent : baseEnd_4911543 < baseStart_4911543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911559 : List Nat := [1, 1, 4, 1, 1, 4, 1, 1, 1, 8]
def baseStart_4911559 : Nat := 118140960795 + 4911559 * 2 ^ 59
def prefixEnd_4911559 : Nat := 4983230072969 + 3 ^ 40 * 4911559 * 2
def baseEnd_4911559 : Nat := 840663509972084745508219

theorem tailTrace_4911559 : CollatzResearch.WordTrace tailWord_4911559 prefixEnd_4911559 840663509972084745508219 := by
  unfold tailWord_4911559
  simp only [CollatzResearch.WordTrace]
  refine ⟨179139273613268045339841731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119426182408845363559894487 179139273613268045339841731)
  ·
    refine ⟨268708910419902068009762597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179139273613268045339841731 268708910419902068009762597)
    ·
      refine ⟨50382920703731637751830487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 268708910419902068009762597 50382920703731637751830487)
      ·
        refine ⟨75574381055597456627745731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50382920703731637751830487 75574381055597456627745731)
        ·
          refine ⟨113361571583396184941618597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75574381055597456627745731 113361571583396184941618597)
          ·
            refine ⟨21255294671886784676553487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113361571583396184941618597 21255294671886784676553487)
            ·
              refine ⟨31882942007830177014830231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21255294671886784676553487 31882942007830177014830231)
              ·
                refine ⟨47824413011745265522245347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31882942007830177014830231 47824413011745265522245347)
                ·
                  refine ⟨71736619517617898283368021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47824413011745265522245347 71736619517617898283368021)
                  ·
                    refine ⟨840663509972084745508219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 71736619517617898283368021 840663509972084745508219)
                    ·
                      rfl

theorem cell23_4911559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_4911559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911559 prefixEnd_4911559 := by exact prefixLift 4911559
  have htrace : WordTrace (prefixWord ++ tailWord_4911559) baseStart_4911559 baseEnd_4911559 := by
    simpa [prefixWord, tailWord_4911559, baseEnd_4911559] using wordTrace_append hprefix tailTrace_4911559
  have hstable : (prefixWord ++ tailWord_4911559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911559).length < 2 ^ (prefixWord ++ tailWord_4911559).sum := by decide
  have hdescent : baseEnd_4911559 < baseStart_4911559 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911569 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 4, 1, 5]
def baseStart_4911569 : Nat := 118140960795 + 4911569 * 2 ^ 59
def prefixEnd_4911569 : Nat := 4983230072969 + 3 ^ 40 * 4911569 * 2
def baseEnd_4911569 : Nat := 2521995664722799197399611

theorem tailTrace_4911569 : CollatzResearch.WordTrace tailWord_4911569 prefixEnd_4911569 2521995664722799197399611 := by
  unfold tailWord_4911569
  simp only [CollatzResearch.WordTrace]
  refine ⟨179139638343231817047705761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119426425562154544698470507 179139638343231817047705761)
  ·
    refine ⟨134354728757423862785779321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179139638343231817047705761 134354728757423862785779321)
    ·
      refine ⟨100766046568067897089334491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134354728757423862785779321 100766046568067897089334491)
      ·
        refine ⟨151149069852101845634001737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100766046568067897089334491 151149069852101845634001737)
        ·
          refine ⟨113361802389076384225501303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151149069852101845634001737 113361802389076384225501303)
          ·
            refine ⟨170042703583614576338251955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113361802389076384225501303 170042703583614576338251955)
            ·
              refine ⟨255064055375421864507377933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170042703583614576338251955 255064055375421864507377933)
              ·
                refine ⟨95649020765783199190266725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 255064055375421864507377933 95649020765783199190266725)
                ·
                  refine ⟨17934191393584349848175011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95649020765783199190266725 17934191393584349848175011)
                  ·
                    refine ⟨26901287090376524772262517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17934191393584349848175011 26901287090376524772262517)
                    ·
                      refine ⟨2521995664722799197399611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26901287090376524772262517 2521995664722799197399611)
                      ·
                        rfl

theorem cell23_4911569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 1, 5].length) (baseStart_4911569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911569 prefixEnd_4911569 := by exact prefixLift 4911569
  have htrace : WordTrace (prefixWord ++ tailWord_4911569) baseStart_4911569 baseEnd_4911569 := by
    simpa [prefixWord, tailWord_4911569, baseEnd_4911569] using wordTrace_append hprefix tailTrace_4911569
  have hstable : (prefixWord ++ tailWord_4911569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911569).length < 2 ^ (prefixWord ++ tailWord_4911569).sum := by decide
  have hdescent : baseEnd_4911569 < baseStart_4911569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911583 : List Nat := [1, 1, 2, 3, 3, 2, 2, 2, 1, 4, 2]
def baseStart_4911583 : Nat := 118140960795 + 4911583 * 2 ^ 59
def prefixEnd_4911583 : Nat := 4983230072969 + 3 ^ 40 * 4911583 * 2
def baseEnd_4911583 : Nat := 2522002853451962142624547

theorem tailTrace_4911583 : CollatzResearch.WordTrace tailWord_4911583 prefixEnd_4911583 2522002853451962142624547 := by
  unfold tailWord_4911583
  simp only [CollatzResearch.WordTrace]
  refine ⟨179140148965181097438715403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119426765976787398292476935 179140148965181097438715403)
  ·
    refine ⟨268710223447771646158073105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179140148965181097438715403 268710223447771646158073105)
    ·
      refine ⟨201532667585828734618554829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268710223447771646158073105 201532667585828734618554829)
      ·
        refine ⟨75574750344685775481958061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201532667585828734618554829 75574750344685775481958061)
        ·
          refine ⟨28340531379257165805734273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75574750344685775481958061 28340531379257165805734273)
          ·
            refine ⟨21255398534442874354300705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28340531379257165805734273 21255398534442874354300705)
            ·
              refine ⟨15941548900832155765725529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21255398534442874354300705 15941548900832155765725529)
              ·
                refine ⟨11956161675624116824294147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15941548900832155765725529 11956161675624116824294147)
                ·
                  refine ⟨17934242513436175236441221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11956161675624116824294147 17934242513436175236441221)
                  ·
                    refine ⟨3362670471269282856832729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17934242513436175236441221 3362670471269282856832729)
                    ·
                      refine ⟨2522002853451962142624547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3362670471269282856832729 2522002853451962142624547)
                      ·
                        rfl

theorem cell23_4911583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 4, 2].length) (baseStart_4911583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911583 prefixEnd_4911583 := by exact prefixLift 4911583
  have htrace : WordTrace (prefixWord ++ tailWord_4911583) baseStart_4911583 baseEnd_4911583 := by
    simpa [prefixWord, tailWord_4911583, baseEnd_4911583] using wordTrace_append hprefix tailTrace_4911583
  have hstable : (prefixWord ++ tailWord_4911583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911583).length < 2 ^ (prefixWord ++ tailWord_4911583).sum := by decide
  have hdescent : baseEnd_4911583 < baseStart_4911583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911619 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 3, 7]
def baseStart_4911619 : Nat := 118140960795 + 4911619 * 2 ^ 59
def prefixEnd_4911619 : Nat := 4983230072969 + 3 ^ 40 * 4911619 * 2
def baseEnd_4911619 : Nat := 840673779585174667258127

theorem tailTrace_4911619 : CollatzResearch.WordTrace tailWord_4911619 prefixEnd_4911619 840673779585174667258127 := by
  unfold tailWord_4911619
  simp only [CollatzResearch.WordTrace]
  refine ⟨179141461993050675587025911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119427641328700450391350607 179141461993050675587025911)
  ·
    refine ⟨268712192989576013380538867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179141461993050675587025911 268712192989576013380538867)
    ·
      refine ⟨403068289484364020070808301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268712192989576013380538867 403068289484364020070808301)
      ·
        refine ⟨151150608556636507526553113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 403068289484364020070808301 151150608556636507526553113)
        ·
          refine ⟨113362956417477380644914835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151150608556636507526553113 113362956417477380644914835)
          ·
            refine ⟨170044434626216070967372253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113362956417477380644914835 170044434626216070967372253)
            ·
              refine ⟨63766662984831026612764595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 170044434626216070967372253 63766662984831026612764595)
              ·
                refine ⟨95649994477246539919146893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63766662984831026612764595 95649994477246539919146893)
                ·
                  refine ⟨35868747928967452469680085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95649994477246539919146893 35868747928967452469680085)
                  ·
                    refine ⟨840673779585174667258127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35868747928967452469680085 840673779585174667258127)
                    ·
                      rfl

theorem cell23_4911619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 7].length) (baseStart_4911619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911619 prefixEnd_4911619 := by exact prefixLift 4911619
  have htrace : WordTrace (prefixWord ++ tailWord_4911619) baseStart_4911619 baseEnd_4911619 := by
    simpa [prefixWord, tailWord_4911619, baseEnd_4911619] using wordTrace_append hprefix tailTrace_4911619
  have hstable : (prefixWord ++ tailWord_4911619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911619).length < 2 ^ (prefixWord ++ tailWord_4911619).sum := by decide
  have hdescent : baseEnd_4911619 < baseStart_4911619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911640 : List Nat := [2, 1, 2, 3, 3, 3, 1, 3, 5]
def baseStart_4911640 : Nat := 118140960795 + 4911640 * 2 ^ 59
def prefixEnd_4911640 : Nat := 4983230072969 + 3 ^ 40 * 4911640 * 2
def baseEnd_4911640 : Nat := 280225791316585379956865

theorem tailTrace_4911640 : CollatzResearch.WordTrace tailWord_4911640 prefixEnd_4911640 280225791316585379956865 := by
  unfold tailWord_4911640
  simp only [CollatzResearch.WordTrace]
  refine ⟨89571113962987298086770187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119428151950649730782360249 89571113962987298086770187)
  ·
    refine ⟨134356670944480947130155281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89571113962987298086770187 134356670944480947130155281)
    ·
      refine ⟨100767503208360710347616461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134356670944480947130155281 100767503208360710347616461)
      ·
        refine ⟨37787813703135266380356173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100767503208360710347616461 37787813703135266380356173)
        ·
          refine ⟨14170430138675724892633565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37787813703135266380356173 14170430138675724892633565)
          ·
            refine ⟨5313911302003396834737587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14170430138675724892633565 5313911302003396834737587)
            ·
              refine ⟨7970866953005095252106381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5313911302003396834737587 7970866953005095252106381)
              ·
                refine ⟨2989075107376910719539893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7970866953005095252106381 2989075107376910719539893)
                ·
                  refine ⟨280225791316585379956865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2989075107376910719539893 280225791316585379956865)
                  ·
                    rfl

theorem cell23_4911640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 3, 5].length) (baseStart_4911640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911640 prefixEnd_4911640 := by exact prefixLift 4911640
  have htrace : WordTrace (prefixWord ++ tailWord_4911640) baseStart_4911640 baseEnd_4911640 := by
    simpa [prefixWord, tailWord_4911640, baseEnd_4911640] using wordTrace_append hprefix tailTrace_4911640
  have hstable : (prefixWord ++ tailWord_4911640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911640).length < 2 ^ (prefixWord ++ tailWord_4911640).sum := by decide
  have hdescent : baseEnd_4911640 < baseStart_4911640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911668 : List Nat := [2, 5, 1, 3, 1, 2, 2, 1, 2, 2, 2]
def baseStart_4911668 : Nat := 118140960795 + 4911668 * 2 ^ 59
def prefixEnd_4911668 : Nat := 4983230072969 + 3 ^ 40 * 4911668 * 2
def baseEnd_4911668 : Nat := 2522046499307594310061657

theorem tailTrace_4911668 : CollatzResearch.WordTrace tailWord_4911668 prefixEnd_4911668 2522046499307594310061657 := by
  unfold tailWord_4911668
  simp only [CollatzResearch.WordTrace]
  refine ⟨89571624584936578477779829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119428832779915437970373105 89571624584936578477779829)
  ·
    refine ⟨8397339804837804232291859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89571624584936578477779829 8397339804837804232291859)
    ·
      refine ⟨12596009707256706348437789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8397339804837804232291859 12596009707256706348437789)
      ·
        refine ⟨4723503640221264880664171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12596009707256706348437789 4723503640221264880664171)
        ·
          refine ⟨7085255460331897320996257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4723503640221264880664171 7085255460331897320996257)
          ·
            refine ⟨5313941595248922990747193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7085255460331897320996257 5313941595248922990747193)
            ·
              refine ⟨3985456196436692243060395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5313941595248922990747193 3985456196436692243060395)
              ·
                refine ⟨5978184294655038364590593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3985456196436692243060395 5978184294655038364590593)
                ·
                  refine ⟨4483638220991278773442945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5978184294655038364590593 4483638220991278773442945)
                  ·
                    refine ⟨3362728665743459080082209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4483638220991278773442945 3362728665743459080082209)
                    ·
                      refine ⟨2522046499307594310061657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3362728665743459080082209 2522046499307594310061657)
                      ·
                        rfl

theorem cell23_4911668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_4911668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911668 prefixEnd_4911668 := by exact prefixLift 4911668
  have htrace : WordTrace (prefixWord ++ tailWord_4911668) baseStart_4911668 baseEnd_4911668 := by
    simpa [prefixWord, tailWord_4911668, baseEnd_4911668] using wordTrace_append hprefix tailTrace_4911668
  have hstable : (prefixWord ++ tailWord_4911668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911668).length < 2 ^ (prefixWord ++ tailWord_4911668).sum := by decide
  have hdescent : baseEnd_4911668 < baseStart_4911668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911673 : List Nat := [1, 2, 1, 5, 1, 1, 2, 1, 1, 6, 2]
def baseStart_4911673 : Nat := 118140960795 + 4911673 * 2 ^ 59
def prefixEnd_4911673 : Nat := 4983230072969 + 3 ^ 40 * 4911673 * 2
def baseEnd_4911673 : Nat := 2522049066710866790499133

theorem tailTrace_4911673 : CollatzResearch.WordTrace tailWord_4911673 prefixEnd_4911673 2522049066710866790499133 := by
  unfold tailWord_4911673
  simp only [CollatzResearch.WordTrace]
  refine ⟨179143431534855042809491673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119428954356570028539661115 179143431534855042809491673)
  ·
    refine ⟨134357573651141282107118755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179143431534855042809491673 134357573651141282107118755)
    ·
      refine ⟨201536360476711923160678133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134357573651141282107118755 201536360476711923160678133)
      ·
        refine ⟨18894033794691742796313575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 201536360476711923160678133 18894033794691742796313575)
        ·
          refine ⟨28341050692037614194470363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18894033794691742796313575 28341050692037614194470363)
          ·
            refine ⟨42511576038056421291705545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28341050692037614194470363 42511576038056421291705545)
            ·
              refine ⟨31883682028542315968779159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42511576038056421291705545 31883682028542315968779159)
              ·
                refine ⟨47825523042813473953168739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31883682028542315968779159 47825523042813473953168739)
                ·
                  refine ⟨71738284564220210929753109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47825523042813473953168739 71738284564220210929753109)
                  ·
                    refine ⟨3362732088947822387332177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 71738284564220210929753109 3362732088947822387332177)
                    ·
                      refine ⟨2522049066710866790499133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3362732088947822387332177 2522049066710866790499133)
                      ·
                        rfl

theorem cell23_4911673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_4911673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911673 prefixEnd_4911673 := by exact prefixLift 4911673
  have htrace : WordTrace (prefixWord ++ tailWord_4911673) baseStart_4911673 baseEnd_4911673 := by
    simpa [prefixWord, tailWord_4911673, baseEnd_4911673] using wordTrace_append hprefix tailTrace_4911673
  have hstable : (prefixWord ++ tailWord_4911673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911673).length < 2 ^ (prefixWord ++ tailWord_4911673).sum := by decide
  have hdescent : baseEnd_4911673 < baseStart_4911673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911713 : List Nat := [1, 2, 3, 1, 1, 5, 2, 2, 6]
def baseStart_4911713 : Nat := 118140960795 + 4911713 * 2 ^ 59
def prefixEnd_4911713 : Nat := 4983230072969 + 3 ^ 40 * 4911713 * 2
def baseEnd_4911713 : Nat := 280229956215227403777661

theorem tailTrace_4911713 : CollatzResearch.WordTrace tailWord_4911713 prefixEnd_4911713 280229956215227403777661 := by
  unfold tailWord_4911713
  simp only [CollatzResearch.WordTrace]
  refine ⟨179144890454710129640947793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119429926969806753093965195 179144890454710129640947793)
  ·
    refine ⟨134358667841032597230710845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179144890454710129640947793 134358667841032597230710845)
    ·
      refine ⟨50384500440387223961516567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134358667841032597230710845 50384500440387223961516567)
      ·
        refine ⟨75576750660580835942274851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50384500440387223961516567 75576750660580835942274851)
        ·
          refine ⟨113365125990871253913412277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75576750660580835942274851 113365125990871253913412277)
          ·
            refine ⟨10627980561644180054382401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 113365125990871253913412277 10627980561644180054382401)
            ·
              refine ⟨7970985421233135040786801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10627980561644180054382401 7970985421233135040786801)
              ·
                refine ⟨5978239065924851280590101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7970985421233135040786801 5978239065924851280590101)
                ·
                  refine ⟨280229956215227403777661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5978239065924851280590101 280229956215227403777661)
                  ·
                    rfl

theorem cell23_4911713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 2, 6].length) (baseStart_4911713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911713 prefixEnd_4911713 := by exact prefixLift 4911713
  have htrace : WordTrace (prefixWord ++ tailWord_4911713) baseStart_4911713 baseEnd_4911713 := by
    simpa [prefixWord, tailWord_4911713, baseEnd_4911713] using wordTrace_append hprefix tailTrace_4911713
  have hstable : (prefixWord ++ tailWord_4911713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911713).length < 2 ^ (prefixWord ++ tailWord_4911713).sum := by decide
  have hdescent : baseEnd_4911713 < baseStart_4911713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911716 : List Nat := [2, 3, 1, 1, 2, 2, 2, 1, 1, 2, 6]
def baseStart_4911716 : Nat := 118140960795 + 4911716 * 2 ^ 59
def prefixEnd_4911716 : Nat := 4983230072969 + 3 ^ 40 * 4911716 * 2
def baseEnd_4911716 : Nat := 2522071146379010122261435

theorem tailTrace_4911716 : CollatzResearch.WordTrace tailWord_4911716 prefixEnd_4911716 2522071146379010122261435 := by
  unfold tailWord_4911716
  simp only [CollatzResearch.WordTrace]
  refine ⟨89572499936849630576653501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119429999915799507435538001 89572499936849630576653501)
  ·
    refine ⟨33589687476318611466245063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89572499936849630576653501 33589687476318611466245063)
    ·
      refine ⟨50384531214477917199367595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33589687476318611466245063 50384531214477917199367595)
      ·
        refine ⟨75576796821716875799051393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50384531214477917199367595 75576796821716875799051393)
        ·
          refine ⟨56682597616287656849288545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75576796821716875799051393 56682597616287656849288545)
          ·
            refine ⟨42511948212215742636966409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56682597616287656849288545 42511948212215742636966409)
            ·
              refine ⟨31883961159161806977724807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42511948212215742636966409 31883961159161806977724807)
              ·
                refine ⟨47825941738742710466587211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31883961159161806977724807 47825941738742710466587211)
                ·
                  refine ⟨71738912608114065699880817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47825941738742710466587211 71738912608114065699880817)
                  ·
                    refine ⟨53804184456085549274910613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 71738912608114065699880817 53804184456085549274910613)
                    ·
                      refine ⟨2522071146379010122261435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53804184456085549274910613 2522071146379010122261435)
                      ·
                        rfl

theorem cell23_4911716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_4911716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911716 prefixEnd_4911716 := by exact prefixLift 4911716
  have htrace : WordTrace (prefixWord ++ tailWord_4911716) baseStart_4911716 baseEnd_4911716 := by
    simpa [prefixWord, tailWord_4911716, baseEnd_4911716] using wordTrace_append hprefix tailTrace_4911716
  have hstable : (prefixWord ++ tailWord_4911716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911716).length < 2 ^ (prefixWord ++ tailWord_4911716).sum := by decide
  have hdescent : baseEnd_4911716 < baseStart_4911716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911717 : List Nat := [1, 3, 1, 3, 4, 1, 1, 4, 1, 4]
def baseStart_4911717 : Nat := 118140960795 + 4911717 * 2 ^ 59
def prefixEnd_4911717 : Nat := 4983230072969 + 3 ^ 40 * 4911717 * 2
def baseEnd_4911717 : Nat := 840690553286554872782977

theorem tailTrace_4911717 : CollatzResearch.WordTrace tailWord_4911717 prefixEnd_4911717 840690553286554872782977 := by
  unfold tailWord_4911717
  simp only [CollatzResearch.WordTrace]
  refine ⟨179145036346695638324093405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119430024231130425549395603 179145036346695638324093405)
  ·
    refine ⟨67179388630010864371535027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179145036346695638324093405 67179388630010864371535027)
    ·
      refine ⟨100769082945016296557302541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67179388630010864371535027 100769082945016296557302541)
      ·
        refine ⟨37788406104381111208988453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100769082945016296557302541 37788406104381111208988453)
        ·
          refine ⟨7085326144571458351685335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37788406104381111208988453 7085326144571458351685335)
          ·
            refine ⟨10627989216857187527528003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7085326144571458351685335 10627989216857187527528003)
            ·
              refine ⟨15941983825285781291292005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10627989216857187527528003 15941983825285781291292005)
              ·
                refine ⟨2989121967241083992117251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15941983825285781291292005 2989121967241083992117251)
                ·
                  refine ⟨4483682950861625988175877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2989121967241083992117251 4483682950861625988175877)
                  ·
                    refine ⟨840690553286554872782977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4483682950861625988175877 840690553286554872782977)
                    ·
                      rfl

theorem cell23_4911717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 4, 1, 4].length) (baseStart_4911717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911717 prefixEnd_4911717 := by exact prefixLift 4911717
  have htrace : WordTrace (prefixWord ++ tailWord_4911717) baseStart_4911717 baseEnd_4911717 := by
    simpa [prefixWord, tailWord_4911717, baseEnd_4911717] using wordTrace_append hprefix tailTrace_4911717
  have hstable : (prefixWord ++ tailWord_4911717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911717).length < 2 ^ (prefixWord ++ tailWord_4911717).sum := by decide
  have hdescent : baseEnd_4911717 < baseStart_4911717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911756 : List Nat := [2, 2, 1, 2, 1, 1, 2, 3, 3, 6]
def baseStart_4911756 : Nat := 118140960795 + 4911756 * 2 ^ 59
def prefixEnd_4911756 : Nat := 4983230072969 + 3 ^ 40 * 4911756 * 2
def baseEnd_4911756 : Nat := 840697228535063321920417

theorem tailTrace_4911756 : CollatzResearch.WordTrace tailWord_4911756 prefixEnd_4911756 840697228535063321920417 := by
  unfold tailWord_4911756
  simp only [CollatzResearch.WordTrace]
  refine ⟨89573229396777173992381561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119430972529036231989842081 89573229396777173992381561)
  ·
    refine ⟨67179922047582880494286171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89573229396777173992381561 67179922047582880494286171)
    ·
      refine ⟨100769883071374320741429257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67179922047582880494286171 100769883071374320741429257)
      ·
        refine ⟨75577412303530740556071943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100769883071374320741429257 75577412303530740556071943)
        ·
          refine ⟨113366118455296110834107915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75577412303530740556071943 113366118455296110834107915)
          ·
            refine ⟨170049177682944166251161873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113366118455296110834107915 170049177682944166251161873)
            ·
              refine ⟨127536883262208124688371405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170049177682944166251161873 127536883262208124688371405)
              ·
                refine ⟨47826331223328046758139277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127536883262208124688371405 47826331223328046758139277)
                ·
                  refine ⟨17934874208748017534302229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47826331223328046758139277 17934874208748017534302229)
                  ·
                    refine ⟨840697228535063321920417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17934874208748017534302229 840697228535063321920417)
                    ·
                      rfl

theorem cell23_4911756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 3, 6].length) (baseStart_4911756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911756 prefixEnd_4911756 := by exact prefixLift 4911756
  have htrace : WordTrace (prefixWord ++ tailWord_4911756) baseStart_4911756 baseEnd_4911756 := by
    simpa [prefixWord, tailWord_4911756, baseEnd_4911756] using wordTrace_append hprefix tailTrace_4911756
  have hstable : (prefixWord ++ tailWord_4911756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911756).length < 2 ^ (prefixWord ++ tailWord_4911756).sum := by decide
  have hdescent : baseEnd_4911756 < baseStart_4911756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911763 : List Nat := [1, 1, 1, 2, 1, 2, 2, 7, 1, 1, 4]
def baseStart_4911763 : Nat := 118140960795 + 4911763 * 2 ^ 59
def prefixEnd_4911763 : Nat := 4983230072969 + 3 ^ 40 * 4911763 * 2
def baseEnd_4911763 : Nat := 2522095279969771438373719

theorem tailTrace_4911763 : CollatzResearch.WordTrace tailWord_4911763 prefixEnd_4911763 2522095279969771438373719 := by
  unfold tailWord_4911763
  simp only [CollatzResearch.WordTrace]
  refine ⟨179146714104528988180267943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119431142736352658786845295 179146714104528988180267943)
  ·
    refine ⟨268720071156793482270401915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179146714104528988180267943 268720071156793482270401915)
    ·
      refine ⟨403080106735190223405602873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268720071156793482270401915 403080106735190223405602873)
      ·
        refine ⟨302310080051392667554202155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 403080106735190223405602873 302310080051392667554202155)
        ·
          refine ⟨453465120077089001331303233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302310080051392667554202155 453465120077089001331303233)
          ·
            refine ⟨340098840057816750998477425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 453465120077089001331303233 340098840057816750998477425)
            ·
              refine ⟨255074130043362563248858069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 340098840057816750998477425 255074130043362563248858069)
              ·
                refine ⟨5978299922891310076145111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 255074130043362563248858069 5978299922891310076145111)
                ·
                  refine ⟨8967449884336965114217667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5978299922891310076145111 8967449884336965114217667)
                  ·
                    refine ⟨13451174826505447671326501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8967449884336965114217667 13451174826505447671326501)
                    ·
                      refine ⟨2522095279969771438373719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13451174826505447671326501 2522095279969771438373719)
                      ·
                        rfl

theorem cell23_4911763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 7, 1, 1, 4].length) (baseStart_4911763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911763 prefixEnd_4911763 := by exact prefixLift 4911763
  have htrace : WordTrace (prefixWord ++ tailWord_4911763) baseStart_4911763 baseEnd_4911763 := by
    simpa [prefixWord, tailWord_4911763, baseEnd_4911763] using wordTrace_append hprefix tailTrace_4911763
  have hstable : (prefixWord ++ tailWord_4911763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911763).length < 2 ^ (prefixWord ++ tailWord_4911763).sum := by decide
  have hdescent : baseEnd_4911763 < baseStart_4911763 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911774 : List Nat := [4, 3, 1, 1, 1, 1, 1, 6, 1, 1, 3]
def baseStart_4911774 : Nat := 118140960795 + 4911774 * 2 ^ 59
def prefixEnd_4911774 : Nat := 4983230072969 + 3 ^ 40 * 4911774 * 2
def baseEnd_4911774 : Nat := 2522100928256970895336169

theorem tailTrace_4911774 : CollatzResearch.WordTrace tailWord_4911774 prefixEnd_4911774 2522100928256970895336169 := by
  unfold tailWord_4911774
  simp only [CollatzResearch.WordTrace]
  refine ⟨22393389413436142132364797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119431410204992758039278917 22393389413436142132364797)
  ·
    refine ⟨8397521030038553299636799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22393389413436142132364797 8397521030038553299636799)
    ·
      refine ⟨12596281545057829949455199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8397521030038553299636799 12596281545057829949455199)
      ·
        refine ⟨18894422317586744924182799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12596281545057829949455199 18894422317586744924182799)
        ·
          refine ⟨28341633476380117386274199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18894422317586744924182799 28341633476380117386274199)
          ·
            refine ⟨42512450214570176079411299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28341633476380117386274199 42512450214570176079411299)
            ·
              refine ⟨63768675321855264119116949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42512450214570176079411299 63768675321855264119116949)
              ·
                refine ⟨2989156655711965505583607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 63768675321855264119116949 2989156655711965505583607)
                ·
                  refine ⟨4483734983567948258375411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2989156655711965505583607 4483734983567948258375411)
                  ·
                    refine ⟨6725602475351922387563117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4483734983567948258375411 6725602475351922387563117)
                    ·
                      refine ⟨2522100928256970895336169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6725602475351922387563117 2522100928256970895336169)
                      ·
                        rfl

theorem cell23_4911774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_4911774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911774 prefixEnd_4911774 := by exact prefixLift 4911774
  have htrace : WordTrace (prefixWord ++ tailWord_4911774) baseStart_4911774 baseEnd_4911774 := by
    simpa [prefixWord, tailWord_4911774, baseEnd_4911774] using wordTrace_append hprefix tailTrace_4911774
  have hstable : (prefixWord ++ tailWord_4911774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911774).length < 2 ^ (prefixWord ++ tailWord_4911774).sum := by decide
  have hdescent : baseEnd_4911774 < baseStart_4911774 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911797 : List Nat := [1, 3, 3, 3, 1, 2, 2, 2, 1, 1, 4]
def baseStart_4911797 : Nat := 118140960795 + 4911797 * 2 ^ 59
def prefixEnd_4911797 : Nat := 4983230072969 + 3 ^ 40 * 4911797 * 2
def baseEnd_4911797 : Nat := 2522112738312024305348563

theorem tailTrace_4911797 : CollatzResearch.WordTrace tailWord_4911797 prefixEnd_4911797 2522112738312024305348563 := by
  unfold tailWord_4911797
  simp only [CollatzResearch.WordTrace]
  refine ⟨179147954186405811987005645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119431969457603874658003763 179147954186405811987005645)
  ·
    refine ⟨67180482819902179495127117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179147954186405811987005645 67180482819902179495127117)
    ·
      refine ⟨25192681057463317310672669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67180482819902179495127117 25192681057463317310672669)
      ·
        refine ⟨9447255396548743991502251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25192681057463317310672669 9447255396548743991502251)
        ·
          refine ⟨14170883094823115987253377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9447255396548743991502251 14170883094823115987253377)
          ·
            refine ⟨10628162321117336990440033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14170883094823115987253377 10628162321117336990440033)
            ·
              refine ⟨7971121740838002742830025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10628162321117336990440033 7971121740838002742830025)
              ·
                refine ⟨5978341305628502057122519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7971121740838002742830025 5978341305628502057122519)
                ·
                  refine ⟨8967511958442753085683779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5978341305628502057122519 8967511958442753085683779)
                  ·
                    refine ⟨13451267937664129628525669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8967511958442753085683779 13451267937664129628525669)
                    ·
                      refine ⟨2522112738312024305348563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13451267937664129628525669 2522112738312024305348563)
                      ·
                        rfl

theorem cell23_4911797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_4911797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911797 prefixEnd_4911797 := by exact prefixLift 4911797
  have htrace : WordTrace (prefixWord ++ tailWord_4911797) baseStart_4911797 baseEnd_4911797 := by
    simpa [prefixWord, tailWord_4911797, baseEnd_4911797] using wordTrace_append hprefix tailTrace_4911797
  have hstable : (prefixWord ++ tailWord_4911797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911797).length < 2 ^ (prefixWord ++ tailWord_4911797).sum := by decide
  have hdescent : baseEnd_4911797 < baseStart_4911797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911831 : List Nat := [1, 1, 3, 2, 1, 5, 3, 2, 1, 2, 2]
def baseStart_4911831 : Nat := 118140960795 + 4911831 * 2 ^ 59
def prefixEnd_4911831 : Nat := 4983230072969 + 3 ^ 40 * 4911831 * 2
def baseEnd_4911831 : Nat := 2522130196654277172323407

theorem tailTrace_4911831 : CollatzResearch.WordTrace tailWord_4911831 prefixEnd_4911831 2522130196654277172323407 := by
  unfold tailWord_4911831
  simp only [CollatzResearch.WordTrace]
  refine ⟨179149194268282635793743347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119432796178855090529162231 179149194268282635793743347)
  ·
    refine ⟨268723791402423953690615021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179149194268282635793743347 268723791402423953690615021)
    ·
      refine ⟨100771421775908982633980633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 268723791402423953690615021 100771421775908982633980633)
      ·
        refine ⟨75578566331931736975485475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100771421775908982633980633 75578566331931736975485475)
        ·
          refine ⟨113367849497897605463228213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75578566331931736975485475 113367849497897605463228213)
          ·
            refine ⟨10628235890427900512177645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 113367849497897605463228213 10628235890427900512177645)
            ·
              refine ⟨3985588458910462692066617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10628235890427900512177645 3985588458910462692066617)
              ·
                refine ⟨2989191344182847019049963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3985588458910462692066617 2989191344182847019049963)
                ·
                  refine ⟨4483787016274270528574945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2989191344182847019049963 4483787016274270528574945)
                  ·
                    refine ⟨3362840262205702896431209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4483787016274270528574945 3362840262205702896431209)
                    ·
                      refine ⟨2522130196654277172323407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3362840262205702896431209 2522130196654277172323407)
                      ·
                        rfl

theorem cell23_4911831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 2, 1, 2, 2].length) (baseStart_4911831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911831 prefixEnd_4911831 := by exact prefixLift 4911831
  have htrace : WordTrace (prefixWord ++ tailWord_4911831) baseStart_4911831 baseEnd_4911831 := by
    simpa [prefixWord, tailWord_4911831, baseEnd_4911831] using wordTrace_append hprefix tailTrace_4911831
  have hstable : (prefixWord ++ tailWord_4911831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911831).length < 2 ^ (prefixWord ++ tailWord_4911831).sum := by decide
  have hdescent : baseEnd_4911831 < baseStart_4911831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911840 : List Nat := [2, 1, 1, 3, 1, 2, 1, 4, 3, 3, 2]
def baseStart_4911840 : Nat := 118140960795 + 4911840 * 2 ^ 59
def prefixEnd_4911840 : Nat := 4983230072969 + 3 ^ 40 * 4911840 * 2
def baseEnd_4911840 : Nat := 2522134817980167637110865

theorem tailTrace_4911840 : CollatzResearch.WordTrace tailWord_4911840 prefixEnd_4911840 2522134817980167637110865 := by
  unfold tailWord_4911840
  simp only [CollatzResearch.WordTrace]
  refine ⟨89574761262625015165410487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119433015016833353553880649 89574761262625015165410487)
  ·
    refine ⟨134362141893937522748115731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89574761262625015165410487 134362141893937522748115731)
    ·
      refine ⟨201543212840906284122173597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134362141893937522748115731 201543212840906284122173597)
      ·
        refine ⟨75578704815339856545815099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201543212840906284122173597 75578704815339856545815099)
        ·
          refine ⟨113368057223009784818722649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75578704815339856545815099 113368057223009784818722649)
          ·
            refine ⟨85026042917257338614041987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113368057223009784818722649 85026042917257338614041987)
            ·
              refine ⟨127539064375886007921062981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85026042917257338614041987 127539064375886007921062981)
              ·
                refine ⟨23913574570478626485199309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 127539064375886007921062981 23913574570478626485199309)
                ·
                  refine ⟨8967590463929484931949741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23913574570478626485199309 8967590463929484931949741)
                  ·
                    refine ⟨3362846423973556849481153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8967590463929484931949741 3362846423973556849481153)
                    ·
                      refine ⟨2522134817980167637110865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3362846423973556849481153 2522134817980167637110865)
                      ·
                        rfl

theorem cell23_4911840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 3, 3, 2].length) (baseStart_4911840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911840 prefixEnd_4911840 := by exact prefixLift 4911840
  have htrace : WordTrace (prefixWord ++ tailWord_4911840) baseStart_4911840 baseEnd_4911840 := by
    simpa [prefixWord, tailWord_4911840, baseEnd_4911840] using wordTrace_append hprefix tailTrace_4911840
  have hstable : (prefixWord ++ tailWord_4911840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911840).length < 2 ^ (prefixWord ++ tailWord_4911840).sum := by decide
  have hdescent : baseEnd_4911840 < baseStart_4911840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911883 : List Nat := [1, 1, 1, 1, 5, 1, 1, 4, 2, 2, 4]
def baseStart_4911883 : Nat := 118140960795 + 4911883 * 2 ^ 59
def prefixEnd_4911883 : Nat := 4983230072969 + 3 ^ 40 * 4911883 * 2
def baseEnd_4911883 : Nat := 2522156897648310968873167

theorem tailTrace_4911883 : CollatzResearch.WordTrace tailWord_4911883 prefixEnd_4911883 2522156897648310968873167 := by
  unfold tailWord_4911883
  simp only [CollatzResearch.WordTrace]
  refine ⟨179151090864094248674636303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119434060576062832449757535 179151090864094248674636303)
  ·
    refine ⟨268726636296141373011954455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179151090864094248674636303 268726636296141373011954455)
    ·
      refine ⟨403089954444212059517931683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268726636296141373011954455 403089954444212059517931683)
      ·
        refine ⟨604634931666318089276897525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 403089954444212059517931683 604634931666318089276897525)
        ·
          refine ⟨56684524843717320869709143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 604634931666318089276897525 56684524843717320869709143)
          ·
            refine ⟨85026787265575981304563715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56684524843717320869709143 85026787265575981304563715)
            ·
              refine ⟨127540180898363971956845573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85026787265575981304563715 127540180898363971956845573)
              ·
                refine ⟨23913783918443244741908545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 127540180898363971956845573 23913783918443244741908545)
                ·
                  refine ⟨17935337938832433556431409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23913783918443244741908545 17935337938832433556431409)
                  ·
                    refine ⟨13451503454124325167323557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17935337938832433556431409 13451503454124325167323557)
                    ·
                      refine ⟨2522156897648310968873167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13451503454124325167323557 2522156897648310968873167)
                      ·
                        rfl

theorem cell23_4911883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 2, 4].length) (baseStart_4911883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911883 prefixEnd_4911883 := by exact prefixLift 4911883
  have htrace : WordTrace (prefixWord ++ tailWord_4911883) baseStart_4911883 baseEnd_4911883 := by
    simpa [prefixWord, tailWord_4911883, baseEnd_4911883] using wordTrace_append hprefix tailTrace_4911883
  have hstable : (prefixWord ++ tailWord_4911883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911883).length < 2 ^ (prefixWord ++ tailWord_4911883).sum := by decide
  have hdescent : baseEnd_4911883 < baseStart_4911883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911893 : List Nat := [1, 3, 2, 1, 2, 2, 2, 3, 7]
def baseStart_4911893 : Nat := 118140960795 + 4911893 * 2 ^ 59
def prefixEnd_4911893 : Nat := 4983230072969 + 3 ^ 40 * 4911893 * 2
def baseEnd_4911893 : Nat := 280240225828317325527569

theorem tailTrace_4911893 : CollatzResearch.WordTrace tailWord_4911893 prefixEnd_4911893 280240225828317325527569 := by
  unfold tailWord_4911893
  simp only [CollatzResearch.WordTrace]
  refine ⟨179151455594058020382500333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119434303729372013588333555 179151455594058020382500333)
  ·
    refine ⟨67181795847771757643437625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179151455594058020382500333 67181795847771757643437625)
    ·
      refine ⟨50386346885828818232578219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67181795847771757643437625 50386346885828818232578219)
      ·
        refine ⟨75579520328743227348867329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50386346885828818232578219 75579520328743227348867329)
        ·
          refine ⟨56684640246557420511650497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75579520328743227348867329 56684640246557420511650497)
          ·
            refine ⟨42513480184918065383737873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56684640246557420511650497 42513480184918065383737873)
            ·
              refine ⟨31885110138688549037803405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42513480184918065383737873 31885110138688549037803405)
              ·
                refine ⟨11956916302008205889176277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31885110138688549037803405 11956916302008205889176277)
                ·
                  refine ⟨280240225828317325527569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11956916302008205889176277 280240225828317325527569)
                  ·
                    rfl

theorem cell23_4911893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 7].length) (baseStart_4911893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911893 prefixEnd_4911893 := by exact prefixLift 4911893
  have htrace : WordTrace (prefixWord ++ tailWord_4911893) baseStart_4911893 baseEnd_4911893 := by
    simpa [prefixWord, tailWord_4911893, baseEnd_4911893] using wordTrace_append hprefix tailTrace_4911893
  have hstable : (prefixWord ++ tailWord_4911893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911893).length < 2 ^ (prefixWord ++ tailWord_4911893).sum := by decide
  have hdescent : baseEnd_4911893 < baseStart_4911893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911900 : List Nat := [2, 2, 3, 1, 1, 4, 1, 1, 2, 2, 4]
def baseStart_4911900 : Nat := 118140960795 + 4911900 * 2 ^ 59
def prefixEnd_4911900 : Nat := 4983230072969 + 3 ^ 40 * 4911900 * 2
def baseEnd_4911900 : Nat := 2522165626819437402360589

theorem tailTrace_4911900 : CollatzResearch.WordTrace tailWord_4911900 prefixEnd_4911900 2522165626819437402360589 := by
  unfold tailWord_4911900
  simp only [CollatzResearch.WordTrace]
  refine ⟨89575855452516330289002577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119434473936688440385336769 89575855452516330289002577)
  ·
    refine ⟨67181891589387247716751933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89575855452516330289002577 67181891589387247716751933)
    ·
      refine ⟨25193209346020217893781975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67181891589387247716751933 25193209346020217893781975)
      ·
        refine ⟨37789814019030326840672963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25193209346020217893781975 37789814019030326840672963)
        ·
          refine ⟨56684721028545490261009445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37789814019030326840672963 56684721028545490261009445)
          ·
            refine ⟨10628385192852279423939271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56684721028545490261009445 10628385192852279423939271)
            ·
              refine ⟨15942577789278419135908907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10628385192852279423939271 15942577789278419135908907)
              ·
                refine ⟨23913866683917628703863361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15942577789278419135908907 23913866683917628703863361)
                ·
                  refine ⟨17935400012938221527897521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23913866683917628703863361 17935400012938221527897521)
                  ·
                    refine ⟨13451550009703666145923141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17935400012938221527897521 13451550009703666145923141)
                    ·
                      refine ⟨2522165626819437402360589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13451550009703666145923141 2522165626819437402360589)
                      ·
                        rfl

theorem cell23_4911900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_4911900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911900 prefixEnd_4911900 := by exact prefixLift 4911900
  have htrace : WordTrace (prefixWord ++ tailWord_4911900) baseStart_4911900 baseEnd_4911900 := by
    simpa [prefixWord, tailWord_4911900, baseEnd_4911900] using wordTrace_append hprefix tailTrace_4911900
  have hstable : (prefixWord ++ tailWord_4911900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911900).length < 2 ^ (prefixWord ++ tailWord_4911900).sum := by decide
  have hdescent : baseEnd_4911900 < baseStart_4911900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911904 : List Nat := [2, 1, 1, 5, 1, 2, 2, 3, 2, 2, 2]
def baseStart_4911904 : Nat := 118140960795 + 4911904 * 2 ^ 59
def prefixEnd_4911904 : Nat := 4983230072969 + 3 ^ 40 * 4911904 * 2
def baseEnd_4911904 : Nat := 2522167680742055386710571

theorem tailTrace_4911904 : CollatzResearch.WordTrace tailWord_4911904 prefixEnd_4911904 2522167680742055386710571 := by
  unfold tailWord_4911904
  simp only [CollatzResearch.WordTrace]
  refine ⟨89575928398509084630575383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119434571198012112840767177 89575928398509084630575383)
  ·
    refine ⟨134363892597763626945863075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89575928398509084630575383 134363892597763626945863075)
    ·
      refine ⟨201545838896645440418794613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134363892597763626945863075 201545838896645440418794613)
      ·
        refine ⟨18894922396560510039261995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 201545838896645440418794613 18894922396560510039261995)
        ·
          refine ⟨28342383594840765058892993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18894922396560510039261995 28342383594840765058892993)
          ·
            refine ⟨21256787696130573794169745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28342383594840765058892993 21256787696130573794169745)
            ·
              refine ⟨15942590772097930345627309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21256787696130573794169745 15942590772097930345627309)
              ·
                refine ⟨5978471539536723879610241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15942590772097930345627309 5978471539536723879610241)
                ·
                  refine ⟨4483853654652542909707681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5978471539536723879610241 4483853654652542909707681)
                  ·
                    refine ⟨3362890240989407182280761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4483853654652542909707681 3362890240989407182280761)
                    ·
                      refine ⟨2522167680742055386710571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3362890240989407182280761 2522167680742055386710571)
                      ·
                        rfl

theorem cell23_4911904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_4911904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911904 prefixEnd_4911904 := by exact prefixLift 4911904
  have htrace : WordTrace (prefixWord ++ tailWord_4911904) baseStart_4911904 baseEnd_4911904 := by
    simpa [prefixWord, tailWord_4911904, baseEnd_4911904] using wordTrace_append hprefix tailTrace_4911904
  have hstable : (prefixWord ++ tailWord_4911904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911904).length < 2 ^ (prefixWord ++ tailWord_4911904).sum := by decide
  have hdescent : baseEnd_4911904 < baseStart_4911904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4911980 : List Nat := [2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 3]
def baseStart_4911980 : Nat := 118140960795 + 4911980 * 2 ^ 59
def prefixEnd_4911980 : Nat := 4983230072969 + 3 ^ 40 * 4911980 * 2
def baseEnd_4911980 : Nat := 2522206705271797089360221

theorem tailTrace_4911980 : CollatzResearch.WordTrace tailWord_4911980 prefixEnd_4911980 2522206705271797089360221 := by
  unfold tailWord_4911980
  simp only [CollatzResearch.WordTrace]
  refine ⟨89577314372371417120458697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119436419163161889493944929 89577314372371417120458697)
  ·
    refine ⟨67182985779278562840344023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89577314372371417120458697 67182985779278562840344023)
    ·
      refine ⟨100774478668917844260516035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67182985779278562840344023 100774478668917844260516035)
      ·
        refine ⟨151161718003376766390774053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100774478668917844260516035 151161718003376766390774053)
        ·
          refine ⟨28342822125633143698270135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 151161718003376766390774053 28342822125633143698270135)
          ·
            refine ⟨42514233188449715547405203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28342822125633143698270135 42514233188449715547405203)
            ·
              refine ⟨63771349782674573321107805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42514233188449715547405203 63771349782674573321107805)
              ·
                refine ⟨23914256168502964995415427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63771349782674573321107805 23914256168502964995415427)
                ·
                  refine ⟨35871384252754447493123141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23914256168502964995415427 35871384252754447493123141)
                  ·
                    refine ⟨6725884547391458904960589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35871384252754447493123141 6725884547391458904960589)
                    ·
                      refine ⟨2522206705271797089360221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6725884547391458904960589 2522206705271797089360221)
                      ·
                        rfl

theorem cell23_4911980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 3].length) (baseStart_4911980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4911980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4911980 prefixEnd_4911980 := by exact prefixLift 4911980
  have htrace : WordTrace (prefixWord ++ tailWord_4911980) baseStart_4911980 baseEnd_4911980 := by
    simpa [prefixWord, tailWord_4911980, baseEnd_4911980] using wordTrace_append hprefix tailTrace_4911980
  have hstable : (prefixWord ++ tailWord_4911980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4911980).length < 2 ^ (prefixWord ++ tailWord_4911980).sum := by decide
  have hdescent : baseEnd_4911980 < baseStart_4911980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4911980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4912098 : List Nat := [3, 3, 3, 1, 1, 3, 2, 1, 1, 5]
def baseStart_4912098 : Nat := 118140960795 + 4912098 * 2 ^ 59
def prefixEnd_4912098 : Nat := 4983230072969 + 3 ^ 40 * 4912098 * 2
def baseEnd_4912098 : Nat := 840755765329675875894893

theorem tailTrace_4912098 : CollatzResearch.WordTrace tailWord_4912098 prefixEnd_4912098 840755765329675875894893 := by
  unfold tailWord_4912098
  simp only [CollatzResearch.WordTrace]
  refine ⟨44789733139578835098428237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119439288372210226929141965 44789733139578835098428237)
  ·
    refine ⟨16796149927342063161910589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44789733139578835098428237 16796149927342063161910589)
    ·
      refine ⟨6298556222753273685716471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16796149927342063161910589 6298556222753273685716471)
      ·
        refine ⟨9447834334129910528574707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6298556222753273685716471 9447834334129910528574707)
        ·
          refine ⟨14171751501194865792862061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9447834334129910528574707 14171751501194865792862061)
          ·
            refine ⟨5314406812948074672323273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14171751501194865792862061 5314406812948074672323273)
            ·
              refine ⟨3985805109711056004242455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5314406812948074672323273 3985805109711056004242455)
              ·
                refine ⟨5978707664566584006363683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3985805109711056004242455 5978707664566584006363683)
                ·
                  refine ⟨8968061496849876009545525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5978707664566584006363683 8968061496849876009545525)
                  ·
                    refine ⟨840755765329675875894893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8968061496849876009545525 840755765329675875894893)
                    ·
                      rfl

theorem cell23_4912098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_4912098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4912098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4912098 prefixEnd_4912098 := by exact prefixLift 4912098
  have htrace : WordTrace (prefixWord ++ tailWord_4912098) baseStart_4912098 baseEnd_4912098 := by
    simpa [prefixWord, tailWord_4912098, baseEnd_4912098] using wordTrace_append hprefix tailTrace_4912098
  have hstable : (prefixWord ++ tailWord_4912098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4912098).length < 2 ^ (prefixWord ++ tailWord_4912098).sum := by decide
  have hdescent : baseEnd_4912098 < baseStart_4912098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4912098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4912101 : List Nat := [1, 3, 1, 6, 1, 1, 1, 3, 1, 1, 4]
def baseStart_4912101 : Nat := 118140960795 + 4912101 * 2 ^ 59
def prefixEnd_4912101 : Nat := 4983230072969 + 3 ^ 40 * 4912101 * 2
def baseEnd_4912101 : Nat := 2522268836430991115947165

theorem tailTrace_4912101 : CollatzResearch.WordTrace tailWord_4912101 prefixEnd_4912101 2522268836430991115947165 := by
  unfold tailWord_4912101
  simp only [CollatzResearch.WordTrace]
  refine ⟨179159041977304471906072157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119439361318202981270714771 179159041977304471906072157)
  ·
    refine ⟨67184640741489176964777059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179159041977304471906072157 67184640741489176964777059)
    ·
      refine ⟨100776961112233765447165589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67184640741489176964777059 100776961112233765447165589)
      ·
        refine ⟨4723920052135957755335887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 100776961112233765447165589 4723920052135957755335887)
        ·
          refine ⟨7085880078203936633003831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4723920052135957755335887 7085880078203936633003831)
          ·
            refine ⟨10628820117305904949505747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7085880078203936633003831 10628820117305904949505747)
            ·
              refine ⟨15943230175958857424258621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10628820117305904949505747 15943230175958857424258621)
              ·
                refine ⟨5978711315984571534096983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15943230175958857424258621 5978711315984571534096983)
                ·
                  refine ⟨8968066973976857301145475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5978711315984571534096983 8968066973976857301145475)
                  ·
                    refine ⟨13452100460965285951718213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8968066973976857301145475 13452100460965285951718213)
                    ·
                      refine ⟨2522268836430991115947165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13452100460965285951718213 2522268836430991115947165)
                      ·
                        rfl

theorem cell23_4912101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_4912101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4912101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4912101 prefixEnd_4912101 := by exact prefixLift 4912101
  have htrace : WordTrace (prefixWord ++ tailWord_4912101) baseStart_4912101 baseEnd_4912101 := by
    simpa [prefixWord, tailWord_4912101, baseEnd_4912101] using wordTrace_append hprefix tailTrace_4912101
  have hstable : (prefixWord ++ tailWord_4912101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4912101).length < 2 ^ (prefixWord ++ tailWord_4912101).sum := by decide
  have hdescent : baseEnd_4912101 < baseStart_4912101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4912101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4912118 : List Nat := [5, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2]
def baseStart_4912118 : Nat := 118140960795 + 4912118 * 2 ^ 59
def prefixEnd_4912118 : Nat := 4983230072969 + 3 ^ 40 * 4912118 * 2
def baseEnd_4912118 : Nat := 2522277565602117549434587

theorem tailTrace_4912118 : CollatzResearch.WordTrace tailWord_4912118 prefixEnd_4912118 2522277565602117549434587 := by
  unfold tailWord_4912118
  simp only [CollatzResearch.WordTrace]
  refine ⟨11197478876140180238090063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 119439774678828589206294005 11197478876140180238090063)
  ·
    refine ⟨16796218314210270357135095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11197478876140180238090063 16796218314210270357135095)
    ·
      refine ⟨25194327471315405535702643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16796218314210270357135095 25194327471315405535702643)
      ·
        refine ⟨37791491206973108303553965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25194327471315405535702643 37791491206973108303553965)
        ·
          refine ⟨14171809202614915613832737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37791491206973108303553965 14171809202614915613832737)
          ·
            refine ⟨10628856901961186710374553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14171809202614915613832737 10628856901961186710374553)
            ·
              refine ⟨7971642676470890032780915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10628856901961186710374553 7971642676470890032780915)
              ·
                refine ⟨11957464014706335049171373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7971642676470890032780915 11957464014706335049171373)
                ·
                  refine ⟨4484049005514875643439265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11957464014706335049171373 4484049005514875643439265)
                  ·
                    refine ⟨3363036754136156732579449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4484049005514875643439265 3363036754136156732579449)
                    ·
                      refine ⟨2522277565602117549434587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3363036754136156732579449 2522277565602117549434587)
                      ·
                        rfl

theorem cell23_4912118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2].length) (baseStart_4912118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4912118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4912118 prefixEnd_4912118 := by exact prefixLift 4912118
  have htrace : WordTrace (prefixWord ++ tailWord_4912118) baseStart_4912118 baseEnd_4912118 := by
    simpa [prefixWord, tailWord_4912118, baseEnd_4912118] using wordTrace_append hprefix tailTrace_4912118
  have hstable : (prefixWord ++ tailWord_4912118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4912118).length < 2 ^ (prefixWord ++ tailWord_4912118).sum := by decide
  have hdescent : baseEnd_4912118 < baseStart_4912118 := by decide
  rcases family_descends (prefixWord ++ tailWord_4912118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4912161 : List Nat := [1, 2, 3, 2, 3, 1, 2, 3, 1, 3, 2]
def baseStart_4912161 : Nat := 118140960795 + 4912161 * 2 ^ 59
def prefixEnd_4912161 : Nat := 4983230072969 + 3 ^ 40 * 4912161 * 2
def baseEnd_4912161 : Nat := 2522299645270260881196889

theorem tailTrace_4912161 : CollatzResearch.WordTrace tailWord_4912161 prefixEnd_4912161 2522299645270260881196889 := by
  unfold tailWord_4912161
  simp only [CollatzResearch.WordTrace]
  refine ⟨179161230357087102153256337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119440820238058068102170891 179161230357087102153256337)
  ·
    refine ⟨134370922767815326614942253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179161230357087102153256337 134370922767815326614942253)
    ·
      refine ⟨50389096037930747480603345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134370922767815326614942253 50389096037930747480603345)
      ·
        refine ⟨37791822028448060610452509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50389096037930747480603345 37791822028448060610452509)
        ·
          refine ⟨14171933260668022728919691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37791822028448060610452509 14171933260668022728919691)
          ·
            refine ⟨21257899891002034093379537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14171933260668022728919691 21257899891002034093379537)
            ·
              refine ⟨15943424918251525570034653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21257899891002034093379537 15943424918251525570034653)
              ·
                refine ⟨5978784344344322088762995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15943424918251525570034653 5978784344344322088762995)
                ·
                  refine ⟨8968176516516483133144493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5978784344344322088762995 8968176516516483133144493)
                  ·
                    refine ⟨3363066193693681174929185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8968176516516483133144493 3363066193693681174929185)
                    ·
                      refine ⟨2522299645270260881196889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3363066193693681174929185 2522299645270260881196889)
                      ·
                        rfl

theorem cell23_4912161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 3, 1, 3, 2].length) (baseStart_4912161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4912161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4912161 prefixEnd_4912161 := by exact prefixLift 4912161
  have htrace : WordTrace (prefixWord ++ tailWord_4912161) baseStart_4912161 baseEnd_4912161 := by
    simpa [prefixWord, tailWord_4912161, baseEnd_4912161] using wordTrace_append hprefix tailTrace_4912161
  have hstable : (prefixWord ++ tailWord_4912161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4912161).length < 2 ^ (prefixWord ++ tailWord_4912161).sum := by decide
  have hdescent : baseEnd_4912161 < baseStart_4912161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4912161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4912177 : List Nat := [1, 2, 2, 3, 1, 2, 2, 1, 2, 4, 3]
def baseStart_4912177 : Nat := 118140960795 + 4912177 * 2 ^ 59
def prefixEnd_4912177 : Nat := 4983230072969 + 3 ^ 40 * 4912177 * 2
def baseEnd_4912177 : Nat := 2522307860960732818596815

theorem tailTrace_4912177 : CollatzResearch.WordTrace tailWord_4912177 prefixEnd_4912177 2522307860960732818596815 := by
  unfold tailWord_4912177
  simp only [CollatzResearch.WordTrace]
  refine ⟨179161813925029136885838785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119441209283352757923892523 179161813925029136885838785)
  ·
    refine ⟨134371360443771852664379089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179161813925029136885838785 134371360443771852664379089)
    ·
      refine ⟨100778520332828889498284317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134371360443771852664379089 100778520332828889498284317)
      ·
        refine ⟨37791945124810833561856619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100778520332828889498284317 37791945124810833561856619)
        ·
          refine ⟨56687917687216250342784929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37791945124810833561856619 56687917687216250342784929)
          ·
            refine ⟨42515938265412187757088697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56687917687216250342784929 42515938265412187757088697)
            ·
              refine ⟨31886953699059140817816523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42515938265412187757088697 31886953699059140817816523)
              ·
                refine ⟨47830430548588711226724785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31886953699059140817816523 47830430548588711226724785)
                ·
                  refine ⟨35872822911441533420043589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47830430548588711226724785 35872822911441533420043589)
                  ·
                    refine ⟨6726154295895287516258173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35872822911441533420043589 6726154295895287516258173)
                    ·
                      refine ⟨2522307860960732818596815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6726154295895287516258173 2522307860960732818596815)
                      ·
                        rfl

theorem cell23_4912177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_4912177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4912177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4912177 prefixEnd_4912177 := by exact prefixLift 4912177
  have htrace : WordTrace (prefixWord ++ tailWord_4912177) baseStart_4912177 baseEnd_4912177 := by
    simpa [prefixWord, tailWord_4912177, baseEnd_4912177] using wordTrace_append hprefix tailTrace_4912177
  have hstable : (prefixWord ++ tailWord_4912177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4912177).length < 2 ^ (prefixWord ++ tailWord_4912177).sum := by decide
  have hdescent : baseEnd_4912177 < baseStart_4912177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4912177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4912231 : List Nat := [1, 1, 5, 1, 1, 3, 4, 2, 5]
def baseStart_4912231 : Nat := 118140960795 + 4912231 * 2 ^ 59
def prefixEnd_4912231 : Nat := 4983230072969 + 3 ^ 40 * 4912231 * 2
def baseEnd_4912231 : Nat := 280259509879563956369063

theorem tailTrace_4912231 : CollatzResearch.WordTrace tailWord_4912231 prefixEnd_4912231 280259509879563956369063 := by
  unfold tailWord_4912231
  simp only [CollatzResearch.WordTrace]
  refine ⟨179163783466833504108304547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119442522311222336072203031 179163783466833504108304547)
  ·
    refine ⟨268745675200250256162456821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179163783466833504108304547 268745675200250256162456821)
    ·
      refine ⟨25194907050023461515230327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 268745675200250256162456821 25194907050023461515230327)
      ·
        refine ⟨37792360575035192272845491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25194907050023461515230327 37792360575035192272845491)
        ·
          refine ⟨56688540862552788409268237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37792360575035192272845491 56688540862552788409268237)
          ·
            refine ⟨21258202823457295653475589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56688540862552788409268237 21258202823457295653475589)
            ·
              refine ⟨3985913029398242935026673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21258202823457295653475589 3985913029398242935026673)
              ·
                refine ⟨2989434772048682201270005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3985913029398242935026673 2989434772048682201270005)
                ·
                  refine ⟨280259509879563956369063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2989434772048682201270005 280259509879563956369063)
                  ·
                    rfl

theorem cell23_4912231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 2, 5].length) (baseStart_4912231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4912231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4912231 prefixEnd_4912231 := by exact prefixLift 4912231
  have htrace : WordTrace (prefixWord ++ tailWord_4912231) baseStart_4912231 baseEnd_4912231 := by
    simpa [prefixWord, tailWord_4912231, baseEnd_4912231] using wordTrace_append hprefix tailTrace_4912231
  have hstable : (prefixWord ++ tailWord_4912231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4912231).length < 2 ^ (prefixWord ++ tailWord_4912231).sum := by decide
  have hdescent : baseEnd_4912231 < baseStart_4912231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4912231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4912247 : List Nat := [1, 1, 3, 1, 1, 4, 2, 2, 1, 3, 4]
def baseStart_4912247 : Nat := 118140960795 + 4912247 * 2 ^ 59
def prefixEnd_4912247 : Nat := 4983230072969 + 3 ^ 40 * 4912247 * 2
def baseEnd_4912247 : Nat := 2522343804606547544721493

theorem tailTrace_4912247 : CollatzResearch.WordTrace tailWord_4912247 prefixEnd_4912247 2522343804606547544721493 := by
  unfold tailWord_4912247
  simp only [CollatzResearch.WordTrace]
  refine ⟨179164367034775538840886995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119442911356517025893924663 179164367034775538840886995)
  ·
    refine ⟨268746550552163308261330493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179164367034775538840886995 268746550552163308261330493)
    ·
      refine ⟨100779956457061240597998935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 268746550552163308261330493 100779956457061240597998935)
      ·
        refine ⟨151169934685591860896998403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100779956457061240597998935 151169934685591860896998403)
        ·
          refine ⟨226754902028387791345497605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151169934685591860896998403 226754902028387791345497605)
          ·
            refine ⟨42516544130322710877280801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 226754902028387791345497605 42516544130322710877280801)
            ·
              refine ⟨31887408097742033157960601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42516544130322710877280801 31887408097742033157960601)
              ·
                refine ⟨23915556073306524868470451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31887408097742033157960601 23915556073306524868470451)
                ·
                  refine ⟨35873334109959787302705677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23915556073306524868470451 35873334109959787302705677)
                  ·
                    refine ⟨13452500291234920238514629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35873334109959787302705677 13452500291234920238514629)
                    ·
                      refine ⟨2522343804606547544721493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13452500291234920238514629 2522343804606547544721493)
                      ·
                        rfl

theorem cell23_4912247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 3, 4].length) (baseStart_4912247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4912247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4912247 prefixEnd_4912247 := by exact prefixLift 4912247
  have htrace : WordTrace (prefixWord ++ tailWord_4912247) baseStart_4912247 baseEnd_4912247 := by
    simpa [prefixWord, tailWord_4912247, baseEnd_4912247] using wordTrace_append hprefix tailTrace_4912247
  have hstable : (prefixWord ++ tailWord_4912247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4912247).length < 2 ^ (prefixWord ++ tailWord_4912247).sum := by decide
  have hdescent : baseEnd_4912247 < baseStart_4912247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4912247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4912261 : List Nat := [1, 3, 1, 1, 6, 2, 1, 1, 2, 5]
def baseStart_4912261 : Nat := 118140960795 + 4912261 * 2 ^ 59
def prefixEnd_4912261 : Nat := 4983230072969 + 3 ^ 40 * 4912261 * 2
def baseEnd_4912261 : Nat := 840783664445236829982143

theorem tailTrace_4912261 : CollatzResearch.WordTrace tailWord_4912261 prefixEnd_4912261 840783664445236829982143 := by
  unfold tailWord_4912261
  simp only [CollatzResearch.WordTrace]
  refine ⟨179164877656724819231896637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119443251771149879487931091 179164877656724819231896637)
  ·
    refine ⟨67186829121271807211961239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179164877656724819231896637 67186829121271807211961239)
    ·
      refine ⟨100780243681907710817941859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67186829121271807211961239 100780243681907710817941859)
      ·
        refine ⟨151170365522861566226912789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100780243681907710817941859 151170365522861566226912789)
        ·
          refine ⟨7086110883884135916886537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 151170365522861566226912789 7086110883884135916886537)
          ·
            refine ⟨5314583162913101937664903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7086110883884135916886537 5314583162913101937664903)
            ·
              refine ⟨7971874744369652906497355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5314583162913101937664903 7971874744369652906497355)
              ·
                refine ⟨11957812116554479359746033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7971874744369652906497355 11957812116554479359746033)
                ·
                  refine ⟨8968359087415859519809525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11957812116554479359746033 8968359087415859519809525)
                  ·
                    refine ⟨840783664445236829982143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8968359087415859519809525 840783664445236829982143)
                    ·
                      rfl

theorem cell23_4912261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 2, 5].length) (baseStart_4912261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4912261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4912261 prefixEnd_4912261 := by exact prefixLift 4912261
  have htrace : WordTrace (prefixWord ++ tailWord_4912261) baseStart_4912261 baseEnd_4912261 := by
    simpa [prefixWord, tailWord_4912261, baseEnd_4912261] using wordTrace_append hprefix tailTrace_4912261
  have hstable : (prefixWord ++ tailWord_4912261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4912261).length < 2 ^ (prefixWord ++ tailWord_4912261).sum := by decide
  have hdescent : baseEnd_4912261 < baseStart_4912261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4912261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4912298 : List Nat := [3, 1, 5, 1, 1, 1, 2, 1, 2, 4, 2]
def baseStart_4912298 : Nat := 118140960795 + 4912298 * 2 ^ 59
def prefixEnd_4912298 : Nat := 4983230072969 + 3 ^ 40 * 4912298 * 2
def baseEnd_4912298 : Nat := 2522369992119926845183759

theorem tailTrace_4912298 : CollatzResearch.WordTrace tailWord_4912298 prefixEnd_4912298 2522369992119926845183759 := by
  unfold tailWord_4912298
  simp only [CollatzResearch.WordTrace]
  refine ⟨44791556789397693637748387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119444151438393849700662365 44791556789397693637748387)
  ·
    refine ⟨67187335184096540456622581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44791556789397693637748387 67187335184096540456622581)
    ·
      refine ⟨6298812673509050667808367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67187335184096540456622581 6298812673509050667808367)
      ·
        refine ⟨9448219010263576001712551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6298812673509050667808367 9448219010263576001712551)
        ·
          refine ⟨14172328515395364002568827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9448219010263576001712551 14172328515395364002568827)
          ·
            refine ⟨21258492773093046003853241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14172328515395364002568827 21258492773093046003853241)
            ·
              refine ⟨15943869579819784502889931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21258492773093046003853241 15943869579819784502889931)
              ·
                refine ⟨23915804369729676754334897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15943869579819784502889931 23915804369729676754334897)
                ·
                  refine ⟨17936853277297257565751173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23915804369729676754334897 17936853277297257565751173)
                  ·
                    refine ⟨3363159989493235793578345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17936853277297257565751173 3363159989493235793578345)
                    ·
                      refine ⟨2522369992119926845183759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3363159989493235793578345 2522369992119926845183759)
                      ·
                        rfl

theorem cell23_4912298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_4912298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4912298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4912298 prefixEnd_4912298 := by exact prefixLift 4912298
  have htrace : WordTrace (prefixWord ++ tailWord_4912298) baseStart_4912298 baseEnd_4912298 := by
    simpa [prefixWord, tailWord_4912298, baseEnd_4912298] using wordTrace_append hprefix tailTrace_4912298
  have hstable : (prefixWord ++ tailWord_4912298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4912298).length < 2 ^ (prefixWord ++ tailWord_4912298).sum := by decide
  have hdescent : baseEnd_4912298 < baseStart_4912298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4912298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4912342 : List Nat := [5, 2, 1, 2, 3, 1, 1, 1, 3, 4]
def baseStart_4912342 : Nat := 118140960795 + 4912342 * 2 ^ 59
def prefixEnd_4912342 : Nat := 4983230072969 + 3 ^ 40 * 4912342 * 2
def baseEnd_4912342 : Nat := 840797528422908224344519

theorem tailTrace_4912342 : CollatzResearch.WordTrace tailWord_4912342 prefixEnd_4912342 840797528422908224344519 := by
  unfold tailWord_4912342
  simp only [CollatzResearch.WordTrace]
  refine ⟨11197989498089460629099705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 119445221312954246710396853 11197989498089460629099705)
  ·
    refine ⟨8398492123567095471824779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11197989498089460629099705 8398492123567095471824779)
    ·
      refine ⟨12597738185350643207737169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8398492123567095471824779 12597738185350643207737169)
      ·
        refine ⟨9448303639012982405802877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12597738185350643207737169 9448303639012982405802877)
        ·
          refine ⟨3543113864629868402176079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9448303639012982405802877 3543113864629868402176079)
          ·
            refine ⟨5314670796944802603264119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3543113864629868402176079 5314670796944802603264119)
            ·
              refine ⟨7972006195417203904896179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5314670796944802603264119 7972006195417203904896179)
              ·
                refine ⟨11958009293125805857344269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7972006195417203904896179 11958009293125805857344269)
                ·
                  refine ⟨4484253484922177196504101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11958009293125805857344269 4484253484922177196504101)
                  ·
                    refine ⟨840797528422908224344519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4484253484922177196504101 840797528422908224344519)
                    ·
                      rfl

theorem cell23_4912342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_4912342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4912342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4912342 prefixEnd_4912342 := by exact prefixLift 4912342
  have htrace : WordTrace (prefixWord ++ tailWord_4912342) baseStart_4912342 baseEnd_4912342 := by
    simpa [prefixWord, tailWord_4912342, baseEnd_4912342] using wordTrace_append hprefix tailTrace_4912342
  have hstable : (prefixWord ++ tailWord_4912342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4912342).length < 2 ^ (prefixWord ++ tailWord_4912342).sum := by decide
  have hdescent : baseEnd_4912342 < baseStart_4912342 := by decide
  rcases family_descends (prefixWord ++ tailWord_4912342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4912371 : List Nat := [1, 1, 1, 2, 2, 5, 3, 2, 1, 1, 4]
def baseStart_4912371 : Nat := 118140960795 + 4912371 * 2 ^ 59
def prefixEnd_4912371 : Nat := 4983230072969 + 3 ^ 40 * 4912371 * 2
def baseEnd_4912371 : Nat := 2522407476207705059570923

theorem tailTrace_4912371 : CollatzResearch.WordTrace tailWord_4912371 prefixEnd_4912371 2522407476207705059570923 := by
  unfold tailWord_4912371
  simp only [CollatzResearch.WordTrace]
  refine ⟨179168889686326308018400967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119445926457550872012267311 179168889686326308018400967)
  ·
    refine ⟨268753334529489462027601451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179168889686326308018400967 268753334529489462027601451)
    ·
      refine ⟨403130001794234193041402177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268753334529489462027601451 403130001794234193041402177)
      ·
        refine ⟨302347501345675644781051633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 403130001794234193041402177 302347501345675644781051633)
        ·
          refine ⟨226760626009256733585788725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 302347501345675644781051633 226760626009256733585788725)
          ·
            refine ⟨21258808688367818773667693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 226760626009256733585788725 21258808688367818773667693)
            ·
              refine ⟨7972053258137932040125385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21258808688367818773667693 7972053258137932040125385)
              ·
                refine ⟨5979039943603449030094039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7972053258137932040125385 5979039943603449030094039)
                ·
                  refine ⟨8968559915405173545141059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5979039943603449030094039 8968559915405173545141059)
                  ·
                    refine ⟨13452839873107760317711589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8968559915405173545141059 13452839873107760317711589)
                    ·
                      refine ⟨2522407476207705059570923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13452839873107760317711589 2522407476207705059570923)
                      ·
                        rfl

theorem cell23_4912371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 2, 1, 1, 4].length) (baseStart_4912371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4912371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4912371 prefixEnd_4912371 := by exact prefixLift 4912371
  have htrace : WordTrace (prefixWord ++ tailWord_4912371) baseStart_4912371 baseEnd_4912371 := by
    simpa [prefixWord, tailWord_4912371, baseEnd_4912371] using wordTrace_append hprefix tailTrace_4912371
  have hstable : (prefixWord ++ tailWord_4912371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4912371).length < 2 ^ (prefixWord ++ tailWord_4912371).sum := by decide
  have hdescent : baseEnd_4912371 < baseStart_4912371 := by decide
  rcases family_descends (prefixWord ++ tailWord_4912371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4912377 : List Nat := [1, 2, 1, 3, 1, 1, 3, 11]
def baseStart_4912377 : Nat := 118140960795 + 4912377 * 2 ^ 59
def prefixEnd_4912377 : Nat := 4983230072969 + 3 ^ 40 * 4912377 * 2
def baseEnd_4912377 : Nat := 93422613225616001336885

theorem tailTrace_4912377 : CollatzResearch.WordTrace tailWord_4912377 prefixEnd_4912377 93422613225616001336885 := by
  unfold tailWord_4912377
  simp only [CollatzResearch.WordTrace]
  refine ⟨179169108524304571043119385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119446072349536380695412923 179169108524304571043119385)
  ·
    refine ⟨134376831393228428282339539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179169108524304571043119385 134376831393228428282339539)
    ·
      refine ⟨201565247089842642423509309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134376831393228428282339539 201565247089842642423509309)
      ·
        refine ⟨75586967658690990908815991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201565247089842642423509309 75586967658690990908815991)
        ·
          refine ⟨113380451488036486363223987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75586967658690990908815991 113380451488036486363223987)
          ·
            refine ⟨170070677232054729544835981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113380451488036486363223987 170070677232054729544835981)
            ·
              refine ⟨63776503962020523579313493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 170070677232054729544835981 63776503962020523579313493)
              ·
                refine ⟨93422613225616001336885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 63776503962020523579313493 93422613225616001336885)
                ·
                  rfl

theorem cell23_4912377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 11].length) (baseStart_4912377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4912377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4912377 prefixEnd_4912377 := by exact prefixLift 4912377
  have htrace : WordTrace (prefixWord ++ tailWord_4912377) baseStart_4912377 baseEnd_4912377 := by
    simpa [prefixWord, tailWord_4912377, baseEnd_4912377] using wordTrace_append hprefix tailTrace_4912377
  have hstable : (prefixWord ++ tailWord_4912377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4912377).length < 2 ^ (prefixWord ++ tailWord_4912377).sum := by decide
  have hdescent : baseEnd_4912377 < baseStart_4912377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4912377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4912398 : List Nat := [4, 1, 1, 2, 1, 4, 2, 2, 2, 4]
def baseStart_4912398 : Nat := 118140960795 + 4912398 * 2 ^ 59
def prefixEnd_4912398 : Nat := 4983230072969 + 3 ^ 40 * 4912398 * 2
def baseEnd_4912398 : Nat := 840807113395125484644433

theorem tailTrace_4912398 : CollatzResearch.WordTrace tailWord_4912398 prefixEnd_4912398 840807113395125484644433 := by
  unfold tailWord_4912398
  simp only [CollatzResearch.WordTrace]
  refine ⟨22396234307153561453704231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119446582971485661086422565 22396234307153561453704231)
  ·
    refine ⟨33594351460730342180556347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22396234307153561453704231 33594351460730342180556347)
    ·
      refine ⟨50391527191095513270834521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33594351460730342180556347 50391527191095513270834521)
      ·
        refine ⟨37793645393321634953125891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50391527191095513270834521 37793645393321634953125891)
        ·
          refine ⟨56690468089982452429688837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37793645393321634953125891 56690468089982452429688837)
          ·
            refine ⟨10629462766871709830566657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56690468089982452429688837 10629462766871709830566657)
            ·
              refine ⟨7972097075153782372924993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10629462766871709830566657 7972097075153782372924993)
              ·
                refine ⟨5979072806365336779693745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7972097075153782372924993 5979072806365336779693745)
                ·
                  refine ⟨4484304604774002584770309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5979072806365336779693745 4484304604774002584770309)
                  ·
                    refine ⟨840807113395125484644433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4484304604774002584770309 840807113395125484644433)
                    ·
                      rfl

theorem cell23_4912398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 2, 2, 4].length) (baseStart_4912398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4912398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4912398 prefixEnd_4912398 := by exact prefixLift 4912398
  have htrace : WordTrace (prefixWord ++ tailWord_4912398) baseStart_4912398 baseEnd_4912398 := by
    simpa [prefixWord, tailWord_4912398, baseEnd_4912398] using wordTrace_append hprefix tailTrace_4912398
  have hstable : (prefixWord ++ tailWord_4912398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4912398).length < 2 ^ (prefixWord ++ tailWord_4912398).sum := by decide
  have hdescent : baseEnd_4912398 < baseStart_4912398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4912398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4912418 : List Nat := [3, 3, 1, 1, 4, 1, 2, 1, 1, 2, 4]
def baseStart_4912418 : Nat := 118140960795 + 4912418 * 2 ^ 59
def prefixEnd_4912418 : Nat := 4983230072969 + 3 ^ 40 * 4912418 * 2
def baseEnd_4912418 : Nat := 2522431609798466375683207

theorem tailTrace_4912418 : CollatzResearch.WordTrace tailWord_4912418 prefixEnd_4912418 2522431609798466375683207 := by
  unfold tailWord_4912418
  simp only [CollatzResearch.WordTrace]
  refine ⟨44792650979289008761340477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119447069278104023363574605 44792650979289008761340477)
  ·
    refine ⟨16797244117233378285502679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44792650979289008761340477 16797244117233378285502679)
    ·
      refine ⟨25195866175850067428254019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16797244117233378285502679 25195866175850067428254019)
      ·
        refine ⟨37793799263775101142381029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25195866175850067428254019 37793799263775101142381029)
        ·
          refine ⟨7086337361957831464196443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37793799263775101142381029 7086337361957831464196443)
          ·
            refine ⟨10629506042936747196294665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7086337361957831464196443 10629506042936747196294665)
            ·
              refine ⟨7972129532202560397220999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10629506042936747196294665 7972129532202560397220999)
              ·
                refine ⟨11958194298303840595831499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7972129532202560397220999 11958194298303840595831499)
                ·
                  refine ⟨17937291447455760893747249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11958194298303840595831499 17937291447455760893747249)
                  ·
                    refine ⟨13452968585591820670310437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17937291447455760893747249 13452968585591820670310437)
                    ·
                      refine ⟨2522431609798466375683207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13452968585591820670310437 2522431609798466375683207)
                      ·
                        rfl

theorem cell23_4912418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_4912418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4912418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4912418 prefixEnd_4912418 := by exact prefixLift 4912418
  have htrace : WordTrace (prefixWord ++ tailWord_4912418) baseStart_4912418 baseEnd_4912418 := by
    simpa [prefixWord, tailWord_4912418, baseEnd_4912418] using wordTrace_append hprefix tailTrace_4912418
  have hstable : (prefixWord ++ tailWord_4912418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4912418).length < 2 ^ (prefixWord ++ tailWord_4912418).sum := by decide
  have hdescent : baseEnd_4912418 < baseStart_4912418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4912418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4912421 : List Nat := [1, 3, 1, 2, 4, 1, 1, 3, 1, 3, 3]
def baseStart_4912421 : Nat := 118140960795 + 4912421 * 2 ^ 59
def prefixEnd_4912421 : Nat := 4983230072969 + 3 ^ 40 * 4912421 * 2
def baseEnd_4912421 : Nat := 2522433150240429863945693

theorem tailTrace_4912421 : CollatzResearch.WordTrace tailWord_4912421 prefixEnd_4912421 2522433150240429863945693 := by
  unfold tailWord_4912421
  simp only [CollatzResearch.WordTrace]
  refine ⟨179170713336145166557721117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119447142224096777705147411 179170713336145166557721117)
  ·
    refine ⟨67189017501054437459145419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179170713336145166557721117 67189017501054437459145419)
    ·
      refine ⟨100783526251581656188718129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67189017501054437459145419 100783526251581656188718129)
      ·
        refine ⟨75587644688686242141538597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100783526251581656188718129 75587644688686242141538597)
        ·
          refine ⟨14172683379128670401538487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75587644688686242141538597 14172683379128670401538487)
          ·
            refine ⟨21259025068693005602307731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14172683379128670401538487 21259025068693005602307731)
            ·
              refine ⟨31888537603039508403461597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21259025068693005602307731 31888537603039508403461597)
              ·
                refine ⟨11958201601139815651298099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31888537603039508403461597 11958201601139815651298099)
                ·
                  refine ⟨17937302401709723476947149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11958201601139815651298099 17937302401709723476947149)
                  ·
                    refine ⟨6726488400641146303855181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17937302401709723476947149 6726488400641146303855181)
                    ·
                      refine ⟨2522433150240429863945693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6726488400641146303855181 2522433150240429863945693)
                      ·
                        rfl

theorem cell23_4912421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 3, 3].length) (baseStart_4912421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4912421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4912421 prefixEnd_4912421 := by exact prefixLift 4912421
  have htrace : WordTrace (prefixWord ++ tailWord_4912421) baseStart_4912421 baseEnd_4912421 := by
    simpa [prefixWord, tailWord_4912421, baseEnd_4912421] using wordTrace_append hprefix tailTrace_4912421
  have hstable : (prefixWord ++ tailWord_4912421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4912421).length < 2 ^ (prefixWord ++ tailWord_4912421).sum := by decide
  have hdescent : baseEnd_4912421 < baseStart_4912421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4912421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4912448 : List Nat := [2, 1, 1, 2, 2, 1, 5, 3, 1, 3, 2]
def baseStart_4912448 : Nat := 118140960795 + 4912448 * 2 ^ 59
def prefixEnd_4912448 : Nat := 4983230072969 + 3 ^ 40 * 4912448 * 2
def baseEnd_4912448 : Nat := 2522447014218101258308069

theorem tailTrace_4912448 : CollatzResearch.WordTrace tailWord_4912448 prefixEnd_4912448 2522447014218101258308069 := by
  unfold tailWord_4912448
  simp only [CollatzResearch.WordTrace]
  refine ⟨89585849053523675084476999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119447798738031566779302665 89585849053523675084476999)
  ·
    refine ⟨134378773580285512626715499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89585849053523675084476999 134378773580285512626715499)
    ·
      refine ⟨201568160370428268940073249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134378773580285512626715499 201568160370428268940073249)
      ·
        refine ⟨151176120277821201705054937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201568160370428268940073249 151176120277821201705054937)
        ·
          refine ⟨113382090208365901278791203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151176120277821201705054937 113382090208365901278791203)
          ·
            refine ⟨170073135312548851918186805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113382090208365901278791203 170073135312548851918186805)
            ·
              refine ⟨15944356435551454867330013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 170073135312548851918186805 15944356435551454867330013)
              ·
                refine ⟨5979133663331795575248755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15944356435551454867330013 5979133663331795575248755)
                ·
                  refine ⟨8968700494997693362873133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5979133663331795575248755 8968700494997693362873133)
                  ·
                    refine ⟨3363262685624135011077425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8968700494997693362873133 3363262685624135011077425)
                    ·
                      refine ⟨2522447014218101258308069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3363262685624135011077425 2522447014218101258308069)
                      ·
                        rfl

theorem cell23_4912448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 3, 1, 3, 2].length) (baseStart_4912448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4912448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4912448 prefixEnd_4912448 := by exact prefixLift 4912448
  have htrace : WordTrace (prefixWord ++ tailWord_4912448) baseStart_4912448 baseEnd_4912448 := by
    simpa [prefixWord, tailWord_4912448, baseEnd_4912448] using wordTrace_append hprefix tailTrace_4912448
  have hstable : (prefixWord ++ tailWord_4912448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4912448).length < 2 ^ (prefixWord ++ tailWord_4912448).sum := by decide
  have hdescent : baseEnd_4912448 < baseStart_4912448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4912448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4912455 : List Nat := [1, 1, 4, 1, 2, 5, 1, 2, 2, 1, 3]
def baseStart_4912455 : Nat := 118140960795 + 4912455 * 2 ^ 59
def prefixEnd_4912455 : Nat := 4983230072969 + 3 ^ 40 * 4912455 * 2
def baseEnd_4912455 : Nat := 2522450608582682730920537

theorem tailTrace_4912455 : CollatzResearch.WordTrace tailWord_4912455 prefixEnd_4912455 2522450608582682730920537 := by
  unfold tailWord_4912455
  simp only [CollatzResearch.WordTrace]
  refine ⟨179171953418021990364458819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119447968945347993576305879 179171953418021990364458819)
  ·
    refine ⟨268757930127032985546688229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179171953418021990364458819 268757930127032985546688229)
    ·
      refine ⟨50392111898818684790004043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 268757930127032985546688229 50392111898818684790004043)
      ·
        refine ⟨75588167848228027185006065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50392111898818684790004043 75588167848228027185006065)
        ·
          refine ⟨56691125886171020388754549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75588167848228027185006065 56691125886171020388754549)
          ·
            refine ⟨5314793051828533161445739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56691125886171020388754549 5314793051828533161445739)
            ·
              refine ⟨7972189577742799742168609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5314793051828533161445739 7972189577742799742168609)
              ·
                refine ⟨5979142183307099806626457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7972189577742799742168609 5979142183307099806626457)
                ·
                  refine ⟨4484356637480324854969843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5979142183307099806626457 4484356637480324854969843)
                  ·
                    refine ⟨6726534956220487282454765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4484356637480324854969843 6726534956220487282454765)
                    ·
                      refine ⟨2522450608582682730920537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6726534956220487282454765 2522450608582682730920537)
                      ·
                        rfl

theorem cell23_4912455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 2, 2, 1, 3].length) (baseStart_4912455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4912455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4912455 prefixEnd_4912455 := by exact prefixLift 4912455
  have htrace : WordTrace (prefixWord ++ tailWord_4912455) baseStart_4912455 baseEnd_4912455 := by
    simpa [prefixWord, tailWord_4912455, baseEnd_4912455] using wordTrace_append hprefix tailTrace_4912455
  have hstable : (prefixWord ++ tailWord_4912455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4912455).length < 2 ^ (prefixWord ++ tailWord_4912455).sum := by decide
  have hdescent : baseEnd_4912455 < baseStart_4912455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4912455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4912591 : List Nat := [1, 1, 2, 1, 1, 4, 4, 3, 6]
def baseStart_4912591 : Nat := 118140960795 + 4912591 * 2 ^ 59
def prefixEnd_4912591 : Nat := 4983230072969 + 3 ^ 40 * 4912591 * 2
def baseEnd_4912591 : Nat := 280280049105743799868879

theorem tailTrace_4912591 : CollatzResearch.WordTrace tailWord_4912591 prefixEnd_4912591 280280049105743799868879 := by
  unfold tailWord_4912591
  simp only [CollatzResearch.WordTrace]
  refine ⟨179176913745529285591409627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119451275830352857060939751 179176913745529285591409627)
  ·
    refine ⟨268765370618293928387114441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179176913745529285591409627 268765370618293928387114441)
    ·
      refine ⟨201574027963720446290335831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268765370618293928387114441 201574027963720446290335831)
      ·
        refine ⟨302361041945580669435503747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201574027963720446290335831 302361041945580669435503747)
        ·
          refine ⟨453541562918371004153255621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302361041945580669435503747 453541562918371004153255621)
          ·
            refine ⟨85039043047194563278735429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 453541562918371004153255621 85039043047194563278735429)
            ·
              refine ⟨15944820571348980614762893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85039043047194563278735429 15944820571348980614762893)
              ·
                refine ⟨5979307714255867730536085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15944820571348980614762893 5979307714255867730536085)
                ·
                  refine ⟨280280049105743799868879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5979307714255867730536085 280280049105743799868879)
                  ·
                    rfl

theorem cell23_4912591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 3, 6].length) (baseStart_4912591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4912591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4912591 prefixEnd_4912591 := by exact prefixLift 4912591
  have htrace : WordTrace (prefixWord ++ tailWord_4912591) baseStart_4912591 baseEnd_4912591 := by
    simpa [prefixWord, tailWord_4912591, baseEnd_4912591] using wordTrace_append hprefix tailTrace_4912591
  have hstable : (prefixWord ++ tailWord_4912591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4912591).length < 2 ^ (prefixWord ++ tailWord_4912591).sum := by decide
  have hdescent : baseEnd_4912591 < baseStart_4912591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4912591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4912605 : List Nat := [1, 4, 3, 1, 1, 2, 3, 1, 2, 2, 3]
def baseStart_4912605 : Nat := 118140960795 + 4912605 * 2 ^ 59
def prefixEnd_4912605 : Nat := 4983230072969 + 3 ^ 40 * 4912605 * 2
def baseEnd_4912605 : Nat := 2522527630680857144044847

theorem tailTrace_4912605 : CollatzResearch.WordTrace tailWord_4912605 prefixEnd_4912605 2522527630680857144044847 := by
  unfold tailWord_4912605
  simp only [CollatzResearch.WordTrace]
  refine ⟨179177424367478565982419269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119451616244985710654946179 179177424367478565982419269)
  ·
    refine ⟨33595767068902231121703613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 179177424367478565982419269 33595767068902231121703613)
    ·
      refine ⟨12598412650838336670638855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33595767068902231121703613 12598412650838336670638855)
      ·
        refine ⟨18897618976257505005958283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12598412650838336670638855 18897618976257505005958283)
        ·
          refine ⟨28346428464386257508937425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18897618976257505005958283 28346428464386257508937425)
          ·
            refine ⟨21259821348289693131703069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28346428464386257508937425 21259821348289693131703069)
            ·
              refine ⟨7972433005608634924388651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21259821348289693131703069 7972433005608634924388651)
              ·
                refine ⟨11958649508412952386582977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7972433005608634924388651 11958649508412952386582977)
                ·
                  refine ⟨8968987131309714289937233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11958649508412952386582977 8968987131309714289937233)
                  ·
                    refine ⟨6726740348482285717452925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8968987131309714289937233 6726740348482285717452925)
                    ·
                      refine ⟨2522527630680857144044847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6726740348482285717452925 2522527630680857144044847)
                      ·
                        rfl

theorem cell23_4912605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_4912605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4912605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4912605 prefixEnd_4912605 := by exact prefixLift 4912605
  have htrace : WordTrace (prefixWord ++ tailWord_4912605) baseStart_4912605 baseEnd_4912605 := by
    simpa [prefixWord, tailWord_4912605, baseEnd_4912605] using wordTrace_append hprefix tailTrace_4912605
  have hstable : (prefixWord ++ tailWord_4912605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4912605).length < 2 ^ (prefixWord ++ tailWord_4912605).sum := by decide
  have hdescent : baseEnd_4912605 < baseStart_4912605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4912605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4912642 : List Nat := [3, 4, 1, 2, 1, 2, 3, 1, 6]
def baseStart_4912642 : Nat := 118140960795 + 4912642 * 2 ^ 59
def prefixEnd_4912642 : Nat := 4983230072969 + 3 ^ 40 * 4912642 * 2
def baseEnd_4912642 : Nat := 280282958829452611031353

theorem tailTrace_4912642 : CollatzResearch.WordTrace tailWord_4912642 prefixEnd_4912642 280282958829452611031353 := by
  unfold tailWord_4912642
  simp only [CollatzResearch.WordTrace]
  refine ⟨44794693467086130325379045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119452515912229680867677453 44794693467086130325379045)
  ·
    refine ⟨8399005025078649436008571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44794693467086130325379045 8399005025078649436008571)
    ·
      refine ⟨12598507537617974154012857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8399005025078649436008571 12598507537617974154012857)
      ·
        refine ⟨9448880653213480615509643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12598507537617974154012857 9448880653213480615509643)
        ·
          refine ⟨14173320979820220923264465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9448880653213480615509643 14173320979820220923264465)
          ·
            refine ⟨10629990734865165692448349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14173320979820220923264465 10629990734865165692448349)
            ·
              refine ⟨3986246525574437134668131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10629990734865165692448349 3986246525574437134668131)
              ·
                refine ⟨5979369788361655702002197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3986246525574437134668131 5979369788361655702002197)
                ·
                  refine ⟨280282958829452611031353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5979369788361655702002197 280282958829452611031353)
                  ·
                    rfl

theorem cell23_4912642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_4912642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4912642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4912642 prefixEnd_4912642 := by exact prefixLift 4912642
  have htrace : WordTrace (prefixWord ++ tailWord_4912642) baseStart_4912642 baseEnd_4912642 := by
    simpa [prefixWord, tailWord_4912642, baseEnd_4912642] using wordTrace_append hprefix tailTrace_4912642
  have hstable : (prefixWord ++ tailWord_4912642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4912642).length < 2 ^ (prefixWord ++ tailWord_4912642).sum := by decide
  have hdescent : baseEnd_4912642 < baseStart_4912642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4912642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4912668 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 6, 4]
def baseStart_4912668 : Nat := 118140960795 + 4912668 * 2 ^ 59
def prefixEnd_4912668 : Nat := 4983230072969 + 3 ^ 40 * 4912668 * 2
def baseEnd_4912668 : Nat := 840853326654030132519019

theorem tailTrace_4912668 : CollatzResearch.WordTrace tailWord_4912668 prefixEnd_4912668 840853326654030132519019 := by
  unfold tailWord_4912668
  simp only [CollatzResearch.WordTrace]
  refine ⟨89589861083125163870981329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119453148110833551827975105 89589861083125163870981329)
  ·
    refine ⟨67192395812343872903235997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89589861083125163870981329 67192395812343872903235997)
    ·
      refine ⟨25197148429628952338713499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67192395812343872903235997 25197148429628952338713499)
      ·
        refine ⟨37795722644443428508070249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25197148429628952338713499 37795722644443428508070249)
        ·
          refine ⟨28346791983332571381052687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37795722644443428508070249 28346791983332571381052687)
          ·
            refine ⟨42520187974998857071579031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28346791983332571381052687 42520187974998857071579031)
            ·
              refine ⟨63780281962498285607368547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42520187974998857071579031 63780281962498285607368547)
              ·
                refine ⟨95670422943747428411052821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63780281962498285607368547 95670422943747428411052821)
                ·
                  refine ⟨4484551075488160706768101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 95670422943747428411052821 4484551075488160706768101)
                  ·
                    refine ⟨840853326654030132519019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4484551075488160706768101 840853326654030132519019)
                    ·
                      rfl

theorem cell23_4912668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_4912668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4912668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4912668 prefixEnd_4912668 := by exact prefixLift 4912668
  have htrace : WordTrace (prefixWord ++ tailWord_4912668) baseStart_4912668 baseEnd_4912668 := by
    simpa [prefixWord, tailWord_4912668, baseEnd_4912668] using wordTrace_append hprefix tailTrace_4912668
  have hstable : (prefixWord ++ tailWord_4912668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4912668).length < 2 ^ (prefixWord ++ tailWord_4912668).sum := by decide
  have hdescent : baseEnd_4912668 < baseStart_4912668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4912668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4912686 : List Nat := [4, 1, 3, 1, 2, 2, 3, 2, 1, 1, 3]
def baseStart_4912686 : Nat := 118140960795 + 4912686 * 2 ^ 59
def prefixEnd_4912686 : Nat := 4983230072969 + 3 ^ 40 * 4912686 * 2
def baseEnd_4912686 : Nat := 2522569222613871327131975

theorem tailTrace_4912686 : CollatzResearch.WordTrace tailWord_4912686 prefixEnd_4912686 2522569222613871327131975 := by
  unfold tailWord_4912686
  simp only [CollatzResearch.WordTrace]
  refine ⟨22397547335023139602014739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119453585786790077877411941 22397547335023139602014739)
  ·
    refine ⟨33596321002534709403022109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22397547335023139602014739 33596321002534709403022109)
    ·
      refine ⟨12598620375950516026133291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33596321002534709403022109 12598620375950516026133291)
      ·
        refine ⟨18897930563925774039199937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12598620375950516026133291 18897930563925774039199937)
        ·
          refine ⟨14173447922944330529399953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18897930563925774039199937 14173447922944330529399953)
          ·
            refine ⟨10630085942208247897049965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14173447922944330529399953 10630085942208247897049965)
            ·
              refine ⟨3986282228328092961393737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10630085942208247897049965 3986282228328092961393737)
              ·
                refine ⟨2989711671246069721045303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3986282228328092961393737 2989711671246069721045303)
                ·
                  refine ⟨4484567506869104581567955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2989711671246069721045303 4484567506869104581567955)
                  ·
                    refine ⟨6726851260303656872351933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4484567506869104581567955 6726851260303656872351933)
                    ·
                      refine ⟨2522569222613871327131975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6726851260303656872351933 2522569222613871327131975)
                      ·
                        rfl

theorem cell23_4912686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_4912686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4912686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4912686 prefixEnd_4912686 := by exact prefixLift 4912686
  have htrace : WordTrace (prefixWord ++ tailWord_4912686) baseStart_4912686 baseEnd_4912686 := by
    simpa [prefixWord, tailWord_4912686, baseEnd_4912686] using wordTrace_append hprefix tailTrace_4912686
  have hstable : (prefixWord ++ tailWord_4912686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4912686).length < 2 ^ (prefixWord ++ tailWord_4912686).sum := by decide
  have hdescent : baseEnd_4912686 < baseStart_4912686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4912686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4912768 : List Nat := [2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 3]
def baseStart_4912768 : Nat := 118140960795 + 4912768 * 2 ^ 59
def prefixEnd_4912768 : Nat := 4983230072969 + 3 ^ 40 * 4912768 * 2
def baseEnd_4912768 : Nat := 2522611328027540006306597

theorem tailTrace_4912768 : CollatzResearch.WordTrace tailWord_4912768 prefixEnd_4912768 2522611328027540006306597 := by
  unfold tailWord_4912768
  simp only [CollatzResearch.WordTrace]
  refine ⟨89591684732944022410301479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119455579643925363213735305 89591684732944022410301479)
  ·
    refine ⟨134387527099416033615452219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89591684732944022410301479 134387527099416033615452219)
    ·
      refine ⟨201581290649124050423178329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134387527099416033615452219 201581290649124050423178329)
      ·
        refine ⟨151185967986843037817383747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201581290649124050423178329 151185967986843037817383747)
        ·
          refine ⟨226778951980264556726075621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151185967986843037817383747 226778951980264556726075621)
          ·
            refine ⟨42521053496299604386139179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 226778951980264556726075621 42521053496299604386139179)
            ·
              refine ⟨63781580244449406579208769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42521053496299604386139179 63781580244449406579208769)
              ·
                refine ⟨47836185183337054934406577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63781580244449406579208769 47836185183337054934406577)
                ·
                  refine ⟨35877138887502791200804933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47836185183337054934406577 35877138887502791200804933)
                  ·
                    refine ⟨6726963541406773350150925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35877138887502791200804933 6726963541406773350150925)
                    ·
                      refine ⟨2522611328027540006306597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6726963541406773350150925 2522611328027540006306597)
                      ·
                        rfl

theorem cell23_4912768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 3].length) (baseStart_4912768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4912768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4912768 prefixEnd_4912768 := by exact prefixLift 4912768
  have htrace : WordTrace (prefixWord ++ tailWord_4912768) baseStart_4912768 baseEnd_4912768 := by
    simpa [prefixWord, tailWord_4912768, baseEnd_4912768] using wordTrace_append hprefix tailTrace_4912768
  have hstable : (prefixWord ++ tailWord_4912768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4912768).length < 2 ^ (prefixWord ++ tailWord_4912768).sum := by decide
  have hdescent : baseEnd_4912768 < baseStart_4912768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4912768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4912782 : List Nat := [4, 1, 1, 3, 1, 2, 2, 2, 1, 4, 2]
def baseStart_4912782 : Nat := 118140960795 + 4912782 * 2 ^ 59
def prefixEnd_4912782 : Nat := 4983230072969 + 3 ^ 40 * 4912782 * 2
def baseEnd_4912782 : Nat := 2522618516756702951531533

theorem tailTrace_4912782 : CollatzResearch.WordTrace tailWord_4912782 prefixEnd_4912782 2522618516756702951531533 := by
  unfold tailWord_4912782
  simp only [CollatzResearch.WordTrace]
  refine ⟨22397985010979665651451575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119455920058558216807741733 22397985010979665651451575)
  ·
    refine ⟨33596977516469498477177363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22397985010979665651451575 33596977516469498477177363)
    ·
      refine ⟨50395466274704247715766045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33596977516469498477177363 50395466274704247715766045)
      ·
        refine ⟨18898299853014092893412267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50395466274704247715766045 18898299853014092893412267)
        ·
          refine ⟨28347449779521139340118401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18898299853014092893412267 28347449779521139340118401)
          ·
            refine ⟨21260587334640854505088801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28347449779521139340118401 21260587334640854505088801)
            ·
              refine ⟨15945440500980640878816601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21260587334640854505088801 15945440500980640878816601)
              ·
                refine ⟨11959080375735480659112451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15945440500980640878816601 11959080375735480659112451)
                ·
                  refine ⟨17938620563603220988668677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11959080375735480659112451 17938620563603220988668677)
                  ·
                    refine ⟨3363491355675603935375377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17938620563603220988668677 3363491355675603935375377)
                    ·
                      refine ⟨2522618516756702951531533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3363491355675603935375377 2522618516756702951531533)
                      ·
                        rfl

theorem cell23_4912782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_4912782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4912782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4912782 prefixEnd_4912782 := by exact prefixLift 4912782
  have htrace : WordTrace (prefixWord ++ tailWord_4912782) baseStart_4912782 baseEnd_4912782 := by
    simpa [prefixWord, tailWord_4912782, baseEnd_4912782] using wordTrace_append hprefix tailTrace_4912782
  have hstable : (prefixWord ++ tailWord_4912782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4912782).length < 2 ^ (prefixWord ++ tailWord_4912782).sum := by decide
  have hdescent : baseEnd_4912782 < baseStart_4912782 := by decide
  rcases family_descends (prefixWord ++ tailWord_4912782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4912805 : List Nat := [1, 3, 1, 2, 1, 2, 4, 4, 5]
def baseStart_4912805 : Nat := 118140960795 + 4912805 * 2 ^ 59
def prefixEnd_4912805 : Nat := 4983230072969 + 3 ^ 40 * 4912805 * 2
def baseEnd_4912805 : Nat := 280292258534639595727103

theorem tailTrace_4912805 : CollatzResearch.WordTrace tailWord_4912805 prefixEnd_4912805 280292258534639595727103 := by
  unfold tailWord_4912805
  simp only [CollatzResearch.WordTrace]
  refine ⟨179184718966754000139699869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119456479311169333426466579 179184718966754000139699869)
  ·
    refine ⟨67194269612532750052387451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179184718966754000139699869 67194269612532750052387451)
    ·
      refine ⟨100791404418799125078581177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67194269612532750052387451 100791404418799125078581177)
      ·
        refine ⟨75593553314099343808935883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100791404418799125078581177 75593553314099343808935883)
        ·
          refine ⟨113390329971149015713403825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75593553314099343808935883 113390329971149015713403825)
          ·
            refine ⟨85042747478361761785052869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113390329971149015713403825 85042747478361761785052869)
            ·
              refine ⟨15945515152192830334697413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85042747478361761785052869 15945515152192830334697413)
              ·
                refine ⟨2989784091036155687755765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15945515152192830334697413 2989784091036155687755765)
                ·
                  refine ⟨280292258534639595727103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2989784091036155687755765 280292258534639595727103)
                  ·
                    rfl

theorem cell23_4912805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 4, 5].length) (baseStart_4912805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4912805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4912805 prefixEnd_4912805 := by exact prefixLift 4912805
  have htrace : WordTrace (prefixWord ++ tailWord_4912805) baseStart_4912805 baseEnd_4912805 := by
    simpa [prefixWord, tailWord_4912805, baseEnd_4912805] using wordTrace_append hprefix tailTrace_4912805
  have hstable : (prefixWord ++ tailWord_4912805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4912805).length < 2 ^ (prefixWord ++ tailWord_4912805).sum := by decide
  have hdescent : baseEnd_4912805 < baseStart_4912805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4912805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4912818 : List Nat := [3, 2, 1, 1, 1, 2, 3, 2, 1, 7]
def baseStart_4912818 : Nat := 118140960795 + 4912818 * 2 ^ 59
def prefixEnd_4912818 : Nat := 4983230072969 + 3 ^ 40 * 4912818 * 2
def baseEnd_4912818 : Nat := 840879000686754936893789

theorem tailTrace_4912818 : CollatzResearch.WordTrace tailWord_4912818 prefixEnd_4912818 840879000686754936893789 := by
  unfold tailWord_4912818
  simp only [CollatzResearch.WordTrace]
  refine ⟨44796298278926725839980777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119456795410471268906615405 44796298278926725839980777)
  ·
    refine ⟨33597223709195044379985583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44796298278926725839980777 33597223709195044379985583)
    ·
      refine ⟨50395835563792566569978375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33597223709195044379985583 50395835563792566569978375)
      ·
        refine ⟨75593753345688849854967563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50395835563792566569978375 75593753345688849854967563)
        ·
          refine ⟨113390630018533274782451345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75593753345688849854967563 113390630018533274782451345)
          ·
            refine ⟨85042972513899956086838509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113390630018533274782451345 85042972513899956086838509)
            ·
              refine ⟨31891114692712483532564441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85042972513899956086838509 31891114692712483532564441)
              ·
                refine ⟨23918336019534362649423331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31891114692712483532564441 23918336019534362649423331)
                ·
                  refine ⟨35877504029301543974134997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23918336019534362649423331 35877504029301543974134997)
                  ·
                    refine ⟨840879000686754936893789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35877504029301543974134997 840879000686754936893789)
                    ·
                      rfl

theorem cell23_4912818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_4912818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4912818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4912818 prefixEnd_4912818 := by exact prefixLift 4912818
  have htrace : WordTrace (prefixWord ++ tailWord_4912818) baseStart_4912818 baseEnd_4912818 := by
    simpa [prefixWord, tailWord_4912818, baseEnd_4912818] using wordTrace_append hprefix tailTrace_4912818
  have hstable : (prefixWord ++ tailWord_4912818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4912818).length < 2 ^ (prefixWord ++ tailWord_4912818).sum := by decide
  have hdescent : baseEnd_4912818 < baseStart_4912818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4912818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4912822 : List Nat := [5, 1, 3, 1, 1, 1, 2, 2, 7]
def baseStart_4912822 : Nat := 118140960795 + 4912822 * 2 ^ 59
def prefixEnd_4912822 : Nat := 4983230072969 + 3 ^ 40 * 4912822 * 2
def baseEnd_4912822 : Nat := 280293228442542532781261

theorem tailTrace_4912822 : CollatzResearch.WordTrace tailWord_4912822 prefixEnd_4912822 280293228442542532781261 := by
  unfold tailWord_4912822
  simp only [CollatzResearch.WordTrace]
  refine ⟨11199083687980775752691795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 119456892671794941362045813 11199083687980775752691795)
  ·
    refine ⟨16798625531971163629037693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11199083687980775752691795 16798625531971163629037693)
    ·
      refine ⟨6299484574489186360889135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16798625531971163629037693 6299484574489186360889135)
      ·
        refine ⟨9449226861733779541333703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6299484574489186360889135 9449226861733779541333703)
        ·
          refine ⟨14173840292600669312000555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9449226861733779541333703 14173840292600669312000555)
          ·
            refine ⟨21260760438901003968000833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14173840292600669312000555 21260760438901003968000833)
            ·
              refine ⟨15945570329175752976000625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21260760438901003968000833 15945570329175752976000625)
              ·
                refine ⟨11959177746881814732000469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15945570329175752976000625 11959177746881814732000469)
                ·
                  refine ⟨280293228442542532781261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11959177746881814732000469 280293228442542532781261)
                  ·
                    rfl

theorem cell23_4912822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_4912822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4912822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4912822 prefixEnd_4912822 := by exact prefixLift 4912822
  have htrace : WordTrace (prefixWord ++ tailWord_4912822) baseStart_4912822 baseEnd_4912822 := by
    simpa [prefixWord, tailWord_4912822, baseEnd_4912822] using wordTrace_append hprefix tailTrace_4912822
  have hstable : (prefixWord ++ tailWord_4912822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4912822).length < 2 ^ (prefixWord ++ tailWord_4912822).sum := by decide
  have hdescent : baseEnd_4912822 < baseStart_4912822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4912822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4912825 : List Nat := [1, 2, 1, 4, 1, 1, 2, 2, 2, 5, 2]
def baseStart_4912825 : Nat := 118140960795 + 4912825 * 2 ^ 59
def prefixEnd_4912825 : Nat := 4983230072969 + 3 ^ 40 * 4912825 * 2
def baseEnd_4912825 : Nat := 2522640596424846283293835

theorem tailTrace_4912825 : CollatzResearch.WordTrace tailWord_4912825 prefixEnd_4912825 2522640596424846283293835 := by
  unfold tailWord_4912825
  simp only [CollatzResearch.WordTrace]
  refine ⟨179185448426681543555427929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119456965617787695703618619 179185448426681543555427929)
  ·
    refine ⟨134389086320011157666570947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179185448426681543555427929 134389086320011157666570947)
    ·
      refine ⟨201583629480016736499856421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134389086320011157666570947 201583629480016736499856421)
      ·
        refine ⟨37796930527503138093723079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 201583629480016736499856421 37796930527503138093723079)
        ·
          refine ⟨56695395791254707140584619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37796930527503138093723079 56695395791254707140584619)
          ·
            refine ⟨85043093686882060710876929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56695395791254707140584619 85043093686882060710876929)
            ·
              refine ⟨63782320265161545533157697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85043093686882060710876929 63782320265161545533157697)
              ·
                refine ⟨47836740198871159149868273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63782320265161545533157697 47836740198871159149868273)
                ·
                  refine ⟨35877555149153369362401205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47836740198871159149868273 35877555149153369362401205)
                  ·
                    refine ⟨3363520795233128377725113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35877555149153369362401205 3363520795233128377725113)
                    ·
                      refine ⟨2522640596424846283293835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3363520795233128377725113 2522640596424846283293835)
                      ·
                        rfl

theorem cell23_4912825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 5, 2].length) (baseStart_4912825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4912825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4912825 prefixEnd_4912825 := by exact prefixLift 4912825
  have htrace : WordTrace (prefixWord ++ tailWord_4912825) baseStart_4912825 baseEnd_4912825 := by
    simpa [prefixWord, tailWord_4912825, baseEnd_4912825] using wordTrace_append hprefix tailTrace_4912825
  have hstable : (prefixWord ++ tailWord_4912825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4912825).length < 2 ^ (prefixWord ++ tailWord_4912825).sum := by decide
  have hdescent : baseEnd_4912825 < baseStart_4912825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4912825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4912852 : List Nat := [2, 4, 1, 3, 1, 2, 1, 2, 2, 5]
def baseStart_4912852 : Nat := 118140960795 + 4912852 * 2 ^ 59
def prefixEnd_4912852 : Nat := 4983230072969 + 3 ^ 40 * 4912852 * 2
def baseEnd_4912852 : Nat := 840884820134172559218737

theorem tailTrace_4912852 : CollatzResearch.WordTrace tailWord_4912852 prefixEnd_4912852 840884820134172559218737 := by
  unfold tailWord_4912852
  simp only [CollatzResearch.WordTrace]
  refine ⟨89593216598791863583330405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119457622131722484777773873 89593216598791863583330405)
  ·
    refine ⟨16798728112273474421874451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89593216598791863583330405 16798728112273474421874451)
    ·
      refine ⟨25198092168410211632811677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16798728112273474421874451 25198092168410211632811677)
      ·
        refine ⟨9449284563153829362304379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25198092168410211632811677 9449284563153829362304379)
        ·
          refine ⟨14173926844730744043456569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9449284563153829362304379 14173926844730744043456569)
          ·
            refine ⟨10630445133548058032592427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14173926844730744043456569 10630445133548058032592427)
            ·
              refine ⟨15945667700322087048888641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10630445133548058032592427 15945667700322087048888641)
              ·
                refine ⟨11959250775241565286666481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15945667700322087048888641 11959250775241565286666481)
                ·
                  refine ⟨8969438081431173964999861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11959250775241565286666481 8969438081431173964999861)
                  ·
                    refine ⟨840884820134172559218737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8969438081431173964999861 840884820134172559218737)
                    ·
                      rfl

theorem cell23_4912852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_4912852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4912852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4912852 prefixEnd_4912852 := by exact prefixLift 4912852
  have htrace : WordTrace (prefixWord ++ tailWord_4912852) baseStart_4912852 baseEnd_4912852 := by
    simpa [prefixWord, tailWord_4912852, baseEnd_4912852] using wordTrace_append hprefix tailTrace_4912852
  have hstable : (prefixWord ++ tailWord_4912852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4912852).length < 2 ^ (prefixWord ++ tailWord_4912852).sum := by decide
  have hdescent : baseEnd_4912852 < baseStart_4912852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4912852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4912855 : List Nat := [1, 1, 3, 2, 1, 3, 3, 2, 2, 1, 4]
def baseStart_4912855 : Nat := 118140960795 + 4912855 * 2 ^ 59
def prefixEnd_4912855 : Nat := 4983230072969 + 3 ^ 40 * 4912855 * 2
def baseEnd_4912855 : Nat := 2522656000844481165918697

theorem tailTrace_4912855 : CollatzResearch.WordTrace tailWord_4912855 prefixEnd_4912855 2522656000844481165918697 := by
  unfold tailWord_4912855
  simp only [CollatzResearch.WordTrace]
  refine ⟨179186542616572858679020019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119457695077715239119346679 179186542616572858679020019)
  ·
    refine ⟨268779813924859288018530029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179186542616572858679020019 268779813924859288018530029)
    ·
      refine ⟨100792430221822233006948761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 268779813924859288018530029 100792430221822233006948761)
      ·
        refine ⟨75594322666366674755211571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100792430221822233006948761 75594322666366674755211571)
        ·
          refine ⟨113391483999550012132817357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75594322666366674755211571 113391483999550012132817357)
          ·
            refine ⟨42521806499831254549806509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113391483999550012132817357 42521806499831254549806509)
            ·
              refine ⟨15945677437436720456177441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42521806499831254549806509 15945677437436720456177441)
              ·
                refine ⟨11959258078077540342133081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15945677437436720456177441 11959258078077540342133081)
                ·
                  refine ⟨8969443558558155256599811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11959258078077540342133081 8969443558558155256599811)
                  ·
                    refine ⟨13454165337837232884899717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8969443558558155256599811 13454165337837232884899717)
                    ·
                      refine ⟨2522656000844481165918697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13454165337837232884899717 2522656000844481165918697)
                      ·
                        rfl

theorem cell23_4912855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_4912855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4912855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4912855 prefixEnd_4912855 := by exact prefixLift 4912855
  have htrace : WordTrace (prefixWord ++ tailWord_4912855) baseStart_4912855 baseEnd_4912855 := by
    simpa [prefixWord, tailWord_4912855, baseEnd_4912855] using wordTrace_append hprefix tailTrace_4912855
  have hstable : (prefixWord ++ tailWord_4912855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4912855).length < 2 ^ (prefixWord ++ tailWord_4912855).sum := by decide
  have hdescent : baseEnd_4912855 < baseStart_4912855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4912855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4912892 : List Nat := [2, 2, 2, 1, 3, 1, 4, 1, 2, 2, 3]
def baseStart_4912892 : Nat := 118140960795 + 4912892 * 2 ^ 59
def prefixEnd_4912892 : Nat := 4983230072969 + 3 ^ 40 * 4912892 * 2
def baseEnd_4912892 : Nat := 2522674999628697521156027

theorem tailTrace_4912892 : CollatzResearch.WordTrace tailWord_4912892 prefixEnd_4912892 2522674999628697521156027 := by
  unfold tailWord_4912892
  simp only [CollatzResearch.WordTrace]
  refine ⟨89593946058719406999058465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119458594744959209332077953 89593946058719406999058465)
  ·
    refine ⟨67195459544039555249293849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89593946058719406999058465 67195459544039555249293849)
    ·
      refine ⟨50396594658029666436970387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67195459544039555249293849 50396594658029666436970387)
      ·
        refine ⟨75594891987044499655455581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50396594658029666436970387 75594891987044499655455581)
        ·
          refine ⟨28348084495141687370795843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75594891987044499655455581 28348084495141687370795843)
          ·
            refine ⟨42522126742712531056193765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28348084495141687370795843 42522126742712531056193765)
            ·
              refine ⟨7972898764258599573036331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42522126742712531056193765 7972898764258599573036331)
              ·
                refine ⟨11959348146387899359554497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7972898764258599573036331 11959348146387899359554497)
                ·
                  refine ⟨8969511109790924519665873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11959348146387899359554497 8969511109790924519665873)
                  ·
                    refine ⟨6727133332343193389749405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8969511109790924519665873 6727133332343193389749405)
                    ·
                      refine ⟨2522674999628697521156027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6727133332343193389749405 2522674999628697521156027)
                      ·
                        rfl

theorem cell23_4912892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 2, 2, 3].length) (baseStart_4912892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4912892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4912892 prefixEnd_4912892 := by exact prefixLift 4912892
  have htrace : WordTrace (prefixWord ++ tailWord_4912892) baseStart_4912892 baseEnd_4912892 := by
    simpa [prefixWord, tailWord_4912892, baseEnd_4912892] using wordTrace_append hprefix tailTrace_4912892
  have hstable : (prefixWord ++ tailWord_4912892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4912892).length < 2 ^ (prefixWord ++ tailWord_4912892).sum := by decide
  have hdescent : baseEnd_4912892 < baseStart_4912892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4912892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4912949 : List Nat := [1, 3, 3, 1, 4, 1, 1, 1, 1, 5, 2]
def baseStart_4912949 : Nat := 118140960795 + 4912949 * 2 ^ 59
def prefixEnd_4912949 : Nat := 4983230072969 + 3 ^ 40 * 4912949 * 2
def baseEnd_4912949 : Nat := 2522704268026003798143265

theorem tailTrace_4912949 : CollatzResearch.WordTrace tailWord_4912949 prefixEnd_4912949 2522704268026003798143265 := by
  unfold tailWord_4912949
  simp only [CollatzResearch.WordTrace]
  refine ⟨179189971078232312732941901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119459980718821541821961267 179189971078232312732941901)
  ·
    refine ⟨67196239154337117274853213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179189971078232312732941901 67196239154337117274853213)
    ·
      refine ⟨25198589682876418978069955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67196239154337117274853213 25198589682876418978069955)
      ·
        refine ⟨37797884524314628467104933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25198589682876418978069955 37797884524314628467104933)
        ·
          refine ⟨7087103348308992837582175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37797884524314628467104933 7087103348308992837582175)
          ·
            refine ⟨10630655022463489256373263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7087103348308992837582175 10630655022463489256373263)
            ·
              refine ⟨15945982533695233884559895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10630655022463489256373263 15945982533695233884559895)
              ·
                refine ⟨23918973800542850826839843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15945982533695233884559895 23918973800542850826839843)
                ·
                  refine ⟨35878460700814276240259765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23918973800542850826839843 35878460700814276240259765)
                  ·
                    refine ⟨3363605690701338397524353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35878460700814276240259765 3363605690701338397524353)
                    ·
                      refine ⟨2522704268026003798143265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3363605690701338397524353 2522704268026003798143265)
                      ·
                        rfl

theorem cell23_4912949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 5, 2].length) (baseStart_4912949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4912949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4912949 prefixEnd_4912949 := by exact prefixLift 4912949
  have htrace : WordTrace (prefixWord ++ tailWord_4912949) baseStart_4912949 baseEnd_4912949 := by
    simpa [prefixWord, tailWord_4912949, baseEnd_4912949] using wordTrace_append hprefix tailTrace_4912949
  have hstable : (prefixWord ++ tailWord_4912949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4912949).length < 2 ^ (prefixWord ++ tailWord_4912949).sum := by decide
  have hdescent : baseEnd_4912949 < baseStart_4912949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4912949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4912965 : List Nat := [1, 3, 1, 1, 1, 2, 4, 3, 1, 1, 5]
def baseStart_4912965 : Nat := 118140960795 + 4912965 * 2 ^ 59
def prefixEnd_4912965 : Nat := 4983230072969 + 3 ^ 40 * 4912965 * 2
def baseEnd_4912965 : Nat := 2522712483716475735543191

theorem tailTrace_4912965 : CollatzResearch.WordTrace tailWord_4912965 prefixEnd_4912965 2522712483716475735543191 := by
  unfold tailWord_4912965
  simp only [CollatzResearch.WordTrace]
  refine ⟨179190554646174347465524349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119460369764116231643682899 179190554646174347465524349)
  ·
    refine ⟨67196457992315380299571631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179190554646174347465524349 67196457992315380299571631)
    ·
      refine ⟨100794686988473070449357447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67196457992315380299571631 100794686988473070449357447)
      ·
        refine ⟨151192030482709605674036171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100794686988473070449357447 151192030482709605674036171)
        ·
          refine ⟨226788045724064408511054257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151192030482709605674036171 226788045724064408511054257)
          ·
            refine ⟨170091034293048306383290693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226788045724064408511054257 170091034293048306383290693)
            ·
              refine ⟨31892068929946557446867005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 170091034293048306383290693 31892068929946557446867005)
              ·
                refine ⟨11959525848729959042575127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31892068929946557446867005 11959525848729959042575127)
                ·
                  refine ⟨17939288773094938563862691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11959525848729959042575127 17939288773094938563862691)
                  ·
                    refine ⟨26908933159642407845794037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17939288773094938563862691 26908933159642407845794037)
                    ·
                      refine ⟨2522712483716475735543191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26908933159642407845794037 2522712483716475735543191)
                      ·
                        rfl

theorem cell23_4912965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 1, 5].length) (baseStart_4912965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4912965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4912965 prefixEnd_4912965 := by exact prefixLift 4912965
  have htrace : WordTrace (prefixWord ++ tailWord_4912965) baseStart_4912965 baseEnd_4912965 := by
    simpa [prefixWord, tailWord_4912965, baseEnd_4912965] using wordTrace_append hprefix tailTrace_4912965
  have hstable : (prefixWord ++ tailWord_4912965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4912965).length < 2 ^ (prefixWord ++ tailWord_4912965).sum := by decide
  have hdescent : baseEnd_4912965 < baseStart_4912965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4912965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4912973 : List Nat := [1, 6, 1, 2, 1, 1, 2, 4, 1, 1, 3]
def baseStart_4912973 : Nat := 118140960795 + 4912973 * 2 ^ 59
def prefixEnd_4912973 : Nat := 4983230072969 + 3 ^ 40 * 4912973 * 2
def baseEnd_4912973 : Nat := 2522716591561711704243155

theorem tailTrace_4912973 : CollatzResearch.WordTrace tailWord_4912973 prefixEnd_4912973 2522716591561711704243155 := by
  unfold tailWord_4912973
  simp only [CollatzResearch.WordTrace]
  refine ⟨179190846430145364831815573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119460564286763576554543715 179190846430145364831815573)
  ·
    refine ⟨8399570926413063976491355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 179190846430145364831815573 8399570926413063976491355)
    ·
      refine ⟨12599356389619595964737033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8399570926413063976491355 12599356389619595964737033)
      ·
        refine ⟨9449517292214696973552775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12599356389619595964737033 9449517292214696973552775)
        ·
          refine ⟨14174275938322045460329163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9449517292214696973552775 14174275938322045460329163)
          ·
            refine ⟨21261413907483068190493745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14174275938322045460329163 21261413907483068190493745)
            ·
              refine ⟨15946060430612301142870309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21261413907483068190493745 15946060430612301142870309)
              ·
                refine ⟨2989886330739806464288183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15946060430612301142870309 2989886330739806464288183)
                ·
                  refine ⟨4484829496109709696432275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2989886330739806464288183 4484829496109709696432275)
                  ·
                    refine ⟨6727244244164564544648413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4484829496109709696432275 6727244244164564544648413)
                    ·
                      refine ⟨2522716591561711704243155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6727244244164564544648413 2522716591561711704243155)
                      ·
                        rfl

theorem cell23_4912973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_4912973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4912973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4912973 prefixEnd_4912973 := by exact prefixLift 4912973
  have htrace : WordTrace (prefixWord ++ tailWord_4912973) baseStart_4912973 baseEnd_4912973 := by
    simpa [prefixWord, tailWord_4912973, baseEnd_4912973] using wordTrace_append hprefix tailTrace_4912973
  have hstable : (prefixWord ++ tailWord_4912973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4912973).length < 2 ^ (prefixWord ++ tailWord_4912973).sum := by decide
  have hdescent : baseEnd_4912973 < baseStart_4912973 := by decide
  rcases family_descends (prefixWord ++ tailWord_4912973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4912992 : List Nat := [2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 4]
def baseStart_4912992 : Nat := 118140960795 + 4912992 * 2 ^ 59
def prefixEnd_4912992 : Nat := 4983230072969 + 3 ^ 40 * 4912992 * 2
def baseEnd_4912992 : Nat := 2522726347694147129905567

theorem tailTrace_4912992 : CollatzResearch.WordTrace tailWord_4912992 prefixEnd_4912992 2522726347694147129905567 := by
  unfold tailWord_4912992
  simp only [CollatzResearch.WordTrace]
  refine ⟨89595769708538265538378615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119461026278051020717838153 89595769708538265538378615)
  ·
    refine ⟨134393654562807398307567923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89595769708538265538378615 134393654562807398307567923)
    ·
      refine ⟨201590481844211097461351885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134393654562807398307567923 201590481844211097461351885)
      ·
        refine ⟨75596430691579161548006957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201590481844211097461351885 75596430691579161548006957)
        ·
          refine ⟨28348661509342185580502609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75596430691579161548006957 28348661509342185580502609)
          ·
            refine ⟨21261496132006639185376957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28348661509342185580502609 21261496132006639185376957)
            ·
              refine ⟨7973061049502489694516359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21261496132006639185376957 7973061049502489694516359)
              ·
                refine ⟨11959591574253734541774539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7973061049502489694516359 11959591574253734541774539)
                ·
                  refine ⟨17939387361380601812661809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11959591574253734541774539 17939387361380601812661809)
                  ·
                    refine ⟨13454540521035451359496357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17939387361380601812661809 13454540521035451359496357)
                    ·
                      refine ⟨2522726347694147129905567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13454540521035451359496357 2522726347694147129905567)
                      ·
                        rfl

theorem cell23_4912992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 4].length) (baseStart_4912992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4912992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4912992 prefixEnd_4912992 := by exact prefixLift 4912992
  have htrace : WordTrace (prefixWord ++ tailWord_4912992) baseStart_4912992 baseEnd_4912992 := by
    simpa [prefixWord, tailWord_4912992, baseEnd_4912992] using wordTrace_append hprefix tailTrace_4912992
  have hstable : (prefixWord ++ tailWord_4912992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4912992).length < 2 ^ (prefixWord ++ tailWord_4912992).sum := by decide
  have hdescent : baseEnd_4912992 < baseStart_4912992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4912992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4912999 : List Nat := [1, 1, 5, 1, 2, 1, 4, 2, 1, 2, 3]
def baseStart_4912999 : Nat := 118140960795 + 4912999 * 2 ^ 59
def prefixEnd_4912999 : Nat := 4983230072969 + 3 ^ 40 * 4912999 * 2
def baseEnd_4912999 : Nat := 2522729942058728602518035

theorem tailTrace_4912999 : CollatzResearch.WordTrace tailWord_4912999 prefixEnd_4912999 2522729942058728602518035 := by
  unfold tailWord_4912999
  simp only [CollatzResearch.WordTrace]
  refine ⟨179191794728051171272262051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119461196485367447514841367 179191794728051171272262051)
  ·
    refine ⟨268787692092076756908393077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179191794728051171272262051 268787692092076756908393077)
    ·
      refine ⟨25198846133632195960161851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 268787692092076756908393077 25198846133632195960161851)
      ·
        refine ⟨37798269200448293940242777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25198846133632195960161851 37798269200448293940242777)
        ·
          refine ⟨28348701900336220455182083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37798269200448293940242777 28348701900336220455182083)
          ·
            refine ⟨42523052850504330682773125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28348701900336220455182083 42523052850504330682773125)
            ·
              refine ⟨7973072409469562003019961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42523052850504330682773125 7973072409469562003019961)
              ·
                refine ⟨5979804307102171502264971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7973072409469562003019961 5979804307102171502264971)
                ·
                  refine ⟨8969706460653257253397457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5979804307102171502264971 8969706460653257253397457)
                  ·
                    refine ⟨6727279845489942940048093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8969706460653257253397457 6727279845489942940048093)
                    ·
                      refine ⟨2522729942058728602518035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6727279845489942940048093 2522729942058728602518035)
                      ·
                        rfl

theorem cell23_4912999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_4912999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4912999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4912999 prefixEnd_4912999 := by exact prefixLift 4912999
  have htrace : WordTrace (prefixWord ++ tailWord_4912999) baseStart_4912999 baseEnd_4912999 := by
    simpa [prefixWord, tailWord_4912999, baseEnd_4912999] using wordTrace_append hprefix tailTrace_4912999
  have hstable : (prefixWord ++ tailWord_4912999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4912999).length < 2 ^ (prefixWord ++ tailWord_4912999).sum := by decide
  have hdescent : baseEnd_4912999 < baseStart_4912999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4912999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4913029 : List Nat := [1, 3, 1, 1, 3, 2, 2, 4, 2, 1, 3]
def baseStart_4913029 : Nat := 118140960795 + 4913029 * 2 ^ 59
def prefixEnd_4913029 : Nat := 4983230072969 + 3 ^ 40 * 4913029 * 2
def baseEnd_4913029 : Nat := 2522745346478363485142897

theorem tailTrace_4913029 : CollatzResearch.WordTrace tailWord_4913029 prefixEnd_4913029 2522745346478363485142897 := by
  unfold tailWord_4913029
  simp only [CollatzResearch.WordTrace]
  refine ⟨179192888917942486395854141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119461925945294990930569427 179192888917942486395854141)
  ·
    refine ⟨67197333344228432398445303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179192888917942486395854141 67197333344228432398445303)
    ·
      refine ⟨100796000016342648597667955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67197333344228432398445303 100796000016342648597667955)
      ·
        refine ⟨151194000024513972896501933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100796000016342648597667955 151194000024513972896501933)
        ·
          refine ⟨56697750009192739836188225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151194000024513972896501933 56697750009192739836188225)
          ·
            refine ⟨42523312506894554877141169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56697750009192739836188225 42523312506894554877141169)
            ·
              refine ⟨31892484380170916157855877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42523312506894554877141169 31892484380170916157855877)
              ·
                refine ⟨5979840821282046779597977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31892484380170916157855877 5979840821282046779597977)
                ·
                  refine ⟨4484880615961535084698483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5979840821282046779597977 4484880615961535084698483)
                  ·
                    refine ⟨6727320923942302627047725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4484880615961535084698483 6727320923942302627047725)
                    ·
                      refine ⟨2522745346478363485142897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6727320923942302627047725 2522745346478363485142897)
                      ·
                        rfl

theorem cell23_4913029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4, 2, 1, 3].length) (baseStart_4913029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4913029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4913029 prefixEnd_4913029 := by exact prefixLift 4913029
  have htrace : WordTrace (prefixWord ++ tailWord_4913029) baseStart_4913029 baseEnd_4913029 := by
    simpa [prefixWord, tailWord_4913029, baseEnd_4913029] using wordTrace_append hprefix tailTrace_4913029
  have hstable : (prefixWord ++ tailWord_4913029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4913029).length < 2 ^ (prefixWord ++ tailWord_4913029).sum := by decide
  have hdescent : baseEnd_4913029 < baseStart_4913029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4913029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4913035 : List Nat := [1, 1, 1, 1, 4, 2, 1, 3, 2, 3, 4]
def baseStart_4913035 : Nat := 118140960795 + 4913035 * 2 ^ 59
def prefixEnd_4913035 : Nat := 4983230072969 + 3 ^ 40 * 4913035 * 2
def baseEnd_4913035 : Nat := 2522748427362290461667869

theorem tailTrace_4913035 : CollatzResearch.WordTrace tailWord_4913035 prefixEnd_4913035 2522748427362290461667869 := by
  unfold tailWord_4913035
  simp only [CollatzResearch.WordTrace]
  refine ⟨179193107755920749420572559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119462071837280499613715039 179193107755920749420572559)
  ·
    refine ⟨268789661633881124130858839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179193107755920749420572559 268789661633881124130858839)
    ·
      refine ⟨403184492450821686196288259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268789661633881124130858839 403184492450821686196288259)
      ·
        refine ⟨604776738676232529294432389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 403184492450821686196288259 604776738676232529294432389)
        ·
          refine ⟨113395638501793599242706073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 604776738676232529294432389 113395638501793599242706073)
          ·
            refine ⟨85046728876345199432029555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113395638501793599242706073 85046728876345199432029555)
            ·
              refine ⟨127570093314517799148044333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85046728876345199432029555 127570093314517799148044333)
              ·
                refine ⟨47838784992944174680516625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127570093314517799148044333 47838784992944174680516625)
                ·
                  refine ⟨35879088744708131010387469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47838784992944174680516625 35879088744708131010387469)
                  ·
                    refine ⟨13454658279265549128895301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35879088744708131010387469 13454658279265549128895301)
                    ·
                      refine ⟨2522748427362290461667869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13454658279265549128895301 2522748427362290461667869)
                      ·
                        rfl

theorem cell23_4913035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 3, 4].length) (baseStart_4913035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4913035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4913035 prefixEnd_4913035 := by exact prefixLift 4913035
  have htrace : WordTrace (prefixWord ++ tailWord_4913035) baseStart_4913035 baseEnd_4913035 := by
    simpa [prefixWord, tailWord_4913035, baseEnd_4913035] using wordTrace_append hprefix tailTrace_4913035
  have hstable : (prefixWord ++ tailWord_4913035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4913035).length < 2 ^ (prefixWord ++ tailWord_4913035).sum := by decide
  have hdescent : baseEnd_4913035 < baseStart_4913035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4913035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4913045 : List Nat := [1, 3, 2, 1, 1, 3, 2, 1, 1, 8]
def baseStart_4913045 : Nat := 118140960795 + 4913045 * 2 ^ 59
def prefixEnd_4913045 : Nat := 4983230072969 + 3 ^ 40 * 4913045 * 2
def baseEnd_4913045 : Nat := 840917854056278474180941

theorem tailTrace_4913045 : CollatzResearch.WordTrace tailWord_4913045 prefixEnd_4913045 840917854056278474180941 := by
  unfold tailWord_4913045
  simp only [CollatzResearch.WordTrace]
  refine ⟨179193472485884521128436589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119462314990589680752291059 179193472485884521128436589)
  ·
    refine ⟨67197552182206695423163721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179193472485884521128436589 67197552182206695423163721)
    ·
      refine ⟨50398164136655021567372791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67197552182206695423163721 50398164136655021567372791)
      ·
        refine ⟨75597246204982532351059187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50398164136655021567372791 75597246204982532351059187)
        ·
          refine ⟨113395869307473798526588781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75597246204982532351059187 113395869307473798526588781)
          ·
            refine ⟨42523450990302674447470793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113395869307473798526588781 42523450990302674447470793)
            ·
              refine ⟨31892588242727005835603095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42523450990302674447470793 31892588242727005835603095)
              ·
                refine ⟨47838882364090508753404643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31892588242727005835603095 47838882364090508753404643)
                ·
                  refine ⟨71758323546135763130106965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47838882364090508753404643 71758323546135763130106965)
                  ·
                    refine ⟨840917854056278474180941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 71758323546135763130106965 840917854056278474180941)
                    ·
                      rfl

theorem cell23_4913045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_4913045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4913045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4913045 prefixEnd_4913045 := by exact prefixLift 4913045
  have htrace : WordTrace (prefixWord ++ tailWord_4913045) baseStart_4913045 baseEnd_4913045 := by
    simpa [prefixWord, tailWord_4913045, baseEnd_4913045] using wordTrace_append hprefix tailTrace_4913045
  have hstable : (prefixWord ++ tailWord_4913045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4913045).length < 2 ^ (prefixWord ++ tailWord_4913045).sum := by decide
  have hdescent : baseEnd_4913045 < baseStart_4913045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4913045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4913065 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 3, 4, 4]
def baseStart_4913065 : Nat := 118140960795 + 4913065 * 2 ^ 59
def prefixEnd_4913065 : Nat := 4983230072969 + 3 ^ 40 * 4913065 * 2
def baseEnd_4913065 : Nat := 2522763831781925344292731

theorem tailTrace_4913065 : CollatzResearch.WordTrace tailWord_4913065 prefixEnd_4913065 2522763831781925344292731 := by
  unfold tailWord_4913065
  simp only [CollatzResearch.WordTrace]
  refine ⟨179194201945812064544164649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119462801297208043029443099 179194201945812064544164649)
  ·
    refine ⟨134395651459359048408123487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179194201945812064544164649 134395651459359048408123487)
    ·
      refine ⟨201593477189038572612185231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134395651459359048408123487 201593477189038572612185231)
      ·
        refine ⟨302390215783557858918277847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201593477189038572612185231 302390215783557858918277847)
        ·
          refine ⟨453585323675336788377416771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302390215783557858918277847 453585323675336788377416771)
          ·
            refine ⟨680377985513005182566125157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 453585323675336788377416771 680377985513005182566125157)
            ·
              refine ⟨127570872283688471731148467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 680377985513005182566125157 127570872283688471731148467)
              ·
                refine ⟨191356308425532707596722701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127570872283688471731148467 191356308425532707596722701)
                ·
                  refine ⟨71758615659574765348771013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 191356308425532707596722701 71758615659574765348771013)
                  ·
                    refine ⟨13454740436170268502894565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 71758615659574765348771013 13454740436170268502894565)
                    ·
                      refine ⟨2522763831781925344292731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13454740436170268502894565 2522763831781925344292731)
                      ·
                        rfl

theorem cell23_4913065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 4, 4].length) (baseStart_4913065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4913065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4913065 prefixEnd_4913065 := by exact prefixLift 4913065
  have htrace : WordTrace (prefixWord ++ tailWord_4913065) baseStart_4913065 baseEnd_4913065 := by
    simpa [prefixWord, tailWord_4913065, baseEnd_4913065] using wordTrace_append hprefix tailTrace_4913065
  have hstable : (prefixWord ++ tailWord_4913065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4913065).length < 2 ^ (prefixWord ++ tailWord_4913065).sum := by decide
  have hdescent : baseEnd_4913065 < baseStart_4913065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4913065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4913073 : List Nat := [1, 2, 2, 4, 2, 2, 3, 1, 1, 3, 2]
def baseStart_4913073 : Nat := 118140960795 + 4913073 * 2 ^ 59
def prefixEnd_4913073 : Nat := 4983230072969 + 3 ^ 40 * 4913073 * 2
def baseEnd_4913073 : Nat := 2522767939627161312992695

theorem tailTrace_4913073 : CollatzResearch.WordTrace tailWord_4913073 prefixEnd_4913073 2522767939627161312992695 := by
  unfold tailWord_4913073
  simp only [CollatzResearch.WordTrace]
  refine ⟨179194493729783081910455873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119462995819855387940303915 179194493729783081910455873)
  ·
    refine ⟨134395870297337311432841905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179194493729783081910455873 134395870297337311432841905)
    ·
      refine ⟨100796902723002983574631429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134395870297337311432841905 100796902723002983574631429)
      ·
        refine ⟨18899419260563059420243393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100796902723002983574631429 18899419260563059420243393)
        ·
          refine ⟨14174564445422294565182545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18899419260563059420243393 14174564445422294565182545)
          ·
            refine ⟨10630923334066720923886909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14174564445422294565182545 10630923334066720923886909)
            ·
              refine ⟨3986596250275020346457591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10630923334066720923886909 3986596250275020346457591)
              ·
                refine ⟨5979894375412530519686387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3986596250275020346457591 5979894375412530519686387)
                ·
                  refine ⟨8969841563118795779529581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5979894375412530519686387 8969841563118795779529581)
                  ·
                    refine ⟨3363690586169548417323593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8969841563118795779529581 3363690586169548417323593)
                    ·
                      refine ⟨2522767939627161312992695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3363690586169548417323593 2522767939627161312992695)
                      ·
                        rfl

theorem cell23_4913073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_4913073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4913073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4913073 prefixEnd_4913073 := by exact prefixLift 4913073
  have htrace : WordTrace (prefixWord ++ tailWord_4913073) baseStart_4913073 baseEnd_4913073 := by
    simpa [prefixWord, tailWord_4913073, baseEnd_4913073] using wordTrace_append hprefix tailTrace_4913073
  have hstable : (prefixWord ++ tailWord_4913073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4913073).length < 2 ^ (prefixWord ++ tailWord_4913073).sum := by decide
  have hdescent : baseEnd_4913073 < baseStart_4913073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4913073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4913095 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 8]
def baseStart_4913095 : Nat := 118140960795 + 4913095 * 2 ^ 59
def prefixEnd_4913095 : Nat := 4983230072969 + 3 ^ 40 * 4913095 * 2
def baseEnd_4913095 : Nat := 2522779236201560226917593

theorem tailTrace_4913095 : CollatzResearch.WordTrace tailWord_4913095 prefixEnd_4913095 2522779236201560226917593 := by
  unfold tailWord_4913095
  simp only [CollatzResearch.WordTrace]
  refine ⟨179195296135703379667756739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119463530757135586445171159 179195296135703379667756739)
  ·
    refine ⟨268792944203555069501635109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179195296135703379667756739 268792944203555069501635109)
    ·
      refine ⟨50398677038166575531556583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 268792944203555069501635109 50398677038166575531556583)
      ·
        refine ⟨75598015557249863297334875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50398677038166575531556583 75598015557249863297334875)
        ·
          refine ⟨113397023335874794946002313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75598015557249863297334875 113397023335874794946002313)
          ·
            refine ⟨85047767501906096209501735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113397023335874794946002313 85047767501906096209501735)
            ·
              refine ⟨127571651252859144314252603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85047767501906096209501735 127571651252859144314252603)
              ·
                refine ⟨191357476879288716471378905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127571651252859144314252603 191357476879288716471378905)
                ·
                  refine ⟨143518107659466537353534179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 191357476879288716471378905 143518107659466537353534179)
                  ·
                    refine ⟨215277161489199806030301269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 143518107659466537353534179 215277161489199806030301269)
                    ·
                      refine ⟨2522779236201560226917593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 215277161489199806030301269 2522779236201560226917593)
                      ·
                        rfl

theorem cell23_4913095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_4913095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4913095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4913095 prefixEnd_4913095 := by exact prefixLift 4913095
  have htrace : WordTrace (prefixWord ++ tailWord_4913095) baseStart_4913095 baseEnd_4913095 := by
    simpa [prefixWord, tailWord_4913095, baseEnd_4913095] using wordTrace_append hprefix tailTrace_4913095
  have hstable : (prefixWord ++ tailWord_4913095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4913095).length < 2 ^ (prefixWord ++ tailWord_4913095).sum := by decide
  have hdescent : baseEnd_4913095 < baseStart_4913095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4913095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4913216 : List Nat := [2, 1, 1, 2, 2, 6, 2, 1, 6]
def baseStart_4913216 : Nat := 118140960795 + 4913216 * 2 ^ 59
def prefixEnd_4913216 : Nat := 4983230072969 + 3 ^ 40 * 4913216 * 2
def baseEnd_4913216 : Nat := 280315707484528250389393

theorem tailTrace_4913216 : CollatzResearch.WordTrace tailWord_4913216 prefixEnd_4913216 280315707484528250389393 := by
  unfold tailWord_4913216
  simp only [CollatzResearch.WordTrace]
  refine ⟨89599854684132508666455751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119466472912176678221941001 89599854684132508666455751)
  ·
    refine ⟨134399782026198762999683627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89599854684132508666455751 134399782026198762999683627)
    ·
      refine ⟨201599673039298144499525441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134399782026198762999683627 201599673039298144499525441)
      ·
        refine ⟨151199754779473608374644081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201599673039298144499525441 151199754779473608374644081)
        ·
          refine ⟨113399816084605206280983061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151199754779473608374644081 113399816084605206280983061)
          ·
            refine ⟨5315616378965869044421081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 113399816084605206280983061 5315616378965869044421081)
            ·
              refine ⟨3986712284224401783315811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5315616378965869044421081 3986712284224401783315811)
              ·
                refine ⟨5980068426336602674973717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3986712284224401783315811 5980068426336602674973717)
                ·
                  refine ⟨280315707484528250389393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5980068426336602674973717 280315707484528250389393)
                  ·
                    rfl

theorem cell23_4913216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 1, 6].length) (baseStart_4913216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4913216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4913216 prefixEnd_4913216 := by exact prefixLift 4913216
  have htrace : WordTrace (prefixWord ++ tailWord_4913216) baseStart_4913216 baseEnd_4913216 := by
    simpa [prefixWord, tailWord_4913216, baseEnd_4913216] using wordTrace_append hprefix tailTrace_4913216
  have hstable : (prefixWord ++ tailWord_4913216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4913216).length < 2 ^ (prefixWord ++ tailWord_4913216).sum := by decide
  have hdescent : baseEnd_4913216 < baseStart_4913216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4913216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4913219 : List Nat := [1, 1, 1, 3, 1, 2, 2, 4, 1, 5, 2]
def baseStart_4913219 : Nat := 118140960795 + 4913219 * 2 ^ 59
def prefixEnd_4913219 : Nat := 4983230072969 + 3 ^ 40 * 4913219 * 2
def baseEnd_4913219 : Nat := 2522842907802717741767023

theorem tailTrace_4913219 : CollatzResearch.WordTrace tailWord_4913219 prefixEnd_4913219 2522842907802717741767023 := by
  unfold tailWord_4913219
  simp only [CollatzResearch.WordTrace]
  refine ⟨179199818787254148845270711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119466545858169432563513807 179199818787254148845270711)
  ·
    refine ⟨268799728180881223267906067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179199818787254148845270711 268799728180881223267906067)
    ·
      refine ⟨403199592271321834901859101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268799728180881223267906067 403199592271321834901859101)
      ·
        refine ⟨151199847101745688088197163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 403199592271321834901859101 151199847101745688088197163)
        ·
          refine ⟨226799770652618532132295745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151199847101745688088197163 226799770652618532132295745)
          ·
            refine ⟨170099827989463899099221809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226799770652618532132295745 170099827989463899099221809)
            ·
              refine ⟨127574870992097924324416357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170099827989463899099221809 127574870992097924324416357)
              ·
                refine ⟨23920288311018360810828067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 127574870992097924324416357 23920288311018360810828067)
                ·
                  refine ⟨35880432466527541216242101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23920288311018360810828067 35880432466527541216242101)
                  ·
                    refine ⟨3363790543736956989022697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35880432466527541216242101 3363790543736956989022697)
                    ·
                      refine ⟨2522842907802717741767023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3363790543736956989022697 2522842907802717741767023)
                      ·
                        rfl

theorem cell23_4913219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 5, 2].length) (baseStart_4913219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4913219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4913219 prefixEnd_4913219 := by exact prefixLift 4913219
  have htrace : WordTrace (prefixWord ++ tailWord_4913219) baseStart_4913219 baseEnd_4913219 := by
    simpa [prefixWord, tailWord_4913219, baseEnd_4913219] using wordTrace_append hprefix tailTrace_4913219
  have hstable : (prefixWord ++ tailWord_4913219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4913219).length < 2 ^ (prefixWord ++ tailWord_4913219).sum := by decide
  have hdescent : baseEnd_4913219 < baseStart_4913219 := by decide
  rcases family_descends (prefixWord ++ tailWord_4913219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4913260 : List Nat := [2, 2, 1, 1, 3, 3, 4, 2, 1, 1, 3]
def baseStart_4913260 : Nat := 118140960795 + 4913260 * 2 ^ 59
def prefixEnd_4913260 : Nat := 4983230072969 + 3 ^ 40 * 4913260 * 2
def baseEnd_4913260 : Nat := 2522863960509552081354335

theorem tailTrace_4913260 : CollatzResearch.WordTrace tailWord_4913260 prefixEnd_4913260 2522863960509552081354335 := by
  unfold tailWord_4913260
  simp only [CollatzResearch.WordTrace]
  refine ⟨89600657090052806423756617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119467542786737075231675489 89600657090052806423756617)
  ·
    refine ⟨67200492817539604817817463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89600657090052806423756617 67200492817539604817817463)
    ·
      refine ⟨100800739226309407226726195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67200492817539604817817463 100800739226309407226726195)
      ·
        refine ⟨151201108839464110840089293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100800739226309407226726195 151201108839464110840089293)
        ·
          refine ⟨56700415814799041565033485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151201108839464110840089293 56700415814799041565033485)
          ·
            refine ⟨21262655930549640586887557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56700415814799041565033485 21262655930549640586887557)
            ·
              refine ⟨3986747986978057610041417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21262655930549640586887557 3986747986978057610041417)
              ·
                refine ⟨2990060990233543207531063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3986747986978057610041417 2990060990233543207531063)
                ·
                  refine ⟨4485091485350314811296595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2990060990233543207531063 4485091485350314811296595)
                  ·
                    refine ⟨6727637228025472216944893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4485091485350314811296595 6727637228025472216944893)
                    ·
                      refine ⟨2522863960509552081354335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6727637228025472216944893 2522863960509552081354335)
                      ·
                        rfl

theorem cell23_4913260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 2, 1, 1, 3].length) (baseStart_4913260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4913260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4913260 prefixEnd_4913260 := by exact prefixLift 4913260
  have htrace : WordTrace (prefixWord ++ tailWord_4913260) baseStart_4913260 baseEnd_4913260 := by
    simpa [prefixWord, tailWord_4913260, baseEnd_4913260] using wordTrace_append hprefix tailTrace_4913260
  have hstable : (prefixWord ++ tailWord_4913260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4913260).length < 2 ^ (prefixWord ++ tailWord_4913260).sum := by decide
  have hdescent : baseEnd_4913260 < baseStart_4913260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4913260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4913276 : List Nat := [2, 2, 2, 1, 1, 4, 2, 3, 2, 4]
def baseStart_4913276 : Nat := 118140960795 + 4913276 * 2 ^ 59
def prefixEnd_4913276 : Nat := 4983230072969 + 3 ^ 40 * 4913276 * 2
def baseEnd_4913276 : Nat := 840957392066674672918087

theorem tailTrace_4913276 : CollatzResearch.WordTrace tailWord_4913276 prefixEnd_4913276 840957392066674672918087 := by
  unfold tailWord_4913276
  simp only [CollatzResearch.WordTrace]
  refine ⟨89600948874023823790047841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119467931832031765053397121 89600948874023823790047841)
  ·
    refine ⟨67200711655517867842535881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89600948874023823790047841 67200711655517867842535881)
    ·
      refine ⟨50400533741638400881901911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67200711655517867842535881 50400533741638400881901911)
      ·
        refine ⟨75600800612457601322852867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50400533741638400881901911 75600800612457601322852867)
        ·
          refine ⟨113401200918686401984279301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75600800612457601322852867 113401200918686401984279301)
          ·
            refine ⟨21262725172253700372052369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113401200918686401984279301 21262725172253700372052369)
            ·
              refine ⟨15947043879190275279039277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21262725172253700372052369 15947043879190275279039277)
              ·
                refine ⟨5980141454696353229639729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15947043879190275279039277 5980141454696353229639729)
                ·
                  refine ⟨4485106091022264922229797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5980141454696353229639729 4485106091022264922229797)
                  ·
                    refine ⟨840957392066674672918087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4485106091022264922229797 840957392066674672918087)
                    ·
                      rfl

theorem cell23_4913276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 3, 2, 4].length) (baseStart_4913276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4913276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4913276 prefixEnd_4913276 := by exact prefixLift 4913276
  have htrace : WordTrace (prefixWord ++ tailWord_4913276) baseStart_4913276 baseEnd_4913276 := by
    simpa [prefixWord, tailWord_4913276, baseEnd_4913276] using wordTrace_append hprefix tailTrace_4913276
  have hstable : (prefixWord ++ tailWord_4913276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4913276).length < 2 ^ (prefixWord ++ tailWord_4913276).sum := by decide
  have hdescent : baseEnd_4913276 < baseStart_4913276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4913276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4913283 : List Nat := [1, 1, 1, 3, 3, 4, 1, 2, 3, 2, 2]
def baseStart_4913283 : Nat := 118140960795 + 4913283 * 2 ^ 59
def prefixEnd_4913283 : Nat := 4983230072969 + 3 ^ 40 * 4913283 * 2
def baseEnd_4913283 : Nat := 2522875770564605491366729

theorem tailTrace_4913283 : CollatzResearch.WordTrace tailWord_4913283 prefixEnd_4913283 2522875770564605491366729 := by
  unfold tailWord_4913283
  simp only [CollatzResearch.WordTrace]
  refine ⟨179202153059022287775600503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119468102039348191850400335 179202153059022287775600503)
  ·
    refine ⟨268803229588533431663400755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179202153059022287775600503 268803229588533431663400755)
    ·
      refine ⟨403204844382800147495101133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268803229588533431663400755 403204844382800147495101133)
      ·
        refine ⟨151201816643550055310662925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 403204844382800147495101133 151201816643550055310662925)
        ·
          refine ⟨56700681241331270741498597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151201816643550055310662925 56700681241331270741498597)
          ·
            refine ⟨10631377732749613264030987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56700681241331270741498597 10631377732749613264030987)
            ·
              refine ⟨15947066599124419896046481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10631377732749613264030987 15947066599124419896046481)
              ·
                refine ⟨11960299949343314922034861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15947066599124419896046481 11960299949343314922034861)
                ·
                  refine ⟨4485112481003743095763073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11960299949343314922034861 4485112481003743095763073)
                  ·
                    refine ⟨3363834360752807321822305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4485112481003743095763073 3363834360752807321822305)
                    ·
                      refine ⟨2522875770564605491366729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3363834360752807321822305 2522875770564605491366729)
                      ·
                        rfl

theorem cell23_4913283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 3, 2, 2].length) (baseStart_4913283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4913283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4913283 prefixEnd_4913283 := by exact prefixLift 4913283
  have htrace : WordTrace (prefixWord ++ tailWord_4913283) baseStart_4913283 baseEnd_4913283 := by
    simpa [prefixWord, tailWord_4913283, baseEnd_4913283] using wordTrace_append hprefix tailTrace_4913283
  have hstable : (prefixWord ++ tailWord_4913283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4913283).length < 2 ^ (prefixWord ++ tailWord_4913283).sum := by decide
  have hdescent : baseEnd_4913283 < baseStart_4913283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4913283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4913289 : List Nat := [1, 2, 1, 1, 4, 2, 5, 7]
def baseStart_4913289 : Nat := 118140960795 + 4913289 * 2 ^ 59
def prefixEnd_4913289 : Nat := 4983230072969 + 3 ^ 40 * 4913289 * 2
def baseEnd_4913289 : Nat := 93439957461056758070063

theorem tailTrace_4913289 : CollatzResearch.WordTrace tailWord_4913289 prefixEnd_4913289 93439957461056758070063 := by
  unfold tailWord_4913289
  simp only [CollatzResearch.WordTrace]
  refine ⟨179202371897000550800318921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119468247931333700533545947 179202371897000550800318921)
  ·
    refine ⟨134401778922750413100239191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179202371897000550800318921 134401778922750413100239191)
    ·
      refine ⟨201602668384125619650358787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134401778922750413100239191 201602668384125619650358787)
      ·
        refine ⟨302404002576188429475538181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201602668384125619650358787 302404002576188429475538181)
        ·
          refine ⟨56700750483035330526663409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 302404002576188429475538181 56700750483035330526663409)
          ·
            refine ⟨42525562862276497894997557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56700750483035330526663409 42525562862276497894997557)
            ·
              refine ⟨3986771518338421677656021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42525562862276497894997557 3986771518338421677656021)
              ·
                refine ⟨93439957461056758070063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3986771518338421677656021 93439957461056758070063)
                ·
                  rfl

theorem cell23_4913289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 7].length) (baseStart_4913289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4913289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4913289 prefixEnd_4913289 := by exact prefixLift 4913289
  have htrace : WordTrace (prefixWord ++ tailWord_4913289) baseStart_4913289 baseEnd_4913289 := by
    simpa [prefixWord, tailWord_4913289, baseEnd_4913289] using wordTrace_append hprefix tailTrace_4913289
  have hstable : (prefixWord ++ tailWord_4913289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4913289).length < 2 ^ (prefixWord ++ tailWord_4913289).sum := by decide
  have hdescent : baseEnd_4913289 < baseStart_4913289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4913289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4913300 : List Nat := [2, 4, 2, 3, 1, 1, 1, 3, 1, 1, 4]
def baseStart_4913300 : Nat := 118140960795 + 4913300 * 2 ^ 59
def prefixEnd_4913300 : Nat := 4983230072969 + 3 ^ 40 * 4913300 * 2
def baseEnd_4913300 : Nat := 2522884499735731924854151

theorem tailTrace_4913300 : CollatzResearch.WordTrace tailWord_4913300 prefixEnd_4913300 2522884499735731924854151 := by
  unfold tailWord_4913300
  simp only [CollatzResearch.WordTrace]
  refine ⟨89601386549980349839484677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119468515399973799785979569 89601386549980349839484677)
  ·
    refine ⟨16800259978121315594903377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89601386549980349839484677 16800259978121315594903377)
    ·
      refine ⟨12600194983590986696177533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16800259978121315594903377 12600194983590986696177533)
      ·
        refine ⟨4725073118846620011066575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12600194983590986696177533 4725073118846620011066575)
        ·
          refine ⟨7087609678269930016599863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4725073118846620011066575 7087609678269930016599863)
          ·
            refine ⟨10631414517404895024899795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7087609678269930016599863 10631414517404895024899795)
            ·
              refine ⟨15947121776107342537349693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10631414517404895024899795 15947121776107342537349693)
              ·
                refine ⟨5980170666040253451506135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15947121776107342537349693 5980170666040253451506135)
                ·
                  refine ⟨8970255999060380177259203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5980170666040253451506135 8970255999060380177259203)
                  ·
                    refine ⟨13455383998590570265888805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8970255999060380177259203 13455383998590570265888805)
                    ·
                      refine ⟨2522884499735731924854151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13455383998590570265888805 2522884499735731924854151)
                      ·
                        rfl

theorem cell23_4913300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_4913300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4913300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4913300 prefixEnd_4913300 := by exact prefixLift 4913300
  have htrace : WordTrace (prefixWord ++ tailWord_4913300) baseStart_4913300 baseEnd_4913300 := by
    simpa [prefixWord, tailWord_4913300, baseEnd_4913300] using wordTrace_append hprefix tailTrace_4913300
  have hstable : (prefixWord ++ tailWord_4913300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4913300).length < 2 ^ (prefixWord ++ tailWord_4913300).sum := by decide
  have hdescent : baseEnd_4913300 < baseStart_4913300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4913300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4913303 : List Nat := [1, 1, 3, 3, 4, 1, 1, 3, 1, 2, 3]
def baseStart_4913303 : Nat := 118140960795 + 4913303 * 2 ^ 59
def prefixEnd_4913303 : Nat := 4983230072969 + 3 ^ 40 * 4913303 * 2
def baseEnd_4913303 : Nat := 2522886040177695413116637

theorem tailTrace_4913303 : CollatzResearch.WordTrace tailWord_4913303 prefixEnd_4913303 2522886040177695413116637 := by
  unfold tailWord_4913303
  simp only [CollatzResearch.WordTrace]
  refine ⟨179202882518949831191328563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119468588345966554127552375 179202882518949831191328563)
  ·
    refine ⟨268804323778424746786992845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179202882518949831191328563 268804323778424746786992845)
    ·
      refine ⟨100801621416909280045122317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 268804323778424746786992845 100801621416909280045122317)
      ·
        refine ⟨37800608031340980016920869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100801621416909280045122317 37800608031340980016920869)
        ·
          refine ⟨7087614005876433753172663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37800608031340980016920869 7087614005876433753172663)
          ·
            refine ⟨10631421008814650629758995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7087614005876433753172663 10631421008814650629758995)
            ·
              refine ⟨15947131513221975944638493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10631421008814650629758995 15947131513221975944638493)
              ·
                refine ⟨5980174317458240979239435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15947131513221975944638493 5980174317458240979239435)
                ·
                  refine ⟨8970261476187361468859153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5980174317458240979239435 8970261476187361468859153)
                  ·
                    refine ⟨6727696107140521101644365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8970261476187361468859153 6727696107140521101644365)
                    ·
                      refine ⟨2522886040177695413116637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6727696107140521101644365 2522886040177695413116637)
                      ·
                        rfl

theorem cell23_4913303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_4913303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4913303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4913303 prefixEnd_4913303 := by exact prefixLift 4913303
  have htrace : WordTrace (prefixWord ++ tailWord_4913303) baseStart_4913303 baseEnd_4913303 := by
    simpa [prefixWord, tailWord_4913303, baseEnd_4913303] using wordTrace_append hprefix tailTrace_4913303
  have hstable : (prefixWord ++ tailWord_4913303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4913303).length < 2 ^ (prefixWord ++ tailWord_4913303).sum := by decide
  have hdescent : baseEnd_4913303 < baseStart_4913303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4913303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4913359 : List Nat := [1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 5]
def baseStart_4913359 : Nat := 118140960795 + 4913359 * 2 ^ 59
def prefixEnd_4913359 : Nat := 4983230072969 + 3 ^ 40 * 4913359 * 2
def baseEnd_4913359 : Nat := 2522914795094347194016379

theorem tailTrace_4913359 : CollatzResearch.WordTrace tailWord_4913359 prefixEnd_4913359 2522914795094347194016379 := by
  unfold tailWord_4913359
  simp only [CollatzResearch.WordTrace]
  refine ⟨179204925006746952755367131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119469950004497968503578087 179204925006746952755367131)
  ·
    refine ⟨268807387510120429133050697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179204925006746952755367131 268807387510120429133050697)
    ·
      refine ⟨201605540632590321849788023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268807387510120429133050697 201605540632590321849788023)
      ·
        refine ⟨302408310948885482774682035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201605540632590321849788023 302408310948885482774682035)
        ·
          refine ⟨453612466423328224162023053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302408310948885482774682035 453612466423328224162023053)
          ·
            refine ⟨170104674908748084060758645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 453612466423328224162023053 170104674908748084060758645)
            ·
              refine ⟨15947313272695132880696123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 170104674908748084060758645 15947313272695132880696123)
              ·
                refine ⟨23920969909042699321044185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15947313272695132880696123 23920969909042699321044185)
                ·
                  refine ⟨17940727431782024490783139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23920969909042699321044185 17940727431782024490783139)
                  ·
                    refine ⟨26911091147673036736174709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17940727431782024490783139 26911091147673036736174709)
                    ·
                      refine ⟨2522914795094347194016379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26911091147673036736174709 2522914795094347194016379)
                      ·
                        rfl

theorem cell23_4913359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 5].length) (baseStart_4913359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4913359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4913359 prefixEnd_4913359 := by exact prefixLift 4913359
  have htrace : WordTrace (prefixWord ++ tailWord_4913359) baseStart_4913359 baseEnd_4913359 := by
    simpa [prefixWord, tailWord_4913359, baseEnd_4913359] using wordTrace_append hprefix tailTrace_4913359
  have hstable : (prefixWord ++ tailWord_4913359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4913359).length < 2 ^ (prefixWord ++ tailWord_4913359).sum := by decide
  have hdescent : baseEnd_4913359 < baseStart_4913359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4913359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4913369 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 4, 2, 4]
def baseStart_4913369 : Nat := 118140960795 + 4913369 * 2 ^ 59
def prefixEnd_4913369 : Nat := 4983230072969 + 3 ^ 40 * 4913369 * 2
def baseEnd_4913369 : Nat := 2522919929900892154891333

theorem tailTrace_4913369 : CollatzResearch.WordTrace tailWord_4913369 prefixEnd_4913369 2522919929900892154891333 := by
  unfold tailWord_4913369
  simp only [CollatzResearch.WordTrace]
  refine ⟨179205289736710724463231161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119470193157807149642154107 179205289736710724463231161)
  ·
    refine ⟨134403967302533043347423371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179205289736710724463231161 134403967302533043347423371)
    ·
      refine ⟨201605950953799565021135057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134403967302533043347423371 201605950953799565021135057)
      ·
        refine ⟨151204463215349673765851293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201605950953799565021135057 151204463215349673765851293)
        ·
          refine ⟨56701673705756127662194235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151204463215349673765851293 56701673705756127662194235)
          ·
            refine ⟨85052510558634191493291353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56701673705756127662194235 85052510558634191493291353)
            ·
              refine ⟨63789382918975643619968515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85052510558634191493291353 63789382918975643619968515)
              ·
                refine ⟨95684074378463465429952773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63789382918975643619968515 95684074378463465429952773)
                ·
                  refine ⟨17940763945961899768116145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95684074378463465429952773 17940763945961899768116145)
                  ·
                    refine ⟨13455572959471424826087109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17940763945961899768116145 13455572959471424826087109)
                    ·
                      refine ⟨2522919929900892154891333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13455572959471424826087109 2522919929900892154891333)
                      ·
                        rfl

theorem cell23_4913369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 2, 4].length) (baseStart_4913369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4913369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4913369 prefixEnd_4913369 := by exact prefixLift 4913369
  have htrace : WordTrace (prefixWord ++ tailWord_4913369) baseStart_4913369 baseEnd_4913369 := by
    simpa [prefixWord, tailWord_4913369, baseEnd_4913369] using wordTrace_append hprefix tailTrace_4913369
  have hstable : (prefixWord ++ tailWord_4913369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4913369).length < 2 ^ (prefixWord ++ tailWord_4913369).sum := by decide
  have hdescent : baseEnd_4913369 < baseStart_4913369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4913369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4913419 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 5]
def baseStart_4913419 : Nat := 118140960795 + 4913419 * 2 ^ 59
def prefixEnd_4913419 : Nat := 4983230072969 + 3 ^ 40 * 4913419 * 2
def baseEnd_4913419 : Nat := 2522945603933616959266103

theorem tailTrace_4913419 : CollatzResearch.WordTrace tailWord_4913419 prefixEnd_4913419 2522945603933616959266103 := by
  unfold tailWord_4913419
  simp only [CollatzResearch.WordTrace]
  refine ⟨179207113386529583002551311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119471408924353055335034207 179207113386529583002551311)
  ·
    refine ⟨268810670079794374503826967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179207113386529583002551311 268810670079794374503826967)
    ·
      refine ⟨403216005119691561755740451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268810670079794374503826967 403216005119691561755740451)
      ·
        refine ⟨604824007679537342633610677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 403216005119691561755740451 604824007679537342633610677)
        ·
          refine ⟨56702250719956625871901001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 604824007679537342633610677 56702250719956625871901001)
          ·
            refine ⟨42526688039967469403925751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56702250719956625871901001 42526688039967469403925751)
            ·
              refine ⟨63790032059951204105888627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42526688039967469403925751 63790032059951204105888627)
              ·
                refine ⟨95685048089926806158832941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63790032059951204105888627 95685048089926806158832941)
                ·
                  refine ⟨35881893033722552309562353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95685048089926806158832941 35881893033722552309562353)
                  ·
                    refine ⟨26911419775291914232171765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35881893033722552309562353 26911419775291914232171765)
                    ·
                      refine ⟨2522945603933616959266103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26911419775291914232171765 2522945603933616959266103)
                      ·
                        rfl

theorem cell23_4913419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 5].length) (baseStart_4913419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4913419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4913419 prefixEnd_4913419 := by exact prefixLift 4913419
  have htrace : WordTrace (prefixWord ++ tailWord_4913419) baseStart_4913419 baseEnd_4913419 := by
    simpa [prefixWord, tailWord_4913419, baseEnd_4913419] using wordTrace_append hprefix tailTrace_4913419
  have hstable : (prefixWord ++ tailWord_4913419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4913419).length < 2 ^ (prefixWord ++ tailWord_4913419).sum := by decide
  have hdescent : baseEnd_4913419 < baseStart_4913419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4913419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4913460 : List Nat := [2, 5, 1, 1, 1, 4, 1, 1, 2, 5]
def baseStart_4913460 : Nat := 118140960795 + 4913460 * 2 ^ 59
def prefixEnd_4913460 : Nat := 4983230072969 + 3 ^ 40 * 4913460 * 2
def baseEnd_4913460 : Nat := 840988885546817099617805

theorem tailTrace_4913460 : CollatzResearch.WordTrace tailWord_4913460 prefixEnd_4913460 840988885546817099617805 := by
  unfold tailWord_4913460
  simp only [CollatzResearch.WordTrace]
  refine ⟨89604304389690523502396917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119472405852920698003195889 89604304389690523502396917)
  ·
    refine ⟨8400403536533486578349711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89604304389690523502396917 8400403536533486578349711)
    ·
      refine ⟨12600605304800229867524567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8400403536533486578349711 12600605304800229867524567)
      ·
        refine ⟨18900907957200344801286851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12600605304800229867524567 18900907957200344801286851)
        ·
          refine ⟨28351361935800517201930277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18900907957200344801286851 28351361935800517201930277)
          ·
            refine ⟨5315880362962596975361927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28351361935800517201930277 5315880362962596975361927)
            ·
              refine ⟨7973820544443895463042891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5315880362962596975361927 7973820544443895463042891)
              ·
                refine ⟨11960730816665843194564337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7973820544443895463042891 11960730816665843194564337)
                ·
                  refine ⟨8970548112499382395923253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11960730816665843194564337 8970548112499382395923253)
                  ·
                    refine ⟨840988885546817099617805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8970548112499382395923253 840988885546817099617805)
                    ·
                      rfl

theorem cell23_4913460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_4913460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4913460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4913460 prefixEnd_4913460 := by exact prefixLift 4913460
  have htrace : WordTrace (prefixWord ++ tailWord_4913460) baseStart_4913460 baseEnd_4913460 := by
    simpa [prefixWord, tailWord_4913460, baseEnd_4913460] using wordTrace_append hprefix tailTrace_4913460
  have hstable : (prefixWord ++ tailWord_4913460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4913460).length < 2 ^ (prefixWord ++ tailWord_4913460).sum := by decide
  have hdescent : baseEnd_4913460 < baseStart_4913460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4913460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4913486 : List Nat := [4, 1, 1, 1, 1, 1, 2, 6, 6]
def baseStart_4913486 : Nat := 118140960795 + 4913486 * 2 ^ 59
def prefixEnd_4913486 : Nat := 4983230072969 + 3 ^ 40 * 4913486 * 2
def baseEnd_4913486 : Nat := 280331111904163133014255

theorem tailTrace_4913486 : CollatzResearch.WordTrace tailWord_4913486 prefixEnd_4913486 280331111904163133014255 := by
  unfold tailWord_4913486
  simp only [CollatzResearch.WordTrace]
  refine ⟨22401194634660856680655039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119473038051524568963493541 22401194634660856680655039)
  ·
    refine ⟨33601791951991285020982559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22401194634660856680655039 33601791951991285020982559)
    ·
      refine ⟨50402687927986927531473839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33601791951991285020982559 50402687927986927531473839)
      ·
        refine ⟨75604031891980391297210759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50402687927986927531473839 75604031891980391297210759)
        ·
          refine ⟨113406047837970586945816139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75604031891980391297210759 113406047837970586945816139)
          ·
            refine ⟨170109071756955880418724209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113406047837970586945816139 170109071756955880418724209)
            ·
              refine ⟨127581803817716910314043157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170109071756955880418724209 127581803817716910314043157)
              ·
                refine ⟨5980397053955480170970773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 127581803817716910314043157 5980397053955480170970773)
                ·
                  refine ⟨280331111904163133014255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5980397053955480170970773 280331111904163133014255)
                  ·
                    rfl

theorem cell23_4913486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 6, 6].length) (baseStart_4913486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4913486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4913486 prefixEnd_4913486 := by exact prefixLift 4913486
  have htrace : WordTrace (prefixWord ++ tailWord_4913486) baseStart_4913486 baseEnd_4913486 := by
    simpa [prefixWord, tailWord_4913486, baseEnd_4913486] using wordTrace_append hprefix tailTrace_4913486
  have hstable : (prefixWord ++ tailWord_4913486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4913486).length < 2 ^ (prefixWord ++ tailWord_4913486).sum := by decide
  have hdescent : baseEnd_4913486 < baseStart_4913486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4913486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4913490 : List Nat := [3, 2, 2, 1, 1, 1, 4, 4, 1, 4]
def baseStart_4913490 : Nat := 118140960795 + 4913490 * 2 ^ 59
def prefixEnd_4913490 : Nat := 4983230072969 + 3 ^ 40 * 4913490 * 2
def baseEnd_4913490 : Nat := 840994020353362060492759

theorem tailTrace_4913490 : CollatzResearch.WordTrace tailWord_4913490 prefixEnd_4913490 840994020353362060492759 := by
  unfold tailWord_4913490
  simp only [CollatzResearch.WordTrace]
  refine ⟨44802425742318090532096481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119473135312848241418923949 44802425742318090532096481)
  ·
    refine ⟨33601819306738567899072361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44802425742318090532096481 33601819306738567899072361)
    ·
      refine ⟨25201364480053925924304271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33601819306738567899072361 25201364480053925924304271)
      ·
        refine ⟨37802046720080888886456407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25201364480053925924304271 37802046720080888886456407)
        ·
          refine ⟨56703070080121333329684611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37802046720080888886456407 56703070080121333329684611)
          ·
            refine ⟨85054605120181999994526917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56703070080121333329684611 85054605120181999994526917)
            ·
              refine ⟨15947738460034124998973797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85054605120181999994526917 15947738460034124998973797)
              ·
                refine ⟨2990200961256398437307587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15947738460034124998973797 2990200961256398437307587)
                ·
                  refine ⟨4485301441884597655961381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2990200961256398437307587 4485301441884597655961381)
                  ·
                    refine ⟨840994020353362060492759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4485301441884597655961381 840994020353362060492759)
                    ·
                      rfl

theorem cell23_4913490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_4913490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4913490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4913490 prefixEnd_4913490 := by exact prefixLift 4913490
  have htrace : WordTrace (prefixWord ++ tailWord_4913490) baseStart_4913490 baseEnd_4913490 := by
    simpa [prefixWord, tailWord_4913490, baseEnd_4913490] using wordTrace_append hprefix tailTrace_4913490
  have hstable : (prefixWord ++ tailWord_4913490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4913490).length < 2 ^ (prefixWord ++ tailWord_4913490).sum := by decide
  have hdescent : baseEnd_4913490 < baseStart_4913490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4913490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4913513 : List Nat := [1, 2, 1, 1, 1, 3, 3, 4, 3, 1, 3]
def baseStart_4913513 : Nat := 118140960795 + 4913513 * 2 ^ 59
def prefixEnd_4913513 : Nat := 4983230072969 + 3 ^ 40 * 4913513 * 2
def baseEnd_4913513 : Nat := 2522993871115139591490671

theorem tailTrace_4913513 : CollatzResearch.WordTrace tailWord_4913513 prefixEnd_4913513 2522993871115139591490671 := by
  unfold tailWord_4913513
  simp only [CollatzResearch.WordTrace]
  refine ⟨179210541848189037056473193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119473694565459358037648795 179210541848189037056473193)
  ·
    refine ⟨134407906386141777792354895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179210541848189037056473193 134407906386141777792354895)
    ·
      refine ⟨201611859579212666688532343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134407906386141777792354895 201611859579212666688532343)
      ·
        refine ⟨302417789368819000032798515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201611859579212666688532343 302417789368819000032798515)
        ·
          refine ⟨453626684053228500049197773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302417789368819000032798515 453626684053228500049197773)
          ·
            refine ⟨170110006519960687518449165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 453626684053228500049197773 170110006519960687518449165)
            ·
              refine ⟨63791252444985257819418437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 170110006519960687518449165 63791252444985257819418437)
              ·
                refine ⟨11960859833434735841140957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63791252444985257819418437 11960859833434735841140957)
                ·
                  refine ⟨4485322437538025940427859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11960859833434735841140957 4485322437538025940427859)
                  ·
                    refine ⟨6727983656307038910641789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4485322437538025940427859 6727983656307038910641789)
                    ·
                      refine ⟨2522993871115139591490671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6727983656307038910641789 2522993871115139591490671)
                      ·
                        rfl

theorem cell23_4913513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 3, 1, 3].length) (baseStart_4913513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4913513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4913513 prefixEnd_4913513 := by exact prefixLift 4913513
  have htrace : WordTrace (prefixWord ++ tailWord_4913513) baseStart_4913513 baseEnd_4913513 := by
    simpa [prefixWord, tailWord_4913513, baseEnd_4913513] using wordTrace_append hprefix tailTrace_4913513
  have hstable : (prefixWord ++ tailWord_4913513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4913513).length < 2 ^ (prefixWord ++ tailWord_4913513).sum := by decide
  have hdescent : baseEnd_4913513 < baseStart_4913513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4913513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4913533 : List Nat := [1, 4, 1, 1, 2, 3, 2, 3, 1, 5]
def baseStart_4913533 : Nat := 118140960795 + 4913533 * 2 ^ 59
def prefixEnd_4913533 : Nat := 4983230072969 + 3 ^ 40 * 4913533 * 2
def baseEnd_4913533 : Nat := 841001380242743171080193

theorem tailTrace_4913533 : CollatzResearch.WordTrace tailWord_4913533 prefixEnd_4913533 841001380242743171080193 := by
  unfold tailWord_4913533
  simp only [CollatzResearch.WordTrace]
  refine ⟨179211271308116580472201253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119474180872077720314800835 179211271308116580472201253)
  ·
    refine ⟨33602113370271858838537735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 179211271308116580472201253 33602113370271858838537735)
    ·
      refine ⟨50403170055407788257806603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33602113370271858838537735 50403170055407788257806603)
      ·
        refine ⟨75604755083111682386709905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50403170055407788257806603 75604755083111682386709905)
        ·
          refine ⟨56703566312333761790032429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75604755083111682386709905 56703566312333761790032429)
          ·
            refine ⟨21263837367125160671262161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56703566312333761790032429 21263837367125160671262161)
            ·
              refine ⟨15947878025343870503446621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21263837367125160671262161 15947878025343870503446621)
              ·
                refine ⟨5980454259503951438792483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15947878025343870503446621 5980454259503951438792483)
                ·
                  refine ⟨8970681389255927158188725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5980454259503951438792483 8970681389255927158188725)
                  ·
                    refine ⟨841001380242743171080193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8970681389255927158188725 841001380242743171080193)
                    ·
                      rfl

theorem cell23_4913533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 3, 1, 5].length) (baseStart_4913533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4913533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4913533 prefixEnd_4913533 := by exact prefixLift 4913533
  have htrace : WordTrace (prefixWord ++ tailWord_4913533) baseStart_4913533 baseEnd_4913533 := by
    simpa [prefixWord, tailWord_4913533, baseEnd_4913533] using wordTrace_append hprefix tailTrace_4913533
  have hstable : (prefixWord ++ tailWord_4913533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4913533).length < 2 ^ (prefixWord ++ tailWord_4913533).sum := by decide
  have hdescent : baseEnd_4913533 < baseStart_4913533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4913533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4913536 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 4]
def baseStart_4913536 : Nat := 118140960795 + 4913536 * 2 ^ 59
def prefixEnd_4913536 : Nat := 4983230072969 + 3 ^ 40 * 4913536 * 2
def baseEnd_4913536 : Nat := 2523005681170193001503065

theorem tailTrace_4913536 : CollatzResearch.WordTrace tailWord_4913536 prefixEnd_4913536 2523005681170193001503065 := by
  unfold tailWord_4913536
  simp only [CollatzResearch.WordTrace]
  refine ⟨89605690363552855992280231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119474253818070474656373641 89605690363552855992280231)
  ·
    refine ⟨134408535545329283988420347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89605690363552855992280231 134408535545329283988420347)
    ·
      refine ⟨201612803317993925982630521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134408535545329283988420347 201612803317993925982630521)
      ·
        refine ⟨151209602488495444486972891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201612803317993925982630521 151209602488495444486972891)
        ·
          refine ⟨226814403732743166730459337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151209602488495444486972891 226814403732743166730459337)
          ·
            refine ⟨170110802799557375047844503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226814403732743166730459337 170110802799557375047844503)
            ·
              refine ⟨255166204199336062571766755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170110802799557375047844503 255166204199336062571766755)
              ·
                refine ⟨382749306299004093857650133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 255166204199336062571766755 382749306299004093857650133)
                ·
                  refine ⟨8970686866382908449788675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 382749306299004093857650133 8970686866382908449788675)
                  ·
                    refine ⟨13456030299574362674683013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8970686866382908449788675 13456030299574362674683013)
                    ·
                      refine ⟨2523005681170193001503065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13456030299574362674683013 2523005681170193001503065)
                      ·
                        rfl

theorem cell23_4913536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 4].length) (baseStart_4913536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4913536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4913536 prefixEnd_4913536 := by exact prefixLift 4913536
  have htrace : WordTrace (prefixWord ++ tailWord_4913536) baseStart_4913536 baseEnd_4913536 := by
    simpa [prefixWord, tailWord_4913536, baseEnd_4913536] using wordTrace_append hprefix tailTrace_4913536
  have hstable : (prefixWord ++ tailWord_4913536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4913536).length < 2 ^ (prefixWord ++ tailWord_4913536).sum := by decide
  have hdescent : baseEnd_4913536 < baseStart_4913536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4913536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4913540 : List Nat := [2, 3, 2, 1, 1, 2, 3, 2, 2, 3, 2]
def baseStart_4913540 : Nat := 118140960795 + 4913540 * 2 ^ 59
def prefixEnd_4913540 : Nat := 4983230072969 + 3 ^ 40 * 4913540 * 2
def baseEnd_4913540 : Nat := 2523007735092810985853047

theorem tailTrace_4913540 : CollatzResearch.WordTrace tailWord_4913540 prefixEnd_4913540 2523007735092810985853047 := by
  unfold tailWord_4913540
  simp only [CollatzResearch.WordTrace]
  refine ⟨89605763309545610333853037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119474351079394147111804049 89605763309545610333853037)
  ·
    refine ⟨33602161241079603875194889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89605763309545610333853037 33602161241079603875194889)
    ·
      refine ⟨25201620930809702906396167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33602161241079603875194889 25201620930809702906396167)
      ·
        refine ⟨37802431396214554359594251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25201620930809702906396167 37802431396214554359594251)
        ·
          refine ⟨56703647094321831539391377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37802431396214554359594251 56703647094321831539391377)
          ·
            refine ⟨42527735320741373654543533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56703647094321831539391377 42527735320741373654543533)
            ·
              refine ⟨15947900745278015120453825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42527735320741373654543533 15947900745278015120453825)
              ·
                refine ⟨11960925558958511340340369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15947900745278015120453825 11960925558958511340340369)
                ·
                  refine ⟨8970694169218883505255277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11960925558958511340340369 8970694169218883505255277)
                  ·
                    refine ⟨3364010313457081314470729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8970694169218883505255277 3364010313457081314470729)
                    ·
                      refine ⟨2523007735092810985853047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3364010313457081314470729 2523007735092810985853047)
                      ·
                        rfl

theorem cell23_4913540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 2, 3, 2].length) (baseStart_4913540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4913540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4913540 prefixEnd_4913540 := by exact prefixLift 4913540
  have htrace : WordTrace (prefixWord ++ tailWord_4913540) baseStart_4913540 baseEnd_4913540 := by
    simpa [prefixWord, tailWord_4913540, baseEnd_4913540] using wordTrace_append hprefix tailTrace_4913540
  have hstable : (prefixWord ++ tailWord_4913540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4913540).length < 2 ^ (prefixWord ++ tailWord_4913540).sum := by decide
  have hdescent : baseEnd_4913540 < baseStart_4913540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4913540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4913573 : List Nat := [1, 3, 1, 2, 1, 1, 5, 1, 3, 2, 3]
def baseStart_4913573 : Nat := 118140960795 + 4913573 * 2 ^ 59
def prefixEnd_4913573 : Nat := 4983230072969 + 3 ^ 40 * 4913573 * 2
def baseEnd_4913573 : Nat := 2523024679954409356740395

theorem tailTrace_4913573 : CollatzResearch.WordTrace tailWord_4913573 prefixEnd_4913573 2523024679954409356740395 := by
  unfold tailWord_4913573
  simp only [CollatzResearch.WordTrace]
  refine ⟨179212730227971667303657373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119475153485314444869104915 179212730227971667303657373)
  ·
    refine ⟨67204773835489375238871515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179212730227971667303657373 67204773835489375238871515)
    ·
      refine ⟨100807160753234062858307273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67204773835489375238871515 100807160753234062858307273)
      ·
        refine ⟨75605370564925547143730455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100807160753234062858307273 75605370564925547143730455)
        ·
          refine ⟨113408055847388320715595683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75605370564925547143730455 113408055847388320715595683)
          ·
            refine ⟨170112083771082481073393525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113408055847388320715595683 170112083771082481073393525)
            ·
              refine ⟨15948007853538982600630643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 170112083771082481073393525 15948007853538982600630643)
              ·
                refine ⟨23922011780308473900945965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15948007853538982600630643 23922011780308473900945965)
                ·
                  refine ⟨8970754417615677712854737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23922011780308473900945965 8970754417615677712854737)
                  ·
                    refine ⟨6728065813211758284641053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8970754417615677712854737 6728065813211758284641053)
                    ·
                      refine ⟨2523024679954409356740395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6728065813211758284641053 2523024679954409356740395)
                      ·
                        rfl

theorem cell23_4913573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 3, 2, 3].length) (baseStart_4913573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4913573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4913573 prefixEnd_4913573 := by exact prefixLift 4913573
  have htrace : WordTrace (prefixWord ++ tailWord_4913573) baseStart_4913573 baseEnd_4913573 := by
    simpa [prefixWord, tailWord_4913573, baseEnd_4913573] using wordTrace_append hprefix tailTrace_4913573
  have hstable : (prefixWord ++ tailWord_4913573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4913573).length < 2 ^ (prefixWord ++ tailWord_4913573).sum := by decide
  have hdescent : baseEnd_4913573 < baseStart_4913573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4913573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4913620 : List Nat := [2, 4, 1, 2, 2, 1, 1, 3, 1, 3, 3]
def baseStart_4913620 : Nat := 118140960795 + 4913620 * 2 ^ 59
def prefixEnd_4913620 : Nat := 4983230072969 + 3 ^ 40 * 4913620 * 2
def baseEnd_4913620 : Nat := 2523048813545170672852679

theorem tailTrace_4913620 : CollatzResearch.WordTrace tailWord_4913620 prefixEnd_4913620 2523048813545170672852679 := by
  unfold tailWord_4913620
  simp only [CollatzResearch.WordTrace]
  refine ⟨89607222229400697165309157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119476296305867596220412209 89607222229400697165309157)
  ·
    refine ⟨16801354168012630718495467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89607222229400697165309157 16801354168012630718495467)
    ·
      refine ⟨25202031252018946077743201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16801354168012630718495467 25202031252018946077743201)
      ·
        refine ⟨18901523439014209558307401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25202031252018946077743201 18901523439014209558307401)
        ·
          refine ⟨14176142579260657168730551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18901523439014209558307401 14176142579260657168730551)
          ·
            refine ⟨21264213868890985753095827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14176142579260657168730551 21264213868890985753095827)
            ·
              refine ⟨31896320803336478629643741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21264213868890985753095827 31896320803336478629643741)
              ·
                refine ⟨11961120301251179486116403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31896320803336478629643741 11961120301251179486116403)
                ·
                  refine ⟨17941680451876769229174605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11961120301251179486116403 17941680451876769229174605)
                  ·
                    refine ⟨6728130169453788460940477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17941680451876769229174605 6728130169453788460940477)
                    ·
                      refine ⟨2523048813545170672852679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6728130169453788460940477 2523048813545170672852679)
                      ·
                        rfl

theorem cell23_4913620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_4913620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4913620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4913620 prefixEnd_4913620 := by exact prefixLift 4913620
  have htrace : WordTrace (prefixWord ++ tailWord_4913620) baseStart_4913620 baseEnd_4913620 := by
    simpa [prefixWord, tailWord_4913620, baseEnd_4913620] using wordTrace_append hprefix tailTrace_4913620
  have hstable : (prefixWord ++ tailWord_4913620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4913620).length < 2 ^ (prefixWord ++ tailWord_4913620).sum := by decide
  have hdescent : baseEnd_4913620 < baseStart_4913620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4913620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4913713 : List Nat := [1, 2, 2, 3, 1, 1, 3, 1, 4, 5]
def baseStart_4913713 : Nat := 118140960795 + 4913713 * 2 ^ 59
def prefixEnd_4913713 : Nat := 4983230072969 + 3 ^ 40 * 4913713 * 2
def baseEnd_4913713 : Nat := 841032189082012936329917

theorem tailTrace_4913713 : CollatzResearch.WordTrace tailWord_4913713 prefixEnd_4913713 841032189082012936329917 := by
  unfold tailWord_4913713
  simp only [CollatzResearch.WordTrace]
  refine ⟨179217836447464471213753793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119478557631642980809169195 179217836447464471213753793)
  ·
    refine ⟨134413377335598353410315345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179217836447464471213753793 134413377335598353410315345)
    ·
      refine ⟨100810033001698765057736509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134413377335598353410315345 100810033001698765057736509)
      ·
        refine ⟨37803762375637036896651191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100810033001698765057736509 37803762375637036896651191)
        ·
          refine ⟨56705643563455555344976787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37803762375637036896651191 56705643563455555344976787)
          ·
            refine ⟨85058465345183333017465181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56705643563455555344976787 85058465345183333017465181)
            ·
              refine ⟨31896924504443749881549443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85058465345183333017465181 31896924504443749881549443)
              ·
                refine ⟨47845386756665624822324165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31896924504443749881549443 47845386756665624822324165)
                ·
                  refine ⟨8971010016874804654185781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47845386756665624822324165 8971010016874804654185781)
                  ·
                    refine ⟨841032189082012936329917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8971010016874804654185781 841032189082012936329917)
                    ·
                      rfl

theorem cell23_4913713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 4, 5].length) (baseStart_4913713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4913713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4913713 prefixEnd_4913713 := by exact prefixLift 4913713
  have htrace : WordTrace (prefixWord ++ tailWord_4913713) baseStart_4913713 baseEnd_4913713 := by
    simpa [prefixWord, tailWord_4913713, baseEnd_4913713] using wordTrace_append hprefix tailTrace_4913713
  have hstable : (prefixWord ++ tailWord_4913713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4913713).length < 2 ^ (prefixWord ++ tailWord_4913713).sum := by decide
  have hdescent : baseEnd_4913713 < baseStart_4913713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4913713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4913717 : List Nat := [1, 3, 3, 1, 1, 2, 5, 2, 5]
def baseStart_4913717 : Nat := 118140960795 + 4913717 * 2 ^ 59
def prefixEnd_4913717 : Nat := 4983230072969 + 3 ^ 40 * 4913717 * 2
def baseEnd_4913717 : Nat := 280344291240961865926637

theorem tailTrace_4913717 : CollatzResearch.WordTrace tailWord_4913717 prefixEnd_4913717 280344291240961865926637 := by
  unfold tailWord_4913717
  simp only [CollatzResearch.WordTrace]
  refine ⟨179217982339449979896899405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119478654892966653264599603 179217982339449979896899405)
  ·
    refine ⟨67206743377293742461337277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179217982339449979896899405 67206743377293742461337277)
    ·
      refine ⟨25202528766485153423001479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67206743377293742461337277 25202528766485153423001479)
      ·
        refine ⟨37803793149727730134502219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25202528766485153423001479 37803793149727730134502219)
        ·
          refine ⟨56705689724591595201753329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37803793149727730134502219 56705689724591595201753329)
          ·
            refine ⟨42529267293443696401314997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56705689724591595201753329 42529267293443696401314997)
            ·
              refine ⟨3987118808760346537623281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42529267293443696401314997 3987118808760346537623281)
              ·
                refine ⟨2990339106570259903217461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3987118808760346537623281 2990339106570259903217461)
                ·
                  refine ⟨280344291240961865926637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2990339106570259903217461 280344291240961865926637)
                  ·
                    rfl

theorem cell23_4913717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 2, 5].length) (baseStart_4913717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4913717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4913717 prefixEnd_4913717 := by exact prefixLift 4913717
  have htrace : WordTrace (prefixWord ++ tailWord_4913717) baseStart_4913717 baseEnd_4913717 := by
    simpa [prefixWord, tailWord_4913717, baseEnd_4913717] using wordTrace_append hprefix tailTrace_4913717
  have hstable : (prefixWord ++ tailWord_4913717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4913717).length < 2 ^ (prefixWord ++ tailWord_4913717).sum := by decide
  have hdescent : baseEnd_4913717 < baseStart_4913717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4913717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4913720 : List Nat := [2, 1, 2, 1, 4, 1, 2, 1, 2, 5, 2]
def baseStart_4913720 : Nat := 118140960795 + 4913720 * 2 ^ 59
def prefixEnd_4913720 : Nat := 4983230072969 + 3 ^ 40 * 4913720 * 2
def baseEnd_4913720 : Nat := 2523100161610620281602219

theorem tailTrace_4913720 : CollatzResearch.WordTrace tailWord_4913720 prefixEnd_4913720 2523100161610620281602219 := by
  unfold tailWord_4913720
  simp only [CollatzResearch.WordTrace]
  refine ⟨89609045879219555704629307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119478727838959407606172409 89609045879219555704629307)
  ·
    refine ⟨134413568818829333556943961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89609045879219555704629307 134413568818829333556943961)
    ·
      refine ⟨100810176614122000167707971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134413568818829333556943961 100810176614122000167707971)
      ·
        refine ⟨151215264921183000251561957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100810176614122000167707971 151215264921183000251561957)
        ·
          refine ⟨28352862172721812547167867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 151215264921183000251561957 28352862172721812547167867)
          ·
            refine ⟨42529293259082718820751801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28352862172721812547167867 42529293259082718820751801)
            ·
              refine ⟨31896969944312039115563851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42529293259082718820751801 31896969944312039115563851)
              ·
                refine ⟨47845454916468058673345777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31896969944312039115563851 47845454916468058673345777)
                ·
                  refine ⟨35884091187351044005009333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47845454916468058673345777 35884091187351044005009333)
                  ·
                    refine ⟨3364133548814160375469625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35884091187351044005009333 3364133548814160375469625)
                    ·
                      refine ⟨2523100161610620281602219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3364133548814160375469625 2523100161610620281602219)
                      ·
                        rfl

theorem cell23_4913720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 2, 5, 2].length) (baseStart_4913720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4913720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4913720 prefixEnd_4913720 := by exact prefixLift 4913720
  have htrace : WordTrace (prefixWord ++ tailWord_4913720) baseStart_4913720 baseEnd_4913720 := by
    simpa [prefixWord, tailWord_4913720, baseEnd_4913720] using wordTrace_append hprefix tailTrace_4913720
  have hstable : (prefixWord ++ tailWord_4913720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4913720).length < 2 ^ (prefixWord ++ tailWord_4913720).sum := by decide
  have hdescent : baseEnd_4913720 < baseStart_4913720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4913720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4913763 : List Nat := [1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 6]
def baseStart_4913763 : Nat := 118140960795 + 4913763 * 2 ^ 59
def prefixEnd_4913763 : Nat := 4983230072969 + 3 ^ 40 * 4913763 * 2
def baseEnd_4913763 : Nat := 2523122241278763613364521

theorem tailTrace_4913763 : CollatzResearch.WordTrace tailWord_4913763 prefixEnd_4913763 2523122241278763613364521 := by
  unfold tailWord_4913763
  simp only [CollatzResearch.WordTrace]
  refine ⟨179219660097283329753073943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119479773398188886502049295 179219660097283329753073943)
  ·
    refine ⟨268829490145924994629610915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179219660097283329753073943 268829490145924994629610915)
    ·
      refine ⟨403244235218887491944416373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268829490145924994629610915 403244235218887491944416373)
      ·
        refine ⟨37804147051770702369789035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 403244235218887491944416373 37804147051770702369789035)
        ·
          refine ⟨56706220577656053554683553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37804147051770702369789035 56706220577656053554683553)
          ·
            refine ⟨42529665433242040166012665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56706220577656053554683553 42529665433242040166012665)
            ·
              refine ⟨31897249074931530124509499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42529665433242040166012665 31897249074931530124509499)
              ·
                refine ⟨47845873612397295186764249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31897249074931530124509499 47845873612397295186764249)
                ·
                  refine ⟨35884405209297971390073187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47845873612397295186764249 35884405209297971390073187)
                  ·
                    refine ⟨53826607813946957085109781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35884405209297971390073187 53826607813946957085109781)
                    ·
                      refine ⟨2523122241278763613364521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53826607813946957085109781 2523122241278763613364521)
                      ·
                        rfl

theorem cell23_4913763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_4913763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4913763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4913763 prefixEnd_4913763 := by exact prefixLift 4913763
  have htrace : WordTrace (prefixWord ++ tailWord_4913763) baseStart_4913763 baseEnd_4913763 := by
    simpa [prefixWord, tailWord_4913763, baseEnd_4913763] using wordTrace_append hprefix tailTrace_4913763
  have hstable : (prefixWord ++ tailWord_4913763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4913763).length < 2 ^ (prefixWord ++ tailWord_4913763).sum := by decide
  have hdescent : baseEnd_4913763 < baseStart_4913763 := by decide
  rcases family_descends (prefixWord ++ tailWord_4913763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4913813 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 1, 6, 5]
def baseStart_4913813 : Nat := 118140960795 + 4913813 * 2 ^ 59
def prefixEnd_4913813 : Nat := 4983230072969 + 3 ^ 40 * 4913813 * 2
def baseEnd_4913813 : Nat := 2523147915311488417739291

theorem tailTrace_4913813 : CollatzResearch.WordTrace tailWord_4913813 prefixEnd_4913813 2523147915311488417739291 := by
  unfold tailWord_4913813
  simp only [CollatzResearch.WordTrace]
  refine ⟨179221483747102188292394093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119480989164734792194929395 179221483747102188292394093)
  ·
    refine ⟨67208056405163320609647785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179221483747102188292394093 67208056405163320609647785)
    ·
      refine ⟨50406042303872490457235839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67208056405163320609647785 50406042303872490457235839)
      ·
        refine ⟨75609063455808735685853759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50406042303872490457235839 75609063455808735685853759)
        ·
          refine ⟨113413595183713103528780639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75609063455808735685853759 113413595183713103528780639)
          ·
            refine ⟨170120392775569655293170959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113413595183713103528780639 170120392775569655293170959)
            ·
              refine ⟨255180589163354482939756439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170120392775569655293170959 255180589163354482939756439)
              ·
                refine ⟨382770883745031724409634659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 255180589163354482939756439 382770883745031724409634659)
                ·
                  refine ⟨574156325617547586614451989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 382770883745031724409634659 574156325617547586614451989)
                  ·
                    refine ⟨26913577763322543122552437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 574156325617547586614451989 26913577763322543122552437)
                    ·
                      refine ⟨2523147915311488417739291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26913577763322543122552437 2523147915311488417739291)
                      ·
                        rfl

theorem cell23_4913813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_4913813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4913813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4913813 prefixEnd_4913813 := by exact prefixLift 4913813
  have htrace : WordTrace (prefixWord ++ tailWord_4913813) baseStart_4913813 baseEnd_4913813 := by
    simpa [prefixWord, tailWord_4913813, baseEnd_4913813] using wordTrace_append hprefix tailTrace_4913813
  have hstable : (prefixWord ++ tailWord_4913813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4913813).length < 2 ^ (prefixWord ++ tailWord_4913813).sum := by decide
  have hdescent : baseEnd_4913813 < baseStart_4913813 := by decide
  rcases family_descends (prefixWord ++ tailWord_4913813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4913824 : List Nat := [2, 1, 1, 4, 5, 1, 1, 2, 6]
def baseStart_4913824 : Nat := 118140960795 + 4913824 * 2 ^ 59
def prefixEnd_4913824 : Nat := 4983230072969 + 3 ^ 40 * 4913824 * 2
def baseEnd_4913824 : Nat := 280350395955409763855749

theorem tailTrace_4913824 : CollatzResearch.WordTrace tailWord_4913824 prefixEnd_4913824 280350395955409763855749 := by
  unfold tailWord_4913824
  simp only [CollatzResearch.WordTrace]
  refine ⟨89610942475031168585522263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119481256633374891447363017 89610942475031168585522263)
  ·
    refine ⟨134416413712546752878283395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89610942475031168585522263 134416413712546752878283395)
    ·
      refine ⟨201624620568820129317425093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134416413712546752878283395 201624620568820129317425093)
      ·
        refine ⟨37804616356653774247017205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 201624620568820129317425093 37804616356653774247017205)
        ·
          refine ⟨3544182783436291335657863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37804616356653774247017205 3544182783436291335657863)
          ·
            refine ⟨5316274175154437003486795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3544182783436291335657863 5316274175154437003486795)
            ·
              refine ⟨7974411262731655505230193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5316274175154437003486795 7974411262731655505230193)
              ·
                refine ⟨5980808447048741628922645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7974411262731655505230193 5980808447048741628922645)
                ·
                  refine ⟨280350395955409763855749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5980808447048741628922645 280350395955409763855749)
                  ·
                    rfl

theorem cell23_4913824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 2, 6].length) (baseStart_4913824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4913824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4913824 prefixEnd_4913824 := by exact prefixLift 4913824
  have htrace : WordTrace (prefixWord ++ tailWord_4913824) baseStart_4913824 baseEnd_4913824 := by
    simpa [prefixWord, tailWord_4913824, baseEnd_4913824] using wordTrace_append hprefix tailTrace_4913824
  have hstable : (prefixWord ++ tailWord_4913824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4913824).length < 2 ^ (prefixWord ++ tailWord_4913824).sum := by decide
  have hdescent : baseEnd_4913824 < baseStart_4913824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4913824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4913833 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 5, 6]
def baseStart_4913833 : Nat := 118140960795 + 4913833 * 2 ^ 59
def prefixEnd_4913833 : Nat := 4983230072969 + 3 ^ 40 * 4913833 * 2
def baseEnd_4913833 : Nat := 841052728308192779829733

theorem tailTrace_4913833 : CollatzResearch.WordTrace tailWord_4913833 prefixEnd_4913833 841052728308192779829733 := by
  unfold tailWord_4913833
  simp only [CollatzResearch.WordTrace]
  refine ⟨179222213207029731708122153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119481475471353154472081435 179222213207029731708122153)
  ·
    refine ⟨134416659905272298781091615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179222213207029731708122153 134416659905272298781091615)
    ·
      refine ⟨201624989857908448171637423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134416659905272298781091615 201624989857908448171637423)
      ·
        refine ⟨302437484786862672257456135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201624989857908448171637423 302437484786862672257456135)
        ·
          refine ⟨453656227180294008386184203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302437484786862672257456135 453656227180294008386184203)
          ·
            refine ⟨680484340770441012579276305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 453656227180294008386184203 680484340770441012579276305)
            ·
              refine ⟨510363255577830759434457229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 680484340770441012579276305 510363255577830759434457229)
              ·
                refine ⟨191386220841686534787921461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 510363255577830759434457229 191386220841686534787921461)
                ·
                  refine ⟨17942458203908112636367637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 191386220841686534787921461 17942458203908112636367637)
                  ·
                    refine ⟨841052728308192779829733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17942458203908112636367637 841052728308192779829733)
                    ·
                      rfl

theorem cell23_4913833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 6].length) (baseStart_4913833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4913833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4913833 prefixEnd_4913833 := by exact prefixLift 4913833
  have htrace : WordTrace (prefixWord ++ tailWord_4913833) baseStart_4913833 baseEnd_4913833 := by
    simpa [prefixWord, tailWord_4913833, baseEnd_4913833] using wordTrace_append hprefix tailTrace_4913833
  have hstable : (prefixWord ++ tailWord_4913833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4913833).length < 2 ^ (prefixWord ++ tailWord_4913833).sum := by decide
  have hdescent : baseEnd_4913833 < baseStart_4913833 := by decide
  rcases family_descends (prefixWord ++ tailWord_4913833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4913862 : List Nat := [6, 1, 2, 1, 3, 1, 1, 3, 1, 4]
def baseStart_4913862 : Nat := 118140960795 + 4913862 * 2 ^ 59
def prefixEnd_4913862 : Nat := 4983230072969 + 3 ^ 40 * 4913862 * 2
def baseEnd_4913862 : Nat := 841057691954519575342189

theorem tailTrace_4913862 : CollatzResearch.WordTrace tailWord_4913862 prefixEnd_4913862 841057691954519575342189 := by
  unfold tailWord_4913862
  simp only [CollatzResearch.WordTrace]
  refine ⟨5600727216372645926903995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 119482180615949779773951893 5600727216372645926903995)
  ·
    refine ⟨8401090824558968890355993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5600727216372645926903995 8401090824558968890355993)
    ·
      refine ⟨6300818118419226667766995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8401090824558968890355993 6300818118419226667766995)
      ·
        refine ⟨9451227177628840001650493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6300818118419226667766995 9451227177628840001650493)
        ·
          refine ⟨3544210191610815000618935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9451227177628840001650493 3544210191610815000618935)
          ·
            refine ⟨5316315287416222500928403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3544210191610815000618935 5316315287416222500928403)
            ·
              refine ⟨7974472931124333751392605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5316315287416222500928403 7974472931124333751392605)
              ·
                refine ⟨2990427349171625156772227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7974472931124333751392605 2990427349171625156772227)
                ·
                  refine ⟨4485641023757437735158341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2990427349171625156772227 4485641023757437735158341)
                  ·
                    refine ⟨841057691954519575342189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4485641023757437735158341 841057691954519575342189)
                    ·
                      rfl

theorem cell23_4913862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_4913862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4913862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4913862 prefixEnd_4913862 := by exact prefixLift 4913862
  have htrace : WordTrace (prefixWord ++ tailWord_4913862) baseStart_4913862 baseEnd_4913862 := by
    simpa [prefixWord, tailWord_4913862, baseEnd_4913862] using wordTrace_append hprefix tailTrace_4913862
  have hstable : (prefixWord ++ tailWord_4913862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4913862).length < 2 ^ (prefixWord ++ tailWord_4913862).sum := by decide
  have hdescent : baseEnd_4913862 < baseStart_4913862 := by decide
  rcases family_descends (prefixWord ++ tailWord_4913862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4913868 : List Nat := [2, 2, 1, 5, 1, 3, 1, 3, 1, 1, 3]
def baseStart_4913868 : Nat := 118140960795 + 4913868 * 2 ^ 59
def prefixEnd_4913868 : Nat := 4983230072969 + 3 ^ 40 * 4913868 * 2
def baseEnd_4913868 : Nat := 2523176156747485702551539

theorem tailTrace_4913868 : CollatzResearch.WordTrace tailWord_4913868 prefixEnd_4913868 2523176156747485702551539 := by
  unfold tailWord_4913868
  simp only [CollatzResearch.WordTrace]
  refine ⟨89611744880951466342823129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119482326507935288457097505 89611744880951466342823129)
  ·
    refine ⟨67208808660713599757117347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89611744880951466342823129 67208808660713599757117347)
    ·
      refine ⟨100813212991070399635676021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67208808660713599757117347 100813212991070399635676021)
      ·
        refine ⟨9451238717912849965844627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 100813212991070399635676021 9451238717912849965844627)
        ·
          refine ⟨14176858076869274948766941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9451238717912849965844627 14176858076869274948766941)
          ·
            refine ⟨5316321778825978105787603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14176858076869274948766941 5316321778825978105787603)
            ·
              refine ⟨7974482668238967158681405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5316321778825978105787603 7974482668238967158681405)
              ·
                refine ⟨2990431000589612684505527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7974482668238967158681405 2990431000589612684505527)
                ·
                  refine ⟨4485646500884419026758291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2990431000589612684505527 4485646500884419026758291)
                  ·
                    refine ⟨6728469751326628540137437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4485646500884419026758291 6728469751326628540137437)
                    ·
                      refine ⟨2523176156747485702551539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6728469751326628540137437 2523176156747485702551539)
                      ·
                        rfl

theorem cell23_4913868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_4913868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4913868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4913868 prefixEnd_4913868 := by exact prefixLift 4913868
  have htrace : WordTrace (prefixWord ++ tailWord_4913868) baseStart_4913868 baseEnd_4913868 := by
    simpa [prefixWord, tailWord_4913868, baseEnd_4913868] using wordTrace_append hprefix tailTrace_4913868
  have hstable : (prefixWord ++ tailWord_4913868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4913868).length < 2 ^ (prefixWord ++ tailWord_4913868).sum := by decide
  have hdescent : baseEnd_4913868 < baseStart_4913868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4913868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4913880 : List Nat := [2, 1, 2, 2, 3, 4, 9]
def baseStart_4913880 : Nat := 118140960795 + 4913880 * 2 ^ 59
def prefixEnd_4913880 : Nat := 4983230072969 + 3 ^ 40 * 4913880 * 2
def baseEnd_4913880 : Nat := 31150398994016538958043

theorem tailTrace_4913880 : CollatzResearch.WordTrace tailWord_4913880 prefixEnd_4913880 31150398994016538958043 := by
  unfold tailWord_4913880
  simp only [CollatzResearch.WordTrace]
  refine ⟨89611963718929729367541547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119482618291906305823388729 89611963718929729367541547)
  ·
    refine ⟨134417945578394594051312321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89611963718929729367541547 134417945578394594051312321)
    ·
      refine ⟨100813459183795945538484241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134417945578394594051312321 100813459183795945538484241)
      ·
        refine ⟨75610094387846959153863181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100813459183795945538484241 75610094387846959153863181)
        ·
          refine ⟨28353785395442609682698693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75610094387846959153863181 28353785395442609682698693)
          ·
            refine ⟨5316334761645489315506005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28353785395442609682698693 5316334761645489315506005)
            ·
              refine ⟨31150398994016538958043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5316334761645489315506005 31150398994016538958043)
              ·
                rfl

theorem cell23_4913880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 9].length) (baseStart_4913880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4913880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4913880 prefixEnd_4913880 := by exact prefixLift 4913880
  have htrace : WordTrace (prefixWord ++ tailWord_4913880) baseStart_4913880 baseEnd_4913880 := by
    simpa [prefixWord, tailWord_4913880, baseEnd_4913880] using wordTrace_append hprefix tailTrace_4913880
  have hstable : (prefixWord ++ tailWord_4913880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4913880).length < 2 ^ (prefixWord ++ tailWord_4913880).sum := by decide
  have hdescent : baseEnd_4913880 < baseStart_4913880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4913880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4913883 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 8]
def baseStart_4913883 : Nat := 118140960795 + 4913883 * 2 ^ 59
def prefixEnd_4913883 : Nat := 4983230072969 + 3 ^ 40 * 4913883 * 2
def baseEnd_4913883 : Nat := 2523183858957303143863969

theorem tailTrace_4913883 : CollatzResearch.WordTrace tailWord_4913883 prefixEnd_4913883 2523183858957303143863969 := by
  unfold tailWord_4913883
  simp only [CollatzResearch.WordTrace]
  refine ⟨179224036856848590247442303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119482691237899060164961535 179224036856848590247442303)
  ·
    refine ⟨268836055285272885371163455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179224036856848590247442303 268836055285272885371163455)
    ·
      refine ⟨403254082927909328056745183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268836055285272885371163455 403254082927909328056745183)
      ·
        refine ⟨604881124391863992085117775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 403254082927909328056745183 604881124391863992085117775)
        ·
          refine ⟨907321686587795988127676663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 604881124391863992085117775 907321686587795988127676663)
          ·
            refine ⟨1360982529881693982191514995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 907321686587795988127676663 1360982529881693982191514995)
            ·
              refine ⟨2041473794822540973287272493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1360982529881693982191514995 2041473794822540973287272493)
              ·
                refine ⟨765552673058452864982727185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2041473794822540973287272493 765552673058452864982727185)
                ·
                  refine ⟨574164504793839648737045389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 765552673058452864982727185 574164504793839648737045389)
                  ·
                    refine ⟨215311689297689868276392021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 574164504793839648737045389 215311689297689868276392021)
                    ·
                      refine ⟨2523183858957303143863969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 215311689297689868276392021 2523183858957303143863969)
                      ·
                        rfl

theorem cell23_4913883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 8].length) (baseStart_4913883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4913883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4913883 prefixEnd_4913883 := by exact prefixLift 4913883
  have htrace : WordTrace (prefixWord ++ tailWord_4913883) baseStart_4913883 baseEnd_4913883 := by
    simpa [prefixWord, tailWord_4913883, baseEnd_4913883] using wordTrace_append hprefix tailTrace_4913883
  have hstable : (prefixWord ++ tailWord_4913883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4913883).length < 2 ^ (prefixWord ++ tailWord_4913883).sum := by decide
  have hdescent : baseEnd_4913883 < baseStart_4913883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4913883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4913884 : List Nat := [2, 2, 5, 1, 1, 1, 2, 1, 4, 4]
def baseStart_4913884 : Nat := 118140960795 + 4913884 * 2 ^ 59
def prefixEnd_4913884 : Nat := 4983230072969 + 3 ^ 40 * 4913884 * 2
def baseEnd_4913884 : Nat := 841061457479319213317155

theorem tailTrace_4913884 : CollatzResearch.WordTrace tailWord_4913884 prefixEnd_4913884 841061457479319213317155 := by
  unfold tailWord_4913884
  simp only [CollatzResearch.WordTrace]
  refine ⟨89612036664922483709114353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119482715553229978278819137 89612036664922483709114353)
  ·
    refine ⟨67209027498691862781835765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89612036664922483709114353 67209027498691862781835765)
    ·
      refine ⟨6300846328002362135797103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67209027498691862781835765 6300846328002362135797103)
      ·
        refine ⟨9451269492003543203695655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6300846328002362135797103 9451269492003543203695655)
        ·
          refine ⟨14176904238005314805543483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9451269492003543203695655 14176904238005314805543483)
          ·
            refine ⟨21265356357007972208315225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14176904238005314805543483 21265356357007972208315225)
            ·
              refine ⟨15949017267755979156236419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21265356357007972208315225 15949017267755979156236419)
              ·
                refine ⟨23923525901633968734354629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15949017267755979156236419 23923525901633968734354629)
                ·
                  refine ⟨4485661106556369137691493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23923525901633968734354629 4485661106556369137691493)
                  ·
                    refine ⟨841061457479319213317155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4485661106556369137691493 841061457479319213317155)
                    ·
                      rfl

theorem cell23_4913884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_4913884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4913884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4913884 prefixEnd_4913884 := by exact prefixLift 4913884
  have htrace : WordTrace (prefixWord ++ tailWord_4913884) baseStart_4913884 baseEnd_4913884 := by
    simpa [prefixWord, tailWord_4913884, baseEnd_4913884] using wordTrace_append hprefix tailTrace_4913884
  have hstable : (prefixWord ++ tailWord_4913884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4913884).length < 2 ^ (prefixWord ++ tailWord_4913884).sum := by decide
  have hdescent : baseEnd_4913884 < baseStart_4913884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4913884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4913891 : List Nat := [1, 1, 1, 7, 1, 1, 3, 1, 3, 2, 2]
def baseStart_4913891 : Nat := 118140960795 + 4913891 * 2 ^ 59
def prefixEnd_4913891 : Nat := 4983230072969 + 3 ^ 40 * 4913891 * 2
def baseEnd_4913891 : Nat := 2523187966802539112563933

theorem tailTrace_4913891 : CollatzResearch.WordTrace tailWord_4913891 prefixEnd_4913891 2523187966802539112563933 := by
  unfold tailWord_4913891
  simp only [CollatzResearch.WordTrace]
  refine ⟨179224328640819607613733527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119482885760546405075822351 179224328640819607613733527)
  ·
    refine ⟨268836492961229411420600291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179224328640819607613733527 268836492961229411420600291)
    ·
      refine ⟨403254739441844117130900437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268836492961229411420600291 403254739441844117130900437)
      ·
        refine ⟨9451282955668221495255479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 403254739441844117130900437 9451282955668221495255479)
        ·
          refine ⟨14176924433502332242883219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9451282955668221495255479 14176924433502332242883219)
          ·
            refine ⟨21265386650253498364324829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14176924433502332242883219 21265386650253498364324829)
            ·
              refine ⟨7974519993845061886621811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21265386650253498364324829 7974519993845061886621811)
              ·
                refine ⟨11961779990767592829932717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7974519993845061886621811 11961779990767592829932717)
                ·
                  refine ⟨4485667496537847311224769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11961779990767592829932717 4485667496537847311224769)
                  ·
                    refine ⟨3364250622403385483418577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4485667496537847311224769 3364250622403385483418577)
                    ·
                      refine ⟨2523187966802539112563933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3364250622403385483418577 2523187966802539112563933)
                      ·
                        rfl

theorem cell23_4913891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_4913891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4913891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4913891 prefixEnd_4913891 := by exact prefixLift 4913891
  have htrace : WordTrace (prefixWord ++ tailWord_4913891) baseStart_4913891 baseEnd_4913891 := by
    simpa [prefixWord, tailWord_4913891, baseEnd_4913891] using wordTrace_append hprefix tailTrace_4913891
  have hstable : (prefixWord ++ tailWord_4913891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4913891).length < 2 ^ (prefixWord ++ tailWord_4913891).sum := by decide
  have hdescent : baseEnd_4913891 < baseStart_4913891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4913891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4913964 : List Nat := [2, 2, 1, 1, 1, 4, 4, 1, 1, 4, 2]
def baseStart_4913964 : Nat := 118140960795 + 4913964 * 2 ^ 59
def prefixEnd_4913964 : Nat := 4983230072969 + 3 ^ 40 * 4913964 * 2
def baseEnd_4913964 : Nat := 2523225450890317326951097

theorem tailTrace_4913964 : CollatzResearch.WordTrace tailWord_4913964 prefixEnd_4913964 2523225450890317326951097 := by
  unfold tailWord_4913964
  simp only [CollatzResearch.WordTrace]
  refine ⟨89613495584777570540570473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119484660779703427387427297 89613495584777570540570473)
  ·
    refine ⟨67210121688583177905427855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89613495584777570540570473 67210121688583177905427855)
    ·
      refine ⟨100815182532874766858141783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67210121688583177905427855 100815182532874766858141783)
      ·
        refine ⟨151222773799312150287212675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100815182532874766858141783 151222773799312150287212675)
        ·
          refine ⟨226834160698968225430819013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151222773799312150287212675 226834160698968225430819013)
          ·
            refine ⟨42531405131056542268278565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 226834160698968225430819013 42531405131056542268278565)
            ·
              refine ⟨7974638462073101675302231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42531405131056542268278565 7974638462073101675302231)
              ·
                refine ⟨11961957693109652512953347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7974638462073101675302231 11961957693109652512953347)
                ·
                  refine ⟨17942936539664478769430021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11961957693109652512953347 17942936539664478769430021)
                  ·
                    refine ⟨3364300601187089769268129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17942936539664478769430021 3364300601187089769268129)
                    ·
                      refine ⟨2523225450890317326951097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3364300601187089769268129 2523225450890317326951097)
                      ·
                        rfl

theorem cell23_4913964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 4, 2].length) (baseStart_4913964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4913964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4913964 prefixEnd_4913964 := by exact prefixLift 4913964
  have htrace : WordTrace (prefixWord ++ tailWord_4913964) baseStart_4913964 baseEnd_4913964 := by
    simpa [prefixWord, tailWord_4913964, baseEnd_4913964] using wordTrace_append hprefix tailTrace_4913964
  have hstable : (prefixWord ++ tailWord_4913964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4913964).length < 2 ^ (prefixWord ++ tailWord_4913964).sum := by decide
  have hdescent : baseEnd_4913964 < baseStart_4913964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4913964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4913980 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 1, 2, 7]
def baseStart_4913980 : Nat := 118140960795 + 4913980 * 2 ^ 59
def prefixEnd_4913980 : Nat := 4983230072969 + 3 ^ 40 * 4913980 * 2
def baseEnd_4913980 : Nat := 2523233666580789264351023

theorem tailTrace_4913980 : CollatzResearch.WordTrace tailWord_4913980 prefixEnd_4913980 2523233666580789264351023 := by
  unfold tailWord_4913980
  simp only [CollatzResearch.WordTrace]
  refine ⟨89613787368748587906861697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119485049824998117209148929 89613787368748587906861697)
  ·
    refine ⟨67210340526561440930146273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89613787368748587906861697 67210340526561440930146273)
    ·
      refine ⟨50407755394921080697609705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67210340526561440930146273 50407755394921080697609705)
      ·
        refine ⟨37805816546190810523207279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50407755394921080697609705 37805816546190810523207279)
        ·
          refine ⟨56708724819286215784810919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37805816546190810523207279 56708724819286215784810919)
          ·
            refine ⟨85063087228929323677216379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56708724819286215784810919 85063087228929323677216379)
            ·
              refine ⟨127594630843393985515824569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85063087228929323677216379 127594630843393985515824569)
              ·
                refine ⟨95695973132545489136868427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127594630843393985515824569 95695973132545489136868427)
                ·
                  refine ⟨143543959698818233705302641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95695973132545489136868427 143543959698818233705302641)
                  ·
                    refine ⟨107657969774113675278976981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 143543959698818233705302641 107657969774113675278976981)
                    ·
                      refine ⟨2523233666580789264351023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 107657969774113675278976981 2523233666580789264351023)
                      ·
                        rfl

theorem cell23_4913980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_4913980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4913980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4913980 prefixEnd_4913980 := by exact prefixLift 4913980
  have htrace : WordTrace (prefixWord ++ tailWord_4913980) baseStart_4913980 baseEnd_4913980 := by
    simpa [prefixWord, tailWord_4913980, baseEnd_4913980] using wordTrace_append hprefix tailTrace_4913980
  have hstable : (prefixWord ++ tailWord_4913980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4913980).length < 2 ^ (prefixWord ++ tailWord_4913980).sum := by decide
  have hdescent : baseEnd_4913980 < baseStart_4913980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4913980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914004 : List Nat := [2, 4, 1, 1, 4, 1, 2, 1, 7]
def baseStart_4914004 : Nat := 118140960795 + 4914004 * 2 ^ 59
def prefixEnd_4914004 : Nat := 4983230072969 + 3 ^ 40 * 4914004 * 2
def baseEnd_4914004 : Nat := 280360665568499685605657

theorem tailTrace_4914004 : CollatzResearch.WordTrace tailWord_4914004 prefixEnd_4914004 280360665568499685605657 := by
  unfold tailWord_4914004
  simp only [CollatzResearch.WordTrace]
  refine ⟨89614225044705113956298533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119485633392940151941731377 89614225044705113956298533)
  ·
    refine ⟨16802667195882208866805975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89614225044705113956298533 16802667195882208866805975)
    ·
      refine ⟨25204000793823313300208963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16802667195882208866805975 25204000793823313300208963)
      ·
        refine ⟨37806001190734969950313445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25204000793823313300208963 37806001190734969950313445)
        ·
          refine ⟨7088625223262806865683771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37806001190734969950313445 7088625223262806865683771)
          ·
            refine ⟨10632937834894210298525657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7088625223262806865683771 10632937834894210298525657)
            ·
              refine ⟨7974703376170657723894243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10632937834894210298525657 7974703376170657723894243)
              ·
                refine ⟨11962055064255986585841365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7974703376170657723894243 11962055064255986585841365)
                ·
                  refine ⟨280360665568499685605657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11962055064255986585841365 280360665568499685605657)
                  ·
                    rfl

theorem cell23_4914004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_4914004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914004 prefixEnd_4914004 := by exact prefixLift 4914004
  have htrace : WordTrace (prefixWord ++ tailWord_4914004) baseStart_4914004 baseEnd_4914004 := by
    simpa [prefixWord, tailWord_4914004, baseEnd_4914004] using wordTrace_append hprefix tailTrace_4914004
  have hstable : (prefixWord ++ tailWord_4914004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914004).length < 2 ^ (prefixWord ++ tailWord_4914004).sum := by decide
  have hdescent : baseEnd_4914004 < baseStart_4914004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914038 : List Nat := [5, 1, 1, 3, 1, 3, 1, 3, 5]
def baseStart_4914038 : Nat := 118140960795 + 4914038 * 2 ^ 59
def prefixEnd_4914038 : Nat := 4983230072969 + 3 ^ 40 * 4914038 * 2
def baseEnd_4914038 : Nat := 280362605384305559713973

theorem tailTrace_4914038 : CollatzResearch.WordTrace tailWord_4914038 prefixEnd_4914038 280362605384305559713973 := by
  unfold tailWord_4914038
  simp only [CollatzResearch.WordTrace]
  refine ⟨11201855635705440732458423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 119486460114191367812889845 11201855635705440732458423)
  ·
    refine ⟨16802783453558161098687635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11201855635705440732458423 16802783453558161098687635)
    ·
      refine ⟨25204175180337241648031453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16802783453558161098687635 25204175180337241648031453)
      ·
        refine ⟨9451565692626465618011795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25204175180337241648031453 9451565692626465618011795)
        ·
          refine ⟨14177348538939698427017693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9451565692626465618011795 14177348538939698427017693)
          ·
            refine ⟨5316505702102386910131635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14177348538939698427017693 5316505702102386910131635)
            ·
              refine ⟨7974758553153580365197453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5316505702102386910131635 7974758553153580365197453)
              ·
                refine ⟨2990534457432592636949045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7974758553153580365197453 2990534457432592636949045)
                ·
                  refine ⟨280362605384305559713973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2990534457432592636949045 280362605384305559713973)
                  ·
                    rfl

theorem cell23_4914038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_4914038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914038 prefixEnd_4914038 := by exact prefixLift 4914038
  have htrace : WordTrace (prefixWord ++ tailWord_4914038) baseStart_4914038 baseEnd_4914038 := by
    simpa [prefixWord, tailWord_4914038, baseEnd_4914038] using wordTrace_append hprefix tailTrace_4914038
  have hstable : (prefixWord ++ tailWord_4914038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914038).length < 2 ^ (prefixWord ++ tailWord_4914038).sum := by decide
  have hdescent : baseEnd_4914038 < baseStart_4914038 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914047 : List Nat := [1, 1, 2, 2, 1, 1, 4, 2, 5, 4]
def baseStart_4914047 : Nat := 118140960795 + 4914047 * 2 ^ 59
def prefixEnd_4914047 : Nat := 4983230072969 + 3 ^ 40 * 4914047 * 2
def baseEnd_4914047 : Nat := 841089356594880167404405

theorem tailTrace_4914047 : CollatzResearch.WordTrace tailWord_4914047 prefixEnd_4914047 841089356594880167404405 := by
  unfold tailWord_4914047
  simp only [CollatzResearch.WordTrace]
  refine ⟨179230018428254446256412395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119486678952169630837608263 179230018428254446256412395)
  ·
    refine ⟨268845027642381669384618593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179230018428254446256412395 268845027642381669384618593)
    ·
      refine ⟨201633770731786252038463945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268845027642381669384618593 201633770731786252038463945)
      ·
        refine ⟨151225328048839689028847959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201633770731786252038463945 151225328048839689028847959)
        ·
          refine ⟨226837992073259533543271939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151225328048839689028847959 226837992073259533543271939)
          ·
            refine ⟨340256988109889300314907909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226837992073259533543271939 340256988109889300314907909)
            ·
              refine ⟨63798185270604243809045233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 340256988109889300314907909 63798185270604243809045233)
              ·
                refine ⟨47848638952953182856783925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63798185270604243809045233 47848638952953182856783925)
                ·
                  refine ⟨4485809901839360892823493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47848638952953182856783925 4485809901839360892823493)
                  ·
                    refine ⟨841089356594880167404405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4485809901839360892823493 841089356594880167404405)
                    ·
                      rfl

theorem cell23_4914047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 5, 4].length) (baseStart_4914047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914047 prefixEnd_4914047 := by exact prefixLift 4914047
  have htrace : WordTrace (prefixWord ++ tailWord_4914047) baseStart_4914047 baseEnd_4914047 := by
    simpa [prefixWord, tailWord_4914047, baseEnd_4914047] using wordTrace_append hprefix tailTrace_4914047
  have hstable : (prefixWord ++ tailWord_4914047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914047).length < 2 ^ (prefixWord ++ tailWord_4914047).sum := by decide
  have hdescent : baseEnd_4914047 < baseStart_4914047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914154 : List Nat := [3, 1, 3, 1, 2, 2, 2, 2, 1, 6]
def baseStart_4914154 : Nat := 118140960795 + 4914154 * 2 ^ 59
def prefixEnd_4914154 : Nat := 4983230072969 + 3 ^ 40 * 4914154 * 2
def baseEnd_4914154 : Nat := 841107670738223861191741

theorem tailTrace_4914154 : CollatzResearch.WordTrace tailWord_4914154 prefixEnd_4914154 841107670738223861191741 := by
  unfold tailWord_4914154
  simp only [CollatzResearch.WordTrace]
  refine ⟨44808480259716700882639379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119489280692577869020371677 44808480259716700882639379)
  ·
    refine ⟨67212720389575051323959069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44808480259716700882639379 67212720389575051323959069)
    ·
      refine ⟨25204770146090644246484651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67212720389575051323959069 25204770146090644246484651)
      ·
        refine ⟨37807155219135966369726977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25204770146090644246484651 37807155219135966369726977)
        ·
          refine ⟨28355366414351974777295233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37807155219135966369726977 28355366414351974777295233)
          ·
            refine ⟨21266524810763981082971425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28355366414351974777295233 21266524810763981082971425)
            ·
              refine ⟨15949893608072985812228569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21266524810763981082971425 15949893608072985812228569)
              ·
                refine ⟨11962420206054739359171427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15949893608072985812228569 11962420206054739359171427)
                ·
                  refine ⟨17943630309082109038757141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11962420206054739359171427 17943630309082109038757141)
                  ·
                    refine ⟨841107670738223861191741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17943630309082109038757141 841107670738223861191741)
                    ·
                      rfl

theorem cell23_4914154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_4914154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914154 prefixEnd_4914154 := by exact prefixLift 4914154
  have htrace : WordTrace (prefixWord ++ tailWord_4914154) baseStart_4914154 baseEnd_4914154 := by
    simpa [prefixWord, tailWord_4914154, baseEnd_4914154] using wordTrace_append hprefix tailTrace_4914154
  have hstable : (prefixWord ++ tailWord_4914154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914154).length < 2 ^ (prefixWord ++ tailWord_4914154).sum := by decide
  have hdescent : baseEnd_4914154 < baseStart_4914154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914161 : List Nat := [1, 2, 2, 2, 4, 2, 1, 3, 1, 1, 4]
def baseStart_4914161 : Nat := 118140960795 + 4914161 * 2 ^ 59
def prefixEnd_4914161 : Nat := 4983230072969 + 3 ^ 40 * 4914161 * 2
def baseEnd_4914161 : Nat := 2523326606579253056187691

theorem tailTrace_4914161 : CollatzResearch.WordTrace tailWord_4914161 prefixEnd_4914161 2523326606579253056187691 := by
  unfold tailWord_4914161
  simp only [CollatzResearch.WordTrace]
  refine ⟨179234176349841443726062337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119489450899894295817374891 179234176349841443726062337)
  ·
    refine ⟨134425632262381082794546753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179234176349841443726062337 134425632262381082794546753)
    ·
      refine ⟨100819224196785812095910065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134425632262381082794546753 100819224196785812095910065)
      ·
        refine ⟨75614418147589359071932549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100819224196785812095910065 75614418147589359071932549)
        ·
          refine ⟨14177703402673004825987353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75614418147589359071932549 14177703402673004825987353)
          ·
            refine ⟨10633277552004753619490515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14177703402673004825987353 10633277552004753619490515)
            ·
              refine ⟨15949916328007130429235773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10633277552004753619490515 15949916328007130429235773)
              ·
                refine ⟨5981218623002673910963415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15949916328007130429235773 5981218623002673910963415)
                ·
                  refine ⟨8971827934504010866445123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5981218623002673910963415 8971827934504010866445123)
                  ·
                    refine ⟨13457741901756016299667685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8971827934504010866445123 13457741901756016299667685)
                    ·
                      refine ⟨2523326606579253056187691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13457741901756016299667685 2523326606579253056187691)
                      ·
                        rfl

theorem cell23_4914161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 3, 1, 1, 4].length) (baseStart_4914161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914161 prefixEnd_4914161 := by exact prefixLift 4914161
  have htrace : WordTrace (prefixWord ++ tailWord_4914161) baseStart_4914161 baseEnd_4914161 := by
    simpa [prefixWord, tailWord_4914161, baseEnd_4914161] using wordTrace_append hprefix tailTrace_4914161
  have hstable : (prefixWord ++ tailWord_4914161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914161).length < 2 ^ (prefixWord ++ tailWord_4914161).sum := by decide
  have hdescent : baseEnd_4914161 < baseStart_4914161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914188 : List Nat := [2, 2, 1, 2, 3, 3, 3, 1, 2, 4]
def baseStart_4914188 : Nat := 118140960795 + 4914188 * 2 ^ 59
def prefixEnd_4914188 : Nat := 4983230072969 + 3 ^ 40 * 4914188 * 2
def baseEnd_4914188 : Nat := 841113490185641483516689

theorem tailTrace_4914188 : CollatzResearch.WordTrace tailWord_4914188 prefixEnd_4914188 841113490185641483516689 := by
  unfold tailWord_4914188
  simp only [CollatzResearch.WordTrace]
  refine ⟨89617580560371813668647609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119490107413829084891530145 89617580560371813668647609)
  ·
    refine ⟨67213185420278860251485707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89617580560371813668647609 67213185420278860251485707)
    ·
      refine ⟨100819778130418290377228561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67213185420278860251485707 100819778130418290377228561)
      ·
        refine ⟨75614833597813717782921421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100819778130418290377228561 75614833597813717782921421)
        ·
          refine ⟨28355562599180144168595533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75614833597813717782921421 28355562599180144168595533)
          ·
            refine ⟨10633335974692554063223325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28355562599180144168595533 10633335974692554063223325)
            ·
              refine ⟨3987500990509707773708747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10633335974692554063223325 3987500990509707773708747)
              ·
                refine ⟨5981251485764561660563121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3987500990509707773708747 5981251485764561660563121)
                ·
                  refine ⟨4485938614323421245422341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5981251485764561660563121 4485938614323421245422341)
                  ·
                    refine ⟨841113490185641483516689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4485938614323421245422341 841113490185641483516689)
                    ·
                      rfl

theorem cell23_4914188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 1, 2, 4].length) (baseStart_4914188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914188 prefixEnd_4914188 := by exact prefixLift 4914188
  have htrace : WordTrace (prefixWord ++ tailWord_4914188) baseStart_4914188 baseEnd_4914188 := by
    simpa [prefixWord, tailWord_4914188, baseEnd_4914188] using wordTrace_append hprefix tailTrace_4914188
  have hstable : (prefixWord ++ tailWord_4914188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914188).length < 2 ^ (prefixWord ++ tailWord_4914188).sum := by decide
  have hdescent : baseEnd_4914188 < baseStart_4914188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914211 : List Nat := [1, 1, 1, 4, 3, 2, 1, 2, 4, 1, 3]
def baseStart_4914211 : Nat := 118140960795 + 4914211 * 2 ^ 59
def prefixEnd_4914211 : Nat := 4983230072969 + 3 ^ 40 * 4914211 * 2
def baseEnd_4914211 : Nat := 2523352280611977860562461

theorem tailTrace_4914211 : CollatzResearch.WordTrace tailWord_4914211 prefixEnd_4914211 2523352280611977860562461 := by
  unfold tailWord_4914211
  simp only [CollatzResearch.WordTrace]
  refine ⟨179235999999660302265382487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119490666666440201510254991 179235999999660302265382487)
  ·
    refine ⟨268853999999490453398073731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179235999999660302265382487 268853999999490453398073731)
    ·
      refine ⟨403280999999235680097110597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268853999999490453398073731 403280999999235680097110597)
      ·
        refine ⟨75615187499856690018208237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 403280999999235680097110597 75615187499856690018208237)
        ·
          refine ⟨28355695312446258756828089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75615187499856690018208237 28355695312446258756828089)
          ·
            refine ⟨21266771484334694067621067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28355695312446258756828089 21266771484334694067621067)
            ·
              refine ⟨31900157226502041101431601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21266771484334694067621067 31900157226502041101431601)
              ·
                refine ⟨23925117919876530826073701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31900157226502041101431601 23925117919876530826073701)
                ·
                  refine ⟨4485959609976849529888819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23925117919876530826073701 4485959609976849529888819)
                  ·
                    refine ⟨6728939414965274294833229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4485959609976849529888819 6728939414965274294833229)
                    ·
                      refine ⟨2523352280611977860562461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6728939414965274294833229 2523352280611977860562461)
                      ·
                        rfl

theorem cell23_4914211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 4, 1, 3].length) (baseStart_4914211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914211 prefixEnd_4914211 := by exact prefixLift 4914211
  have htrace : WordTrace (prefixWord ++ tailWord_4914211) baseStart_4914211 baseEnd_4914211 := by
    simpa [prefixWord, tailWord_4914211, baseEnd_4914211] using wordTrace_append hprefix tailTrace_4914211
  have hstable : (prefixWord ++ tailWord_4914211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914211).length < 2 ^ (prefixWord ++ tailWord_4914211).sum := by decide
  have hdescent : baseEnd_4914211 < baseStart_4914211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914212 : List Nat := [2, 3, 1, 4, 1, 1, 3, 3, 1, 2, 2]
def baseStart_4914212 : Nat := 118140960795 + 4914212 * 2 ^ 59
def prefixEnd_4914212 : Nat := 4983230072969 + 3 ^ 40 * 4914212 * 2
def baseEnd_4914212 : Nat := 2523352794092632356649957

theorem tailTrace_4914212 : CollatzResearch.WordTrace tailWord_4914212 prefixEnd_4914212 2523352794092632356649957 := by
  unfold tailWord_4914212
  simp only [CollatzResearch.WordTrace]
  refine ⟨89618018236328339718084445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119490690981771119624112593 89618018236328339718084445)
  ·
    refine ⟨33606756838623127394281667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89618018236328339718084445 33606756838623127394281667)
    ·
      refine ⟨50410135257934691091422501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33606756838623127394281667 50410135257934691091422501)
      ·
        refine ⟨9451900360862754579641719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50410135257934691091422501 9451900360862754579641719)
        ·
          refine ⟨14177850541294131869462579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9451900360862754579641719 14177850541294131869462579)
          ·
            refine ⟨21266775811941197804193869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14177850541294131869462579 21266775811941197804193869)
            ·
              refine ⟨7975040929477949176572701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21266775811941197804193869 7975040929477949176572701)
              ·
                refine ⟨2990640348554230941214763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7975040929477949176572701 2990640348554230941214763)
                ·
                  refine ⟨4485960522831346411822145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2990640348554230941214763 4485960522831346411822145)
                  ·
                    refine ⟨3364470392123509808866609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4485960522831346411822145 3364470392123509808866609)
                    ·
                      refine ⟨2523352794092632356649957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3364470392123509808866609 2523352794092632356649957)
                      ·
                        rfl

theorem cell23_4914212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_4914212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914212 prefixEnd_4914212 := by exact prefixLift 4914212
  have htrace : WordTrace (prefixWord ++ tailWord_4914212) baseStart_4914212 baseEnd_4914212 := by
    simpa [prefixWord, tailWord_4914212, baseEnd_4914212] using wordTrace_append hprefix tailTrace_4914212
  have hstable : (prefixWord ++ tailWord_4914212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914212).length < 2 ^ (prefixWord ++ tailWord_4914212).sum := by decide
  have hdescent : baseEnd_4914212 < baseStart_4914212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914254 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 4, 1, 5]
def baseStart_4914254 : Nat := 118140960795 + 4914254 * 2 ^ 59
def prefixEnd_4914254 : Nat := 4983230072969 + 3 ^ 40 * 4914254 * 2
def baseEnd_4914254 : Nat := 2523374360280121192324763

theorem tailTrace_4914254 : CollatzResearch.WordTrace tailWord_4914254 prefixEnd_4914254 2523374360280121192324763 := by
  unfold tailWord_4914254
  simp only [CollatzResearch.WordTrace]
  refine ⟨22404696042313065076149727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119491712225669680406131877 22404696042313065076149727)
  ·
    refine ⟨33607044063469597614224591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22404696042313065076149727 33607044063469597614224591)
    ·
      refine ⟨50410566095204396421336887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33607044063469597614224591 50410566095204396421336887)
      ·
        refine ⟨75615849142806594632005331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50410566095204396421336887 75615849142806594632005331)
        ·
          refine ⟨113423773714209891948007997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75615849142806594632005331 113423773714209891948007997)
          ·
            refine ⟨42533915142828709480502999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113423773714209891948007997 42533915142828709480502999)
            ·
              refine ⟨63800872714243064220754499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42533915142828709480502999 63800872714243064220754499)
              ·
                refine ⟨95701309071364596331131749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63800872714243064220754499 95701309071364596331131749)
                ·
                  refine ⟨17943995450880861812087203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95701309071364596331131749 17943995450880861812087203)
                  ·
                    refine ⟨26915993176321292718130805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17943995450880861812087203 26915993176321292718130805)
                    ·
                      refine ⟨2523374360280121192324763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26915993176321292718130805 2523374360280121192324763)
                      ·
                        rfl

theorem cell23_4914254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_4914254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914254 prefixEnd_4914254 := by exact prefixLift 4914254
  have htrace : WordTrace (prefixWord ++ tailWord_4914254) baseStart_4914254 baseEnd_4914254 := by
    simpa [prefixWord, tailWord_4914254, baseEnd_4914254] using wordTrace_append hprefix tailTrace_4914254
  have hstable : (prefixWord ++ tailWord_4914254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914254).length < 2 ^ (prefixWord ++ tailWord_4914254).sum := by decide
  have hdescent : baseEnd_4914254 < baseStart_4914254 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914268 : List Nat := [2, 2, 4, 1, 1, 1, 3, 2, 1, 4, 2]
def baseStart_4914268 : Nat := 118140960795 + 4914268 * 2 ^ 59
def prefixEnd_4914268 : Nat := 4983230072969 + 3 ^ 40 * 4914268 * 2
def baseEnd_4914268 : Nat := 2523381549009284137549699

theorem tailTrace_4914268 : CollatzResearch.WordTrace tailWord_4914268 prefixEnd_4914268 2523381549009284137549699 := by
  unfold tailWord_4914268
  simp only [CollatzResearch.WordTrace]
  refine ⟨89619039480226900500103729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119492052640302534000138305 89619039480226900500103729)
  ·
    refine ⟨67214279610170175375077797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89619039480226900500103729 67214279610170175375077797)
    ·
      refine ⟨12602677426906907882827087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67214279610170175375077797 12602677426906907882827087)
      ·
        refine ⟨18904016140360361824240631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12602677426906907882827087 18904016140360361824240631)
        ·
          refine ⟨28356024210540542736360947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18904016140360361824240631 28356024210540542736360947)
          ·
            refine ⟨42534036315810814104541421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28356024210540542736360947 42534036315810814104541421)
            ·
              refine ⟨15950263618429055289203033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42534036315810814104541421 15950263618429055289203033)
              ·
                refine ⟨11962697713821791466902275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15950263618429055289203033 11962697713821791466902275)
                ·
                  refine ⟨17944046570732687200353413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11962697713821791466902275 17944046570732687200353413)
                  ·
                    refine ⟨3364508732012378850066265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17944046570732687200353413 3364508732012378850066265)
                    ·
                      refine ⟨2523381549009284137549699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3364508732012378850066265 2523381549009284137549699)
                      ·
                        rfl

theorem cell23_4914268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_4914268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914268 prefixEnd_4914268 := by exact prefixLift 4914268
  have htrace : WordTrace (prefixWord ++ tailWord_4914268) baseStart_4914268 baseEnd_4914268 := by
    simpa [prefixWord, tailWord_4914268, baseEnd_4914268] using wordTrace_append hprefix tailTrace_4914268
  have hstable : (prefixWord ++ tailWord_4914268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914268).length < 2 ^ (prefixWord ++ tailWord_4914268).sum := by decide
  have hdescent : baseEnd_4914268 < baseStart_4914268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914285 : List Nat := [1, 5, 1, 1, 2, 2, 1, 4, 2, 2, 2]
def baseStart_4914285 : Nat := 118140960795 + 4914285 * 2 ^ 59
def prefixEnd_4914285 : Nat := 4983230072969 + 3 ^ 40 * 4914285 * 2
def baseEnd_4914285 : Nat := 2523390278180410571037121

theorem tailTrace_4914285 : CollatzResearch.WordTrace tailWord_4914285 prefixEnd_4914285 2523390278180410571037121 := by
  unfold tailWord_4914285
  simp only [CollatzResearch.WordTrace]
  refine ⟨179238699001392212903576309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119492466000928141935717539 179238699001392212903576309)
  ·
    refine ⟨16803628031380519959710279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 179238699001392212903576309 16803628031380519959710279)
    ·
      refine ⟨25205442047070779939565419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16803628031380519959710279 25205442047070779939565419)
      ·
        refine ⟨37808163070606169909348129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25205442047070779939565419 37808163070606169909348129)
        ·
          refine ⟨28356122302954627432011097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37808163070606169909348129 28356122302954627432011097)
          ·
            refine ⟨21267091727215970574008323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28356122302954627432011097 21267091727215970574008323)
            ·
              refine ⟨31900637590823955861012485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21267091727215970574008323 31900637590823955861012485)
              ·
                refine ⟨5981369548279491723939841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31900637590823955861012485 5981369548279491723939841)
                ·
                  refine ⟨4486027161209618792954881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5981369548279491723939841 4486027161209618792954881)
                  ·
                    refine ⟨3364520370907214094716161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4486027161209618792954881 3364520370907214094716161)
                    ·
                      refine ⟨2523390278180410571037121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3364520370907214094716161 2523390278180410571037121)
                      ·
                        rfl

theorem cell23_4914285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 4, 2, 2, 2].length) (baseStart_4914285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914285 prefixEnd_4914285 := by exact prefixLift 4914285
  have htrace : WordTrace (prefixWord ++ tailWord_4914285) baseStart_4914285 baseEnd_4914285 := by
    simpa [prefixWord, tailWord_4914285, baseEnd_4914285] using wordTrace_append hprefix tailTrace_4914285
  have hstable : (prefixWord ++ tailWord_4914285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914285).length < 2 ^ (prefixWord ++ tailWord_4914285).sum := by decide
  have hdescent : baseEnd_4914285 < baseStart_4914285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914301 : List Nat := [1, 4, 1, 1, 3, 1, 3, 1, 2, 3, 3]
def baseStart_4914301 : Nat := 118140960795 + 4914301 * 2 ^ 59
def prefixEnd_4914301 : Nat := 4983230072969 + 3 ^ 40 * 4914301 * 2
def baseEnd_4914301 : Nat := 2523398493870882508437047

theorem tailTrace_4914301 : CollatzResearch.WordTrace tailWord_4914301 prefixEnd_4914301 2523398493870882508437047 := by
  unfold tailWord_4914301
  simp only [CollatzResearch.WordTrace]
  refine ⟨179239282569334247636158757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119492855046222831757439171 179239282569334247636158757)
  ·
    refine ⟨33607365481750171431779767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 179239282569334247636158757 33607365481750171431779767)
    ·
      refine ⟨50411048222625257147669651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33607365481750171431779767 50411048222625257147669651)
      ·
        refine ⟨75616572333937885721504477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50411048222625257147669651 75616572333937885721504477)
        ·
          refine ⟨28356214625226707145564179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75616572333937885721504477 28356214625226707145564179)
          ·
            refine ⟨42534321937840060718346269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28356214625226707145564179 42534321937840060718346269)
            ·
              refine ⟨15950370726690022769379851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42534321937840060718346269 15950370726690022769379851)
              ·
                refine ⟨23925556090035034154069777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15950370726690022769379851 23925556090035034154069777)
                ·
                  refine ⟨17944167067526275615552333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23925556090035034154069777 17944167067526275615552333)
                  ·
                    refine ⟨6729062650322353355832125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17944167067526275615552333 6729062650322353355832125)
                    ·
                      refine ⟨2523398493870882508437047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6729062650322353355832125 2523398493870882508437047)
                      ·
                        rfl

theorem cell23_4914301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 3, 3].length) (baseStart_4914301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914301 prefixEnd_4914301 := by exact prefixLift 4914301
  have htrace : WordTrace (prefixWord ++ tailWord_4914301) baseStart_4914301 baseEnd_4914301 := by
    simpa [prefixWord, tailWord_4914301, baseEnd_4914301] using wordTrace_append hprefix tailTrace_4914301
  have hstable : (prefixWord ++ tailWord_4914301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914301).length < 2 ^ (prefixWord ++ tailWord_4914301).sum := by decide
  have hdescent : baseEnd_4914301 < baseStart_4914301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914304 : List Nat := [2, 1, 1, 2, 1, 3, 2, 2, 4, 5]
def baseStart_4914304 : Nat := 118140960795 + 4914304 * 2 ^ 59
def prefixEnd_4914304 : Nat := 4983230072969 + 3 ^ 40 * 4914304 * 2
def baseEnd_4914304 : Nat := 841133344770948665566511

theorem tailTrace_4914304 : CollatzResearch.WordTrace tailWord_4914304 prefixEnd_4914304 841133344770948665566511 := by
  unfold tailWord_4914304
  simp only [CollatzResearch.WordTrace]
  refine ⟨89619695994161689574258983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119492927992215586099011977 89619695994161689574258983)
  ·
    refine ⟨134429543991242534361388475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89619695994161689574258983 134429543991242534361388475)
    ·
      refine ⟨201644315986863801542082713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134429543991242534361388475 201644315986863801542082713)
      ·
        refine ⟨151233236990147851156562035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201644315986863801542082713 151233236990147851156562035)
        ·
          refine ⟨226849855485221776734843053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151233236990147851156562035 226849855485221776734843053)
          ·
            refine ⟨85068695806958166275566145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 226849855485221776734843053 85068695806958166275566145)
            ·
              refine ⟨63801521855218624706674609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85068695806958166275566145 63801521855218624706674609)
              ·
                refine ⟨47851141391413968530005957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63801521855218624706674609 47851141391413968530005957)
                ·
                  refine ⟨8972089010890119099376117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47851141391413968530005957 8972089010890119099376117)
                  ·
                    refine ⟨841133344770948665566511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8972089010890119099376117 841133344770948665566511)
                    ·
                      rfl

theorem cell23_4914304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 4, 5].length) (baseStart_4914304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914304 prefixEnd_4914304 := by exact prefixLift 4914304
  have htrace : WordTrace (prefixWord ++ tailWord_4914304) baseStart_4914304 baseEnd_4914304 := by
    simpa [prefixWord, tailWord_4914304, baseEnd_4914304] using wordTrace_append hprefix tailTrace_4914304
  have hstable : (prefixWord ++ tailWord_4914304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914304).length < 2 ^ (prefixWord ++ tailWord_4914304).sum := by decide
  have hdescent : baseEnd_4914304 < baseStart_4914304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914311 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 4, 5, 2]
def baseStart_4914311 : Nat := 118140960795 + 4914311 * 2 ^ 59
def prefixEnd_4914311 : Nat := 4983230072969 + 3 ^ 40 * 4914311 * 2
def baseEnd_4914311 : Nat := 2523403628677427469312001

theorem tailTrace_4914311 : CollatzResearch.WordTrace tailWord_4914311 prefixEnd_4914311 2523403628677427469312001 := by
  unfold tailWord_4914311
  simp only [CollatzResearch.WordTrace]
  refine ⟨179239647299298019344022787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119493098199532012896015191 179239647299298019344022787)
  ·
    refine ⟨268859470948947029016034181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179239647299298019344022787 268859470948947029016034181)
    ·
      refine ⟨50411150802927567940506409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 268859470948947029016034181 50411150802927567940506409)
      ·
        refine ⟨37808363102195675955379807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50411150802927567940506409 37808363102195675955379807)
        ·
          refine ⟨56712544653293513933069711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37808363102195675955379807 56712544653293513933069711)
          ·
            refine ⟨85068816979940270899604567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56712544653293513933069711 85068816979940270899604567)
            ·
              refine ⟨127603225469910406349406851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85068816979940270899604567 127603225469910406349406851)
              ·
                refine ⟨191404838204865609524110277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127603225469910406349406851 191404838204865609524110277)
                ·
                  refine ⟨35888407163412301785770677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 191404838204865609524110277 35888407163412301785770677)
                  ·
                    refine ⟨3364538171569903292416001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35888407163412301785770677 3364538171569903292416001)
                    ·
                      refine ⟨2523403628677427469312001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3364538171569903292416001 2523403628677427469312001)
                      ·
                        rfl

theorem cell23_4914311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 5, 2].length) (baseStart_4914311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914311 prefixEnd_4914311 := by exact prefixLift 4914311
  have htrace : WordTrace (prefixWord ++ tailWord_4914311) baseStart_4914311 baseEnd_4914311 := by
    simpa [prefixWord, tailWord_4914311, baseEnd_4914311] using wordTrace_append hprefix tailTrace_4914311
  have hstable : (prefixWord ++ tailWord_4914311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914311).length < 2 ^ (prefixWord ++ tailWord_4914311).sum := by decide
  have hdescent : baseEnd_4914311 < baseStart_4914311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914351 : List Nat := [1, 1, 2, 1, 2, 3, 3, 3, 3, 4]
def baseStart_4914351 : Nat := 118140960795 + 4914351 * 2 ^ 59
def prefixEnd_4914351 : Nat := 4983230072969 + 3 ^ 40 * 4914351 * 2
def baseEnd_4914351 : Nat := 841141389301202437603939

theorem tailTrace_4914351 : CollatzResearch.WordTrace tailWord_4914351 prefixEnd_4914351 841141389301202437603939 := by
  unfold tailWord_4914351
  simp only [CollatzResearch.WordTrace]
  refine ⟨179241106219153106175478907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119494070812768737450319271 179241106219153106175478907)
  ·
    refine ⟨268861659328729659263218361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179241106219153106175478907 268861659328729659263218361)
    ·
      refine ⟨201646244496547244447413771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268861659328729659263218361 201646244496547244447413771)
      ·
        refine ⟨302469366744820866671120657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201646244496547244447413771 302469366744820866671120657)
        ·
          refine ⟨226852025058615650003340493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 302469366744820866671120657 226852025058615650003340493)
          ·
            refine ⟨85069509396980868751252685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 226852025058615650003340493 85069509396980868751252685)
            ·
              refine ⟨31901066023867825781719757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85069509396980868751252685 31901066023867825781719757)
              ·
                refine ⟨11962899758950434668144909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31901066023867825781719757 11962899758950434668144909)
                ·
                  refine ⟨4486087409606413000554341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11962899758950434668144909 4486087409606413000554341)
                  ·
                    refine ⟨841141389301202437603939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4486087409606413000554341 841141389301202437603939)
                    ·
                      rfl

theorem cell23_4914351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 3, 4].length) (baseStart_4914351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914351 prefixEnd_4914351 := by exact prefixLift 4914351
  have htrace : WordTrace (prefixWord ++ tailWord_4914351) baseStart_4914351 baseEnd_4914351 := by
    simpa [prefixWord, tailWord_4914351, baseEnd_4914351] using wordTrace_append hprefix tailTrace_4914351
  have hstable : (prefixWord ++ tailWord_4914351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914351).length < 2 ^ (prefixWord ++ tailWord_4914351).sum := by decide
  have hdescent : baseEnd_4914351 < baseStart_4914351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914361 : List Nat := [1, 2, 1, 4, 1, 3, 1, 2, 1, 4, 3]
def baseStart_4914361 : Nat := 118140960795 + 4914361 * 2 ^ 59
def prefixEnd_4914361 : Nat := 4983230072969 + 3 ^ 40 * 4914361 * 2
def baseEnd_4914361 : Nat := 2523429302710152273686771

theorem tailTrace_4914361 : CollatzResearch.WordTrace tailWord_4914361 prefixEnd_4914361 2523429302710152273686771 := by
  unfold tailWord_4914361
  simp only [CollatzResearch.WordTrace]
  refine ⟨179241470949116877883342937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119494313966077918588895291 179241470949116877883342937)
  ·
    refine ⟨134431103211837658412507203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179241470949116877883342937 134431103211837658412507203)
    ·
      refine ⟨201646654817756487618760805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134431103211837658412507203 201646654817756487618760805)
      ·
        refine ⟨37808747778329341428517651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 201646654817756487618760805 37808747778329341428517651)
        ·
          refine ⟨56713121667494012142776477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37808747778329341428517651 56713121667494012142776477)
          ·
            refine ⟨21267420625310254553541179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56713121667494012142776477 21267420625310254553541179)
            ·
              refine ⟨31901130937965381830311769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21267420625310254553541179 31901130937965381830311769)
              ·
                refine ⟨23925848203474036372733827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31901130937965381830311769 23925848203474036372733827)
                ·
                  refine ⟨35888772305211054559100741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23925848203474036372733827 35888772305211054559100741)
                  ·
                    refine ⟨6729144807227072729831389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35888772305211054559100741 6729144807227072729831389)
                    ·
                      refine ⟨2523429302710152273686771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6729144807227072729831389 2523429302710152273686771)
                      ·
                        rfl

theorem cell23_4914361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_4914361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914361 prefixEnd_4914361 := by exact prefixLift 4914361
  have htrace : WordTrace (prefixWord ++ tailWord_4914361) baseStart_4914361 baseEnd_4914361 := by
    simpa [prefixWord, tailWord_4914361, baseEnd_4914361] using wordTrace_append hprefix tailTrace_4914361
  have hstable : (prefixWord ++ tailWord_4914361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914361).length < 2 ^ (prefixWord ++ tailWord_4914361).sum := by decide
  have hdescent : baseEnd_4914361 < baseStart_4914361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914415 : List Nat := [1, 1, 2, 1, 7, 2, 2, 1, 6]
def baseStart_4914415 : Nat := 118140960795 + 4914415 * 2 ^ 59
def prefixEnd_4914415 : Nat := 4983230072969 + 3 ^ 40 * 4914415 * 2
def baseEnd_4914415 : Nat := 280384114518388340267947

theorem tailTrace_4914415 : CollatzResearch.WordTrace tailWord_4914415 prefixEnd_4914415 280384114518388340267947 := by
  unfold tailWord_4914415
  simp only [CollatzResearch.WordTrace]
  refine ⟨179243440490921245105808699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119495626993947496737205799 179243440490921245105808699)
  ·
    refine ⟨268865160736381867658713049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179243440490921245105808699 268865160736381867658713049)
    ·
      refine ⟨201648870552286400744034787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268865160736381867658713049 201648870552286400744034787)
      ·
        refine ⟨302473305828429601116052181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201648870552286400744034787 302473305828429601116052181)
        ·
          refine ⟨7089218105353818776157473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 302473305828429601116052181 7089218105353818776157473)
          ·
            refine ⟨5316913579015364082118105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7089218105353818776157473 5316913579015364082118105)
            ·
              refine ⟨3987685184261523061588579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5316913579015364082118105 3987685184261523061588579)
              ·
                refine ⟨5981527776392284592382869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3987685184261523061588579 5981527776392284592382869)
                ·
                  refine ⟨280384114518388340267947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5981527776392284592382869 280384114518388340267947)
                  ·
                    rfl

theorem cell23_4914415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 1, 6].length) (baseStart_4914415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914415 prefixEnd_4914415 := by exact prefixLift 4914415
  have htrace : WordTrace (prefixWord ++ tailWord_4914415) baseStart_4914415 baseEnd_4914415 := by
    simpa [prefixWord, tailWord_4914415, baseEnd_4914415] using wordTrace_append hprefix tailTrace_4914415
  have hstable : (prefixWord ++ tailWord_4914415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914415).length < 2 ^ (prefixWord ++ tailWord_4914415).sum := by decide
  have hdescent : baseEnd_4914415 < baseStart_4914415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914428 : List Nat := [2, 2, 2, 1, 5, 1, 1, 1, 3, 5]
def baseStart_4914428 : Nat := 118140960795 + 4914428 * 2 ^ 59
def prefixEnd_4914428 : Nat := 4983230072969 + 3 ^ 40 * 4914428 * 2
def baseEnd_4914428 : Nat := 841154568638001170516321

theorem tailTrace_4914428 : CollatzResearch.WordTrace tailWord_4914428 prefixEnd_4914428 841154568638001170516321 := by
  unfold tailWord_4914428
  simp only [CollatzResearch.WordTrace]
  refine ⟨89621957319937074163015969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119495943093249432217354625 89621957319937074163015969)
  ·
    refine ⟨67216467989952805622261977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89621957319937074163015969 67216467989952805622261977)
    ·
      refine ⟨50412350992464604216696483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67216467989952805622261977 50412350992464604216696483)
      ·
        refine ⟨75618526488696906325044725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50412350992464604216696483 75618526488696906325044725)
        ·
          refine ⟨7089236858315334967972943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75618526488696906325044725 7089236858315334967972943)
          ·
            refine ⟨10633855287473002451959415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7089236858315334967972943 10633855287473002451959415)
            ·
              refine ⟨15950782931209503677939123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10633855287473002451959415 15950782931209503677939123)
              ·
                refine ⟨23926174396814255516908685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15950782931209503677939123 23926174396814255516908685)
                ·
                  refine ⟨8972315398805345818840757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23926174396814255516908685 8972315398805345818840757)
                  ·
                    refine ⟨841154568638001170516321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8972315398805345818840757 841154568638001170516321)
                    ·
                      rfl

theorem cell23_4914428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 3, 5].length) (baseStart_4914428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914428 prefixEnd_4914428 := by exact prefixLift 4914428
  have htrace : WordTrace (prefixWord ++ tailWord_4914428) baseStart_4914428 baseEnd_4914428 := by
    simpa [prefixWord, tailWord_4914428, baseEnd_4914428] using wordTrace_append hprefix tailTrace_4914428
  have hstable : (prefixWord ++ tailWord_4914428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914428).length < 2 ^ (prefixWord ++ tailWord_4914428).sum := by decide
  have hdescent : baseEnd_4914428 < baseStart_4914428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914435 : List Nat := [1, 1, 1, 3, 2, 5, 2, 1, 2, 3, 2]
def baseStart_4914435 : Nat := 118140960795 + 4914435 * 2 ^ 59
def prefixEnd_4914435 : Nat := 4983230072969 + 3 ^ 40 * 4914435 * 2
def baseEnd_4914435 : Nat := 2523467300278584984161431

theorem tailTrace_4914435 : CollatzResearch.WordTrace tailWord_4914435 prefixEnd_4914435 2523467300278584984161431 := by
  unfold tailWord_4914435
  simp only [CollatzResearch.WordTrace]
  refine ⟨179244169950848788521536759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119496113300565859014357839 179244169950848788521536759)
  ·
    refine ⟨268866254926273182782305139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179244169950848788521536759 268866254926273182782305139)
    ·
      refine ⟨403299382389409774173457709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268866254926273182782305139 403299382389409774173457709)
      ·
        refine ⟨151237268396028665315046641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 403299382389409774173457709 151237268396028665315046641)
        ·
          refine ⟨113427951297021498986284981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151237268396028665315046641 113427951297021498986284981)
          ·
            refine ⟨10633870434095765529964217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 113427951297021498986284981 10633870434095765529964217)
            ·
              refine ⟨7975402825571824147473163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10633870434095765529964217 7975402825571824147473163)
              ·
                refine ⟨11963104238357736221209745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7975402825571824147473163 11963104238357736221209745)
                ·
                  refine ⟨8972328178768302165907309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11963104238357736221209745 8972328178768302165907309)
                  ·
                    refine ⟨3364623067038113312215241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8972328178768302165907309 3364623067038113312215241)
                    ·
                      refine ⟨2523467300278584984161431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3364623067038113312215241 2523467300278584984161431)
                      ·
                        rfl

theorem cell23_4914435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 2, 3, 2].length) (baseStart_4914435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914435 prefixEnd_4914435 := by exact prefixLift 4914435
  have htrace : WordTrace (prefixWord ++ tailWord_4914435) baseStart_4914435 baseEnd_4914435 := by
    simpa [prefixWord, tailWord_4914435, baseEnd_4914435] using wordTrace_append hprefix tailTrace_4914435
  have hstable : (prefixWord ++ tailWord_4914435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914435).length < 2 ^ (prefixWord ++ tailWord_4914435).sum := by decide
  have hdescent : baseEnd_4914435 < baseStart_4914435 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914441 : List Nat := [1, 2, 1, 1, 3, 3, 3, 2, 1, 6]
def baseStart_4914441 : Nat := 118140960795 + 4914441 * 2 ^ 59
def prefixEnd_4914441 : Nat := 4983230072969 + 3 ^ 40 * 4914441 * 2
def baseEnd_4914441 : Nat := 841156793720837320228801

theorem tailTrace_4914441 : CollatzResearch.WordTrace tailWord_4914441 prefixEnd_4914441 841156793720837320228801 := by
  unfold tailWord_4914441
  simp only [CollatzResearch.WordTrace]
  refine ⟨179244388788827051546255177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119496259192551367697503451 179244388788827051546255177)
  ·
    refine ⟨134433291591620288659691383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179244388788827051546255177 134433291591620288659691383)
    ·
      refine ⟨201649937387430432989537075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134433291591620288659691383 201649937387430432989537075)
      ·
        refine ⟨302474906081145649484305613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201649937387430432989537075 302474906081145649484305613)
        ·
          refine ⟨113428089780429618556614605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 302474906081145649484305613 113428089780429618556614605)
          ·
            refine ⟨42535533667661106958730477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113428089780429618556614605 42535533667661106958730477)
            ·
              refine ⟨15950825125372915109523929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42535533667661106958730477 15950825125372915109523929)
              ·
                refine ⟨11963118844029686332142947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15950825125372915109523929 11963118844029686332142947)
                ·
                  refine ⟨17944678266044529498214421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11963118844029686332142947 17944678266044529498214421)
                  ·
                    refine ⟨841156793720837320228801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17944678266044529498214421 841156793720837320228801)
                    ·
                      rfl

theorem cell23_4914441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 6].length) (baseStart_4914441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914441 prefixEnd_4914441 := by exact prefixLift 4914441
  have htrace : WordTrace (prefixWord ++ tailWord_4914441) baseStart_4914441 baseEnd_4914441 := by
    simpa [prefixWord, tailWord_4914441, baseEnd_4914441] using wordTrace_append hprefix tailTrace_4914441
  have hstable : (prefixWord ++ tailWord_4914441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914441).length < 2 ^ (prefixWord ++ tailWord_4914441).sum := by decide
  have hdescent : baseEnd_4914441 < baseStart_4914441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914465 : List Nat := [1, 2, 3, 2, 1, 1, 1, 5, 3, 2, 2]
def baseStart_4914465 : Nat := 118140960795 + 4914465 * 2 ^ 59
def prefixEnd_4914465 : Nat := 4983230072969 + 3 ^ 40 * 4914465 * 2
def baseEnd_4914465 : Nat := 2523482704698219866786293

theorem tailTrace_4914465 : CollatzResearch.WordTrace tailWord_4914465 prefixEnd_4914465 2523482704698219866786293 := by
  unfold tailWord_4914465
  simp only [CollatzResearch.WordTrace]
  refine ⟨179245264140740103645128849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119496842760493402430085899 179245264140740103645128849)
  ·
    refine ⟨134433948105555077733846637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179245264140740103645128849 134433948105555077733846637)
    ·
      refine ⟨50412730539583154150192489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134433948105555077733846637 50412730539583154150192489)
      ·
        refine ⟨37809547904687365612644367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50412730539583154150192489 37809547904687365612644367)
        ·
          refine ⟨56714321857031048418966551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37809547904687365612644367 56714321857031048418966551)
          ·
            refine ⟨85071482785546572628449827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56714321857031048418966551 85071482785546572628449827)
            ·
              refine ⟨127607224178319858942674741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85071482785546572628449827 127607224178319858942674741)
              ·
                refine ⟨11963177266717486775875757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 127607224178319858942674741 11963177266717486775875757)
                ·
                  refine ⟨4486191475019057540953409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11963177266717486775875757 4486191475019057540953409)
                  ·
                    refine ⟨3364643606264293155715057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4486191475019057540953409 3364643606264293155715057)
                    ·
                      refine ⟨2523482704698219866786293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3364643606264293155715057 2523482704698219866786293)
                      ·
                        rfl

theorem cell23_4914465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 3, 2, 2].length) (baseStart_4914465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914465 prefixEnd_4914465 := by exact prefixLift 4914465
  have htrace : WordTrace (prefixWord ++ tailWord_4914465) baseStart_4914465 baseEnd_4914465 := by
    simpa [prefixWord, tailWord_4914465, baseEnd_4914465] using wordTrace_append hprefix tailTrace_4914465
  have hstable : (prefixWord ++ tailWord_4914465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914465).length < 2 ^ (prefixWord ++ tailWord_4914465).sum := by decide
  have hdescent : baseEnd_4914465 < baseStart_4914465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914468 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 5, 2, 3]
def baseStart_4914468 : Nat := 118140960795 + 4914468 * 2 ^ 59
def prefixEnd_4914468 : Nat := 4983230072969 + 3 ^ 40 * 4914468 * 2
def baseEnd_4914468 : Nat := 2523484245140183355048779

theorem tailTrace_4914468 : CollatzResearch.WordTrace tailWord_4914468 prefixEnd_4914468 2523484245140183355048779 := by
  unfold tailWord_4914468
  simp only [CollatzResearch.WordTrace]
  refine ⟨89622686779864617578744029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119496915706486156771658705 89622686779864617578744029)
  ·
    refine ⟨33608507542449231592029011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89622686779864617578744029 33608507542449231592029011)
    ·
      refine ⟨50412761313673847388043517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33608507542449231592029011 50412761313673847388043517)
      ·
        refine ⟨18904785492627692770516319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50412761313673847388043517 18904785492627692770516319)
        ·
          refine ⟨28357178238941539155774479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18904785492627692770516319 28357178238941539155774479)
          ·
            refine ⟨42535767358412308733661719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28357178238941539155774479 42535767358412308733661719)
            ·
              refine ⟨63803651037618463100492579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42535767358412308733661719 63803651037618463100492579)
              ·
                refine ⟨95705476556427694650738869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63803651037618463100492579 95705476556427694650738869)
                ·
                  refine ⟨8972388427165096373506769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 95705476556427694650738869 8972388427165096373506769)
                  ·
                    refine ⟨6729291320373822280130077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8972388427165096373506769 6729291320373822280130077)
                    ·
                      refine ⟨2523484245140183355048779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6729291320373822280130077 2523484245140183355048779)
                      ·
                        rfl

theorem cell23_4914468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_4914468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914468 prefixEnd_4914468 := by exact prefixLift 4914468
  have htrace : WordTrace (prefixWord ++ tailWord_4914468) baseStart_4914468 baseEnd_4914468 := by
    simpa [prefixWord, tailWord_4914468, baseEnd_4914468] using wordTrace_append hprefix tailTrace_4914468
  have hstable : (prefixWord ++ tailWord_4914468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914468).length < 2 ^ (prefixWord ++ tailWord_4914468).sum := by decide
  have hdescent : baseEnd_4914468 < baseStart_4914468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914482 : List Nat := [3, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2]
def baseStart_4914482 : Nat := 118140960795 + 4914482 * 2 ^ 59
def prefixEnd_4914482 : Nat := 4983230072969 + 3 ^ 40 * 4914482 * 2
def baseEnd_4914482 : Nat := 2523491433869346300273715

theorem tailTrace_4914482 : CollatzResearch.WordTrace tailWord_4914482 prefixEnd_4914482 2523491433869346300273715 := by
  unfold tailWord_4914482
  simp only [CollatzResearch.WordTrace]
  refine ⟨44811471045419628887124425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119497256121119010365665133 44811471045419628887124425)
  ·
    refine ⟨33608603284064721665343319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44811471045419628887124425 33608603284064721665343319)
    ·
      refine ⟨50412904926097082498014979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33608603284064721665343319 50412904926097082498014979)
      ·
        refine ⟨75619357389145623747022469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50412904926097082498014979 75619357389145623747022469)
        ·
          refine ⟨14178629510464804452566713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75619357389145623747022469 14178629510464804452566713)
          ·
            refine ⟨10633972132848603339425035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14178629510464804452566713 10633972132848603339425035)
            ·
              refine ⟨15950958199272905009137553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10633972132848603339425035 15950958199272905009137553)
              ·
                refine ⟨11963218649454678756853165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15950958199272905009137553 11963218649454678756853165)
                ·
                  refine ⟨4486206993545504533819937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11963218649454678756853165 4486206993545504533819937)
                  ·
                    refine ⟨3364655245159128400364953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4486206993545504533819937 3364655245159128400364953)
                    ·
                      refine ⟨2523491433869346300273715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3364655245159128400364953 2523491433869346300273715)
                      ·
                        rfl

theorem cell23_4914482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2].length) (baseStart_4914482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914482 prefixEnd_4914482 := by exact prefixLift 4914482
  have htrace : WordTrace (prefixWord ++ tailWord_4914482) baseStart_4914482 baseEnd_4914482 := by
    simpa [prefixWord, tailWord_4914482, baseEnd_4914482] using wordTrace_append hprefix tailTrace_4914482
  have hstable : (prefixWord ++ tailWord_4914482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914482).length < 2 ^ (prefixWord ++ tailWord_4914482).sum := by decide
  have hdescent : baseEnd_4914482 < baseStart_4914482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914486 : List Nat := [5, 1, 2, 3, 1, 2, 1, 1, 2, 3, 2]
def baseStart_4914486 : Nat := 118140960795 + 4914486 * 2 ^ 59
def prefixEnd_4914486 : Nat := 4983230072969 + 3 ^ 40 * 4914486 * 2
def baseEnd_4914486 : Nat := 2523493487791964284623697

theorem tailTrace_4914486 : CollatzResearch.WordTrace tailWord_4914486 prefixEnd_4914486 2523493487791964284623697 := by
  unfold tailWord_4914486
  simp only [CollatzResearch.WordTrace]
  refine ⟨11202876879604001514477707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 119497353382442682821095541 11202876879604001514477707)
  ·
    refine ⟨16804315319406002271716561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11202876879604001514477707 16804315319406002271716561)
    ·
      refine ⟨12603236489554501703787421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16804315319406002271716561 12603236489554501703787421)
      ·
        refine ⟨4726213683582938138920283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12603236489554501703787421 4726213683582938138920283)
        ·
          refine ⟨7089320525374407208380425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4726213683582938138920283 7089320525374407208380425)
          ·
            refine ⟨5316990394030805406285319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7089320525374407208380425 5316990394030805406285319)
            ·
              refine ⟨7975485591046208109427979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5316990394030805406285319 7975485591046208109427979)
              ·
                refine ⟨11963228386569312164141969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7975485591046208109427979 11963228386569312164141969)
                ·
                  refine ⟨8972421289926984123106477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11963228386569312164141969 8972421289926984123106477)
                  ·
                    refine ⟨3364657983722619046164929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8972421289926984123106477 3364657983722619046164929)
                    ·
                      refine ⟨2523493487791964284623697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3364657983722619046164929 2523493487791964284623697)
                      ·
                        rfl

theorem cell23_4914486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_4914486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914486 prefixEnd_4914486 := by exact prefixLift 4914486
  have htrace : WordTrace (prefixWord ++ tailWord_4914486) baseStart_4914486 baseEnd_4914486 := by
    simpa [prefixWord, tailWord_4914486, baseEnd_4914486] using wordTrace_append hprefix tailTrace_4914486
  have hstable : (prefixWord ++ tailWord_4914486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914486).length < 2 ^ (prefixWord ++ tailWord_4914486).sum := by decide
  have hdescent : baseEnd_4914486 < baseStart_4914486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914521 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 1, 5, 4]
def baseStart_4914521 : Nat := 118140960795 + 4914521 * 2 ^ 59
def prefixEnd_4914521 : Nat := 4983230072969 + 3 ^ 40 * 4914521 * 2
def baseEnd_4914521 : Nat := 2523511459614871647686035

theorem tailTrace_4914521 : CollatzResearch.WordTrace tailWord_4914521 prefixEnd_4914521 2523511459614871647686035 := by
  unfold tailWord_4914521
  simp only [CollatzResearch.WordTrace]
  refine ⟨179247306628537225209167417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119498204419024816806111611 179247306628537225209167417)
  ·
    refine ⟨134435479971402918906875563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179247306628537225209167417 134435479971402918906875563)
    ·
      refine ⟨201653219957104378360313345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134435479971402918906875563 201653219957104378360313345)
      ·
        refine ⟨151239914967828283770235009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201653219957104378360313345 151239914967828283770235009)
        ·
          refine ⟨113429936225871212827676257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151239914967828283770235009 113429936225871212827676257)
          ·
            refine ⟨85072452169403409620757193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113429936225871212827676257 85072452169403409620757193)
            ·
              refine ⟨63804339127052557215567895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85072452169403409620757193 63804339127052557215567895)
              ·
                refine ⟨95706508690578835823351843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63804339127052557215567895 95706508690578835823351843)
                ·
                  refine ⟨143559763035868253735027765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95706508690578835823351843 143559763035868253735027765)
                  ·
                    refine ⟨13458727784612648787658853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 143559763035868253735027765 13458727784612648787658853)
                    ·
                      refine ⟨2523511459614871647686035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13458727784612648787658853 2523511459614871647686035)
                      ·
                        rfl

theorem cell23_4914521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 5, 4].length) (baseStart_4914521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914521 prefixEnd_4914521 := by exact prefixLift 4914521
  have htrace : WordTrace (prefixWord ++ tailWord_4914521) baseStart_4914521 baseEnd_4914521 := by
    simpa [prefixWord, tailWord_4914521, baseEnd_4914521] using wordTrace_append hprefix tailTrace_4914521
  have hstable : (prefixWord ++ tailWord_4914521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914521).length < 2 ^ (prefixWord ++ tailWord_4914521).sum := by decide
  have hdescent : baseEnd_4914521 < baseStart_4914521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914555 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 6, 2, 2]
def baseStart_4914555 : Nat := 118140960795 + 4914555 * 2 ^ 59
def prefixEnd_4914555 : Nat := 4983230072969 + 3 ^ 40 * 4914555 * 2
def baseEnd_4914555 : Nat := 2523528917957124514660879

theorem tailTrace_4914555 : CollatzResearch.WordTrace tailWord_4914555 prefixEnd_4914555 2523528917957124514660879 := by
  unfold tailWord_4914555
  simp only [CollatzResearch.WordTrace]
  refine ⟨179248546710414049015905119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119499031140276032677270079 179248546710414049015905119)
  ·
    refine ⟨268872820065621073523857679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179248546710414049015905119 268872820065621073523857679)
    ·
      refine ⟨403309230098431610285786519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268872820065621073523857679 403309230098431610285786519)
      ·
        refine ⟨604963845147647415428679779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 403309230098431610285786519 604963845147647415428679779)
        ·
          refine ⟨907445767721471123143019669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 604963845147647415428679779 907445767721471123143019669)
          ·
            refine ⟨42536520361943958897329047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 907445767721471123143019669 42536520361943958897329047)
            ·
              refine ⟨63804780542915938345993571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42536520361943958897329047 63804780542915938345993571)
              ·
                refine ⟨95707170814373907518990357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63804780542915938345993571 95707170814373907518990357)
                ·
                  refine ⟨4486273631923776914952673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 95707170814373907518990357 4486273631923776914952673)
                  ·
                    refine ⟨3364705223942832686214505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4486273631923776914952673 3364705223942832686214505)
                    ·
                      refine ⟨2523528917957124514660879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3364705223942832686214505 2523528917957124514660879)
                      ·
                        rfl

theorem cell23_4914555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 6, 2, 2].length) (baseStart_4914555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914555 prefixEnd_4914555 := by exact prefixLift 4914555
  have htrace : WordTrace (prefixWord ++ tailWord_4914555) baseStart_4914555 baseEnd_4914555 := by
    simpa [prefixWord, tailWord_4914555, baseEnd_4914555] using wordTrace_append hprefix tailTrace_4914555
  have hstable : (prefixWord ++ tailWord_4914555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914555).length < 2 ^ (prefixWord ++ tailWord_4914555).sum := by decide
  have hdescent : baseEnd_4914555 < baseStart_4914555 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914571 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 7]
def baseStart_4914571 : Nat := 118140960795 + 4914571 * 2 ^ 59
def prefixEnd_4914571 : Nat := 4983230072969 + 3 ^ 40 * 4914571 * 2
def baseEnd_4914571 : Nat := 2523537133647596452060805

theorem tailTrace_4914571 : CollatzResearch.WordTrace tailWord_4914571 prefixEnd_4914571 2523537133647596452060805 := by
  unfold tailWord_4914571
  simp only [CollatzResearch.WordTrace]
  refine ⟨179249130278356083748487567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119499420185570722498991711 179249130278356083748487567)
  ·
    refine ⟨268873695417534125622731351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179249130278356083748487567 268873695417534125622731351)
    ·
      refine ⟨403310543126301188434097027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268873695417534125622731351 403310543126301188434097027)
      ·
        refine ⟨604965814689451782651145541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 403310543126301188434097027 604965814689451782651145541)
        ·
          refine ⟨113431090254272209247089789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 604965814689451782651145541 113431090254272209247089789)
          ·
            refine ⟨42536658845352078467658671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113431090254272209247089789 42536658845352078467658671)
            ·
              refine ⟨63804988268028117701488007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42536658845352078467658671 63804988268028117701488007)
              ·
                refine ⟨95707482402042176552232011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63804988268028117701488007 95707482402042176552232011)
                ·
                  refine ⟨143561223603063264828348017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95707482402042176552232011 143561223603063264828348017)
                  ·
                    refine ⟨107670917702297448621261013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 143561223603063264828348017 107670917702297448621261013)
                    ·
                      refine ⟨2523537133647596452060805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 107670917702297448621261013 2523537133647596452060805)
                      ·
                        rfl

theorem cell23_4914571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 7].length) (baseStart_4914571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914571 prefixEnd_4914571 := by exact prefixLift 4914571
  have htrace : WordTrace (prefixWord ++ tailWord_4914571) baseStart_4914571 baseEnd_4914571 := by
    simpa [prefixWord, tailWord_4914571, baseEnd_4914571] using wordTrace_append hprefix tailTrace_4914571
  have hstable : (prefixWord ++ tailWord_4914571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914571).length < 2 ^ (prefixWord ++ tailWord_4914571).sum := by decide
  have hdescent : baseEnd_4914571 < baseStart_4914571 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914572 : List Nat := [2, 2, 1, 2, 1, 3, 2, 4, 2, 2, 2]
def baseStart_4914572 : Nat := 118140960795 + 4914572 * 2 ^ 59
def prefixEnd_4914572 : Nat := 4983230072969 + 3 ^ 40 * 4914572 * 2
def baseEnd_4914572 : Nat := 2523537647128250948148301

theorem tailTrace_4914572 : CollatzResearch.WordTrace tailWord_4914572 prefixEnd_4914572 2523537647128250948148301 := by
  unfold tailWord_4914572
  simp only [CollatzResearch.WordTrace]
  refine ⟨89624583375676230459636985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119499444500901640612849313 89624583375676230459636985)
  ·
    refine ⟨67218437531757172844727739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89624583375676230459636985 67218437531757172844727739)
    ·
      refine ⟨100827656297635759267091609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67218437531757172844727739 100827656297635759267091609)
      ·
        refine ⟨75620742223226819450318707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100827656297635759267091609 75620742223226819450318707)
        ·
          refine ⟨113431113334840229175478061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75620742223226819450318707 113431113334840229175478061)
          ·
            refine ⟨42536667500565085940804273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113431113334840229175478061 42536667500565085940804273)
            ·
              refine ⟨31902500625423814455603205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42536667500565085940804273 31902500625423814455603205)
              ·
                refine ⟨5981718867266965210425601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31902500625423814455603205 5981718867266965210425601)
                ·
                  refine ⟨4486289150450223907819201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5981718867266965210425601 4486289150450223907819201)
                  ·
                    refine ⟨3364716862837667930864401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4486289150450223907819201 3364716862837667930864401)
                    ·
                      refine ⟨2523537647128250948148301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3364716862837667930864401 2523537647128250948148301)
                      ·
                        rfl

theorem cell23_4914572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 4, 2, 2, 2].length) (baseStart_4914572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914572 prefixEnd_4914572 := by exact prefixLift 4914572
  have htrace : WordTrace (prefixWord ++ tailWord_4914572) baseStart_4914572 baseEnd_4914572 := by
    simpa [prefixWord, tailWord_4914572, baseEnd_4914572] using wordTrace_append hprefix tailTrace_4914572
  have hstable : (prefixWord ++ tailWord_4914572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914572).length < 2 ^ (prefixWord ++ tailWord_4914572).sum := by decide
  have hdescent : baseEnd_4914572 < baseStart_4914572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914589 : List Nat := [1, 4, 2, 1, 3, 2, 1, 3, 2, 2, 2]
def baseStart_4914589 : Nat := 118140960795 + 4914589 * 2 ^ 59
def prefixEnd_4914589 : Nat := 4983230072969 + 3 ^ 40 * 4914589 * 2
def baseEnd_4914589 : Nat := 2523546376299377381635723

theorem tailTrace_4914589 : CollatzResearch.WordTrace tailWord_4914589 prefixEnd_4914589 2523546376299377381635723 := by
  unfold tailWord_4914589
  simp only [CollatzResearch.WordTrace]
  refine ⟨179249786792290872822642821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119499857861527248548428547 179249786792290872822642821)
  ·
    refine ⟨33609335023554538654245529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 179249786792290872822642821 33609335023554538654245529)
    ·
      refine ⟨25207001267665903990684147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33609335023554538654245529 25207001267665903990684147)
      ·
        refine ⟨37810501901498855986026221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25207001267665903990684147 37810501901498855986026221)
        ·
          refine ⟨14178938213062070994759833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37810501901498855986026221 14178938213062070994759833)
          ·
            refine ⟨10634203659796553246069875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14178938213062070994759833 10634203659796553246069875)
            ·
              refine ⟨15951305489694829869104813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10634203659796553246069875 15951305489694829869104813)
              ·
                refine ⟨5981739558635561200914305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15951305489694829869104813 5981739558635561200914305)
                ·
                  refine ⟨4486304668976670900685729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5981739558635561200914305 4486304668976670900685729)
                  ·
                    refine ⟨3364728501732503175514297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4486304668976670900685729 3364728501732503175514297)
                    ·
                      refine ⟨2523546376299377381635723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3364728501732503175514297 2523546376299377381635723)
                      ·
                        rfl

theorem cell23_4914589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 3, 2, 2, 2].length) (baseStart_4914589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914589 prefixEnd_4914589 := by exact prefixLift 4914589
  have htrace : WordTrace (prefixWord ++ tailWord_4914589) baseStart_4914589 baseEnd_4914589 := by
    simpa [prefixWord, tailWord_4914589, baseEnd_4914589] using wordTrace_append hprefix tailTrace_4914589
  have hstable : (prefixWord ++ tailWord_4914589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914589).length < 2 ^ (prefixWord ++ tailWord_4914589).sum := by decide
  have hdescent : baseEnd_4914589 < baseStart_4914589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914655 : List Nat := [1, 1, 2, 3, 3, 1, 3, 2, 3, 4]
def baseStart_4914655 : Nat := 118140960795 + 4914655 * 2 ^ 59
def prefixEnd_4914655 : Nat := 4983230072969 + 3 ^ 40 * 4914655 * 2
def baseEnd_4914655 : Nat := 841193422007524707803473

theorem tailTrace_4914655 : CollatzResearch.WordTrace tailWord_4914655 prefixEnd_4914655 841193422007524707803473 := by
  unfold tailWord_4914655
  simp only [CollatzResearch.WordTrace]
  refine ⟨179252194010051766094545419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119501462673367844063030279 179252194010051766094545419)
  ·
    refine ⟨268878291015077649141818129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179252194010051766094545419 268878291015077649141818129)
    ·
      refine ⟨201658718261308236856363597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268878291015077649141818129 201658718261308236856363597)
      ·
        refine ⟨75622019347990588821136349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201658718261308236856363597 75622019347990588821136349)
        ·
          refine ⟨28358257255496470807926131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75622019347990588821136349 28358257255496470807926131)
          ·
            refine ⟨42537385883244706211889197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28358257255496470807926131 42537385883244706211889197)
            ·
              refine ⟨15951519706216764829458449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42537385883244706211889197 15951519706216764829458449)
              ·
                refine ⟨11963639779662573622093837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15951519706216764829458449 11963639779662573622093837)
                ·
                  refine ⟨4486364917373465108285189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11963639779662573622093837 4486364917373465108285189)
                  ·
                    refine ⟨841193422007524707803473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4486364917373465108285189 841193422007524707803473)
                    ·
                      rfl

theorem cell23_4914655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 3, 4].length) (baseStart_4914655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914655 prefixEnd_4914655 := by exact prefixLift 4914655
  have htrace : WordTrace (prefixWord ++ tailWord_4914655) baseStart_4914655 baseEnd_4914655 := by
    simpa [prefixWord, tailWord_4914655, baseEnd_4914655] using wordTrace_append hprefix tailTrace_4914655
  have hstable : (prefixWord ++ tailWord_4914655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914655).length < 2 ^ (prefixWord ++ tailWord_4914655).sum := by decide
  have hdescent : baseEnd_4914655 < baseStart_4914655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914672 : List Nat := [2, 1, 1, 1, 3, 4, 1, 5, 1, 4]
def baseStart_4914672 : Nat := 118140960795 + 4914672 * 2 ^ 59
def prefixEnd_4914672 : Nat := 4983230072969 + 3 ^ 40 * 4914672 * 2
def baseEnd_4914672 : Nat := 841196331731233518965947

theorem tailTrace_4914672 : CollatzResearch.WordTrace tailWord_4914672 prefixEnd_4914672 841196331731233518965947 := by
  unfold tailWord_4914672
  simp only [CollatzResearch.WordTrace]
  refine ⟨89626407025495088998957135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119501876033993451998609513 89626407025495088998957135)
  ·
    refine ⟨134439610538242633498435703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89626407025495088998957135 134439610538242633498435703)
    ·
      refine ⟨201659415807363950247653555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134439610538242633498435703 201659415807363950247653555)
      ·
        refine ⟨302489123711045925371480333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201659415807363950247653555 302489123711045925371480333)
        ·
          refine ⟨113433421391642222014305125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 302489123711045925371480333 113433421391642222014305125)
          ·
            refine ⟨21268766510932916627682211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113433421391642222014305125 21268766510932916627682211)
            ·
              refine ⟨31903149766399374941523317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21268766510932916627682211 31903149766399374941523317)
              ·
                refine ⟨2990920290599941400767811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31903149766399374941523317 2990920290599941400767811)
                ·
                  refine ⟨4486380435899912101151717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2990920290599941400767811 4486380435899912101151717)
                  ·
                    refine ⟨841196331731233518965947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4486380435899912101151717 841196331731233518965947)
                    ·
                      rfl

theorem cell23_4914672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 5, 1, 4].length) (baseStart_4914672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914672 prefixEnd_4914672 := by exact prefixLift 4914672
  have htrace : WordTrace (prefixWord ++ tailWord_4914672) baseStart_4914672 baseEnd_4914672 := by
    simpa [prefixWord, tailWord_4914672, baseEnd_4914672] using wordTrace_append hprefix tailTrace_4914672
  have hstable : (prefixWord ++ tailWord_4914672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914672).length < 2 ^ (prefixWord ++ tailWord_4914672).sum := by decide
  have hdescent : baseEnd_4914672 < baseStart_4914672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914685 : List Nat := [1, 4, 1, 1, 1, 4, 3, 2, 6]
def baseStart_4914685 : Nat := 118140960795 + 4914685 * 2 ^ 59
def prefixEnd_4914685 : Nat := 4983230072969 + 3 ^ 40 * 4914685 * 2
def baseEnd_4914685 : Nat := 280399518938023222892809

theorem tailTrace_4914685 : CollatzResearch.WordTrace tailWord_4914685 prefixEnd_4914685 280399518938023222892809 := by
  unfold tailWord_4914685
  simp only [CollatzResearch.WordTrace]
  refine ⟨179253288199943081218137509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119502192133295387478758339 179253288199943081218137509)
  ·
    refine ⟨33609991537489327728400783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 179253288199943081218137509 33609991537489327728400783)
    ·
      refine ⟨50414987306233991592601175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33609991537489327728400783 50414987306233991592601175)
      ·
        refine ⟨75622480959350987388901763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50414987306233991592601175 75622480959350987388901763)
        ·
          refine ⟨113433721439026481083352645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75622480959350987388901763 113433721439026481083352645)
          ·
            refine ⟨21268822769817465203128621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113433721439026481083352645 21268822769817465203128621)
            ·
              refine ⟨7975808538681549451173233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21268822769817465203128621 7975808538681549451173233)
              ·
                refine ⟨5981856404011162088379925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7975808538681549451173233 5981856404011162088379925)
                ·
                  refine ⟨280399518938023222892809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5981856404011162088379925 280399518938023222892809)
                  ·
                    rfl

theorem cell23_4914685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 2, 6].length) (baseStart_4914685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914685 prefixEnd_4914685 := by exact prefixLift 4914685
  have htrace : WordTrace (prefixWord ++ tailWord_4914685) baseStart_4914685 baseEnd_4914685 := by
    simpa [prefixWord, tailWord_4914685, baseEnd_4914685] using wordTrace_append hprefix tailTrace_4914685
  have hstable : (prefixWord ++ tailWord_4914685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914685).length < 2 ^ (prefixWord ++ tailWord_4914685).sum := by decide
  have hdescent : baseEnd_4914685 < baseStart_4914685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914705 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 3, 5, 2]
def baseStart_4914705 : Nat := 118140960795 + 4914705 * 2 ^ 59
def prefixEnd_4914705 : Nat := 4983230072969 + 3 ^ 40 * 4914705 * 2
def baseEnd_4914705 : Nat := 2523605940055298927785189

theorem tailTrace_4914705 : CollatzResearch.WordTrace tailWord_4914705 prefixEnd_4914705 2523605940055298927785189 := by
  unfold tailWord_4914705
  simp only [CollatzResearch.WordTrace]
  refine ⟨179254017659870624633865569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119502678439913749755910379 179254017659870624633865569)
  ·
    refine ⟨134440513244902968475399177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179254017659870624633865569 134440513244902968475399177)
    ·
      refine ⟨100830384933677226356549383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134440513244902968475399177 100830384933677226356549383)
      ·
        refine ⟨151245577400515839534824075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100830384933677226356549383 151245577400515839534824075)
        ·
          refine ⟨226868366100773759302236113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151245577400515839534824075 226868366100773759302236113)
          ·
            refine ⟨170151274575580319476677085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226868366100773759302236113 170151274575580319476677085)
            ·
              refine ⟨63806727965842619803753907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 170151274575580319476677085 63806727965842619803753907)
              ·
                refine ⟨95710091948763929705630861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63806727965842619803753907 95710091948763929705630861)
                ·
                  refine ⟨35891284480786473639611573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95710091948763929705630861 35891284480786473639611573)
                  ·
                    refine ⟨3364807920073731903713585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35891284480786473639611573 3364807920073731903713585)
                    ·
                      refine ⟨2523605940055298927785189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3364807920073731903713585 2523605940055298927785189)
                      ·
                        rfl

theorem cell23_4914705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 5, 2].length) (baseStart_4914705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914705 prefixEnd_4914705 := by exact prefixLift 4914705
  have htrace : WordTrace (prefixWord ++ tailWord_4914705) baseStart_4914705 baseEnd_4914705 := by
    simpa [prefixWord, tailWord_4914705, baseEnd_4914705] using wordTrace_append hprefix tailTrace_4914705
  have hstable : (prefixWord ++ tailWord_4914705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914705).length < 2 ^ (prefixWord ++ tailWord_4914705).sum := by decide
  have hdescent : baseEnd_4914705 < baseStart_4914705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914722 : List Nat := [3, 3, 1, 1, 1, 1, 4, 1, 1, 5, 2]
def baseStart_4914722 : Nat := 118140960795 + 4914722 * 2 ^ 59
def prefixEnd_4914722 : Nat := 4983230072969 + 3 ^ 40 * 4914722 * 2
def baseEnd_4914722 : Nat := 2523614669226425361272611

theorem tailTrace_4914722 : CollatzResearch.WordTrace tailWord_4914722 prefixEnd_4914722 2523614669226425361272611 := by
  unfold tailWord_4914722
  simp only [CollatzResearch.WordTrace]
  refine ⟨44813659425202259134308605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119503091800539357691489613 44813659425202259134308605)
  ·
    refine ⟨16805122284450847175365727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44813659425202259134308605 16805122284450847175365727)
    ·
      refine ⟨25207683426676270763048591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16805122284450847175365727 25207683426676270763048591)
      ·
        refine ⟨37811525140014406144572887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25207683426676270763048591 37811525140014406144572887)
        ·
          refine ⟨56717287710021609216859331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37811525140014406144572887 56717287710021609216859331)
          ·
            refine ⟨85075931565032413825288997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56717287710021609216859331 85075931565032413825288997)
            ·
              refine ⟨15951737168443577592241687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85075931565032413825288997 15951737168443577592241687)
              ·
                refine ⟨23927605752665366388362531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15951737168443577592241687 23927605752665366388362531)
                ·
                  refine ⟨35891408628998049582543797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23927605752665366388362531 35891408628998049582543797)
                  ·
                    refine ⟨3364819558968567148363481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35891408628998049582543797 3364819558968567148363481)
                    ·
                      refine ⟨2523614669226425361272611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3364819558968567148363481 2523614669226425361272611)
                      ·
                        rfl

theorem cell23_4914722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 1, 5, 2].length) (baseStart_4914722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914722 prefixEnd_4914722 := by exact prefixLift 4914722
  have htrace : WordTrace (prefixWord ++ tailWord_4914722) baseStart_4914722 baseEnd_4914722 := by
    simpa [prefixWord, tailWord_4914722, baseEnd_4914722] using wordTrace_append hprefix tailTrace_4914722
  have hstable : (prefixWord ++ tailWord_4914722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914722).length < 2 ^ (prefixWord ++ tailWord_4914722).sum := by decide
  have hdescent : baseEnd_4914722 < baseStart_4914722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914746 : List Nat := [3, 1, 1, 1, 3, 2, 5, 2, 1, 1, 3]
def baseStart_4914746 : Nat := 118140960795 + 4914746 * 2 ^ 59
def prefixEnd_4914746 : Nat := 4983230072969 + 3 ^ 40 * 4914746 * 2
def baseEnd_4914746 : Nat := 2523626992762133267372501

theorem tailTrace_4914746 : CollatzResearch.WordTrace tailWord_4914746 prefixEnd_4914746 2523626992762133267372501 := by
  unfold tailWord_4914746
  simp only [CollatzResearch.WordTrace]
  refine ⟨44813878263180522159027023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119503675368481392424072061 44813878263180522159027023)
  ·
    refine ⟨67220817394770783238540535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44813878263180522159027023 67220817394770783238540535)
    ·
      refine ⟨100831226092156174857810803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67220817394770783238540535 100831226092156174857810803)
      ·
        refine ⟨151246839138234262286716205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100831226092156174857810803 151246839138234262286716205)
        ·
          refine ⟨56717564676837848357518577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151246839138234262286716205 56717564676837848357518577)
          ·
            refine ⟨42538173507628386268138933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56717564676837848357518577 42538173507628386268138933)
            ·
              refine ⟨3987953766340161212638025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42538173507628386268138933 3987953766340161212638025)
              ·
                refine ⟨2990965324755120909478519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3987953766340161212638025 2990965324755120909478519)
                ·
                  refine ⟨4486447987132681364217779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2990965324755120909478519 4486447987132681364217779)
                  ·
                    refine ⟨6729671980699022046326669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4486447987132681364217779 6729671980699022046326669)
                    ·
                      refine ⟨2523626992762133267372501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6729671980699022046326669 2523626992762133267372501)
                      ·
                        rfl

theorem cell23_4914746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 2, 1, 1, 3].length) (baseStart_4914746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914746 prefixEnd_4914746 := by exact prefixLift 4914746
  have htrace : WordTrace (prefixWord ++ tailWord_4914746) baseStart_4914746 baseEnd_4914746 := by
    simpa [prefixWord, tailWord_4914746, baseEnd_4914746] using wordTrace_append hprefix tailTrace_4914746
  have hstable : (prefixWord ++ tailWord_4914746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914746).length < 2 ^ (prefixWord ++ tailWord_4914746).sum := by decide
  have hdescent : baseEnd_4914746 < baseStart_4914746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914762 : List Nat := [3, 1, 2, 1, 1, 3, 3, 3, 2, 4]
def baseStart_4914762 : Nat := 118140960795 + 4914762 * 2 ^ 59
def prefixEnd_4914762 : Nat := 4983230072969 + 3 ^ 40 * 4914762 * 2
def baseEnd_4914762 : Nat := 841211736150868401590809

theorem tailTrace_4914762 : CollatzResearch.WordTrace tailWord_4914762 prefixEnd_4914762 841211736150868401590809 := by
  unfold tailWord_4914762
  simp only [CollatzResearch.WordTrace]
  refine ⟨44814024155166030842172635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119504064413776082245793693 44814024155166030842172635)
  ·
    refine ⟨67221036232749046263258953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44814024155166030842172635 67221036232749046263258953)
    ·
      refine ⟨50415777174561784697444215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67221036232749046263258953 50415777174561784697444215)
      ·
        refine ⟨75623665761842677046166323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50415777174561784697444215 75623665761842677046166323)
        ·
          refine ⟨113435498642764015569249485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75623665761842677046166323 113435498642764015569249485)
          ·
            refine ⟨42538311991036505838468557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113435498642764015569249485 42538311991036505838468557)
            ·
              refine ⟨15951866996638689689425709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42538311991036505838468557 15951866996638689689425709)
              ·
                refine ⟨5981950123739508633534641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15951866996638689689425709 5981950123739508633534641)
                ·
                  refine ⟨4486462592804631475150981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5981950123739508633534641 4486462592804631475150981)
                  ·
                    refine ⟨841211736150868401590809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4486462592804631475150981 841211736150868401590809)
                    ·
                      rfl

theorem cell23_4914762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 3, 2, 4].length) (baseStart_4914762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914762 prefixEnd_4914762 := by exact prefixLift 4914762
  have htrace : WordTrace (prefixWord ++ tailWord_4914762) baseStart_4914762 baseEnd_4914762 := by
    simpa [prefixWord, tailWord_4914762, baseEnd_4914762] using wordTrace_append hprefix tailTrace_4914762
  have hstable : (prefixWord ++ tailWord_4914762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914762).length < 2 ^ (prefixWord ++ tailWord_4914762).sum := by decide
  have hdescent : baseEnd_4914762 < baseStart_4914762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914772 : List Nat := [2, 4, 1, 1, 1, 2, 3, 1, 3, 2, 3]
def baseStart_4914772 : Nat := 118140960795 + 4914772 * 2 ^ 59
def prefixEnd_4914772 : Nat := 4983230072969 + 3 ^ 40 * 4914772 * 2
def baseEnd_4914772 : Nat := 2523640343259150165647381

theorem tailTrace_4914772 : CollatzResearch.WordTrace tailWord_4914772 prefixEnd_4914772 2523640343259150165647381 := by
  unfold tailWord_4914772
  simp only [CollatzResearch.WordTrace]
  refine ⟨89628230675313947538277285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119504307567085263384369713 89628230675313947538277285)
  ·
    refine ⟨16805293251621365163426991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89628230675313947538277285 16805293251621365163426991)
    ·
      refine ⟨25207939877432047745140487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16805293251621365163426991 25207939877432047745140487)
      ·
        refine ⟨37811909816148071617710731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25207939877432047745140487 37811909816148071617710731)
        ·
          refine ⟨56717864724222107426566097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37811909816148071617710731 56717864724222107426566097)
          ·
            refine ⟨42538398543166580569924573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56717864724222107426566097 42538398543166580569924573)
            ·
              refine ⟨15951899453687467713721715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42538398543166580569924573 15951899453687467713721715)
              ·
                refine ⟨23927849180531201570582573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15951899453687467713721715 23927849180531201570582573)
                ·
                  refine ⟨8972943442699200588968465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23927849180531201570582573 8972943442699200588968465)
                  ·
                    refine ⟨6729707582024400441726349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8972943442699200588968465 6729707582024400441726349)
                    ·
                      refine ⟨2523640343259150165647381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6729707582024400441726349 2523640343259150165647381)
                      ·
                        rfl

theorem cell23_4914772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_4914772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914772 prefixEnd_4914772 := by exact prefixLift 4914772
  have htrace : WordTrace (prefixWord ++ tailWord_4914772) baseStart_4914772 baseEnd_4914772 := by
    simpa [prefixWord, tailWord_4914772, baseEnd_4914772] using wordTrace_append hprefix tailTrace_4914772
  have hstable : (prefixWord ++ tailWord_4914772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914772).length < 2 ^ (prefixWord ++ tailWord_4914772).sum := by decide
  have hdescent : baseEnd_4914772 < baseStart_4914772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914845 : List Nat := [1, 4, 2, 1, 1, 1, 1, 3, 1, 3, 5]
def baseStart_4914845 : Nat := 118140960795 + 4914845 * 2 ^ 59
def prefixEnd_4914845 : Nat := 4983230072969 + 3 ^ 40 * 4914845 * 2
def baseEnd_4914845 : Nat := 2523677827346928380034545

theorem tailTrace_4914845 : CollatzResearch.WordTrace tailWord_4914845 prefixEnd_4914845 2523677827346928380034545 := by
  unfold tailWord_4914845
  simp only [CollatzResearch.WordTrace]
  refine ⟨179259123879363428543961989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119506082586242285695974659 179259123879363428543961989)
  ·
    refine ⟨33611085727380642851992873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 179259123879363428543961989 33611085727380642851992873)
    ·
      refine ⟨25208314295535482138994655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33611085727380642851992873 25208314295535482138994655)
      ·
        refine ⟨37812471443303223208491983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25208314295535482138994655 37812471443303223208491983)
        ·
          refine ⟨56718707164954834812737975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37812471443303223208491983 56718707164954834812737975)
          ·
            refine ⟨85078060747432252219106963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56718707164954834812737975 85078060747432252219106963)
            ·
              refine ⟨127617091121148378328660445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85078060747432252219106963 127617091121148378328660445)
              ·
                refine ⟨47856409170430641873247667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127617091121148378328660445 47856409170430641873247667)
                ·
                  refine ⟨71784613755645962809871501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47856409170430641873247667 71784613755645962809871501)
                  ·
                    refine ⟨26919230158367236053701813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71784613755645962809871501 26919230158367236053701813)
                    ·
                      refine ⟨2523677827346928380034545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26919230158367236053701813 2523677827346928380034545)
                      ·
                        rfl

theorem cell23_4914845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_4914845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914845 prefixEnd_4914845 := by exact prefixLift 4914845
  have htrace : WordTrace (prefixWord ++ tailWord_4914845) baseStart_4914845 baseEnd_4914845 := by
    simpa [prefixWord, tailWord_4914845, baseEnd_4914845] using wordTrace_append hprefix tailTrace_4914845
  have hstable : (prefixWord ++ tailWord_4914845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914845).length < 2 ^ (prefixWord ++ tailWord_4914845).sum := by decide
  have hdescent : baseEnd_4914845 < baseStart_4914845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914870 : List Nat := [5, 1, 3, 1, 1, 2, 3, 1, 2, 1, 3]
def baseStart_4914870 : Nat := 118140960795 + 4914870 * 2 ^ 59
def prefixEnd_4914870 : Nat := 4983230072969 + 3 ^ 40 * 4914870 * 2
def baseEnd_4914870 : Nat := 2523690664363290782221931

theorem tailTrace_4914870 : CollatzResearch.WordTrace tailWord_4914870 prefixEnd_4914870 2523690664363290782221931 := by
  unfold tailWord_4914870
  simp only [CollatzResearch.WordTrace]
  refine ⟨11203752231517053613351379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 119506690469515238542414709 11203752231517053613351379)
  ·
    refine ⟨16805628347275580420027069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11203752231517053613351379 16805628347275580420027069)
    ·
      refine ⟨6302110630228342657510151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16805628347275580420027069 6302110630228342657510151)
      ·
        refine ⟨9453165945342513986265227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6302110630228342657510151 9453165945342513986265227)
        ·
          refine ⟨14179748918013770979397841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9453165945342513986265227 14179748918013770979397841)
          ·
            refine ⟨10634811688510328234548381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14179748918013770979397841 10634811688510328234548381)
            ·
              refine ⟨3988054383191373087955643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10634811688510328234548381 3988054383191373087955643)
              ·
                refine ⟨5982081574787059631933465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3988054383191373087955643 5982081574787059631933465)
                ·
                  refine ⟨4486561181090294723950099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5982081574787059631933465 4486561181090294723950099)
                  ·
                    refine ⟨6729841771635442085925149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4486561181090294723950099 6729841771635442085925149)
                    ·
                      refine ⟨2523690664363290782221931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6729841771635442085925149 2523690664363290782221931)
                      ·
                        rfl

theorem cell23_4914870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_4914870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914870 prefixEnd_4914870 := by exact prefixLift 4914870
  have htrace : WordTrace (prefixWord ++ tailWord_4914870) baseStart_4914870 baseEnd_4914870 := by
    simpa [prefixWord, tailWord_4914870, baseEnd_4914870] using wordTrace_append hprefix tailTrace_4914870
  have hstable : (prefixWord ++ tailWord_4914870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914870).length < 2 ^ (prefixWord ++ tailWord_4914870).sum := by decide
  have hdescent : baseEnd_4914870 < baseStart_4914870 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914876 : List Nat := [2, 2, 2, 3, 1, 4, 1, 1, 1, 4, 2]
def baseStart_4914876 : Nat := 118140960795 + 4914876 * 2 ^ 59
def prefixEnd_4914876 : Nat := 4983230072969 + 3 ^ 40 * 4914876 * 2
def baseEnd_4914876 : Nat := 2523693745247217758746903

theorem tailTrace_4914876 : CollatzResearch.WordTrace tailWord_4914876 prefixEnd_4914876 2523693745247217758746903 := by
  unfold tailWord_4914876
  simp only [CollatzResearch.WordTrace]
  refine ⟨89630127271125560419170241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119506836361500747225560321 89630127271125560419170241)
  ·
    refine ⟨67222595453344170314377681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89630127271125560419170241 67222595453344170314377681)
    ·
      refine ⟨50416946590008127735783261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67222595453344170314377681 50416946590008127735783261)
      ·
        refine ⟨18906354971253047900918723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50416946590008127735783261 18906354971253047900918723)
        ·
          refine ⟨28359532456879571851378085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18906354971253047900918723 28359532456879571851378085)
          ·
            refine ⟨5317412335664919722133391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28359532456879571851378085 5317412335664919722133391)
            ·
              refine ⟨7976118503497379583200087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5317412335664919722133391 7976118503497379583200087)
              ·
                refine ⟨11964177755246069374800131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7976118503497379583200087 11964177755246069374800131)
                ·
                  refine ⟨17946266632869104062200197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11964177755246069374800131 17946266632869104062200197)
                  ·
                    refine ⟨3364924993662957011662537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17946266632869104062200197 3364924993662957011662537)
                    ·
                      refine ⟨2523693745247217758746903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3364924993662957011662537 2523693745247217758746903)
                      ·
                        rfl

theorem cell23_4914876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_4914876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914876 prefixEnd_4914876 := by exact prefixLift 4914876
  have htrace : WordTrace (prefixWord ++ tailWord_4914876) baseStart_4914876 baseEnd_4914876 := by
    simpa [prefixWord, tailWord_4914876, baseEnd_4914876] using wordTrace_append hprefix tailTrace_4914876
  have hstable : (prefixWord ++ tailWord_4914876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914876).length < 2 ^ (prefixWord ++ tailWord_4914876).sum := by decide
  have hdescent : baseEnd_4914876 < baseStart_4914876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914893 : List Nat := [1, 6, 2, 1, 1, 1, 1, 2, 4, 2, 2]
def baseStart_4914893 : Nat := 118140960795 + 4914893 * 2 ^ 59
def prefixEnd_4914893 : Nat := 4983230072969 + 3 ^ 40 * 4914893 * 2
def baseEnd_4914893 : Nat := 2523702474418344192234325

theorem tailTrace_4914893 : CollatzResearch.WordTrace tailWord_4914893 prefixEnd_4914893 2523702474418344192234325 := by
  unfold tailWord_4914893
  simp only [CollatzResearch.WordTrace]
  refine ⟨179260874583189532741709333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119507249722126355161139555 179260874583189532741709333)
  ·
    refine ⟨8402853496087009347267625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 179260874583189532741709333 8402853496087009347267625)
    ·
      refine ⟨6302140122065257010450719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8402853496087009347267625 6302140122065257010450719)
      ·
        refine ⟨9453210183097885515676079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6302140122065257010450719 9453210183097885515676079)
        ·
          refine ⟨14179815274646828273514119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9453210183097885515676079 14179815274646828273514119)
          ·
            refine ⟨21269722911970242410271179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14179815274646828273514119 21269722911970242410271179)
            ·
              refine ⟨31904584367955363615406769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21269722911970242410271179 31904584367955363615406769)
              ·
                refine ⟨23928438275966522711555077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31904584367955363615406769 23928438275966522711555077)
                ·
                  refine ⟨4486582176743723008416577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23928438275966522711555077 4486582176743723008416577)
                  ·
                    refine ⟨3364936632557792256312433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4486582176743723008416577 3364936632557792256312433)
                    ·
                      refine ⟨2523702474418344192234325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3364936632557792256312433 2523702474418344192234325)
                      ·
                        rfl

theorem cell23_4914893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_4914893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914893 prefixEnd_4914893 := by exact prefixLift 4914893
  have htrace : WordTrace (prefixWord ++ tailWord_4914893) baseStart_4914893 baseEnd_4914893 := by
    simpa [prefixWord, tailWord_4914893, baseEnd_4914893] using wordTrace_append hprefix tailTrace_4914893
  have hstable : (prefixWord ++ tailWord_4914893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914893).length < 2 ^ (prefixWord ++ tailWord_4914893).sum := by decide
  have hdescent : baseEnd_4914893 < baseStart_4914893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914895 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 6, 5]
def baseStart_4914895 : Nat := 118140960795 + 4914895 * 2 ^ 59
def prefixEnd_4914895 : Nat := 4983230072969 + 3 ^ 40 * 4914895 * 2
def baseEnd_4914895 : Nat := 841234500459884394803105

theorem tailTrace_4914895 : CollatzResearch.WordTrace tailWord_4914895 prefixEnd_4914895 841234500459884394803105 := by
  unfold tailWord_4914895
  simp only [CollatzResearch.WordTrace]
  refine ⟨179260947529182287083282139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119507298352788191388854759 179260947529182287083282139)
  ·
    refine ⟨268891421293773430624923209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179260947529182287083282139 268891421293773430624923209)
    ·
      refine ⟨201668565970330072968692407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268891421293773430624923209 201668565970330072968692407)
      ·
        refine ⟨302502848955495109453038611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201668565970330072968692407 302502848955495109453038611)
        ·
          refine ⟨453754273433242664179557917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302502848955495109453038611 453754273433242664179557917)
          ·
            refine ⟨170157852537465999067334219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 453754273433242664179557917 170157852537465999067334219)
            ·
              refine ⟨255236778806198998601001329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170157852537465999067334219 255236778806198998601001329)
              ·
                refine ⟨191427584104649248950750997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 255236778806198998601001329 191427584104649248950750997)
                ·
                  refine ⟨8973168004905433544566453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 191427584104649248950750997 8973168004905433544566453)
                  ·
                    refine ⟨841234500459884394803105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8973168004905433544566453 841234500459884394803105)
                    ·
                      rfl

theorem cell23_4914895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 6, 5].length) (baseStart_4914895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914895 prefixEnd_4914895 := by exact prefixLift 4914895
  have htrace : WordTrace (prefixWord ++ tailWord_4914895) baseStart_4914895 baseEnd_4914895 := by
    simpa [prefixWord, tailWord_4914895, baseEnd_4914895] using wordTrace_append hprefix tailTrace_4914895
  have hstable : (prefixWord ++ tailWord_4914895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914895).length < 2 ^ (prefixWord ++ tailWord_4914895).sum := by decide
  have hdescent : baseEnd_4914895 < baseStart_4914895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914955 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 10]
def baseStart_4914955 : Nat := 118140960795 + 4914955 * 2 ^ 59
def prefixEnd_4914955 : Nat := 4983230072969 + 3 ^ 40 * 4914955 * 2
def baseEnd_4914955 : Nat := 280414923357658105517671

theorem tailTrace_4914955 : CollatzResearch.WordTrace tailWord_4914955 prefixEnd_4914955 280414923357658105517671 := by
  unfold tailWord_4914955
  simp only [CollatzResearch.WordTrace]
  refine ⟨179263135908964917330466319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119508757272643278220310879 179263135908964917330466319)
  ·
    refine ⟨268894703863447375995699479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179263135908964917330466319 268894703863447375995699479)
    ·
      refine ⟨403342055795171063993549219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268894703863447375995699479 403342055795171063993549219)
      ·
        refine ⟨605013083692756595990323829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 403342055795171063993549219 605013083692756595990323829)
        ·
          refine ⟨56719976596195930874092859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 605013083692756595990323829 56719976596195930874092859)
          ·
            refine ⟨85079964894293896311139289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56719976596195930874092859 85079964894293896311139289)
            ·
              refine ⟨63809973670720422233354467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85079964894293896311139289 63809973670720422233354467)
              ·
                refine ⟨95714960506080633350031701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63809973670720422233354467 95714960506080633350031701)
                ·
                  refine ⟨280414923357658105517671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 95714960506080633350031701 280414923357658105517671)
                  ·
                    rfl

theorem cell23_4914955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 10].length) (baseStart_4914955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914955 prefixEnd_4914955 := by exact prefixLift 4914955
  have htrace : WordTrace (prefixWord ++ tailWord_4914955) baseStart_4914955 baseEnd_4914955 := by
    simpa [prefixWord, tailWord_4914955, baseEnd_4914955] using wordTrace_append hprefix tailTrace_4914955
  have hstable : (prefixWord ++ tailWord_4914955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914955).length < 2 ^ (prefixWord ++ tailWord_4914955).sum := by decide
  have hdescent : baseEnd_4914955 < baseStart_4914955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914976 : List Nat := [2, 1, 1, 5, 1, 1, 3, 4, 1, 4]
def baseStart_4914976 : Nat := 118140960795 + 4914976 * 2 ^ 59
def prefixEnd_4914976 : Nat := 4983230072969 + 3 ^ 40 * 4914976 * 2
def baseEnd_4914976 : Nat := 841248364437555789165481

theorem tailTrace_4914976 : CollatzResearch.WordTrace tailWord_4914976 prefixEnd_4914976 841248364437555789165481 := by
  unfold tailWord_4914976
  simp only [CollatzResearch.WordTrace]
  refine ⟨89631950920944418958490391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119509267894592558611320521 89631950920944418958490391)
  ·
    refine ⟨134447926381416628437735587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89631950920944418958490391 134447926381416628437735587)
    ·
      refine ⟨201671889572124942656603381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134447926381416628437735587 201671889572124942656603381)
      ·
        refine ⟨18906739647386713374056567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 201671889572124942656603381 18906739647386713374056567)
        ·
          refine ⟨28360109471080070061084851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18906739647386713374056567 28360109471080070061084851)
          ·
            refine ⟨42540164206620105091627277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28360109471080070061084851 42540164206620105091627277)
            ·
              refine ⟨15952561577482539409360229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42540164206620105091627277 15952561577482539409360229)
              ·
                refine ⟨2991105295777976139255043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15952561577482539409360229 2991105295777976139255043)
                ·
                  refine ⟨4486657943666964208882565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2991105295777976139255043 4486657943666964208882565)
                  ·
                    refine ⟨841248364437555789165481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4486657943666964208882565 841248364437555789165481)
                    ·
                      rfl

theorem cell23_4914976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 4, 1, 4].length) (baseStart_4914976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914976 prefixEnd_4914976 := by exact prefixLift 4914976
  have htrace : WordTrace (prefixWord ++ tailWord_4914976) baseStart_4914976 baseEnd_4914976 := by
    simpa [prefixWord, tailWord_4914976, baseEnd_4914976] using wordTrace_append hprefix tailTrace_4914976
  have hstable : (prefixWord ++ tailWord_4914976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914976).length < 2 ^ (prefixWord ++ tailWord_4914976).sum := by decide
  have hdescent : baseEnd_4914976 < baseStart_4914976 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914985 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 1, 11]
def baseStart_4914985 : Nat := 118140960795 + 4914985 * 2 ^ 59
def prefixEnd_4914985 : Nat := 4983230072969 + 3 ^ 40 * 4914985 * 2
def baseEnd_4914985 : Nat := 841249904879519277427967

theorem tailTrace_4914985 : CollatzResearch.WordTrace tailWord_4914985 prefixEnd_4914985 841249904879519277427967 := by
  unfold tailWord_4914985
  simp only [CollatzResearch.WordTrace]
  refine ⟨179264230098856232454058409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119509486732570821636038939 179264230098856232454058409)
  ·
    refine ⟨134448172574142174340543807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179264230098856232454058409 134448172574142174340543807)
    ·
      refine ⟨201672258861213261510815711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134448172574142174340543807 201672258861213261510815711)
      ·
        refine ⟨302508388291819892266223567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201672258861213261510815711 302508388291819892266223567)
        ·
          refine ⟨453762582437729838399335351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302508388291819892266223567 453762582437729838399335351)
          ·
            refine ⟨680643873656594757599003027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 453762582437729838399335351 680643873656594757599003027)
            ·
              refine ⟨1020965810484892136398504541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 680643873656594757599003027 1020965810484892136398504541)
              ·
                refine ⟨382862178931834551149439203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1020965810484892136398504541 382862178931834551149439203)
                ·
                  refine ⟨574293268397751826724158805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 382862178931834551149439203 574293268397751826724158805)
                  ·
                    refine ⟨841249904879519277427967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 574293268397751826724158805 841249904879519277427967)
                    ·
                      rfl

theorem cell23_4914985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 11].length) (baseStart_4914985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914985 prefixEnd_4914985 := by exact prefixLift 4914985
  have htrace : WordTrace (prefixWord ++ tailWord_4914985) baseStart_4914985 baseEnd_4914985 := by
    simpa [prefixWord, tailWord_4914985, baseEnd_4914985] using wordTrace_append hprefix tailTrace_4914985
  have hstable : (prefixWord ++ tailWord_4914985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914985).length < 2 ^ (prefixWord ++ tailWord_4914985).sum := by decide
  have hdescent : baseEnd_4914985 < baseStart_4914985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4915049 : List Nat := [1, 2, 1, 1, 1, 3, 1, 7, 2, 4]
def baseStart_4915049 : Nat := 118140960795 + 4915049 * 2 ^ 59
def prefixEnd_4915049 : Nat := 4983230072969 + 3 ^ 40 * 4915049 * 2
def baseEnd_4915049 : Nat := 841260859133481860627869

theorem tailTrace_4915049 : CollatzResearch.WordTrace tailWord_4915049 prefixEnd_4915049 841260859133481860627869 := by
  unfold tailWord_4915049
  simp only [CollatzResearch.WordTrace]
  refine ⟨179266564370624371384388201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119511042913749580922925467 179266564370624371384388201)
  ·
    refine ⟨134449923277968278538291151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179266564370624371384388201 134449923277968278538291151)
    ·
      refine ⟨201674884916952417807436727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134449923277968278538291151 201674884916952417807436727)
      ·
        refine ⟨302512327375428626711155091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201674884916952417807436727 302512327375428626711155091)
        ·
          refine ⟨453768491063142940066732637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302512327375428626711155091 453768491063142940066732637)
          ·
            refine ⟨170163184148678602525024739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 453768491063142940066732637 170163184148678602525024739)
            ·
              refine ⟨255244776223017903787537109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170163184148678602525024739 255244776223017903787537109)
              ·
                refine ⟨5982299442726982120020401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 255244776223017903787537109 5982299442726982120020401)
                ·
                  refine ⟨4486724582045236590015301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5982299442726982120020401 4486724582045236590015301)
                  ·
                    refine ⟨841260859133481860627869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4486724582045236590015301 841260859133481860627869)
                    ·
                      rfl

theorem cell23_4915049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 7, 2, 4].length) (baseStart_4915049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4915049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4915049 prefixEnd_4915049 := by exact prefixLift 4915049
  have htrace : WordTrace (prefixWord ++ tailWord_4915049) baseStart_4915049 baseEnd_4915049 := by
    simpa [prefixWord, tailWord_4915049, baseEnd_4915049] using wordTrace_append hprefix tailTrace_4915049
  have hstable : (prefixWord ++ tailWord_4915049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4915049).length < 2 ^ (prefixWord ++ tailWord_4915049).sum := by decide
  have hdescent : baseEnd_4915049 < baseStart_4915049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4915049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4915076 : List Nat := [2, 3, 2, 1, 1, 1, 4, 3, 1, 2, 3]
def baseStart_4915076 : Nat := 118140960795 + 4915076 * 2 ^ 59
def prefixEnd_4915076 : Nat := 4983230072969 + 3 ^ 40 * 4915076 * 2
def baseEnd_4915076 : Nat := 2523796441378116976245983

theorem tailTrace_4915076 : CollatzResearch.WordTrace tailWord_4915076 prefixEnd_4915076 2523796441378116976245983 := by
  unfold tailWord_4915076
  simp only [CollatzResearch.WordTrace]
  refine ⟨89633774570763277497810541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119511699427684369997080721 89633774570763277497810541)
  ·
    refine ⟨33612665464036229061678953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89633774570763277497810541 33612665464036229061678953)
    ·
      refine ⟨25209499098027171796259215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33612665464036229061678953 25209499098027171796259215)
      ·
        refine ⟨37814248647040757694388823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25209499098027171796259215 37814248647040757694388823)
        ·
          refine ⟨56721372970561136541583235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37814248647040757694388823 56721372970561136541583235)
          ·
            refine ⟨85082059455841704812374853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56721372970561136541583235 85082059455841704812374853)
            ·
              refine ⟨15952886147970319652320285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85082059455841704812374853 15952886147970319652320285)
              ·
                refine ⟨5982332305488869869620107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15952886147970319652320285 5982332305488869869620107)
                ·
                  refine ⟨8973498458233304804430161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5982332305488869869620107 8973498458233304804430161)
                  ·
                    refine ⟨6730123843674978603322621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8973498458233304804430161 6730123843674978603322621)
                    ·
                      refine ⟨2523796441378116976245983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6730123843674978603322621 2523796441378116976245983)
                      ·
                        rfl

theorem cell23_4915076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_4915076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4915076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4915076 prefixEnd_4915076 := by exact prefixLift 4915076
  have htrace : WordTrace (prefixWord ++ tailWord_4915076) baseStart_4915076 baseEnd_4915076 := by
    simpa [prefixWord, tailWord_4915076, baseEnd_4915076] using wordTrace_append hprefix tailTrace_4915076
  have hstable : (prefixWord ++ tailWord_4915076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4915076).length < 2 ^ (prefixWord ++ tailWord_4915076).sum := by decide
  have hdescent : baseEnd_4915076 < baseStart_4915076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4915076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4915079 : List Nat := [1, 1, 4, 2, 4, 2, 9]
def baseStart_4915079 : Nat := 118140960795 + 4915079 * 2 ^ 59
def prefixEnd_4915079 : Nat := 4983230072969 + 3 ^ 40 * 4915079 * 2
def baseEnd_4915079 : Nat := 31157999775556548944549

theorem tailTrace_4915079 : CollatzResearch.WordTrace tailWord_4915079 prefixEnd_4915079 31157999775556548944549 := by
  unfold tailWord_4915079
  simp only [CollatzResearch.WordTrace]
  refine ⟨179267658560515686507980291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119511772373677124338653527 179267658560515686507980291)
  ·
    refine ⟨268901487840773529761970437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179267658560515686507980291 268901487840773529761970437)
    ·
      refine ⟨50419028970145036830369457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 268901487840773529761970437 50419028970145036830369457)
      ·
        refine ⟨37814271727608777622777093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50419028970145036830369457 37814271727608777622777093)
        ·
          refine ⟨7090175948926645804270705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37814271727608777622777093 7090175948926645804270705)
          ·
            refine ⟨5317631961694984353203029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7090175948926645804270705 5317631961694984353203029)
            ·
              refine ⟨31157999775556548944549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5317631961694984353203029 31157999775556548944549)
              ·
                rfl

theorem cell23_4915079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 9].length) (baseStart_4915079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4915079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4915079 prefixEnd_4915079 := by exact prefixLift 4915079
  have htrace : WordTrace (prefixWord ++ tailWord_4915079) baseStart_4915079 baseEnd_4915079 := by
    simpa [prefixWord, tailWord_4915079, baseEnd_4915079] using wordTrace_append hprefix tailTrace_4915079
  have hstable : (prefixWord ++ tailWord_4915079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4915079).length < 2 ^ (prefixWord ++ tailWord_4915079).sum := by decide
  have hdescent : baseEnd_4915079 < baseStart_4915079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4915079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4915090 : List Nat := [3, 2, 3, 2, 1, 1, 3, 1, 3, 2, 2]
def baseStart_4915090 : Nat := 118140960795 + 4915090 * 2 ^ 59
def prefixEnd_4915090 : Nat := 4983230072969 + 3 ^ 40 * 4915090 * 2
def baseEnd_4915090 : Nat := 2523803630107279921470919

theorem tailTrace_4915090 : CollatzResearch.WordTrace tailWord_4915090 prefixEnd_4915090 2523803630107279921470919 := by
  unfold tailWord_4915090
  simp only [CollatzResearch.WordTrace]
  refine ⟨44817014940868958846657681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119512039842317223591087149 44817014940868958846657681)
  ·
    refine ⟨33612761205651719134993261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44817014940868958846657681 33612761205651719134993261)
    ·
      refine ⟨12604785452119394675622473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33612761205651719134993261 12604785452119394675622473)
      ·
        refine ⟨9453589089089546006716855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12604785452119394675622473 9453589089089546006716855)
        ·
          refine ⟨14180383633634319010075283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9453589089089546006716855 14180383633634319010075283)
          ·
            refine ⟨21270575450451478515112925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14180383633634319010075283 21270575450451478515112925)
            ·
              refine ⟨7976465793919304443167347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21270575450451478515112925 7976465793919304443167347)
              ·
                refine ⟨11964698690878956664751021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7976465793919304443167347 11964698690878956664751021)
                ·
                  refine ⟨4486762009079608749281633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11964698690878956664751021 4486762009079608749281633)
                  ·
                    refine ⟨3365071506809706561961225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4486762009079608749281633 3365071506809706561961225)
                    ·
                      refine ⟨2523803630107279921470919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3365071506809706561961225 2523803630107279921470919)
                      ·
                        rfl

theorem cell23_4915090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_4915090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4915090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4915090 prefixEnd_4915090 := by exact prefixLift 4915090
  have htrace : WordTrace (prefixWord ++ tailWord_4915090) baseStart_4915090 baseEnd_4915090 := by
    simpa [prefixWord, tailWord_4915090, baseEnd_4915090] using wordTrace_append hprefix tailTrace_4915090
  have hstable : (prefixWord ++ tailWord_4915090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4915090).length < 2 ^ (prefixWord ++ tailWord_4915090).sum := by decide
  have hdescent : baseEnd_4915090 < baseStart_4915090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4915090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4915096 : List Nat := [2, 1, 2, 6, 1, 1, 2, 8]
def baseStart_4915096 : Nat := 118140960795 + 4915096 * 2 ^ 59
def prefixEnd_4915096 : Nat := 4983230072969 + 3 ^ 40 * 4915096 * 2
def baseEnd_4915096 : Nat := 93474322629303959185033

theorem tailTrace_4915096 : CollatzResearch.WordTrace tailWord_4915096 prefixEnd_4915096 93474322629303959185033 := by
  unfold tailWord_4915096
  simp only [CollatzResearch.WordTrace]
  refine ⟨89634139300727049205674571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119512185734302732274232761 89634139300727049205674571)
  ·
    refine ⟨134451208951090573808511857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89634139300727049205674571 134451208951090573808511857)
    ·
      refine ⟨100838406713317930356383893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134451208951090573808511857 100838406713317930356383893)
      ·
        refine ⟨4726800314686777985455495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 100838406713317930356383893 4726800314686777985455495)
        ·
          refine ⟨7090200472030166978183243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4726800314686777985455495 7090200472030166978183243)
          ·
            refine ⟨10635300708045250467274865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7090200472030166978183243 10635300708045250467274865)
            ·
              refine ⟨7976475531033937850456149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10635300708045250467274865 7976475531033937850456149)
              ·
                refine ⟨93474322629303959185033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7976475531033937850456149 93474322629303959185033)
                ·
                  rfl

theorem cell23_4915096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 8].length) (baseStart_4915096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4915096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4915096 prefixEnd_4915096 := by exact prefixLift 4915096
  have htrace : WordTrace (prefixWord ++ tailWord_4915096) baseStart_4915096 baseEnd_4915096 := by
    simpa [prefixWord, tailWord_4915096, baseEnd_4915096] using wordTrace_append hprefix tailTrace_4915096
  have hstable : (prefixWord ++ tailWord_4915096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4915096).length < 2 ^ (prefixWord ++ tailWord_4915096).sum := by decide
  have hdescent : baseEnd_4915096 < baseStart_4915096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4915096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4915100 : List Nat := [2, 2, 3, 3, 1, 3, 2, 1, 2, 4]
def baseStart_4915100 : Nat := 118140960795 + 4915100 * 2 ^ 59
def prefixEnd_4915100 : Nat := 4983230072969 + 3 ^ 40 * 4915100 * 2
def baseEnd_4915100 : Nat := 841269588304608294115291

theorem tailTrace_4915100 : CollatzResearch.WordTrace tailWord_4915100 prefixEnd_4915100 841269588304608294115291 := by
  unfold tailWord_4915100
  simp only [CollatzResearch.WordTrace]
  refine ⟨89634212246719803547247377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119512282995626404729663169 89634212246719803547247377)
  ·
    refine ⟨67225659185039852660435533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89634212246719803547247377 67225659185039852660435533)
    ·
      refine ⟨25209622194389944747663325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67225659185039852660435533 25209622194389944747663325)
      ·
        refine ⟨9453608322896229280373747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25209622194389944747663325 9453608322896229280373747)
        ·
          refine ⟨14180412484344343920560621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9453608322896229280373747 14180412484344343920560621)
          ·
            refine ⟨5317654681629128970210233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14180412484344343920560621 5317654681629128970210233)
            ·
              refine ⟨3988241011221846727657675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5317654681629128970210233 3988241011221846727657675)
              ·
                refine ⟨5982361516832770091486513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3988241011221846727657675 5982361516832770091486513)
                ·
                  refine ⟨4486771137624577568614885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5982361516832770091486513 4486771137624577568614885)
                  ·
                    refine ⟨841269588304608294115291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4486771137624577568614885 841269588304608294115291)
                    ·
                      rfl

theorem cell23_4915100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_4915100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4915100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4915100 prefixEnd_4915100 := by exact prefixLift 4915100
  have htrace : WordTrace (prefixWord ++ tailWord_4915100) baseStart_4915100 baseEnd_4915100 := by
    simpa [prefixWord, tailWord_4915100, baseEnd_4915100] using wordTrace_append hprefix tailTrace_4915100
  have hstable : (prefixWord ++ tailWord_4915100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4915100).length < 2 ^ (prefixWord ++ tailWord_4915100).sum := by decide
  have hdescent : baseEnd_4915100 < baseStart_4915100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4915100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4915159 : List Nat := [1, 1, 3, 2, 1, 1, 5, 1, 2, 2, 4]
def baseStart_4915159 : Nat := 118140960795 + 4915159 * 2 ^ 59
def prefixEnd_4915159 : Nat := 4983230072969 + 3 ^ 40 * 4915159 * 2
def baseEnd_4915159 : Nat := 2523839060272440151508101

theorem tailTrace_4915159 : CollatzResearch.WordTrace tailWord_4915159 prefixEnd_4915159 2523839060272440151508101 := by
  unfold tailWord_4915159
  simp only [CollatzResearch.WordTrace]
  refine ⟨179270576400225860170892531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119513717600150573447261687 179270576400225860170892531)
  ·
    refine ⟨268905864600338790256338797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179270576400225860170892531 268905864600338790256338797)
    ·
      refine ⟨100839699225127046346127049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 268905864600338790256338797 100839699225127046346127049)
      ·
        refine ⟨75629774418845284759595287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100839699225127046346127049 75629774418845284759595287)
        ·
          refine ⟨113444661628267927139392931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75629774418845284759595287 113444661628267927139392931)
          ·
            refine ⟨170166992442401890709089397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113444661628267927139392931 170166992442401890709089397)
            ·
              refine ⟨15953155541475177253977131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 170166992442401890709089397 15953155541475177253977131)
              ·
                refine ⟨23929733312212765880965697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15953155541475177253977131 23929733312212765880965697)
                ·
                  refine ⟨17947299984159574410724273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23929733312212765880965697 17947299984159574410724273)
                  ·
                    refine ⟨13460474988119680808043205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17947299984159574410724273 13460474988119680808043205)
                    ·
                      refine ⟨2523839060272440151508101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13460474988119680808043205 2523839060272440151508101)
                      ·
                        rfl

theorem cell23_4915159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_4915159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4915159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4915159 prefixEnd_4915159 := by exact prefixLift 4915159
  have htrace : WordTrace (prefixWord ++ tailWord_4915159) baseStart_4915159 baseEnd_4915159 := by
    simpa [prefixWord, tailWord_4915159, baseEnd_4915159] using wordTrace_append hprefix tailTrace_4915159
  have hstable : (prefixWord ++ tailWord_4915159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4915159).length < 2 ^ (prefixWord ++ tailWord_4915159).sum := by decide
  have hdescent : baseEnd_4915159 < baseStart_4915159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4915159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4915199 : List Nat := [1, 1, 2, 2, 1, 2, 1, 6, 2, 5]
def baseStart_4915199 : Nat := 118140960795 + 4915199 * 2 ^ 59
def prefixEnd_4915199 : Nat := 4983230072969 + 3 ^ 40 * 4915199 * 2
def baseEnd_4915199 : Nat := 841286533166206665002639

theorem tailTrace_4915199 : CollatzResearch.WordTrace tailWord_4915199 prefixEnd_4915199 841286533166206665002639 := by
  unfold tailWord_4915199
  simp only [CollatzResearch.WordTrace]
  refine ⟨179272035320080947002348651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119514690213387298001565767 179272035320080947002348651)
  ·
    refine ⟨268908052980121420503522977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179272035320080947002348651 268908052980121420503522977)
    ·
      refine ⟨201681039735091065377642233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268908052980121420503522977 201681039735091065377642233)
      ·
        refine ⟨151260779801318299033231675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201681039735091065377642233 151260779801318299033231675)
        ·
          refine ⟨226891169701977448549847513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151260779801318299033231675 226891169701977448549847513)
          ·
            refine ⟨170168377276483086412385635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226891169701977448549847513 170168377276483086412385635)
            ·
              refine ⟨255252565914724629618578453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170168377276483086412385635 255252565914724629618578453)
              ·
                refine ⟨11964964027252717013370865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 255252565914724629618578453 11964964027252717013370865)
                ·
                  refine ⟨8973723020439537760028149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11964964027252717013370865 8973723020439537760028149)
                  ·
                    refine ⟨841286533166206665002639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8973723020439537760028149 841286533166206665002639)
                    ·
                      rfl

theorem cell23_4915199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 2, 5].length) (baseStart_4915199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4915199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4915199 prefixEnd_4915199 := by exact prefixLift 4915199
  have htrace : WordTrace (prefixWord ++ tailWord_4915199) baseStart_4915199 baseEnd_4915199 := by
    simpa [prefixWord, tailWord_4915199, baseEnd_4915199] using wordTrace_append hprefix tailTrace_4915199
  have hstable : (prefixWord ++ tailWord_4915199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4915199).length < 2 ^ (prefixWord ++ tailWord_4915199).sum := by decide
  have hdescent : baseEnd_4915199 < baseStart_4915199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4915199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4915219 : List Nat := [1, 1, 1, 2, 1, 4, 3, 2, 1, 3, 4]
def baseStart_4915219 : Nat := 118140960795 + 4915219 * 2 ^ 59
def prefixEnd_4915219 : Nat := 4983230072969 + 3 ^ 40 * 4915219 * 2
def baseEnd_4915219 : Nat := 2523869869111709916757825

theorem tailTrace_4915219 : CollatzResearch.WordTrace tailWord_4915219 prefixEnd_4915219 2523869869111709916757825 := by
  unfold tailWord_4915219
  simp only [CollatzResearch.WordTrace]
  refine ⟨179272764780008490418076711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119515176520005660278717807 179272764780008490418076711)
  ·
    refine ⟨268909147170012735627115067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179272764780008490418076711 268909147170012735627115067)
    ·
      refine ⟨403363720755019103440672601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268909147170012735627115067 403363720755019103440672601)
      ·
        refine ⟨302522790566264327580504451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 403363720755019103440672601 302522790566264327580504451)
        ·
          refine ⟨453784185849396491370756677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302522790566264327580504451 453784185849396491370756677)
          ·
            refine ⟨85084534846761842132016877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 453784185849396491370756677 85084534846761842132016877)
            ·
              refine ⟨31906700567535690799506329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85084534846761842132016877 31906700567535690799506329)
              ·
                refine ⟨23930025425651768099629747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31906700567535690799506329 23930025425651768099629747)
                ·
                  refine ⟨35895038138477652149444621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23930025425651768099629747 35895038138477652149444621)
                  ·
                    refine ⟨13460639301929119556041733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35895038138477652149444621 13460639301929119556041733)
                    ·
                      refine ⟨2523869869111709916757825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13460639301929119556041733 2523869869111709916757825)
                      ·
                        rfl

theorem cell23_4915219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 3, 4].length) (baseStart_4915219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4915219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4915219 prefixEnd_4915219 := by exact prefixLift 4915219
  have htrace : WordTrace (prefixWord ++ tailWord_4915219) baseStart_4915219 baseEnd_4915219 := by
    simpa [prefixWord, tailWord_4915219, baseEnd_4915219] using wordTrace_append hprefix tailTrace_4915219
  have hstable : (prefixWord ++ tailWord_4915219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4915219).length < 2 ^ (prefixWord ++ tailWord_4915219).sum := by decide
  have hdescent : baseEnd_4915219 < baseStart_4915219 := by decide
  rcases family_descends (prefixWord ++ tailWord_4915219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4915263 : List Nat := [1, 1, 2, 2, 3, 1, 2, 6, 1, 4]
def baseStart_4915263 : Nat := 118140960795 + 4915263 * 2 ^ 59
def prefixEnd_4915263 : Nat := 4983230072969 + 3 ^ 40 * 4915263 * 2
def baseEnd_4915263 : Nat := 841297487420169248202541

theorem tailTrace_4915263 : CollatzResearch.WordTrace tailWord_4915263 prefixEnd_4915263 841297487420169248202541 := by
  unfold tailWord_4915263
  simp only [CollatzResearch.WordTrace]
  refine ⟨179274369591849085932678443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119516246394566057288452295 179274369591849085932678443)
  ·
    refine ⟨268911554387773628899017665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179274369591849085932678443 268911554387773628899017665)
    ·
      refine ⟨201683665790830221674263249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268911554387773628899017665 201683665790830221674263249)
      ·
        refine ⟨151262749343122666255697437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201683665790830221674263249 151262749343122666255697437)
        ·
          refine ⟨56723531003670999845886539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151262749343122666255697437 56723531003670999845886539)
          ·
            refine ⟨85085296505506499768829809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56723531003670999845886539 85085296505506499768829809)
            ·
              refine ⟨63813972379129874826622357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85085296505506499768829809 63813972379129874826622357)
              ·
                refine ⟨2991279955271712882497923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 63813972379129874826622357 2991279955271712882497923)
                ·
                  refine ⟨4486919932907569323746885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2991279955271712882497923 4486919932907569323746885)
                  ·
                    refine ⟨841297487420169248202541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4486919932907569323746885 841297487420169248202541)
                    ·
                      rfl

theorem cell23_4915263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 6, 1, 4].length) (baseStart_4915263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4915263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4915263 prefixEnd_4915263 := by exact prefixLift 4915263
  have htrace : WordTrace (prefixWord ++ tailWord_4915263) baseStart_4915263 baseEnd_4915263 := by
    simpa [prefixWord, tailWord_4915263, baseEnd_4915263] using wordTrace_append hprefix tailTrace_4915263
  have hstable : (prefixWord ++ tailWord_4915263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4915263).length < 2 ^ (prefixWord ++ tailWord_4915263).sum := by decide
  have hdescent : baseEnd_4915263 < baseStart_4915263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4915263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4915270 : List Nat := [6, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2]
def baseStart_4915270 : Nat := 118140960795 + 4915270 * 2 ^ 59
def prefixEnd_4915270 : Nat := 4983230072969 + 3 ^ 40 * 4915270 * 2
def baseEnd_4915270 : Nat := 2523896056625089217220091

theorem tailTrace_4915270 : CollatzResearch.WordTrace tailWord_4915270 prefixEnd_4915270 2523896056625089217220091 := by
  unfold tailWord_4915270
  simp only [CollatzResearch.WordTrace]
  refine ⟨5602332028213241441505727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 119516416601882484085455509 5602332028213241441505727)
  ·
    refine ⟨8403498042319862162258591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5602332028213241441505727 8403498042319862162258591)
    ·
      refine ⟨12605247063479793243387887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8403498042319862162258591 12605247063479793243387887)
      ·
        refine ⟨18907870595219689865081831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12605247063479793243387887 18907870595219689865081831)
        ·
          refine ⟨28361805892829534797622747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18907870595219689865081831 28361805892829534797622747)
          ·
            refine ⟨42542708839244302196434121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28361805892829534797622747 42542708839244302196434121)
            ·
              refine ⟨31907031629433226647325591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42542708839244302196434121 31907031629433226647325591)
              ·
                refine ⟨47860547444149839970988387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31907031629433226647325591 47860547444149839970988387)
                ·
                  refine ⟨71790821166224759956482581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47860547444149839970988387 71790821166224759956482581)
                  ·
                    refine ⟨3365194742166785622960121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 71790821166224759956482581 3365194742166785622960121)
                    ·
                      refine ⟨2523896056625089217220091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3365194742166785622960121 2523896056625089217220091)
                      ·
                        rfl

theorem cell23_4915270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_4915270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4915270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4915270 prefixEnd_4915270 := by exact prefixLift 4915270
  have htrace : WordTrace (prefixWord ++ tailWord_4915270) baseStart_4915270 baseEnd_4915270 := by
    simpa [prefixWord, tailWord_4915270, baseEnd_4915270] using wordTrace_append hprefix tailTrace_4915270
  have hstable : (prefixWord ++ tailWord_4915270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4915270).length < 2 ^ (prefixWord ++ tailWord_4915270).sum := by decide
  have hdescent : baseEnd_4915270 < baseStart_4915270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4915270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4915313 : List Nat := [1, 2, 2, 2, 1, 1, 3, 4, 2, 3, 2]
def baseStart_4915313 : Nat := 118140960795 + 4915313 * 2 ^ 59
def prefixEnd_4915313 : Nat := 4983230072969 + 3 ^ 40 * 4915313 * 2
def baseEnd_4915313 : Nat := 2523918136293232548982393

theorem tailTrace_4915313 : CollatzResearch.WordTrace tailWord_4915313 prefixEnd_4915313 2523918136293232548982393 := by
  unfold tailWord_4915313
  simp only [CollatzResearch.WordTrace]
  refine ⟨179276193241667944471998593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119517462161111962981332395 179276193241667944471998593)
  ·
    refine ⟨134457144931250958353998945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179276193241667944471998593 134457144931250958353998945)
    ·
      refine ⟨100842858698438218765499209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134457144931250958353998945 100842858698438218765499209)
      ·
        refine ⟨75632144023828664074124407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100842858698438218765499209 75632144023828664074124407)
        ·
          refine ⟨113448216035742996111186611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75632144023828664074124407 113448216035742996111186611)
          ·
            refine ⟨170172324053614494166779917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113448216035742996111186611 170172324053614494166779917)
            ·
              refine ⟨63814621520105435312542469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 170172324053614494166779917 63814621520105435312542469)
              ·
                refine ⟨11965241535019769121101713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63814621520105435312542469 11965241535019769121101713)
                ·
                  refine ⟨8973931151264826840826285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11965241535019769121101713 8973931151264826840826285)
                  ·
                    refine ⟨3365224181724310065309857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8973931151264826840826285 3365224181724310065309857)
                    ·
                      refine ⟨2523918136293232548982393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3365224181724310065309857 2523918136293232548982393)
                      ·
                        rfl

theorem cell23_4915313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 2, 3, 2].length) (baseStart_4915313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4915313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4915313 prefixEnd_4915313 := by exact prefixLift 4915313
  have htrace : WordTrace (prefixWord ++ tailWord_4915313) baseStart_4915313 baseEnd_4915313 := by
    simpa [prefixWord, tailWord_4915313, baseEnd_4915313] using wordTrace_append hprefix tailTrace_4915313
  have hstable : (prefixWord ++ tailWord_4915313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4915313).length < 2 ^ (prefixWord ++ tailWord_4915313).sum := by decide
  have hdescent : baseEnd_4915313 < baseStart_4915313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4915313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4915354 : List Nat := [3, 1, 1, 5, 2, 1, 2, 3, 1, 1, 3]
def baseStart_4915354 : Nat := 118140960795 + 4915354 * 2 ^ 59
def prefixEnd_4915354 : Nat := 4983230072969 + 3 ^ 40 * 4915354 * 2
def baseEnd_4915354 : Nat := 2523939189000066888569705

theorem tailTrace_4915354 : CollatzResearch.WordTrace tailWord_4915354 prefixEnd_4915354 2523939189000066888569705 := by
  unfold tailWord_4915354
  simp only [CollatzResearch.WordTrace]
  refine ⟨44819422158629852118560279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119518459089679605649494077 44819422158629852118560279)
  ·
    refine ⟨67229133237944778177840419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44819422158629852118560279 67229133237944778177840419)
    ·
      refine ⟨100843699856917167266760629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67229133237944778177840419 100843699856917167266760629)
      ·
        refine ⟨9454096861585984431258809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 100843699856917167266760629 9454096861585984431258809)
        ·
          refine ⟨7090572646189488323444107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9454096861585984431258809 7090572646189488323444107)
          ·
            refine ⟨10635858969284232485166161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7090572646189488323444107 10635858969284232485166161)
            ·
              refine ⟨7976894226963174363874621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10635858969284232485166161 7976894226963174363874621)
              ·
                refine ⟨2991335335111190386452983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7976894226963174363874621 2991335335111190386452983)
                ·
                  refine ⟨4487003002666785579679475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2991335335111190386452983 4487003002666785579679475)
                  ·
                    refine ⟨6730504504000178369519213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4487003002666785579679475 6730504504000178369519213)
                    ·
                      refine ⟨2523939189000066888569705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6730504504000178369519213 2523939189000066888569705)
                      ·
                        rfl

theorem cell23_4915354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_4915354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4915354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4915354 prefixEnd_4915354 := by exact prefixLift 4915354
  have htrace : WordTrace (prefixWord ++ tailWord_4915354) baseStart_4915354 baseEnd_4915354 := by
    simpa [prefixWord, tailWord_4915354, baseEnd_4915354] using wordTrace_append hprefix tailTrace_4915354
  have hstable : (prefixWord ++ tailWord_4915354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4915354).length < 2 ^ (prefixWord ++ tailWord_4915354).sum := by decide
  have hdescent : baseEnd_4915354 < baseStart_4915354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4915354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4915360 : List Nat := [2, 1, 1, 4, 2, 2, 4, 1, 1, 1, 4]
def baseStart_4915360 : Nat := 118140960795 + 4915360 * 2 ^ 59
def prefixEnd_4915360 : Nat := 4983230072969 + 3 ^ 40 * 4915360 * 2
def baseEnd_4915360 : Nat := 2523942269883993865094677

theorem tailTrace_4915360 : CollatzResearch.WordTrace tailWord_4915360 prefixEnd_4915360 2523942269883993865094677 := by
  unfold tailWord_4915360
  simp only [CollatzResearch.WordTrace]
  refine ⟨89638953736248835749479767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119518604981665114332639689 89638953736248835749479767)
  ·
    refine ⟨134458430604373253624219651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89638953736248835749479767 134458430604373253624219651)
    ·
      refine ⟨201687645906559880436329477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134458430604373253624219651 201687645906559880436329477)
      ·
        refine ⟨37816433607479977581811777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 201687645906559880436329477 37816433607479977581811777)
        ·
          refine ⟨28362325205609983186358833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37816433607479977581811777 28362325205609983186358833)
          ·
            refine ⟨21271743904207487389769125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28362325205609983186358833 21271743904207487389769125)
            ·
              refine ⟨3988451982038903885581711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21271743904207487389769125 3988451982038903885581711)
              ·
                refine ⟨5982677973058355828372567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3988451982038903885581711 5982677973058355828372567)
                ·
                  refine ⟨8974016959587533742558851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5982677973058355828372567 8974016959587533742558851)
                  ·
                    refine ⟨13461025439381300613838277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8974016959587533742558851 13461025439381300613838277)
                    ·
                      refine ⟨2523942269883993865094677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13461025439381300613838277 2523942269883993865094677)
                      ·
                        rfl

theorem cell23_4915360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 1, 1, 1, 4].length) (baseStart_4915360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4915360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4915360 prefixEnd_4915360 := by exact prefixLift 4915360
  have htrace : WordTrace (prefixWord ++ tailWord_4915360) baseStart_4915360 baseEnd_4915360 := by
    simpa [prefixWord, tailWord_4915360, baseEnd_4915360] using wordTrace_append hprefix tailTrace_4915360
  have hstable : (prefixWord ++ tailWord_4915360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4915360).length < 2 ^ (prefixWord ++ tailWord_4915360).sum := by decide
  have hdescent : baseEnd_4915360 < baseStart_4915360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4915360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4915394 : List Nat := [3, 5, 1, 1, 1, 2, 2, 2, 1, 1, 4]
def baseStart_4915394 : Nat := 118140960795 + 4915394 * 2 ^ 59
def prefixEnd_4915394 : Nat := 4983230072969 + 3 ^ 40 * 4915394 * 2
def baseEnd_4915394 : Nat := 2523959728226246732069521

theorem tailTrace_4915394 : CollatzResearch.WordTrace tailWord_4915394 prefixEnd_4915394 2523959728226246732069521 := by
  unfold tailWord_4915394
  simp only [CollatzResearch.WordTrace]
  refine ⟨44819786888593623826424309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119519431702916330203798157 44819786888593623826424309)
  ·
    refine ⟨4201855020805652233727279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44819786888593623826424309 4201855020805652233727279)
    ·
      refine ⟨6302782531208478350590919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4201855020805652233727279 6302782531208478350590919)
      ·
        refine ⟨9454173796812717525886379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6302782531208478350590919 9454173796812717525886379)
        ·
          refine ⟨14181260695219076288829569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9454173796812717525886379 14181260695219076288829569)
          ·
            refine ⟨10635945521414307216622177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14181260695219076288829569 10635945521414307216622177)
            ·
              refine ⟨7976959141060730412466633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10635945521414307216622177 7976959141060730412466633)
              ·
                refine ⟨5982719355795547809349975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7976959141060730412466633 5982719355795547809349975)
                ·
                  refine ⟨8974079033693321714024963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5982719355795547809349975 8974079033693321714024963)
                  ·
                    refine ⟨13461118550539982571037445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8974079033693321714024963 13461118550539982571037445)
                    ·
                      refine ⟨2523959728226246732069521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13461118550539982571037445 2523959728226246732069521)
                      ·
                        rfl

theorem cell23_4915394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_4915394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4915394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4915394 prefixEnd_4915394 := by exact prefixLift 4915394
  have htrace : WordTrace (prefixWord ++ tailWord_4915394) baseStart_4915394 baseEnd_4915394 := by
    simpa [prefixWord, tailWord_4915394, baseEnd_4915394] using wordTrace_append hprefix tailTrace_4915394
  have hstable : (prefixWord ++ tailWord_4915394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4915394).length < 2 ^ (prefixWord ++ tailWord_4915394).sum := by decide
  have hdescent : baseEnd_4915394 < baseStart_4915394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4915394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4915410 : List Nat := [3, 2, 2, 2, 1, 2, 1, 2, 4, 1, 3]
def baseStart_4915410 : Nat := 118140960795 + 4915410 * 2 ^ 59
def prefixEnd_4915410 : Nat := 4983230072969 + 3 ^ 40 * 4915410 * 2
def baseEnd_4915410 : Nat := 2523967943916718669469447

theorem tailTrace_4915410 : CollatzResearch.WordTrace tailWord_4915410 prefixEnd_4915410 2523967943916718669469447 := by
  unfold tailWord_4915410
  simp only [CollatzResearch.WordTrace]
  refine ⟨44819932780579132509569921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119519820748211020025519789 44819932780579132509569921)
  ·
    refine ⟨33614949585434349382177441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44819932780579132509569921 33614949585434349382177441)
    ·
      refine ⟨25211212189075762036633081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33614949585434349382177441 25211212189075762036633081)
      ·
        refine ⟨18908409141806821527474811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25211212189075762036633081 18908409141806821527474811)
        ·
          refine ⟨28362613712710232291212217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18908409141806821527474811 28362613712710232291212217)
          ·
            refine ⟨21271960284532674218409163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28362613712710232291212217 21271960284532674218409163)
            ·
              refine ⟨31907940426799011327613745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21271960284532674218409163 31907940426799011327613745)
              ·
                refine ⟨23930955320099258495710309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31907940426799011327613745 23930955320099258495710309)
                ·
                  refine ⟨4487054122518610967945683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23930955320099258495710309 4487054122518610967945683)
                  ·
                    refine ⟨6730581183777916451918525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4487054122518610967945683 6730581183777916451918525)
                    ·
                      refine ⟨2523967943916718669469447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6730581183777916451918525 2523967943916718669469447)
                      ·
                        rfl

theorem cell23_4915410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_4915410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4915410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4915410 prefixEnd_4915410 := by exact prefixLift 4915410
  have htrace : WordTrace (prefixWord ++ tailWord_4915410) baseStart_4915410 baseEnd_4915410 := by
    simpa [prefixWord, tailWord_4915410, baseEnd_4915410] using wordTrace_append hprefix tailTrace_4915410
  have hstable : (prefixWord ++ tailWord_4915410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4915410).length < 2 ^ (prefixWord ++ tailWord_4915410).sum := by decide
  have hdescent : baseEnd_4915410 < baseStart_4915410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4915410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4915433 : List Nat := [1, 2, 1, 1, 1, 2, 2, 4, 3, 4, 2]
def baseStart_4915433 : Nat := 118140960795 + 4915433 * 2 ^ 59
def prefixEnd_4915433 : Nat := 4983230072969 + 3 ^ 40 * 4915433 * 2
def baseEnd_4915433 : Nat := 2523979753971772079481841

theorem tailTrace_4915433 : CollatzResearch.WordTrace tailWord_4915433 prefixEnd_4915433 2523979753971772079481841 := by
  unfold tailWord_4915433
  simp only [CollatzResearch.WordTrace]
  refine ⟨179280570001233204966366953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119520380000822136644244635 179280570001233204966366953)
  ·
    refine ⟨134460427500924903724775215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179280570001233204966366953 134460427500924903724775215)
    ·
      refine ⟨201690641251387355587162823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134460427500924903724775215 201690641251387355587162823)
      ·
        refine ⟨302535961877081033380744235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201690641251387355587162823 302535961877081033380744235)
        ·
          refine ⟨453803942815621550071116353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302535961877081033380744235 453803942815621550071116353)
          ·
            refine ⟨340352957111716162553337265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 453803942815621550071116353 340352957111716162553337265)
            ·
              refine ⟨255264717833787121915002949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 340352957111716162553337265 255264717833787121915002949)
              ·
                refine ⟨47862134593835085359063053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 255264717833787121915002949 47862134593835085359063053)
                ·
                  refine ⟨17948300472688157009648645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47862134593835085359063053 17948300472688157009648645)
                  ·
                    refine ⟨3365306338629029439309121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17948300472688157009648645 3365306338629029439309121)
                    ·
                      refine ⟨2523979753971772079481841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3365306338629029439309121 2523979753971772079481841)
                      ·
                        rfl

theorem cell23_4915433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 4, 2].length) (baseStart_4915433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4915433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4915433 prefixEnd_4915433 := by exact prefixLift 4915433
  have htrace : WordTrace (prefixWord ++ tailWord_4915433) baseStart_4915433 baseEnd_4915433 := by
    simpa [prefixWord, tailWord_4915433, baseEnd_4915433] using wordTrace_append hprefix tailTrace_4915433
  have hstable : (prefixWord ++ tailWord_4915433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4915433).length < 2 ^ (prefixWord ++ tailWord_4915433).sum := by decide
  have hdescent : baseEnd_4915433 < baseStart_4915433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4915433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4915436 : List Nat := [2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 5]
def baseStart_4915436 : Nat := 118140960795 + 4915436 * 2 ^ 59
def prefixEnd_4915436 : Nat := 4983230072969 + 3 ^ 40 * 4915436 * 2
def baseEnd_4915436 : Nat := 2523981294413735567744327

theorem tailTrace_4915436 : CollatzResearch.WordTrace tailWord_4915436 prefixEnd_4915436 2523981294413735567744327 := by
  unfold tailWord_4915436
  simp only [CollatzResearch.WordTrace]
  refine ⟨89640339710111168239363081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119520452946814890985817441 89640339710111168239363081)
  ·
    refine ⟨67230254782583376179522311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89640339710111168239363081 67230254782583376179522311)
    ·
      refine ⟨100845382173875064269283467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67230254782583376179522311 100845382173875064269283467)
      ·
        refine ⟨151268073260812596403925201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100845382173875064269283467 151268073260812596403925201)
        ·
          refine ⟨113451054945609447302943901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151268073260812596403925201 113451054945609447302943901)
          ·
            refine ⟨42544145604603542738603963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113451054945609447302943901 42544145604603542738603963)
            ·
              refine ⟨63816218406905314107905945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42544145604603542738603963 63816218406905314107905945)
              ·
                refine ⟨47862163805178985580929459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63816218406905314107905945 47862163805178985580929459)
                ·
                  refine ⟨71793245707768478371394189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47862163805178985580929459 71793245707768478371394189)
                  ·
                    refine ⟨26922467140413179389272821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71793245707768478371394189 26922467140413179389272821)
                    ·
                      refine ⟨2523981294413735567744327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26922467140413179389272821 2523981294413735567744327)
                      ·
                        rfl

theorem cell23_4915436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_4915436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4915436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4915436 prefixEnd_4915436 := by exact prefixLift 4915436
  have htrace : WordTrace (prefixWord ++ tailWord_4915436) baseStart_4915436 baseEnd_4915436 := by
    simpa [prefixWord, tailWord_4915436, baseEnd_4915436] using wordTrace_append hprefix tailTrace_4915436
  have hstable : (prefixWord ++ tailWord_4915436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4915436).length < 2 ^ (prefixWord ++ tailWord_4915436).sum := by decide
  have hdescent : baseEnd_4915436 < baseStart_4915436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4915436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4915456 : List Nat := [2, 1, 1, 2, 1, 1, 4, 4, 7]
def baseStart_4915456 : Nat := 118140960795 + 4915456 * 2 ^ 59
def prefixEnd_4915456 : Nat := 4983230072969 + 3 ^ 40 * 4915456 * 2
def baseEnd_4915456 : Nat := 280443507114091721054915

theorem tailTrace_4915456 : CollatzResearch.WordTrace tailWord_4915456 prefixEnd_4915456 280443507114091721054915 := by
  unfold tailWord_4915456
  simp only [CollatzResearch.WordTrace]
  refine ⟨89640704440074939947227111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119520939253433253262969481 89640704440074939947227111)
  ·
    refine ⟨134461056660112409920840667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89640704440074939947227111 134461056660112409920840667)
    ·
      refine ⟨201691584990168614881261001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134461056660112409920840667 201691584990168614881261001)
      ·
        refine ⟨151268688742626461160945751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201691584990168614881261001 151268688742626461160945751)
        ·
          refine ⟨226903033113939691741418627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151268688742626461160945751 226903033113939691741418627)
          ·
            refine ⟨340354549670909537612127941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226903033113939691741418627 340354549670909537612127941)
            ·
              refine ⟨63816478063295538302273989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 340354549670909537612127941 63816478063295538302273989)
              ·
                refine ⟨11965589636867913431676373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63816478063295538302273989 11965589636867913431676373)
                ·
                  refine ⟨280443507114091721054915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11965589636867913431676373 280443507114091721054915)
                  ·
                    rfl

theorem cell23_4915456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 7].length) (baseStart_4915456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4915456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4915456 prefixEnd_4915456 := by exact prefixLift 4915456
  have htrace : WordTrace (prefixWord ++ tailWord_4915456) baseStart_4915456 baseEnd_4915456 := by
    simpa [prefixWord, tailWord_4915456, baseEnd_4915456] using wordTrace_append hprefix tailTrace_4915456
  have hstable : (prefixWord ++ tailWord_4915456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4915456).length < 2 ^ (prefixWord ++ tailWord_4915456).sum := by decide
  have hdescent : baseEnd_4915456 < baseStart_4915456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4915456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4915524 : List Nat := [2, 3, 4, 1, 2, 1, 2, 3, 5]
def baseStart_4915524 : Nat := 118140960795 + 4915524 * 2 ^ 59
def prefixEnd_4915524 : Nat := 4983230072969 + 3 ^ 40 * 4915524 * 2
def baseEnd_4915524 : Nat := 280447386745703469271547

theorem tailTrace_4915524 : CollatzResearch.WordTrace tailWord_4915524 prefixEnd_4915524 280447386745703469271547 := by
  unfold tailWord_4915524
  simp only [CollatzResearch.WordTrace]
  refine ⟨89641944521951763753964813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119522592695935685005286417 89641944521951763753964813)
  ·
    refine ⟨33615729195731911407736805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89641944521951763753964813 33615729195731911407736805)
    ·
      refine ⟨6302949224199733388950651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33615729195731911407736805 6302949224199733388950651)
      ·
        refine ⟨9454423836299600083425977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6302949224199733388950651 9454423836299600083425977)
        ·
          refine ⟨7090817877224700062569483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9454423836299600083425977 7090817877224700062569483)
          ·
            refine ⟨10636226815837050093854225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7090817877224700062569483 10636226815837050093854225)
            ·
              refine ⟨7977170111877787570390669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10636226815837050093854225 7977170111877787570390669)
              ·
                refine ⟨2991438791954170338896501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7977170111877787570390669 2991438791954170338896501)
                ·
                  refine ⟨280447386745703469271547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2991438791954170338896501 280447386745703469271547)
                  ·
                    rfl

theorem cell23_4915524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 3, 5].length) (baseStart_4915524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4915524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4915524 prefixEnd_4915524 := by exact prefixLift 4915524
  have htrace : WordTrace (prefixWord ++ tailWord_4915524) baseStart_4915524 baseEnd_4915524 := by
    simpa [prefixWord, tailWord_4915524, baseEnd_4915524] using wordTrace_append hprefix tailTrace_4915524
  have hstable : (prefixWord ++ tailWord_4915524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4915524).length < 2 ^ (prefixWord ++ tailWord_4915524).sum := by decide
  have hdescent : baseEnd_4915524 < baseStart_4915524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4915524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4915560 : List Nat := [2, 1, 4, 2, 2, 1, 1, 2, 1, 4, 3]
def baseStart_4915560 : Nat := 118140960795 + 4915560 * 2 ^ 59
def prefixEnd_4915560 : Nat := 4983230072969 + 3 ^ 40 * 4915560 * 2
def baseEnd_4915560 : Nat := 2524044966014893082593757

theorem tailTrace_4915560 : CollatzResearch.WordTrace tailWord_4915560 prefixEnd_4915560 2524044966014893082593757 := by
  unfold tailWord_4915560
  simp only [CollatzResearch.WordTrace]
  refine ⟨89642601035886552828120067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119523468047848737104160089 89642601035886552828120067)
  ·
    refine ⟨134463901553829829242180101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89642601035886552828120067 134463901553829829242180101)
    ·
      refine ⟨25211981541343092982908769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134463901553829829242180101 25211981541343092982908769)
      ·
        refine ⟨18908986156007319737181577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25211981541343092982908769 18908986156007319737181577)
        ·
          refine ⟨14181739617005489802886183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18908986156007319737181577 14181739617005489802886183)
          ·
            refine ⟨21272609425508234704329275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14181739617005489802886183 21272609425508234704329275)
            ·
              refine ⟨31908914138262352056493913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21272609425508234704329275 31908914138262352056493913)
              ·
                refine ⟨23931685603696764042370435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31908914138262352056493913 23931685603696764042370435)
                ·
                  refine ⟨35897528405545146063555653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23931685603696764042370435 35897528405545146063555653)
                  ·
                    refine ⟨6730786576039714886916685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35897528405545146063555653 6730786576039714886916685)
                    ·
                      refine ⟨2524044966014893082593757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6730786576039714886916685 2524044966014893082593757)
                      ·
                        rfl

theorem cell23_4915560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_4915560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4915560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4915560 prefixEnd_4915560 := by exact prefixLift 4915560
  have htrace : WordTrace (prefixWord ++ tailWord_4915560) baseStart_4915560 baseEnd_4915560 := by
    simpa [prefixWord, tailWord_4915560, baseEnd_4915560] using wordTrace_append hprefix tailTrace_4915560
  have hstable : (prefixWord ++ tailWord_4915560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4915560).length < 2 ^ (prefixWord ++ tailWord_4915560).sum := by decide
  have hdescent : baseEnd_4915560 < baseStart_4915560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4915560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4915594 : List Nat := [3, 1, 2, 5, 1, 1, 1, 2, 2, 2, 3]
def baseStart_4915594 : Nat := 118140960795 + 4915594 * 2 ^ 59
def prefixEnd_4915594 : Nat := 4983230072969 + 3 ^ 40 * 4915594 * 2
def baseEnd_4915594 : Nat := 2524062424357145949568601

theorem tailTrace_4915594 : CollatzResearch.WordTrace tailWord_4915594 prefixEnd_4915594 2524062424357145949568601 := by
  unfold tailWord_4915594
  simp only [CollatzResearch.WordTrace]
  refine ⟨44821610538412482365744459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119524294769099952975318557 44821610538412482365744459)
  ·
    refine ⟨67232415807618723548616689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44821610538412482365744459 67232415807618723548616689)
    ·
      refine ⟨50424311855714042661462517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67232415807618723548616689 50424311855714042661462517)
      ·
        refine ⟨4727279236473191499512111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50424311855714042661462517 4727279236473191499512111)
        ·
          refine ⟨7090918854709787249268167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4727279236473191499512111 7090918854709787249268167)
          ·
            refine ⟨10636378282064680873902251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7090918854709787249268167 10636378282064680873902251)
            ·
              refine ⟨15954567423097021310853377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10636378282064680873902251 15954567423097021310853377)
              ·
                refine ⟨11965925567322765983140033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15954567423097021310853377 11965925567322765983140033)
                ·
                  refine ⟨8974444175492074487355025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11965925567322765983140033 8974444175492074487355025)
                  ·
                    refine ⟨6730833131619055865516269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8974444175492074487355025 6730833131619055865516269)
                    ·
                      refine ⟨2524062424357145949568601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6730833131619055865516269 2524062424357145949568601)
                      ·
                        rfl

theorem cell23_4915594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_4915594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4915594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4915594 prefixEnd_4915594 := by exact prefixLift 4915594
  have htrace : WordTrace (prefixWord ++ tailWord_4915594) baseStart_4915594 baseEnd_4915594 := by
    simpa [prefixWord, tailWord_4915594, baseEnd_4915594] using wordTrace_append hprefix tailTrace_4915594
  have hstable : (prefixWord ++ tailWord_4915594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4915594).length < 2 ^ (prefixWord ++ tailWord_4915594).sum := by decide
  have hdescent : baseEnd_4915594 < baseStart_4915594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4915594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4915607 : List Nat := [1, 1, 3, 3, 1, 1, 5, 1, 3, 1, 3]
def baseStart_4915607 : Nat := 118140960795 + 4915607 * 2 ^ 59
def prefixEnd_4915607 : Nat := 4983230072969 + 3 ^ 40 * 4915607 * 2
def baseEnd_4915607 : Nat := 2524069099605654398706041

theorem tailTrace_4915607 : CollatzResearch.WordTrace tailWord_4915607 prefixEnd_4915607 2524069099605654398706041 := by
  unfold tailWord_4915607
  simp only [CollatzResearch.WordTrace]
  refine ⟨179286916302602832683201075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119524610868401888455467383 179286916302602832683201075)
  ·
    refine ⟨268930374453904249024801613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179286916302602832683201075 268930374453904249024801613)
    ·
      refine ⟨100848890420214093384300605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 268930374453904249024801613 100848890420214093384300605)
      ·
        refine ⟨37818333907580285019112727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100848890420214093384300605 37818333907580285019112727)
        ·
          refine ⟨56727500861370427528669091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37818333907580285019112727 56727500861370427528669091)
          ·
            refine ⟨85091251292055641293003637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56727500861370427528669091 85091251292055641293003637)
            ·
              refine ⟨7977304808630216371219091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 85091251292055641293003637 7977304808630216371219091)
              ·
                refine ⟨11965957212945324556828637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7977304808630216371219091 11965957212945324556828637)
                ·
                  refine ⟨4487233954854496708810739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11965957212945324556828637 4487233954854496708810739)
                  ·
                    refine ⟨6730850932281745063216109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4487233954854496708810739 6730850932281745063216109)
                    ·
                      refine ⟨2524069099605654398706041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6730850932281745063216109 2524069099605654398706041)
                      ·
                        rfl

theorem cell23_4915607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_4915607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4915607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4915607 prefixEnd_4915607 := by exact prefixLift 4915607
  have htrace : WordTrace (prefixWord ++ tailWord_4915607) baseStart_4915607 baseEnd_4915607 := by
    simpa [prefixWord, tailWord_4915607, baseEnd_4915607] using wordTrace_append hprefix tailTrace_4915607
  have hstable : (prefixWord ++ tailWord_4915607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4915607).length < 2 ^ (prefixWord ++ tailWord_4915607).sum := by decide
  have hdescent : baseEnd_4915607 < baseStart_4915607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4915607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4915614 : List Nat := [4, 3, 1, 2, 1, 1, 4, 1, 6]
def baseStart_4915614 : Nat := 118140960795 + 4915614 * 2 ^ 59
def prefixEnd_4915614 : Nat := 4983230072969 + 3 ^ 40 * 4915614 * 2
def baseEnd_4915614 : Nat := 280452521552248430146501

theorem tailTrace_4915614 : CollatzResearch.WordTrace tailWord_4915614 prefixEnd_4915614 280452521552248430146501 := by
  unfold tailWord_4915614
  simp only [CollatzResearch.WordTrace]
  refine ⟨22410896451697184109838237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119524781075718315252470597 22410896451697184109838237)
  ·
    refine ⟨8404086169386444041189339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22410896451697184109838237 8404086169386444041189339)
    ·
      refine ⟨12606129254079666061784009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8404086169386444041189339 12606129254079666061784009)
      ·
        refine ⟨9454596940559749546338007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12606129254079666061784009 9454596940559749546338007)
        ·
          refine ⟨14181895410839624319507011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9454596940559749546338007 14181895410839624319507011)
          ·
            refine ⟨21272843116259436479260517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14181895410839624319507011 21272843116259436479260517)
            ·
              refine ⟨3988658084298644339861347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21272843116259436479260517 3988658084298644339861347)
              ·
                refine ⟨5982987126447966509792021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3988658084298644339861347 5982987126447966509792021)
                ·
                  refine ⟨280452521552248430146501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5982987126447966509792021 280452521552248430146501)
                  ·
                    rfl

theorem cell23_4915614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_4915614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4915614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4915614 prefixEnd_4915614 := by exact prefixLift 4915614
  have htrace : WordTrace (prefixWord ++ tailWord_4915614) baseStart_4915614 baseEnd_4915614 := by
    simpa [prefixWord, tailWord_4915614, baseEnd_4915614] using wordTrace_append hprefix tailTrace_4915614
  have hstable : (prefixWord ++ tailWord_4915614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4915614).length < 2 ^ (prefixWord ++ tailWord_4915614).sum := by decide
  have hdescent : baseEnd_4915614 < baseStart_4915614 := by decide
  rcases family_descends (prefixWord ++ tailWord_4915614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4915644 : List Nat := [2, 2, 2, 4, 1, 2, 3, 1, 1, 5]
def baseStart_4915644 : Nat := 118140960795 + 4915644 * 2 ^ 59
def prefixEnd_4915644 : Nat := 4983230072969 + 3 ^ 40 * 4915644 * 2
def baseEnd_4915644 : Nat := 841362699463290251314457

theorem tailTrace_4915644 : CollatzResearch.WordTrace tailWord_4915644 prefixEnd_4915644 841362699463290251314457 := by
  unfold tailWord_4915644
  simp only [CollatzResearch.WordTrace]
  refine ⟨89644132901734394001148993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119525510535645858668198657 89644132901734394001148993)
  ·
    refine ⟨67233099676300795500861745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89644132901734394001148993 67233099676300795500861745)
    ·
      refine ⟨50424824757225596625646309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67233099676300795500861745 50424824757225596625646309)
      ·
        refine ⟨9454654641979799367308683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50424824757225596625646309 9454654641979799367308683)
        ·
          refine ⟨14181981962969699050963025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9454654641979799367308683 14181981962969699050963025)
          ·
            refine ⟨10636486472227274288222269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14181981962969699050963025 10636486472227274288222269)
            ·
              refine ⟨3988682427085227858083351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10636486472227274288222269 3988682427085227858083351)
              ·
                refine ⟨5983023640627841787125027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3988682427085227858083351 5983023640627841787125027)
                ·
                  refine ⟨8974535460941762680687541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5983023640627841787125027 8974535460941762680687541)
                  ·
                    refine ⟨841362699463290251314457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8974535460941762680687541 841362699463290251314457)
                    ·
                      rfl

theorem cell23_4915644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 1, 1, 5].length) (baseStart_4915644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4915644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4915644 prefixEnd_4915644 := by exact prefixLift 4915644
  have htrace : WordTrace (prefixWord ++ tailWord_4915644) baseStart_4915644 baseEnd_4915644 := by
    simpa [prefixWord, tailWord_4915644, baseEnd_4915644] using wordTrace_append hprefix tailTrace_4915644
  have hstable : (prefixWord ++ tailWord_4915644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4915644).length < 2 ^ (prefixWord ++ tailWord_4915644).sum := by decide
  have hdescent : baseEnd_4915644 < baseStart_4915644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4915644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4915677 : List Nat := [1, 4, 3, 1, 1, 1, 4, 1, 1, 2, 4]
def baseStart_4915677 : Nat := 118140960795 + 4915677 * 2 ^ 59
def prefixEnd_4915677 : Nat := 4983230072969 + 3 ^ 40 * 4915677 * 2
def baseEnd_4915677 : Nat := 2524105043251469124830719

theorem tailTrace_4915677 : CollatzResearch.WordTrace tailWord_4915677 prefixEnd_4915677 2524105043251469124830719 := by
  unfold tailWord_4915677
  simp only [CollatzResearch.WordTrace]
  refine ⟨179289469412349234638249285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119526312941566156425499523 179289469412349234638249285)
  ·
    refine ⟨33616775514815481494671741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 179289469412349234638249285 33616775514815481494671741)
    ·
      refine ⟨12606290818055805560501903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33616775514815481494671741 12606290818055805560501903)
      ·
        refine ⟨18909436227083708340752855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12606290818055805560501903 18909436227083708340752855)
        ·
          refine ⟨28364154340625562511129283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18909436227083708340752855 28364154340625562511129283)
          ·
            refine ⟨42546231510938343766693925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28364154340625562511129283 42546231510938343766693925)
            ·
              refine ⟨7977418408300939456255111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42546231510938343766693925 7977418408300939456255111)
              ·
                refine ⟨11966127612451409184382667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7977418408300939456255111 11966127612451409184382667)
                ·
                  refine ⟨17949191418677113776574001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11966127612451409184382667 17949191418677113776574001)
                  ·
                    refine ⟨13461893564007835332430501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17949191418677113776574001 13461893564007835332430501)
                    ·
                      refine ⟨2524105043251469124830719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13461893564007835332430501 2524105043251469124830719)
                      ·
                        rfl

theorem cell23_4915677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_4915677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4915677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4915677 prefixEnd_4915677 := by exact prefixLift 4915677
  have htrace : WordTrace (prefixWord ++ tailWord_4915677) baseStart_4915677 baseEnd_4915677 := by
    simpa [prefixWord, tailWord_4915677, baseEnd_4915677] using wordTrace_append hprefix tailTrace_4915677
  have hstable : (prefixWord ++ tailWord_4915677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4915677).length < 2 ^ (prefixWord ++ tailWord_4915677).sum := by decide
  have hdescent : baseEnd_4915677 < baseStart_4915677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4915677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4915697 : List Nat := [1, 2, 2, 2, 3, 1, 2, 2, 4, 1, 3]
def baseStart_4915697 : Nat := 118140960795 + 4915697 * 2 ^ 59
def prefixEnd_4915697 : Nat := 4983230072969 + 3 ^ 40 * 4915697 * 2
def baseEnd_4915697 : Nat := 2524115312864559046580627

theorem tailTrace_4915697 : CollatzResearch.WordTrace tailWord_4915697 prefixEnd_4915697 2524115312864559046580627 := by
  unfold tailWord_4915697
  simp only [CollatzResearch.WordTrace]
  refine ⟨179290198872276778053977345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119526799248184518702651563 179290198872276778053977345)
  ·
    refine ⟨134467649154207583540483009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179290198872276778053977345 134467649154207583540483009)
    ·
      refine ⟨100850736865655687655362257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134467649154207583540483009 100850736865655687655362257)
      ·
        refine ⟨75638052649241765741521693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100850736865655687655362257 75638052649241765741521693)
        ·
          refine ⟨28364269743465662153070635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75638052649241765741521693 28364269743465662153070635)
          ·
            refine ⟨42546404615198493229605953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28364269743465662153070635 42546404615198493229605953)
            ·
              refine ⟨31909803461398869922204465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42546404615198493229605953 31909803461398869922204465)
              ·
                refine ⟨23932352596049152441653349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31909803461398869922204465 23932352596049152441653349)
                ·
                  refine ⟨4487316111759216082810003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23932352596049152441653349 4487316111759216082810003)
                  ·
                    refine ⟨6730974167638824124215005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4487316111759216082810003 6730974167638824124215005)
                    ·
                      refine ⟨2524115312864559046580627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6730974167638824124215005 2524115312864559046580627)
                      ·
                        rfl

theorem cell23_4915697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 4, 1, 3].length) (baseStart_4915697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4915697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4915697 prefixEnd_4915697 := by exact prefixLift 4915697
  have htrace : WordTrace (prefixWord ++ tailWord_4915697) baseStart_4915697 baseEnd_4915697 := by
    simpa [prefixWord, tailWord_4915697, baseEnd_4915697] using wordTrace_append hprefix tailTrace_4915697
  have hstable : (prefixWord ++ tailWord_4915697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4915697).length < 2 ^ (prefixWord ++ tailWord_4915697).sum := by decide
  have hdescent : baseEnd_4915697 < baseStart_4915697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4915697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4915698 : List Nat := [3, 2, 1, 4, 3, 1, 2, 1, 1, 1, 4]
def baseStart_4915698 : Nat := 118140960795 + 4915698 * 2 ^ 59
def prefixEnd_4915698 : Nat := 4983230072969 + 3 ^ 40 * 4915698 * 2
def baseEnd_4915698 : Nat := 2524115826345213542668123

theorem tailTrace_4915698 : CollatzResearch.WordTrace tailWord_4915698 prefixEnd_4915698 2524115826345213542668123 := by
  unfold tailWord_4915698
  simp only [CollatzResearch.WordTrace]
  refine ⟨44822558836318288806190937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119526823563515436816509165 44822558836318288806190937)
  ·
    refine ⟨33616919127238716604643203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44822558836318288806190937 33616919127238716604643203)
    ·
      refine ⟨50425378690858074906964805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33616919127238716604643203 50425378690858074906964805)
      ·
        refine ⟨9454758504535889045055901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50425378690858074906964805 9454758504535889045055901)
        ·
          refine ⟨3545534439200958391895963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9454758504535889045055901 3545534439200958391895963)
          ·
            refine ⟨5318301658801437587843945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3545534439200958391895963 5318301658801437587843945)
            ·
              refine ⟨3988726244101078190882959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5318301658801437587843945 3988726244101078190882959)
              ·
                refine ⟨5983089366151617286324439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3988726244101078190882959 5983089366151617286324439)
                ·
                  refine ⟨8974634049227425929486659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5983089366151617286324439 8974634049227425929486659)
                  ·
                    refine ⟨13461951073841138894229989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8974634049227425929486659 13461951073841138894229989)
                    ·
                      refine ⟨2524115826345213542668123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13461951073841138894229989 2524115826345213542668123)
                      ·
                        rfl

theorem cell23_4915698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_4915698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4915698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4915698 prefixEnd_4915698 := by exact prefixLift 4915698
  have htrace : WordTrace (prefixWord ++ tailWord_4915698) baseStart_4915698 baseEnd_4915698 := by
    simpa [prefixWord, tailWord_4915698, baseEnd_4915698] using wordTrace_append hprefix tailTrace_4915698
  have hstable : (prefixWord ++ tailWord_4915698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4915698).length < 2 ^ (prefixWord ++ tailWord_4915698).sum := by decide
  have hdescent : baseEnd_4915698 < baseStart_4915698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4915698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4915701 : List Nat := [1, 3, 5, 1, 2, 1, 1, 3, 1, 2, 3]
def baseStart_4915701 : Nat := 118140960795 + 4915701 * 2 ^ 59
def prefixEnd_4915701 : Nat := 4983230072969 + 3 ^ 40 * 4915701 * 2
def baseEnd_4915701 : Nat := 2524117366787177030930609

theorem tailTrace_4915701 : CollatzResearch.WordTrace tailWord_4915701 prefixEnd_4915701 2524117366787177030930609 := by
  unfold tailWord_4915701
  simp only [CollatzResearch.WordTrace]
  refine ⟨179290344764262286737122957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119526896509508191158081971 179290344764262286737122957)
  ·
    refine ⟨67233879286598357526421109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179290344764262286737122957 67233879286598357526421109)
    ·
      refine ⟨6303176183118596018101979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67233879286598357526421109 6303176183118596018101979)
      ·
        refine ⟨9454764274677894027152969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6303176183118596018101979 9454764274677894027152969)
        ·
          refine ⟨7091073206008420520364727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9454764274677894027152969 7091073206008420520364727)
          ·
            refine ⟨10636609809012630780547091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7091073206008420520364727 10636609809012630780547091)
            ·
              refine ⟨15954914713518946170820637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10636609809012630780547091 15954914713518946170820637)
              ·
                refine ⟨5983093017569604814057739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15954914713518946170820637 5983093017569604814057739)
                ·
                  refine ⟨8974639526354407221086609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5983093017569604814057739 8974639526354407221086609)
                  ·
                    refine ⟨6730979644765805415814957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8974639526354407221086609 6730979644765805415814957)
                    ·
                      refine ⟨2524117366787177030930609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6730979644765805415814957 2524117366787177030930609)
                      ·
                        rfl

theorem cell23_4915701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_4915701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4915701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4915701 prefixEnd_4915701 := by exact prefixLift 4915701
  have htrace : WordTrace (prefixWord ++ tailWord_4915701) baseStart_4915701 baseEnd_4915701 := by
    simpa [prefixWord, tailWord_4915701, baseEnd_4915701] using wordTrace_append hprefix tailTrace_4915701
  have hstable : (prefixWord ++ tailWord_4915701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4915701).length < 2 ^ (prefixWord ++ tailWord_4915701).sum := by decide
  have hdescent : baseEnd_4915701 < baseStart_4915701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4915701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4915741 : List Nat := [1, 4, 2, 2, 1, 3, 2, 2, 1, 3, 2]
def baseStart_4915741 : Nat := 118140960795 + 4915741 * 2 ^ 59
def prefixEnd_4915741 : Nat := 4983230072969 + 3 ^ 40 * 4915741 * 2
def baseEnd_4915741 : Nat := 2524137906013356874430425

theorem tailTrace_4915741 : CollatzResearch.WordTrace tailWord_4915741 prefixEnd_4915741 2524137906013356874430425 := by
  unfold tailWord_4915741
  simp only [CollatzResearch.WordTrace]
  refine ⟨179291803684117373568579077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119527869122744915712386051 179291803684117373568579077)
  ·
    refine ⟨33617213190772007544108577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 179291803684117373568579077 33617213190772007544108577)
    ·
      refine ⟨25212909893079005658081433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33617213190772007544108577 25212909893079005658081433)
      ·
        refine ⟨18909682419809254243561075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25212909893079005658081433 18909682419809254243561075)
        ·
          refine ⟨28364523629713881365341613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18909682419809254243561075 28364523629713881365341613)
          ·
            refine ⟨10636696361142705512003105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28364523629713881365341613 10636696361142705512003105)
            ·
              refine ⟨7977522270857029134002329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10636696361142705512003105 7977522270857029134002329)
              ·
                refine ⟨5983141703142771850501747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7977522270857029134002329 5983141703142771850501747)
                ·
                  refine ⟨8974712554714157775752621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5983141703142771850501747 8974712554714157775752621)
                  ·
                    refine ⟨3365517208017809165907233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8974712554714157775752621 3365517208017809165907233)
                    ·
                      refine ⟨2524137906013356874430425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3365517208017809165907233 2524137906013356874430425)
                      ·
                        rfl

theorem cell23_4915741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_4915741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4915741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4915741 prefixEnd_4915741 := by exact prefixLift 4915741
  have htrace : WordTrace (prefixWord ++ tailWord_4915741) baseStart_4915741 baseEnd_4915741 := by
    simpa [prefixWord, tailWord_4915741, baseEnd_4915741] using wordTrace_append hprefix tailTrace_4915741
  have hstable : (prefixWord ++ tailWord_4915741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4915741).length < 2 ^ (prefixWord ++ tailWord_4915741).sum := by decide
  have hdescent : baseEnd_4915741 < baseStart_4915741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4915741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4915777 : List Nat := [1, 2, 5, 1, 1, 2, 3, 1, 7]
def baseStart_4915777 : Nat := 118140960795 + 4915777 * 2 ^ 59
def prefixEnd_4915777 : Nat := 4983230072969 + 3 ^ 40 * 4915777 * 2
def baseEnd_4915777 : Nat := 280461821257435414842251

theorem tailTrace_4915777 : CollatzResearch.WordTrace tailWord_4915777 prefixEnd_4915777 280461821257435414842251 := by
  unfold tailWord_4915777
  simp only [CollatzResearch.WordTrace]
  refine ⟨179293116711986951716889585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119528744474657967811259723 179293116711986951716889585)
  ·
    refine ⟨134469837533990213787667189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179293116711986951716889585 134469837533990213787667189)
    ·
      refine ⟨12606547268811582542593799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 134469837533990213787667189 12606547268811582542593799)
      ·
        refine ⟨18909820903217373813890699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12606547268811582542593799 18909820903217373813890699)
        ·
          refine ⟨28364731354826060720836049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18909820903217373813890699 28364731354826060720836049)
          ·
            refine ⟨21273548516119545540627037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28364731354826060720836049 21273548516119545540627037)
            ·
              refine ⟨7977580693544829577735139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21273548516119545540627037 7977580693544829577735139)
              ·
                refine ⟨11966371040317244366602709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7977580693544829577735139 11966371040317244366602709)
                ·
                  refine ⟨280461821257435414842251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11966371040317244366602709 280461821257435414842251)
                  ·
                    rfl

theorem cell23_4915777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 7].length) (baseStart_4915777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4915777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4915777 prefixEnd_4915777 := by exact prefixLift 4915777
  have htrace : WordTrace (prefixWord ++ tailWord_4915777) baseStart_4915777 baseEnd_4915777 := by
    simpa [prefixWord, tailWord_4915777, baseEnd_4915777] using wordTrace_append hprefix tailTrace_4915777
  have hstable : (prefixWord ++ tailWord_4915777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4915777).length < 2 ^ (prefixWord ++ tailWord_4915777).sum := by decide
  have hdescent : baseEnd_4915777 < baseStart_4915777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4915777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4915790 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 3, 7]
def baseStart_4915790 : Nat := 118140960795 + 4915790 * 2 ^ 59
def prefixEnd_4915790 : Nat := 4983230072969 + 3 ^ 40 * 4915790 * 2
def baseEnd_4915790 : Nat := 841387688855142394239233

theorem tailTrace_4915790 : CollatzResearch.WordTrace tailWord_4915790 prefixEnd_4915790 841387688855142394239233 := by
  unfold tailWord_4915790
  simp only [CollatzResearch.WordTrace]
  refine ⟨22411698857617481867139103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119529060573959903291408549 22411698857617481867139103)
  ·
    refine ⟨33617548286426222800708655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22411698857617481867139103 33617548286426222800708655)
    ·
      refine ⟨50426322429639334201062983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33617548286426222800708655 50426322429639334201062983)
      ·
        refine ⟨75639483644459001301594475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50426322429639334201062983 75639483644459001301594475)
        ·
          refine ⟨113459225466688501952391713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75639483644459001301594475 113459225466688501952391713)
          ·
            refine ⟨85094419100016376464293785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113459225466688501952391713 85094419100016376464293785)
            ·
              refine ⟨63820814325012282348220339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85094419100016376464293785 63820814325012282348220339)
              ·
                refine ⟨95731221487518423522330509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63820814325012282348220339 95731221487518423522330509)
                ·
                  refine ⟨35899208057819408820873941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95731221487518423522330509 35899208057819408820873941)
                  ·
                    refine ⟨841387688855142394239233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35899208057819408820873941 841387688855142394239233)
                    ·
                      rfl

theorem cell23_4915790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_4915790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4915790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4915790 prefixEnd_4915790 := by exact prefixLift 4915790
  have htrace : WordTrace (prefixWord ++ tailWord_4915790) baseStart_4915790 baseEnd_4915790 := by
    simpa [prefixWord, tailWord_4915790, baseEnd_4915790] using wordTrace_append hprefix tailTrace_4915790
  have hstable : (prefixWord ++ tailWord_4915790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4915790).length < 2 ^ (prefixWord ++ tailWord_4915790).sum := by decide
  have hdescent : baseEnd_4915790 < baseStart_4915790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4915790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4915844 : List Nat := [2, 3, 2, 1, 3, 1, 1, 1, 1, 6, 2]
def baseStart_4915844 : Nat := 118140960795 + 4915844 * 2 ^ 59
def prefixEnd_4915844 : Nat := 4983230072969 + 3 ^ 40 * 4915844 * 2
def baseEnd_4915844 : Nat := 2524190794520769971442451

theorem tailTrace_4915844 : CollatzResearch.WordTrace tailWord_4915844 prefixEnd_4915844 2524190794520769971442451 := by
  unfold tailWord_4915844
  simp only [CollatzResearch.WordTrace]
  refine ⟨89647780201372111079789293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119530373601829481439719057 89647780201372111079789293)
  ·
    refine ⟨33617917575514541654920985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89647780201372111079789293 33617917575514541654920985)
    ·
      refine ⟨25213438181635906241190739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33617917575514541654920985 25213438181635906241190739)
      ·
        refine ⟨37820157272453859361786109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25213438181635906241190739 37820157272453859361786109)
        ·
          refine ⟨14182558977170197260669791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37820157272453859361786109 14182558977170197260669791)
          ·
            refine ⟨21273838465755295891004687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14182558977170197260669791 21273838465755295891004687)
            ·
              refine ⟨31910757698632943836507031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21273838465755295891004687 31910757698632943836507031)
              ·
                refine ⟨47866136547949415754760547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31910757698632943836507031 47866136547949415754760547)
                ·
                  refine ⟨71799204821924123632140821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47866136547949415754760547 71799204821924123632140821)
                  ·
                    refine ⟨3365587726027693295256601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 71799204821924123632140821 3365587726027693295256601)
                    ·
                      refine ⟨2524190794520769971442451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3365587726027693295256601 2524190794520769971442451)
                      ·
                        rfl

theorem cell23_4915844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 1, 6, 2].length) (baseStart_4915844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4915844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4915844 prefixEnd_4915844 := by exact prefixLift 4915844
  have htrace : WordTrace (prefixWord ++ tailWord_4915844) baseStart_4915844 baseEnd_4915844 := by
    simpa [prefixWord, tailWord_4915844, baseEnd_4915844] using wordTrace_append hprefix tailTrace_4915844
  have hstable : (prefixWord ++ tailWord_4915844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4915844).length < 2 ^ (prefixWord ++ tailWord_4915844).sum := by decide
  have hdescent : baseEnd_4915844 < baseStart_4915844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4915844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4915847 : List Nat := [1, 1, 4, 2, 1, 2, 2, 2, 1, 4, 3]
def baseStart_4915847 : Nat := 118140960795 + 4915847 * 2 ^ 59
def prefixEnd_4915847 : Nat := 4983230072969 + 3 ^ 40 * 4915847 * 2
def baseEnd_4915847 : Nat := 2524192334962733459704937

theorem tailTrace_4915847 : CollatzResearch.WordTrace tailWord_4915847 prefixEnd_4915847 2524192334962733459704937 := by
  unfold tailWord_4915847
  simp only [CollatzResearch.WordTrace]
  refine ⟨179295669821733353671937795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119530446547822235781291863 179295669821733353671937795)
  ·
    refine ⟨268943504732600030507906693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179295669821733353671937795 268943504732600030507906693)
    ·
      refine ⟨50426907137362505720232505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 268943504732600030507906693 50426907137362505720232505)
      ·
        refine ⟨37820180353021879290174379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50426907137362505720232505 37820180353021879290174379)
        ·
          refine ⟨56730270529532818935261569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37820180353021879290174379 56730270529532818935261569)
          ·
            refine ⟨42547702897149614201446177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56730270529532818935261569 42547702897149614201446177)
            ·
              refine ⟨31910777172862210651084633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42547702897149614201446177 31910777172862210651084633)
              ·
                refine ⟨23933082879646657988313475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31910777172862210651084633 23933082879646657988313475)
                ·
                  refine ⟨35899624319469986982470213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23933082879646657988313475 35899624319469986982470213)
                  ·
                    refine ⟨6731179559900622559213165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35899624319469986982470213 6731179559900622559213165)
                    ·
                      refine ⟨2524192334962733459704937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6731179559900622559213165 2524192334962733459704937)
                      ·
                        rfl

theorem cell23_4915847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_4915847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4915847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4915847 prefixEnd_4915847 := by exact prefixLift 4915847
  have htrace : WordTrace (prefixWord ++ tailWord_4915847) baseStart_4915847 baseEnd_4915847 := by
    simpa [prefixWord, tailWord_4915847, baseEnd_4915847] using wordTrace_append hprefix tailTrace_4915847
  have hstable : (prefixWord ++ tailWord_4915847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4915847).length < 2 ^ (prefixWord ++ tailWord_4915847).sum := by decide
  have hdescent : baseEnd_4915847 < baseStart_4915847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4915847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4915854 : List Nat := [4, 1, 1, 3, 1, 1, 3, 2, 3, 4]
def baseStart_4915854 : Nat := 118140960795 + 4915854 * 2 ^ 59
def prefixEnd_4915854 : Nat := 4983230072969 + 3 ^ 40 * 4915854 * 2
def baseEnd_4915854 : Nat := 841398643109104977439135

theorem tailTrace_4915854 : CollatzResearch.WordTrace tailWord_4915854 prefixEnd_4915854 841398643109104977439135 := by
  unfold tailWord_4915854
  simp only [CollatzResearch.WordTrace]
  refine ⟨22411990641588499233430327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119530616755138662578295077 22411990641588499233430327)
  ·
    refine ⟨33617985962382748850145491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22411990641588499233430327 33617985962382748850145491)
    ·
      refine ⟨50426978943574123275218237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33617985962382748850145491 50426978943574123275218237)
      ·
        refine ⟨18910117103840296228206839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50426978943574123275218237 18910117103840296228206839)
        ·
          refine ⟨28365175655760444342310259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18910117103840296228206839 28365175655760444342310259)
          ·
            refine ⟨42547763483640666513465389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28365175655760444342310259 42547763483640666513465389)
            ·
              refine ⟨15955411306365249942549521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42547763483640666513465389 15955411306365249942549521)
              ·
                refine ⟨11966558479773937456912141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15955411306365249942549521 11966558479773937456912141)
                ·
                  refine ⟨4487459429915226546342053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11966558479773937456912141 4487459429915226546342053)
                  ·
                    refine ⟨841398643109104977439135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4487459429915226546342053 841398643109104977439135)
                    ·
                      rfl

theorem cell23_4915854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 3, 4].length) (baseStart_4915854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4915854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4915854 prefixEnd_4915854 := by exact prefixLift 4915854
  have htrace : WordTrace (prefixWord ++ tailWord_4915854) baseStart_4915854 baseEnd_4915854 := by
    simpa [prefixWord, tailWord_4915854, baseEnd_4915854] using wordTrace_append hprefix tailTrace_4915854
  have hstable : (prefixWord ++ tailWord_4915854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4915854).length < 2 ^ (prefixWord ++ tailWord_4915854).sum := by decide
  have hdescent : baseEnd_4915854 < baseStart_4915854 := by decide
  rcases family_descends (prefixWord ++ tailWord_4915854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4915904 : List Nat := [2, 1, 1, 2, 4, 2, 1, 2, 1, 5, 2]
def baseStart_4915904 : Nat := 118140960795 + 4915904 * 2 ^ 59
def prefixEnd_4915904 : Nat := 4983230072969 + 3 ^ 40 * 4915904 * 2
def baseEnd_4915904 : Nat := 2524221603360039736692175

theorem tailTrace_4915904 : CollatzResearch.WordTrace tailWord_4915904 prefixEnd_4915904 2524221603360039736692175 := by
  unfold tailWord_4915904
  simp only [CollatzResearch.WordTrace]
  refine ⟨89648874391263426203381383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119531832521684568271175177 89648874391263426203381383)
  ·
    refine ⟨134473311586895139305072075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89648874391263426203381383 134473311586895139305072075)
    ·
      refine ⟨201709967380342708957608113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134473311586895139305072075 201709967380342708957608113)
      ·
        refine ⟨151282475535257031718206085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201709967380342708957608113 151282475535257031718206085)
        ·
          refine ⟨28365464162860693447163641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 151282475535257031718206085 28365464162860693447163641)
          ·
            refine ⟨21274098122145520085372731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28365464162860693447163641 21274098122145520085372731)
            ·
              refine ⟨31911147183218280128059097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21274098122145520085372731 31911147183218280128059097)
              ·
                refine ⟨23933360387413710096044323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31911147183218280128059097 23933360387413710096044323)
                ·
                  refine ⟨35900040581120565144066485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23933360387413710096044323 35900040581120565144066485)
                  ·
                    refine ⟨3365628804480052982256233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35900040581120565144066485 3365628804480052982256233)
                    ·
                      refine ⟨2524221603360039736692175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3365628804480052982256233 2524221603360039736692175)
                      ·
                        rfl

theorem cell23_4915904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 1, 5, 2].length) (baseStart_4915904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4915904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4915904 prefixEnd_4915904 := by exact prefixLift 4915904
  have htrace : WordTrace (prefixWord ++ tailWord_4915904) baseStart_4915904 baseEnd_4915904 := by
    simpa [prefixWord, tailWord_4915904, baseEnd_4915904] using wordTrace_append hprefix tailTrace_4915904
  have hstable : (prefixWord ++ tailWord_4915904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4915904).length < 2 ^ (prefixWord ++ tailWord_4915904).sum := by decide
  have hdescent : baseEnd_4915904 < baseStart_4915904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4915904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4915914 : List Nat := [3, 1, 2, 1, 4, 1, 1, 4, 1, 5]
def baseStart_4915914 : Nat := 118140960795 + 4915914 * 2 ^ 59
def prefixEnd_4915914 : Nat := 4983230072969 + 3 ^ 40 * 4915914 * 2
def baseEnd_4915914 : Nat := 841408912722194899189043

theorem tailTrace_4915914 : CollatzResearch.WordTrace tailWord_4915914 prefixEnd_4915914 841408912722194899189043 := by
  unfold tailWord_4915914
  simp only [CollatzResearch.WordTrace]
  refine ⟨44824528378122656028656699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119532075674993749409751197 44824528378122656028656699)
  ·
    refine ⟨67236792567183984042985049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44824528378122656028656699 67236792567183984042985049)
    ·
      refine ⟨50427594425387988032238787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67236792567183984042985049 50427594425387988032238787)
      ·
        refine ⟨75641391638081982048358181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50427594425387988032238787 75641391638081982048358181)
        ·
          refine ⟨14182760932140371634067159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75641391638081982048358181 14182760932140371634067159)
          ·
            refine ⟨21274141398210557451100739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14182760932140371634067159 21274141398210557451100739)
            ·
              refine ⟨31911212097315836176651109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21274141398210557451100739 31911212097315836176651109)
              ·
                refine ⟨5983352268246719283122083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31911212097315836176651109 5983352268246719283122083)
                ·
                  refine ⟨8975028402370078924683125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5983352268246719283122083 8975028402370078924683125)
                  ·
                    refine ⟨841408912722194899189043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8975028402370078924683125 841408912722194899189043)
                    ·
                      rfl

theorem cell23_4915914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 4, 1, 5].length) (baseStart_4915914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4915914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4915914 prefixEnd_4915914 := by exact prefixLift 4915914
  have htrace : WordTrace (prefixWord ++ tailWord_4915914) baseStart_4915914 baseEnd_4915914 := by
    simpa [prefixWord, tailWord_4915914, baseEnd_4915914] using wordTrace_append hprefix tailTrace_4915914
  have hstable : (prefixWord ++ tailWord_4915914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4915914).length < 2 ^ (prefixWord ++ tailWord_4915914).sum := by decide
  have hdescent : baseEnd_4915914 < baseStart_4915914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4915914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4915928 : List Nat := [2, 1, 2, 2, 3, 2, 3, 3, 1, 1, 3]
def baseStart_4915928 : Nat := 118140960795 + 4915928 * 2 ^ 59
def prefixEnd_4915928 : Nat := 4983230072969 + 3 ^ 40 * 4915928 * 2
def baseEnd_4915928 : Nat := 2524233926895747642792065

theorem tailTrace_4915928 : CollatzResearch.WordTrace tailWord_4915928 prefixEnd_4915928 2524233926895747642792065 := by
  unfold tailWord_4915928
  simp only [CollatzResearch.WordTrace]
  refine ⟨89649312067219952252818219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119532416089626603003757625 89649312067219952252818219)
  ·
    refine ⟨134473968100829928379227329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89649312067219952252818219 134473968100829928379227329)
    ·
      refine ⟨100855476075622446284420497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134473968100829928379227329 100855476075622446284420497)
      ·
        refine ⟨75641607056716834713315373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100855476075622446284420497 75641607056716834713315373)
        ·
          refine ⟨28365602646268813017493265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75641607056716834713315373 28365602646268813017493265)
          ·
            refine ⟨21274201984701609763119949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28365602646268813017493265 21274201984701609763119949)
            ·
              refine ⟨7977825744263103661169981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21274201984701609763119949 7977825744263103661169981)
              ·
                refine ⟨2991684654098663872938743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7977825744263103661169981 2991684654098663872938743)
                ·
                  refine ⟨4487526981147995809408115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2991684654098663872938743 4487526981147995809408115)
                  ·
                    refine ⟨6731290471721993714112173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4487526981147995809408115 6731290471721993714112173)
                    ·
                      refine ⟨2524233926895747642792065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6731290471721993714112173 2524233926895747642792065)
                      ·
                        rfl

theorem cell23_4915928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 3, 1, 1, 3].length) (baseStart_4915928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4915928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4915928 prefixEnd_4915928 := by exact prefixLift 4915928
  have htrace : WordTrace (prefixWord ++ tailWord_4915928) baseStart_4915928 baseEnd_4915928 := by
    simpa [prefixWord, tailWord_4915928, baseEnd_4915928] using wordTrace_append hprefix tailTrace_4915928
  have hstable : (prefixWord ++ tailWord_4915928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4915928).length < 2 ^ (prefixWord ++ tailWord_4915928).sum := by decide
  have hdescent : baseEnd_4915928 < baseStart_4915928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4915928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4915954 : List Nat := [3, 2, 1, 3, 1, 2, 2, 2, 1, 1, 5]
def baseStart_4915954 : Nat := 118140960795 + 4915954 * 2 ^ 59
def prefixEnd_4915954 : Nat := 4983230072969 + 3 ^ 40 * 4915954 * 2
def baseEnd_4915954 : Nat := 2524247277392764541066945

theorem tailTrace_4915954 : CollatzResearch.WordTrace tailWord_4915954 prefixEnd_4915954 2524247277392764541066945 := by
  unfold tailWord_4915954
  simp only [CollatzResearch.WordTrace]
  refine ⟨44824893108086427736520729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119533048288230473964055277 44824893108086427736520729)
  ·
    refine ⟨33618669831064820802390547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44824893108086427736520729 33618669831064820802390547)
    ·
      refine ⟨50428004746597231203585821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33618669831064820802390547 50428004746597231203585821)
      ·
        refine ⟨18910501779973961701344683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50428004746597231203585821 18910501779973961701344683)
        ·
          refine ⟨28365752669960942552017025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18910501779973961701344683 28365752669960942552017025)
          ·
            refine ⟨21274314502470706914012769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28365752669960942552017025 21274314502470706914012769)
            ·
              refine ⟨15955735876853030185509577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21274314502470706914012769 15955735876853030185509577)
              ·
                refine ⟨11966801907639772639132183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15955735876853030185509577 11966801907639772639132183)
                ·
                  refine ⟨17950202861459658958698275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11966801907639772639132183 17950202861459658958698275)
                  ·
                    refine ⟨26925304292189488438047413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17950202861459658958698275 26925304292189488438047413)
                    ·
                      refine ⟨2524247277392764541066945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26925304292189488438047413 2524247277392764541066945)
                      ·
                        rfl

theorem cell23_4915954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_4915954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4915954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4915954 prefixEnd_4915954 := by exact prefixLift 4915954
  have htrace : WordTrace (prefixWord ++ tailWord_4915954) baseStart_4915954 baseEnd_4915954 := by
    simpa [prefixWord, tailWord_4915954, baseEnd_4915954] using wordTrace_append hprefix tailTrace_4915954
  have hstable : (prefixWord ++ tailWord_4915954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4915954).length < 2 ^ (prefixWord ++ tailWord_4915954).sum := by decide
  have hdescent : baseEnd_4915954 < baseStart_4915954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4915954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4916002 : List Nat := [3, 3, 1, 1, 2, 2, 4, 2, 1, 2, 2]
def baseStart_4916002 : Nat := 118140960795 + 4916002 * 2 ^ 59
def prefixEnd_4916002 : Nat := 4983230072969 + 3 ^ 40 * 4916002 * 2
def baseEnd_4916002 : Nat := 2524271924464180353266725

theorem tailTrace_4916002 : CollatzResearch.WordTrace tailWord_4916002 prefixEnd_4916002 2524271924464180353266725 := by
  unfold tailWord_4916002
  simp only [CollatzResearch.WordTrace]
  refine ⟨44825330784042953785957565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119534215424114543429220173 44825330784042953785957565)
  ·
    refine ⟨16809499044016107669734087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44825330784042953785957565 16809499044016107669734087)
    ·
      refine ⟨25214248566024161504601131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16809499044016107669734087 25214248566024161504601131)
      ·
        refine ⟨37821372849036242256901697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25214248566024161504601131 37821372849036242256901697)
        ·
          refine ⟨28366029636777181692676273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37821372849036242256901697 28366029636777181692676273)
          ·
            refine ⟨21274522227582886269507205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28366029636777181692676273 21274522227582886269507205)
            ·
              refine ⟨3988972917671791175532601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21274522227582886269507205 3988972917671791175532601)
              ·
                refine ⟨2991729688253843381649451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3988972917671791175532601 2991729688253843381649451)
                ·
                  refine ⟨4487594532380765072474177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2991729688253843381649451 4487594532380765072474177)
                  ·
                    refine ⟨3365695899285573804355633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4487594532380765072474177 3365695899285573804355633)
                    ·
                      refine ⟨2524271924464180353266725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3365695899285573804355633 2524271924464180353266725)
                      ·
                        rfl

theorem cell23_4916002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 2, 1, 2, 2].length) (baseStart_4916002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4916002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4916002 prefixEnd_4916002 := by exact prefixLift 4916002
  have htrace : WordTrace (prefixWord ++ tailWord_4916002) baseStart_4916002 baseEnd_4916002 := by
    simpa [prefixWord, tailWord_4916002, baseEnd_4916002] using wordTrace_append hprefix tailTrace_4916002
  have hstable : (prefixWord ++ tailWord_4916002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4916002).length < 2 ^ (prefixWord ++ tailWord_4916002).sum := by decide
  have hdescent : baseEnd_4916002 < baseStart_4916002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4916002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4916041 : List Nat := [1, 2, 1, 1, 2, 5, 2, 2, 1, 4, 2]
def baseStart_4916041 : Nat := 118140960795 + 4916041 * 2 ^ 59
def prefixEnd_4916041 : Nat := 4983230072969 + 3 ^ 40 * 4916041 * 2
def baseEnd_4916041 : Nat := 2524291950209705700679045

theorem tailTrace_4916041 : CollatzResearch.WordTrace tailWord_4916041 prefixEnd_4916041 2524291950209705700679045 := by
  unfold tailWord_4916041
  simp only [CollatzResearch.WordTrace]
  refine ⟨179302745583030524804499977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119535163722020349869666651 179302745583030524804499977)
  ·
    refine ⟨134477059187272893603374983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179302745583030524804499977 134477059187272893603374983)
    ·
      refine ⟨201715588780909340405062475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134477059187272893603374983 201715588780909340405062475)
      ·
        refine ⟨302573383171364010607593713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201715588780909340405062475 302573383171364010607593713)
        ·
          refine ⟨226930037378523007955695285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 302573383171364010607593713 226930037378523007955695285)
          ·
            refine ⟨21274691004236531995846433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 226930037378523007955695285 21274691004236531995846433)
            ·
              refine ⟨15956018253177398996884825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21274691004236531995846433 15956018253177398996884825)
              ·
                refine ⟨11967013689883049247663619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15956018253177398996884825 11967013689883049247663619)
                ·
                  refine ⟨17950520534824573871495429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11967013689883049247663619 17950520534824573871495429)
                  ·
                    refine ⟨3365722600279607600905393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17950520534824573871495429 3365722600279607600905393)
                    ·
                      refine ⟨2524291950209705700679045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3365722600279607600905393 2524291950209705700679045)
                      ·
                        rfl

theorem cell23_4916041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 4, 2].length) (baseStart_4916041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4916041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4916041 prefixEnd_4916041 := by exact prefixLift 4916041
  have htrace : WordTrace (prefixWord ++ tailWord_4916041) baseStart_4916041 baseEnd_4916041 := by
    simpa [prefixWord, tailWord_4916041, baseEnd_4916041] using wordTrace_append hprefix tailTrace_4916041
  have hstable : (prefixWord ++ tailWord_4916041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4916041).length < 2 ^ (prefixWord ++ tailWord_4916041).sum := by decide
  have hdescent : baseEnd_4916041 < baseStart_4916041 := by decide
  rcases family_descends (prefixWord ++ tailWord_4916041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4916052 : List Nat := [2, 4, 1, 1, 5, 1, 1, 2, 2, 1, 3]
def baseStart_4916052 : Nat := 118140960795 + 4916052 * 2 ^ 59
def prefixEnd_4916052 : Nat := 4983230072969 + 3 ^ 40 * 4916052 * 2
def baseEnd_4916052 : Nat := 2524297598496905157641495

theorem tailTrace_4916052 : CollatzResearch.WordTrace tailWord_4916052 prefixEnd_4916052 2524297598496905157641495 := by
  unfold tailWord_4916052
  simp only [CollatzResearch.WordTrace]
  refine ⟨89651573392995336841575205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119535431190660449122100273 89651573392995336841575205)
  ·
    refine ⟨16809670011186625657795351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89651573392995336841575205 16809670011186625657795351)
    ·
      refine ⟨25214505016779938486693027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16809670011186625657795351 25214505016779938486693027)
      ·
        refine ⟨37821757525169907730039541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25214505016779938486693027 37821757525169907730039541)
        ·
          refine ⟨3545789767984678849691207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37821757525169907730039541 3545789767984678849691207)
          ·
            refine ⟨5318684651977018274536811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3545789767984678849691207 5318684651977018274536811)
            ·
              refine ⟨7978026977965527411805217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5318684651977018274536811 7978026977965527411805217)
              ·
                refine ⟨5983520233474145558853913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7978026977965527411805217 5983520233474145558853913)
                ·
                  refine ⟨4487640175105609169140435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5983520233474145558853913 4487640175105609169140435)
                  ·
                    refine ⟨6731460262658413753710653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4487640175105609169140435 6731460262658413753710653)
                    ·
                      refine ⟨2524297598496905157641495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6731460262658413753710653 2524297598496905157641495)
                      ·
                        rfl

theorem cell23_4916052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 2, 2, 1, 3].length) (baseStart_4916052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4916052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4916052 prefixEnd_4916052 := by exact prefixLift 4916052
  have htrace : WordTrace (prefixWord ++ tailWord_4916052) baseStart_4916052 baseEnd_4916052 := by
    simpa [prefixWord, tailWord_4916052, baseEnd_4916052] using wordTrace_append hprefix tailTrace_4916052
  have hstable : (prefixWord ++ tailWord_4916052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4916052).length < 2 ^ (prefixWord ++ tailWord_4916052).sum := by decide
  have hdescent : baseEnd_4916052 < baseStart_4916052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4916052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4916058 : List Nat := [3, 1, 1, 2, 1, 5, 1, 1, 4, 2, 2]
def baseStart_4916058 : Nat := 118140960795 + 4916058 * 2 ^ 59
def prefixEnd_4916058 : Nat := 4983230072969 + 3 ^ 40 * 4916058 * 2
def baseEnd_4916058 : Nat := 2524300679380832134166467

theorem tailTrace_4916058 : CollatzResearch.WordTrace tailWord_4916058 prefixEnd_4916058 2524300679380832134166467 := by
  unfold tailWord_4916058
  simp only [CollatzResearch.WordTrace]
  refine ⟨44825841405992234176967207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119535577082645957805245885 44825841405992234176967207)
  ·
    refine ⟨67238762108988351265450811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44825841405992234176967207 67238762108988351265450811)
    ·
      refine ⟨100858143163482526898176217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67238762108988351265450811 100858143163482526898176217)
      ·
        refine ⟨75643607372611895173632163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100858143163482526898176217 75643607372611895173632163)
        ·
          refine ⟨113465411058917842760448245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75643607372611895173632163 113465411058917842760448245)
          ·
            refine ⟨10637382286773547758792023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 113465411058917842760448245 10637382286773547758792023)
            ·
              refine ⟨15956073430160321638188035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10637382286773547758792023 15956073430160321638188035)
              ·
                refine ⟨23934110145240482457282053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15956073430160321638188035 23934110145240482457282053)
                ·
                  refine ⟨4487645652232590460740385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23934110145240482457282053 4487645652232590460740385)
                  ·
                    refine ⟨3365734239174442845555289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4487645652232590460740385 3365734239174442845555289)
                    ·
                      refine ⟨2524300679380832134166467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3365734239174442845555289 2524300679380832134166467)
                      ·
                        rfl

theorem cell23_4916058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 4, 2, 2].length) (baseStart_4916058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4916058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4916058 prefixEnd_4916058 := by exact prefixLift 4916058
  have htrace : WordTrace (prefixWord ++ tailWord_4916058) baseStart_4916058 baseEnd_4916058 := by
    simpa [prefixWord, tailWord_4916058, baseEnd_4916058] using wordTrace_append hprefix tailTrace_4916058
  have hstable : (prefixWord ++ tailWord_4916058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4916058).length < 2 ^ (prefixWord ++ tailWord_4916058).sum := by decide
  have hdescent : baseEnd_4916058 < baseStart_4916058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4916058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4916064 : List Nat := [2, 1, 1, 3, 3, 1, 4, 1, 7]
def baseStart_4916064 : Nat := 118140960795 + 4916064 * 2 ^ 59
def prefixEnd_4916064 : Nat := 4983230072969 + 3 ^ 40 * 4916064 * 2
def baseEnd_4916064 : Nat := 280478195584973234521271

theorem tailTrace_4916064 : CollatzResearch.WordTrace tailWord_4916064 prefixEnd_4916064 280478195584973234521271 := by
  unfold tailWord_4916064
  simp only [CollatzResearch.WordTrace]
  refine ⟨89651792230973599866293623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119535722974631466488391497 89651792230973599866293623)
  ·
    refine ⟨134477688346460399799440435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89651792230973599866293623 134477688346460399799440435)
    ·
      refine ⟨201716532519690599699160653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134477688346460399799440435 201716532519690599699160653)
      ·
        refine ⟨75643699694883974887185245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201716532519690599699160653 75643699694883974887185245)
        ·
          refine ⟨28366387385581490582694467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75643699694883974887185245 28366387385581490582694467)
          ·
            refine ⟨42549581078372235874041701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28366387385581490582694467 42549581078372235874041701)
            ·
              refine ⟨7978046452194794226382819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42549581078372235874041701 7978046452194794226382819)
              ·
                refine ⟨11967069678292191339574229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7978046452194794226382819 11967069678292191339574229)
                ·
                  refine ⟨280478195584973234521271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11967069678292191339574229 280478195584973234521271)
                  ·
                    rfl

theorem cell23_4916064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 7].length) (baseStart_4916064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4916064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4916064 prefixEnd_4916064 := by exact prefixLift 4916064
  have htrace : WordTrace (prefixWord ++ tailWord_4916064) baseStart_4916064 baseEnd_4916064 := by
    simpa [prefixWord, tailWord_4916064, baseEnd_4916064] using wordTrace_append hprefix tailTrace_4916064
  have hstable : (prefixWord ++ tailWord_4916064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4916064).length < 2 ^ (prefixWord ++ tailWord_4916064).sum := by decide
  have hdescent : baseEnd_4916064 < baseStart_4916064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4916064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4916131 : List Nat := [1, 1, 1, 4, 1, 2, 2, 3, 2, 4, 2]
def baseStart_4916131 : Nat := 118140960795 + 4916131 * 2 ^ 59
def prefixEnd_4916131 : Nat := 4983230072969 + 3 ^ 40 * 4916131 * 2
def baseEnd_4916131 : Nat := 2524338163468610348553631

theorem tailTrace_4916131 : CollatzResearch.WordTrace tailWord_4916131 prefixEnd_4916131 2524338163468610348553631 := by
  unfold tailWord_4916131
  simp only [CollatzResearch.WordTrace]
  refine ⟨179306028152704470175276247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119537352101802980116850831 179306028152704470175276247)
  ·
    refine ⟨268959042229056705262914371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179306028152704470175276247 268959042229056705262914371)
    ·
      refine ⟨403438563343585057894371557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268959042229056705262914371 403438563343585057894371557)
      ·
        refine ⟨75644730626922198355194667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 403438563343585057894371557 75644730626922198355194667)
        ·
          refine ⟨113467095940383297532792001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75644730626922198355194667 113467095940383297532792001)
          ·
            refine ⟨85100321955287473149594001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113467095940383297532792001 85100321955287473149594001)
            ·
              refine ⟨63825241466465604862195501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85100321955287473149594001 63825241466465604862195501)
              ·
                refine ⟨23934465549924601823323313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63825241466465604862195501 23934465549924601823323313)
                ·
                  refine ⟨17950849162443451367492485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23934465549924601823323313 17950849162443451367492485)
                  ·
                    refine ⟨3365784217958147131404841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17950849162443451367492485 3365784217958147131404841)
                    ·
                      refine ⟨2524338163468610348553631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3365784217958147131404841 2524338163468610348553631)
                      ·
                        rfl

theorem cell23_4916131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 4, 2].length) (baseStart_4916131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4916131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4916131 prefixEnd_4916131 := by exact prefixLift 4916131
  have htrace : WordTrace (prefixWord ++ tailWord_4916131) baseStart_4916131 baseEnd_4916131 := by
    simpa [prefixWord, tailWord_4916131, baseEnd_4916131] using wordTrace_append hprefix tailTrace_4916131
  have hstable : (prefixWord ++ tailWord_4916131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4916131).length < 2 ^ (prefixWord ++ tailWord_4916131).sum := by decide
  have hdescent : baseEnd_4916131 < baseStart_4916131 := by decide
  rcases family_descends (prefixWord ++ tailWord_4916131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4916151 : List Nat := [1, 1, 3, 1, 3, 1, 3, 3, 2, 2, 3]
def baseStart_4916151 : Nat := 118140960795 + 4916151 * 2 ^ 59
def prefixEnd_4916151 : Nat := 4983230072969 + 3 ^ 40 * 4916151 * 2
def baseEnd_4916151 : Nat := 2524348433081700270303539

theorem tailTrace_4916151 : CollatzResearch.WordTrace tailWord_4916151 prefixEnd_4916151 2524348433081700270303539 := by
  unfold tailWord_4916151
  simp only [CollatzResearch.WordTrace]
  refine ⟨179306757612632013591004307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119537838408421342394002871 179306757612632013591004307)
  ·
    refine ⟨268960136418948020386506461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179306757612632013591004307 268960136418948020386506461)
    ·
      refine ⟨100860051157105507644939923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 268960136418948020386506461 100860051157105507644939923)
      ·
        refine ⟨151290076735658261467409885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100860051157105507644939923 151290076735658261467409885)
        ·
          refine ⟨56733778775871848050278707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151290076735658261467409885 56733778775871848050278707)
          ·
            refine ⟨85100668163807772075418061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56733778775871848050278707 85100668163807772075418061)
            ·
              refine ⟨31912750561427914528281773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85100668163807772075418061 31912750561427914528281773)
              ·
                refine ⟨11967281460535467948105665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31912750561427914528281773 11967281460535467948105665)
                ·
                  refine ⟨8975461095401600961079249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11967281460535467948105665 8975461095401600961079249)
                  ·
                    refine ⟨6731595821551200720809437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8975461095401600961079249 6731595821551200720809437)
                    ·
                      refine ⟨2524348433081700270303539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6731595821551200720809437 2524348433081700270303539)
                      ·
                        rfl

theorem cell23_4916151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 2, 2, 3].length) (baseStart_4916151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4916151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4916151 prefixEnd_4916151 := by exact prefixLift 4916151
  have htrace : WordTrace (prefixWord ++ tailWord_4916151) baseStart_4916151 baseEnd_4916151 := by
    simpa [prefixWord, tailWord_4916151, baseEnd_4916151] using wordTrace_append hprefix tailTrace_4916151
  have hstable : (prefixWord ++ tailWord_4916151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4916151).length < 2 ^ (prefixWord ++ tailWord_4916151).sum := by decide
  have hdescent : baseEnd_4916151 < baseStart_4916151 := by decide
  rcases family_descends (prefixWord ++ tailWord_4916151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4916171 : List Nat := [1, 1, 1, 1, 3, 6, 2, 2, 6]
def baseStart_4916171 : Nat := 118140960795 + 4916171 * 2 ^ 59
def prefixEnd_4916171 : Nat := 4983230072969 + 3 ^ 40 * 4916171 * 2
def baseEnd_4916171 : Nat := 280484300299421132450383

theorem tailTrace_4916171 : CollatzResearch.WordTrace tailWord_4916171 prefixEnd_4916171 280484300299421132450383 := by
  unfold tailWord_4916171
  simp only [CollatzResearch.WordTrace]
  refine ⟨179307487072559557006732367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119538324715039704671154911 179307487072559557006732367)
  ·
    refine ⟨268961230608839335510098551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179307487072559557006732367 268961230608839335510098551)
    ·
      refine ⟨403441845913259003265147827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268961230608839335510098551 403441845913259003265147827)
      ·
        refine ⟨605162768869888504897721741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 403441845913259003265147827 605162768869888504897721741)
        ·
          refine ⟨226936038326208189336645653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 605162768869888504897721741 226936038326208189336645653)
          ·
            refine ⟨10637626796541008875155265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 226936038326208189336645653 10637626796541008875155265)
            ·
              refine ⟨7978220097405756656366449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10637626796541008875155265 7978220097405756656366449)
              ·
                refine ⟨5983665073054317492274837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7978220097405756656366449 5983665073054317492274837)
                ·
                  refine ⟨280484300299421132450383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5983665073054317492274837 280484300299421132450383)
                  ·
                    rfl

theorem cell23_4916171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 2, 6].length) (baseStart_4916171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4916171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4916171 prefixEnd_4916171 := by exact prefixLift 4916171
  have htrace : WordTrace (prefixWord ++ tailWord_4916171) baseStart_4916171 baseEnd_4916171 := by
    simpa [prefixWord, tailWord_4916171, baseEnd_4916171] using wordTrace_append hprefix tailTrace_4916171
  have hstable : (prefixWord ++ tailWord_4916171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4916171).length < 2 ^ (prefixWord ++ tailWord_4916171).sum := by decide
  have hdescent : baseEnd_4916171 < baseStart_4916171 := by decide
  rcases family_descends (prefixWord ++ tailWord_4916171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4916175 : List Nat := [1, 1, 2, 1, 1, 6, 4, 2, 1, 4]
def baseStart_4916175 : Nat := 118140960795 + 4916175 * 2 ^ 59
def prefixEnd_4916175 : Nat := 4983230072969 + 3 ^ 40 * 4916175 * 2
def baseEnd_4916175 : Nat := 841453585539136058801143

theorem tailTrace_4916175 : CollatzResearch.WordTrace tailWord_4916175 prefixEnd_4916175 841453585539136058801143 := by
  unfold tailWord_4916175
  simp only [CollatzResearch.WordTrace]
  refine ⟨179307632964545065689877979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119538421976363377126585319 179307632964545065689877979)
  ·
    refine ⟨268961449446817598534816969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179307632964545065689877979 268961449446817598534816969)
    ·
      refine ⟨201721087085113198901112727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268961449446817598534816969 201721087085113198901112727)
      ·
        refine ⟨302581630627669798351669091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201721087085113198901112727 302581630627669798351669091)
        ·
          refine ⟨453872445941504697527503637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302581630627669798351669091 453872445941504697527503637)
          ·
            refine ⟨21275270903508032696601733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 453872445941504697527503637 21275270903508032696601733)
            ·
              refine ⟨3989113294407756130612825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21275270903508032696601733 3989113294407756130612825)
              ·
                refine ⟨2991834970805817097959619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3989113294407756130612825 2991834970805817097959619)
                ·
                  refine ⟨4487752456208725646939429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2991834970805817097959619 4487752456208725646939429)
                  ·
                    refine ⟨841453585539136058801143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4487752456208725646939429 841453585539136058801143)
                    ·
                      rfl

theorem cell23_4916175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 2, 1, 4].length) (baseStart_4916175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4916175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4916175 prefixEnd_4916175 := by exact prefixLift 4916175
  have htrace : WordTrace (prefixWord ++ tailWord_4916175) baseStart_4916175 baseEnd_4916175 := by
    simpa [prefixWord, tailWord_4916175, baseEnd_4916175] using wordTrace_append hprefix tailTrace_4916175
  have hstable : (prefixWord ++ tailWord_4916175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4916175).length < 2 ^ (prefixWord ++ tailWord_4916175).sum := by decide
  have hdescent : baseEnd_4916175 < baseStart_4916175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4916175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4916222 : List Nat := [4, 2, 2, 2, 3, 1, 1, 2, 6]
def baseStart_4916222 : Nat := 118140960795 + 4916222 * 2 ^ 59
def prefixEnd_4916222 : Nat := 4983230072969 + 3 ^ 40 * 4916222 * 2
def baseEnd_4916222 : Nat := 280487210023129943612857

theorem tailTrace_4916222 : CollatzResearch.WordTrace tailWord_4916222 prefixEnd_4916222 280487210023129943612857 := by
  unfold tailWord_4916222
  simp only [CollatzResearch.WordTrace]
  refine ⟨22413668399421849089604865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119539564796916528477892613 22413668399421849089604865)
  ·
    refine ⟨16810251299566386817203649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22413668399421849089604865 16810251299566386817203649)
    ·
      refine ⟨12607688474674790112902737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16810251299566386817203649 12607688474674790112902737)
      ·
        refine ⟨9455766356006092584677053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12607688474674790112902737 9455766356006092584677053)
        ·
          refine ⟨3545912383502284719253895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9455766356006092584677053 3545912383502284719253895)
          ·
            refine ⟨5318868575253427078880843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3545912383502284719253895 5318868575253427078880843)
            ·
              refine ⟨7978302862880140618321265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5318868575253427078880843 7978302862880140618321265)
              ·
                refine ⟨5983727147160105463740949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7978302862880140618321265 5983727147160105463740949)
                ·
                  refine ⟨280487210023129943612857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5983727147160105463740949 280487210023129943612857)
                  ·
                    rfl

theorem cell23_4916222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_4916222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4916222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4916222 prefixEnd_4916222 := by exact prefixLift 4916222
  have htrace : WordTrace (prefixWord ++ tailWord_4916222) baseStart_4916222 baseEnd_4916222 := by
    simpa [prefixWord, tailWord_4916222, baseEnd_4916222] using wordTrace_append hprefix tailTrace_4916222
  have hstable : (prefixWord ++ tailWord_4916222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4916222).length < 2 ^ (prefixWord ++ tailWord_4916222).sum := by decide
  have hdescent : baseEnd_4916222 < baseStart_4916222 := by decide
  rcases family_descends (prefixWord ++ tailWord_4916222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4916241 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 3]
def baseStart_4916241 : Nat := 118140960795 + 4916241 * 2 ^ 59
def prefixEnd_4916241 : Nat := 4983230072969 + 3 ^ 40 * 4916241 * 2
def baseEnd_4916241 : Nat := 2524394646340604918178125

theorem tailTrace_4916241 : CollatzResearch.WordTrace tailWord_4916241 prefixEnd_4916241 2524394646340604918178125 := by
  unfold tailWord_4916241
  simp only [CollatzResearch.WordTrace]
  refine ⟨179310040182305958961780577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119540026788203972641187051 179310040182305958961780577)
  ·
    refine ⟨134482530136729469221335433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179310040182305958961780577 134482530136729469221335433)
    ·
      refine ⟨100861897602547101916001575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134482530136729469221335433 100861897602547101916001575)
      ·
        refine ⟨151292846403820652874002363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100861897602547101916001575 151292846403820652874002363)
        ·
          refine ⟨226939269605730979311003545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151292846403820652874002363 226939269605730979311003545)
          ·
            refine ⟨170204452204298234483252659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226939269605730979311003545 170204452204298234483252659)
            ·
              refine ⟨255306678306447351724878989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170204452204298234483252659 255306678306447351724878989)
              ·
                refine ⟨95740004364917756896829621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 255306678306447351724878989 95740004364917756896829621)
                ·
                  refine ⟨8975625409211039709077777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 95740004364917756896829621 8975625409211039709077777)
                  ·
                    refine ⟨6731719056908279781808333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8975625409211039709077777 6731719056908279781808333)
                    ·
                      refine ⟨2524394646340604918178125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6731719056908279781808333 2524394646340604918178125)
                      ·
                        rfl

theorem cell23_4916241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 3].length) (baseStart_4916241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4916241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4916241 prefixEnd_4916241 := by exact prefixLift 4916241
  have htrace : WordTrace (prefixWord ++ tailWord_4916241) baseStart_4916241 baseEnd_4916241 := by
    simpa [prefixWord, tailWord_4916241, baseEnd_4916241] using wordTrace_append hprefix tailTrace_4916241
  have hstable : (prefixWord ++ tailWord_4916241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4916241).length < 2 ^ (prefixWord ++ tailWord_4916241).sum := by decide
  have hdescent : baseEnd_4916241 < baseStart_4916241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4916241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4916248 : List Nat := [2, 1, 2, 3, 2, 4, 1, 1, 1, 6]
def baseStart_4916248 : Nat := 118140960795 + 4916248 * 2 ^ 59
def prefixEnd_4916248 : Nat := 4983230072969 + 3 ^ 40 * 4916248 * 2
def baseEnd_4916248 : Nat := 841466080235062130263531

theorem tailTrace_4916248 : CollatzResearch.WordTrace tailWord_4916248 prefixEnd_4916248 841466080235062130263531 := by
  unfold tailWord_4916248
  simp only [CollatzResearch.WordTrace]
  refine ⟨89655147746640299578642699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119540196995520399438190265 89655147746640299578642699)
  ·
    refine ⟨134482721619960449367964049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89655147746640299578642699 134482721619960449367964049)
    ·
      refine ⟨100862041214970337025973037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134482721619960449367964049 100862041214970337025973037)
      ·
        refine ⟨37823265455613876384739889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100862041214970337025973037 37823265455613876384739889)
        ·
          refine ⟨28367449091710407288554917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37823265455613876384739889 28367449091710407288554917)
          ·
            refine ⟨5318896704695701366604047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28367449091710407288554917 5318896704695701366604047)
            ·
              refine ⟨7978345057043552049906071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5318896704695701366604047 7978345057043552049906071)
              ·
                refine ⟨11967517585565328074859107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7978345057043552049906071 11967517585565328074859107)
                ·
                  refine ⟨17951276378347992112288661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11967517585565328074859107 17951276378347992112288661)
                  ·
                    refine ⟨841466080235062130263531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17951276378347992112288661 841466080235062130263531)
                    ·
                      rfl

theorem cell23_4916248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 1, 6].length) (baseStart_4916248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4916248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4916248 prefixEnd_4916248 := by exact prefixLift 4916248
  have htrace : WordTrace (prefixWord ++ tailWord_4916248) baseStart_4916248 baseEnd_4916248 := by
    simpa [prefixWord, tailWord_4916248, baseEnd_4916248] using wordTrace_append hprefix tailTrace_4916248
  have hstable : (prefixWord ++ tailWord_4916248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4916248).length < 2 ^ (prefixWord ++ tailWord_4916248).sum := by decide
  have hdescent : baseEnd_4916248 < baseStart_4916248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4916248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4916255 : List Nat := [1, 1, 2, 4, 1, 3, 2, 2, 3, 2, 2]
def baseStart_4916255 : Nat := 118140960795 + 4916255 * 2 ^ 59
def prefixEnd_4916255 : Nat := 4983230072969 + 3 ^ 40 * 4916255 * 2
def baseEnd_4916255 : Nat := 2524401835069767863403061

theorem tailTrace_4916255 : CollatzResearch.WordTrace tailWord_4916255 prefixEnd_4916255 2524401835069767863403061 := by
  unfold tailWord_4916255
  simp only [CollatzResearch.WordTrace]
  refine ⟨179310550804255239352790219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119540367202836826235193479 179310550804255239352790219)
  ·
    refine ⟨268965826206382859029185329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179310550804255239352790219 268965826206382859029185329)
    ·
      refine ⟨201724369654787144271888997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268965826206382859029185329 201724369654787144271888997)
      ·
        refine ⟨37823319310272589550979187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 201724369654787144271888997 37823319310272589550979187)
        ·
          refine ⟨56734978965408884326468781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37823319310272589550979187 56734978965408884326468781)
          ·
            refine ⟨21275617112028331622425793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56734978965408884326468781 21275617112028331622425793)
            ·
              refine ⟨15956712834021248716819345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21275617112028331622425793 15956712834021248716819345)
              ·
                refine ⟨11967534625515936537614509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15956712834021248716819345 11967534625515936537614509)
                ·
                  refine ⟨4487825484568476201605441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11967534625515936537614509 4487825484568476201605441)
                  ·
                    refine ⟨3365869113426357151204081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4487825484568476201605441 3365869113426357151204081)
                    ·
                      refine ⟨2524401835069767863403061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3365869113426357151204081 2524401835069767863403061)
                      ·
                        rfl

theorem cell23_4916255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 3, 2, 2].length) (baseStart_4916255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4916255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4916255 prefixEnd_4916255 := by exact prefixLift 4916255
  have htrace : WordTrace (prefixWord ++ tailWord_4916255) baseStart_4916255 baseEnd_4916255 := by
    simpa [prefixWord, tailWord_4916255, baseEnd_4916255] using wordTrace_append hprefix tailTrace_4916255
  have hstable : (prefixWord ++ tailWord_4916255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4916255).length < 2 ^ (prefixWord ++ tailWord_4916255).sum := by decide
  have hdescent : baseEnd_4916255 < baseStart_4916255 := by decide
  rcases family_descends (prefixWord ++ tailWord_4916255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4916266 : List Nat := [3, 1, 4, 1, 4, 1, 1, 3, 1, 1, 3]
def baseStart_4916266 : Nat := 118140960795 + 4916266 * 2 ^ 59
def prefixEnd_4916266 : Nat := 4983230072969 + 3 ^ 40 * 4916266 * 2
def baseEnd_4916266 : Nat := 2524407483356967320365511

theorem tailTrace_4916266 : CollatzResearch.WordTrace tailWord_4916266 prefixEnd_4916266 2524407483356967320365511 := by
  unfold tailWord_4916266
  simp only [CollatzResearch.WordTrace]
  refine ⟨44827738001803847057860163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119540634671476925487627101 44827738001803847057860163)
  ·
    refine ⟨67241607002705770586790245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44827738001803847057860163 67241607002705770586790245)
    ·
      refine ⟨12607801313007331985023171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67241607002705770586790245 12607801313007331985023171)
      ·
        refine ⟨18911701969510997977534757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12607801313007331985023171 18911701969510997977534757)
        ·
          refine ⟨3545944119283312120787767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18911701969510997977534757 3545944119283312120787767)
          ·
            refine ⟨5318916178924968181181651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3545944119283312120787767 5318916178924968181181651)
            ·
              refine ⟨7978374268387452271772477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5318916178924968181181651 7978374268387452271772477)
              ·
                refine ⟨2991890350645294601914679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7978374268387452271772477 2991890350645294601914679)
                ·
                  refine ⟨4487835525967941902872019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2991890350645294601914679 4487835525967941902872019)
                  ·
                    refine ⟨6731753288951912854308029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4487835525967941902872019 6731753288951912854308029)
                    ·
                      refine ⟨2524407483356967320365511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6731753288951912854308029 2524407483356967320365511)
                      ·
                        rfl

theorem cell23_4916266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_4916266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4916266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4916266 prefixEnd_4916266 := by exact prefixLift 4916266
  have htrace : WordTrace (prefixWord ++ tailWord_4916266) baseStart_4916266 baseEnd_4916266 := by
    simpa [prefixWord, tailWord_4916266, baseEnd_4916266] using wordTrace_append hprefix tailTrace_4916266
  have hstable : (prefixWord ++ tailWord_4916266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4916266).length < 2 ^ (prefixWord ++ tailWord_4916266).sum := by decide
  have hdescent : baseEnd_4916266 < baseStart_4916266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4916266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4916278 : List Nat := [5, 1, 2, 1, 1, 4, 9]
def baseStart_4916278 : Nat := 118140960795 + 4916278 * 2 ^ 59
def prefixEnd_4916278 : Nat := 4983230072969 + 3 ^ 40 * 4916278 * 2
def baseEnd_4916278 : Nat := 31165600557096558931055

theorem tailTrace_4916278 : CollatzResearch.WordTrace tailWord_4916278 prefixEnd_4916278 31165600557096558931055 := by
  unfold tailWord_4916278
  simp only [CollatzResearch.WordTrace]
  refine ⟨11206961855198244642554843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 119540926455447942853918325 11206961855198244642554843)
  ·
    refine ⟨16810442782797366963832265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11206961855198244642554843 16810442782797366963832265)
    ·
      refine ⟨12607832087098025222874199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16810442782797366963832265 12607832087098025222874199)
      ·
        refine ⟨18911748130647037834311299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12607832087098025222874199 18911748130647037834311299)
        ·
          refine ⟨28367622195970556751466949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18911748130647037834311299 28367622195970556751466949)
          ·
            refine ⟨5318929161744479390900053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28367622195970556751466949 5318929161744479390900053)
            ·
              refine ⟨31165600557096558931055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5318929161744479390900053 31165600557096558931055)
              ·
                rfl

theorem cell23_4916278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 9].length) (baseStart_4916278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4916278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4916278 prefixEnd_4916278 := by exact prefixLift 4916278
  have htrace : WordTrace (prefixWord ++ tailWord_4916278) baseStart_4916278 baseEnd_4916278 := by
    simpa [prefixWord, tailWord_4916278, baseEnd_4916278] using wordTrace_append hprefix tailTrace_4916278
  have hstable : (prefixWord ++ tailWord_4916278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4916278).length < 2 ^ (prefixWord ++ tailWord_4916278).sum := by decide
  have hdescent : baseEnd_4916278 < baseStart_4916278 := by decide
  rcases family_descends (prefixWord ++ tailWord_4916278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4916288 : List Nat := [2, 1, 1, 2, 2, 3, 1, 3, 4, 1, 3]
def baseStart_4916288 : Nat := 118140960795 + 4916288 * 2 ^ 59
def prefixEnd_4916288 : Nat := 4983230072969 + 3 ^ 40 * 4916288 * 2
def baseEnd_4916288 : Nat := 2524418779931366234290409

theorem tailTrace_4916288 : CollatzResearch.WordTrace tailWord_4916288 prefixEnd_4916288 2524418779931366234290409 := by
  unfold tailWord_4916288
  simp only [CollatzResearch.WordTrace]
  refine ⟨89655877206567842994370759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119541169608757123992494345 89655877206567842994370759)
  ·
    refine ⟨134483815809851764491556139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89655877206567842994370759 134483815809851764491556139)
    ·
      refine ⟨201725723714777646737334209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134483815809851764491556139 201725723714777646737334209)
      ·
        refine ⟨151294292786083235053000657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201725723714777646737334209 151294292786083235053000657)
        ·
          refine ⟨113470719589562426289750493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151294292786083235053000657 113470719589562426289750493)
          ·
            refine ⟨42551519846085909858656435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113470719589562426289750493 42551519846085909858656435)
            ·
              refine ⟨63827279769128864787984653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42551519846085909858656435 63827279769128864787984653)
              ·
                refine ⟨23935229913423324295494245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63827279769128864787984653 23935229913423324295494245)
                ·
                  refine ⟨4487855608766873305405171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23935229913423324295494245 4487855608766873305405171)
                  ·
                    refine ⟨6731783413150309958107757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4487855608766873305405171 6731783413150309958107757)
                    ·
                      refine ⟨2524418779931366234290409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6731783413150309958107757 2524418779931366234290409)
                      ·
                        rfl

theorem cell23_4916288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 4, 1, 3].length) (baseStart_4916288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4916288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4916288 prefixEnd_4916288 := by exact prefixLift 4916288
  have htrace : WordTrace (prefixWord ++ tailWord_4916288) baseStart_4916288 baseEnd_4916288 := by
    simpa [prefixWord, tailWord_4916288, baseEnd_4916288] using wordTrace_append hprefix tailTrace_4916288
  have hstable : (prefixWord ++ tailWord_4916288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4916288).length < 2 ^ (prefixWord ++ tailWord_4916288).sum := by decide
  have hdescent : baseEnd_4916288 < baseStart_4916288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4916288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4916289 : List Nat := [1, 2, 5, 1, 3, 2, 1, 1, 3, 2, 2]
def baseStart_4916289 : Nat := 118140960795 + 4916289 * 2 ^ 59
def prefixEnd_4916289 : Nat := 4983230072969 + 3 ^ 40 * 4916289 * 2
def baseEnd_4916289 : Nat := 2524419293412020730377905

theorem tailTrace_4916289 : CollatzResearch.WordTrace tailWord_4916289 prefixEnd_4916289 2524419293412020730377905 := by
  unfold tailWord_4916289
  simp only [CollatzResearch.WordTrace]
  refine ⟨179311790886132063159527921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119541193924088042106351947 179311790886132063159527921)
  ·
    refine ⟨134483843164599047369645941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179311790886132063159527921 134483843164599047369645941)
    ·
      refine ⟨12607860296681160690904307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 134483843164599047369645941 12607860296681160690904307)
      ·
        refine ⟨18911790445021741036356461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12607860296681160690904307 18911790445021741036356461)
        ·
          refine ⟨7091921416883152888633673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18911790445021741036356461 7091921416883152888633673)
          ·
            refine ⟨5318941062662364666475255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7091921416883152888633673 5318941062662364666475255)
            ·
              refine ⟨7978411593993546999712883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5318941062662364666475255 7978411593993546999712883)
              ·
                refine ⟨11967617390990320499569325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7978411593993546999712883 11967617390990320499569325)
                ·
                  refine ⟨4487856521621370187338497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11967617390990320499569325 4487856521621370187338497)
                  ·
                    refine ⟨3365892391216027640503873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4487856521621370187338497 3365892391216027640503873)
                    ·
                      refine ⟨2524419293412020730377905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3365892391216027640503873 2524419293412020730377905)
                      ·
                        rfl

theorem cell23_4916289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_4916289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4916289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4916289 prefixEnd_4916289 := by exact prefixLift 4916289
  have htrace : WordTrace (prefixWord ++ tailWord_4916289) baseStart_4916289 baseEnd_4916289 := by
    simpa [prefixWord, tailWord_4916289, baseEnd_4916289] using wordTrace_append hprefix tailTrace_4916289
  have hstable : (prefixWord ++ tailWord_4916289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4916289).length < 2 ^ (prefixWord ++ tailWord_4916289).sum := by decide
  have hdescent : baseEnd_4916289 < baseStart_4916289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4916289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4916331 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 6, 4, 3]
def baseStart_4916331 : Nat := 118140960795 + 4916331 * 2 ^ 59
def prefixEnd_4916331 : Nat := 4983230072969 + 3 ^ 40 * 4916331 * 2
def baseEnd_4916331 : Nat := 2524440859599509566052711

theorem tailTrace_4916331 : CollatzResearch.WordTrace tailWord_4916331 prefixEnd_4916331 2524440859599509566052711 := by
  unfold tailWord_4916331
  simp only [CollatzResearch.WordTrace]
  refine ⟨179313322751979904332556847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119542215167986602888371231 179313322751979904332556847)
  ·
    refine ⟨268969984127969856498835271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179313322751979904332556847 268969984127969856498835271)
    ·
      refine ⟨403454976191954784748252907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268969984127969856498835271 403454976191954784748252907)
      ·
        refine ⟨605182464287932177122379361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 403454976191954784748252907 605182464287932177122379361)
        ·
          refine ⟨453886848215949132841784521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 605182464287932177122379361 453886848215949132841784521)
          ·
            refine ⟨340415136161961849631338391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 453886848215949132841784521 340415136161961849631338391)
            ·
              refine ⟨510622704242942774447007587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 340415136161961849631338391 510622704242942774447007587)
              ·
                refine ⟨765934056364414161670511381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 510622704242942774447007587 765934056364414161670511381)
                ·
                  refine ⟨35903158892081913828305221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 765934056364414161670511381 35903158892081913828305221)
                  ·
                    refine ⟨6731842292265358842807229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35903158892081913828305221 6731842292265358842807229)
                    ·
                      refine ⟨2524440859599509566052711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6731842292265358842807229 2524440859599509566052711)
                      ·
                        rfl

theorem cell23_4916331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 4, 3].length) (baseStart_4916331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4916331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4916331 prefixEnd_4916331 := by exact prefixLift 4916331
  have htrace : WordTrace (prefixWord ++ tailWord_4916331) baseStart_4916331 baseEnd_4916331 := by
    simpa [prefixWord, tailWord_4916331, baseEnd_4916331] using wordTrace_append hprefix tailTrace_4916331
  have hstable : (prefixWord ++ tailWord_4916331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4916331).length < 2 ^ (prefixWord ++ tailWord_4916331).sum := by decide
  have hdescent : baseEnd_4916331 < baseStart_4916331 := by decide
  rcases family_descends (prefixWord ++ tailWord_4916331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4916332 : List Nat := [2, 2, 1, 1, 3, 2, 5, 1, 1, 3, 2]
def baseStart_4916332 : Nat := 118140960795 + 4916332 * 2 ^ 59
def prefixEnd_4916332 : Nat := 4983230072969 + 3 ^ 40 * 4916332 * 2
def baseEnd_4916332 : Nat := 2524441373080164062140207

theorem tailTrace_4916332 : CollatzResearch.WordTrace tailWord_4916332 prefixEnd_4916332 2524441373080164062140207 := by
  unfold tailWord_4916332
  simp only [CollatzResearch.WordTrace]
  refine ⟨89656679612488140751671625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119542239483317521002228833 89656679612488140751671625)
  ·
    refine ⟨67242509709366105563753719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89656679612488140751671625 67242509709366105563753719)
    ·
      refine ⟨100863764564049158345630579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67242509709366105563753719 100863764564049158345630579)
      ·
        refine ⟨151295646846073737518445869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100863764564049158345630579 151295646846073737518445869)
        ·
          refine ⟨56735867567277651569417201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151295646846073737518445869 56735867567277651569417201)
          ·
            refine ⟨42551900675458238677062901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56735867567277651569417201 42551900675458238677062901)
            ·
              refine ⟨3989240688324209875974647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42551900675458238677062901 3989240688324209875974647)
              ·
                refine ⟨5983861032486314813961971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3989240688324209875974647 5983861032486314813961971)
                ·
                  refine ⟨8975791548729472220942957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5983861032486314813961971 8975791548729472220942957)
                  ·
                    refine ⟨3365921830773552082853609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8975791548729472220942957 3365921830773552082853609)
                    ·
                      refine ⟨2524441373080164062140207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3365921830773552082853609 2524441373080164062140207)
                      ·
                        rfl

theorem cell23_4916332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 3, 2].length) (baseStart_4916332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4916332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4916332 prefixEnd_4916332 := by exact prefixLift 4916332
  have htrace : WordTrace (prefixWord ++ tailWord_4916332) baseStart_4916332 baseEnd_4916332 := by
    simpa [prefixWord, tailWord_4916332, baseEnd_4916332] using wordTrace_append hprefix tailTrace_4916332
  have hstable : (prefixWord ++ tailWord_4916332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4916332).length < 2 ^ (prefixWord ++ tailWord_4916332).sum := by decide
  have hdescent : baseEnd_4916332 < baseStart_4916332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4916332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4916362 : List Nat := [3, 1, 2, 3, 1, 1, 1, 5, 2, 2, 2]
def baseStart_4916362 : Nat := 118140960795 + 4916362 * 2 ^ 59
def prefixEnd_4916362 : Nat := 4983230072969 + 3 ^ 40 * 4916362 * 2
def baseEnd_4916362 : Nat := 2524456777499798944765069

theorem tailTrace_4916362 : CollatzResearch.WordTrace tailWord_4916362 prefixEnd_4916362 2524456777499798944765069 := by
  unfold tailWord_4916362
  simp only [CollatzResearch.WordTrace]
  refine ⟨44828613353716899156733835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119542968943245064417956893 44828613353716899156733835)
  ·
    refine ⟨67242920030575348735100753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44828613353716899156733835 67242920030575348735100753)
    ·
      refine ⟨50432190022931511551325565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67242920030575348735100753 50432190022931511551325565)
      ·
        refine ⟨18912071258599316831747087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50432190022931511551325565 18912071258599316831747087)
        ·
          refine ⟨28368106887898975247620631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18912071258599316831747087 28368106887898975247620631)
          ·
            refine ⟨42552160331848462871430947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28368106887898975247620631 42552160331848462871430947)
            ·
              refine ⟨63828240497772694307146421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42552160331848462871430947 63828240497772694307146421)
              ·
                refine ⟨5983897546666190091294977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63828240497772694307146421 5983897546666190091294977)
                ·
                  refine ⟨4487923159999642568471233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5983897546666190091294977 4487923159999642568471233)
                  ·
                    refine ⟨3365942369999731926353425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4487923159999642568471233 3365942369999731926353425)
                    ·
                      refine ⟨2524456777499798944765069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3365942369999731926353425 2524456777499798944765069)
                      ·
                        rfl

theorem cell23_4916362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_4916362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4916362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4916362 prefixEnd_4916362 := by exact prefixLift 4916362
  have htrace : WordTrace (prefixWord ++ tailWord_4916362) baseStart_4916362 baseEnd_4916362 := by
    simpa [prefixWord, tailWord_4916362, baseEnd_4916362] using wordTrace_append hprefix tailTrace_4916362
  have hstable : (prefixWord ++ tailWord_4916362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4916362).length < 2 ^ (prefixWord ++ tailWord_4916362).sum := by decide
  have hdescent : baseEnd_4916362 < baseStart_4916362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4916362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4916385 : List Nat := [1, 2, 3, 3, 1, 1, 4, 3, 5]
def baseStart_4916385 : Nat := 118140960795 + 4916385 * 2 ^ 59
def prefixEnd_4916385 : Nat := 4983230072969 + 3 ^ 40 * 4916385 * 2
def baseEnd_4916385 : Nat := 280496509728316928308607

theorem tailTrace_4916385 : CollatzResearch.WordTrace tailWord_4916385 prefixEnd_4916385 280496509728316928308607 := by
  unfold tailWord_4916385
  simp only [CollatzResearch.WordTrace]
  refine ⟨179315292293784271555022609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119543528195856181036681739 179315292293784271555022609)
  ·
    refine ⟨134486469220338203666266957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179315292293784271555022609 134486469220338203666266957)
    ·
      refine ⟨50432425957626826374850109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134486469220338203666266957 50432425957626826374850109)
      ·
        refine ⟨18912159734110059890568791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50432425957626826374850109 18912159734110059890568791)
        ·
          refine ⟨28368239601165089835853187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18912159734110059890568791 28368239601165089835853187)
          ·
            refine ⟨42552359401747634753779781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28368239601165089835853187 42552359401747634753779781)
            ·
              refine ⟨7978567387827681516333709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42552359401747634753779781 7978567387827681516333709)
              ·
                refine ⟨2991962770435380568625141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7978567387827681516333709 2991962770435380568625141)
                ·
                  refine ⟨280496509728316928308607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2991962770435380568625141 280496509728316928308607)
                  ·
                    rfl

theorem cell23_4916385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 3, 5].length) (baseStart_4916385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4916385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4916385 prefixEnd_4916385 := by exact prefixLift 4916385
  have htrace : WordTrace (prefixWord ++ tailWord_4916385) baseStart_4916385 baseEnd_4916385 := by
    simpa [prefixWord, tailWord_4916385, baseEnd_4916385] using wordTrace_append hprefix tailTrace_4916385
  have hstable : (prefixWord ++ tailWord_4916385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4916385).length < 2 ^ (prefixWord ++ tailWord_4916385).sum := by decide
  have hdescent : baseEnd_4916385 < baseStart_4916385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4916385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4916431 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 6]
def baseStart_4916431 : Nat := 118140960795 + 4916431 * 2 ^ 59
def prefixEnd_4916431 : Nat := 4983230072969 + 3 ^ 40 * 4916431 * 2
def baseEnd_4916431 : Nat := 2524492207664959174802251

theorem tailTrace_4916431 : CollatzResearch.WordTrace tailWord_4916431 prefixEnd_4916431 2524492207664959174802251 := by
  unfold tailWord_4916431
  simp only [CollatzResearch.WordTrace]
  refine ⟨179316970051617621411197147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119544646701078414274131431 179316970051617621411197147)
  ·
    refine ⟨268975455077426432116795721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179316970051617621411197147 268975455077426432116795721)
    ·
      refine ⟨201731591308069824087596791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268975455077426432116795721 201731591308069824087596791)
      ·
        refine ⟨302597386962104736131395187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201731591308069824087596791 302597386962104736131395187)
        ·
          refine ⟨453896080443157104197092781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302597386962104736131395187 453896080443157104197092781)
          ·
            refine ⟨170211030166183914073909793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 453896080443157104197092781 170211030166183914073909793)
            ·
              refine ⟨127658272624637935555432345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170211030166183914073909793 127658272624637935555432345)
              ·
                refine ⟨95743704468478451666574259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127658272624637935555432345 95743704468478451666574259)
                ·
                  refine ⟨143615556702717677499861389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95743704468478451666574259 143615556702717677499861389)
                  ·
                    refine ⟨53855833763519129062448021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 143615556702717677499861389 53855833763519129062448021)
                    ·
                      refine ⟨2524492207664959174802251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53855833763519129062448021 2524492207664959174802251)
                      ·
                        rfl

theorem cell23_4916431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 6].length) (baseStart_4916431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4916431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4916431 prefixEnd_4916431 := by exact prefixLift 4916431
  have htrace : WordTrace (prefixWord ++ tailWord_4916431) baseStart_4916431 baseEnd_4916431 := by
    simpa [prefixWord, tailWord_4916431, baseEnd_4916431] using wordTrace_append hprefix tailTrace_4916431
  have hstable : (prefixWord ++ tailWord_4916431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4916431).length < 2 ^ (prefixWord ++ tailWord_4916431).sum := by decide
  have hdescent : baseEnd_4916431 < baseStart_4916431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4916431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4916436 : List Nat := [2, 4, 1, 4, 2, 1, 1, 3, 5]
def baseStart_4916436 : Nat := 118140960795 + 4916436 * 2 ^ 59
def prefixEnd_4916436 : Nat := 4983230072969 + 3 ^ 40 * 4916436 * 2
def baseEnd_4916436 : Nat := 280499419452025739471081

theorem tailTrace_4916436 : CollatzResearch.WordTrace tailWord_4916436 prefixEnd_4916436 280499419452025739471081 := by
  unfold tailWord_4916436
  simp only [CollatzResearch.WordTrace]
  refine ⟨89658576208299753632564581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119544768277733004843419441 89658576208299753632564581)
  ·
    refine ⟨16810983039056203806105859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89658576208299753632564581 16810983039056203806105859)
    ·
      refine ⟨25216474558584305709158789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16810983039056203806105859 25216474558584305709158789)
      ·
        refine ⟨4728088979734557320467273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25216474558584305709158789 4728088979734557320467273)
        ·
          refine ⟨3546066734800917990350455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4728088979734557320467273 3546066734800917990350455)
          ·
            refine ⟨5319100102201376985525683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3546066734800917990350455 5319100102201376985525683)
            ·
              refine ⟨7978650153302065478288525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5319100102201376985525683 7978650153302065478288525)
              ·
                refine ⟨2991993807488274554358197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7978650153302065478288525 2991993807488274554358197)
                ·
                  refine ⟨280499419452025739471081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2991993807488274554358197 280499419452025739471081)
                  ·
                    rfl

theorem cell23_4916436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_4916436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4916436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4916436 prefixEnd_4916436 := by exact prefixLift 4916436
  have htrace : WordTrace (prefixWord ++ tailWord_4916436) baseStart_4916436 baseEnd_4916436 := by
    simpa [prefixWord, tailWord_4916436, baseEnd_4916436] using wordTrace_append hprefix tailTrace_4916436
  have hstable : (prefixWord ++ tailWord_4916436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4916436).length < 2 ^ (prefixWord ++ tailWord_4916436).sum := by decide
  have hdescent : baseEnd_4916436 < baseStart_4916436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4916436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4916458 : List Nat := [3, 1, 3, 1, 1, 3, 2, 1, 8]
def baseStart_4916458 : Nat := 118140960795 + 4916458 * 2 ^ 59
def prefixEnd_4916458 : Nat := 4983230072969 + 3 ^ 40 * 4916458 * 2
def baseEnd_4916458 : Nat := 280500674626958952129403

theorem tailTrace_4916458 : CollatzResearch.WordTrace tailWord_4916458 prefixEnd_4916458 280500674626958952129403 := by
  unfold tailWord_4916458
  simp only [CollatzResearch.WordTrace]
  refine ⟨44829488705629951255607507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119545303215013203348286685 44829488705629951255607507)
  ·
    refine ⟨67244233058444926883411261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44829488705629951255607507 67244233058444926883411261)
    ·
      refine ⟨25216587396916847581279223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67244233058444926883411261 25216587396916847581279223)
      ·
        refine ⟨37824881095375271371918835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25216587396916847581279223 37824881095375271371918835)
        ·
          refine ⟨56737321643062907057878253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37824881095375271371918835 56737321643062907057878253)
          ·
            refine ⟨21276495616148590146704345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56737321643062907057878253 21276495616148590146704345)
            ·
              refine ⟨15957371712111442610028259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21276495616148590146704345 15957371712111442610028259)
              ·
                refine ⟨23936057568167163915042389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15957371712111442610028259 23936057568167163915042389)
                ·
                  refine ⟨280500674626958952129403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23936057568167163915042389 280500674626958952129403)
                  ·
                    rfl

theorem cell23_4916458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 8].length) (baseStart_4916458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4916458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4916458 prefixEnd_4916458 := by exact prefixLift 4916458
  have htrace : WordTrace (prefixWord ++ tailWord_4916458) baseStart_4916458 baseEnd_4916458 := by
    simpa [prefixWord, tailWord_4916458, baseEnd_4916458] using wordTrace_append hprefix tailTrace_4916458
  have hstable : (prefixWord ++ tailWord_4916458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4916458).length < 2 ^ (prefixWord ++ tailWord_4916458).sum := by decide
  have hdescent : baseEnd_4916458 < baseStart_4916458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4916458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4916462 : List Nat := [4, 1, 2, 1, 1, 1, 2, 6, 1, 4]
def baseStart_4916462 : Nat := 118140960795 + 4916462 * 2 ^ 59
def prefixEnd_4916462 : Nat := 4983230072969 + 3 ^ 40 * 4916462 * 2
def baseEnd_4916462 : Nat := 841502708521749517838203

theorem tailTrace_4916462 : CollatzResearch.WordTrace tailWord_4916462 prefixEnd_4916462 841502708521749517838203 := by
  unfold tailWord_4916462
  simp only [CollatzResearch.WordTrace]
  refine ⟨22414762589313164213196955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119545400476336875803717093 22414762589313164213196955)
  ·
    refine ⟨33622143883969746319795433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22414762589313164213196955 33622143883969746319795433)
    ·
      refine ⟨25216607912977309739846575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33622143883969746319795433 25216607912977309739846575)
      ·
        refine ⟨37824911869465964609769863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25216607912977309739846575 37824911869465964609769863)
        ·
          refine ⟨56737367804198946914654795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37824911869465964609769863 56737367804198946914654795)
          ·
            refine ⟨85106051706298420371982193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56737367804198946914654795 85106051706298420371982193)
            ·
              refine ⟨63829538779723815278986645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85106051706298420371982193 63829538779723815278986645)
              ·
                refine ⟨2992009630299553841202499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 63829538779723815278986645 2992009630299553841202499)
                ·
                  refine ⟨4488014445449330761803749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2992009630299553841202499 4488014445449330761803749)
                  ·
                    refine ⟨841502708521749517838203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4488014445449330761803749 841502708521749517838203)
                    ·
                      rfl

theorem cell23_4916462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_4916462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4916462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4916462 prefixEnd_4916462 := by exact prefixLift 4916462
  have htrace : WordTrace (prefixWord ++ tailWord_4916462) baseStart_4916462 baseEnd_4916462 := by
    simpa [prefixWord, tailWord_4916462, baseEnd_4916462] using wordTrace_append hprefix tailTrace_4916462
  have hstable : (prefixWord ++ tailWord_4916462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4916462).length < 2 ^ (prefixWord ++ tailWord_4916462).sum := by decide
  have hdescent : baseEnd_4916462 < baseStart_4916462 := by decide
  rcases family_descends (prefixWord ++ tailWord_4916462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4916485 : List Nat := [1, 3, 1, 1, 2, 1, 4, 1, 5, 1, 3]
def baseStart_4916485 : Nat := 118140960795 + 4916485 * 2 ^ 59
def prefixEnd_4916485 : Nat := 4983230072969 + 3 ^ 40 * 4916485 * 2
def baseEnd_4916485 : Nat := 2524519935620301963527003

theorem tailTrace_4916485 : CollatzResearch.WordTrace tailWord_4916485 prefixEnd_4916485 2524519935620301963527003 := by
  unfold tailWord_4916485
  simp only [CollatzResearch.WordTrace]
  refine ⟨179318939593421988633662909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119545959728947992422441939 179318939593421988633662909)
  ·
    refine ⟨67244602347533245737623591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179318939593421988633662909 67244602347533245737623591)
    ·
      refine ⟨100866903521299868606435387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67244602347533245737623591 100866903521299868606435387)
      ·
        refine ⟨151300355281949802909653081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100866903521299868606435387 151300355281949802909653081)
        ·
          refine ⟨113475266461462352182239811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151300355281949802909653081 113475266461462352182239811)
          ·
            refine ⟨170212899692193528273359717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113475266461462352182239811 170212899692193528273359717)
            ·
              refine ⟨31914918692286286551254947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 170212899692193528273359717 31914918692286286551254947)
              ·
                refine ⟨47872378038429429826882421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31914918692286286551254947 47872378038429429826882421)
                ·
                  refine ⟨4488035441102759046270227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47872378038429429826882421 4488035441102759046270227)
                  ·
                    refine ⟨6732053161654138569405341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4488035441102759046270227 6732053161654138569405341)
                    ·
                      refine ⟨2524519935620301963527003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6732053161654138569405341 2524519935620301963527003)
                      ·
                        rfl

theorem cell23_4916485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 5, 1, 3].length) (baseStart_4916485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4916485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4916485 prefixEnd_4916485 := by exact prefixLift 4916485
  have htrace : WordTrace (prefixWord ++ tailWord_4916485) baseStart_4916485 baseEnd_4916485 := by
    simpa [prefixWord, tailWord_4916485, baseEnd_4916485] using wordTrace_append hprefix tailTrace_4916485
  have hstable : (prefixWord ++ tailWord_4916485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4916485).length < 2 ^ (prefixWord ++ tailWord_4916485).sum := by decide
  have hdescent : baseEnd_4916485 < baseStart_4916485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4916485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4916528 : List Nat := [2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 5]
def baseStart_4916528 : Nat := 118140960795 + 4916528 * 2 ^ 59
def prefixEnd_4916528 : Nat := 4983230072969 + 3 ^ 40 * 4916528 * 2
def baseEnd_4916528 : Nat := 2524542015288445295289305

theorem tailTrace_4916528 : CollatzResearch.WordTrace tailWord_4916528 prefixEnd_4916528 2524542015288445295289305 := by
  unfold tailWord_4916528
  simp only [CollatzResearch.WordTrace]
  refine ⟨89660253966133103488739119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119547005288177471318318825 89660253966133103488739119)
  ·
    refine ⟨134490380949199655233108679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89660253966133103488739119 134490380949199655233108679)
    ·
      refine ⟨201735571423799482849663019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134490380949199655233108679 201735571423799482849663019)
      ·
        refine ⟨302603357135699224274494529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201735571423799482849663019 302603357135699224274494529)
        ·
          refine ⟨226952517851774418205870897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 302603357135699224274494529 226952517851774418205870897)
          ·
            refine ⟨170214388388830813654403173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226952517851774418205870897 170214388388830813654403173)
            ·
              refine ⟨31915197822905777560200595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 170214388388830813654403173 31915197822905777560200595)
              ·
                refine ⟨47872796734358666340300893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31915197822905777560200595 47872796734358666340300893)
                ·
                  refine ⟨17952298775384499877612835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47872796734358666340300893 17952298775384499877612835)
                  ·
                    refine ⟨26928448163076749816419253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17952298775384499877612835 26928448163076749816419253)
                    ·
                      refine ⟨2524542015288445295289305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26928448163076749816419253 2524542015288445295289305)
                      ·
                        rfl

theorem cell23_4916528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 5].length) (baseStart_4916528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4916528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4916528 prefixEnd_4916528 := by exact prefixLift 4916528
  have htrace : WordTrace (prefixWord ++ tailWord_4916528) baseStart_4916528 baseEnd_4916528 := by
    simpa [prefixWord, tailWord_4916528, baseEnd_4916528] using wordTrace_append hprefix tailTrace_4916528
  have hstable : (prefixWord ++ tailWord_4916528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4916528).length < 2 ^ (prefixWord ++ tailWord_4916528).sum := by decide
  have hdescent : baseEnd_4916528 < baseStart_4916528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4916528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4916542 : List Nat := [4, 2, 1, 2, 1, 1, 2, 4, 1, 1, 4]
def baseStart_4916542 : Nat := 118140960795 + 4916542 * 2 ^ 59
def prefixEnd_4916542 : Nat := 4983230072969 + 3 ^ 40 * 4916542 * 2
def baseEnd_4916542 : Nat := 2524549204017608240514241

theorem tailTrace_4916542 : CollatzResearch.WordTrace tailWord_4916542 prefixEnd_4916542 2524549204017608240514241 := by
  unfold tailWord_4916542
  simp only [CollatzResearch.WordTrace]
  refine ⟨22415127319276935921060985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119547345702810324912325253 22415127319276935921060985)
  ·
    refine ⟨16811345489457701940795739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22415127319276935921060985 16811345489457701940795739)
    ·
      refine ⟨25217018234186552911193609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16811345489457701940795739 25217018234186552911193609)
      ·
        refine ⟨18912763675639914683395207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25217018234186552911193609 18912763675639914683395207)
        ·
          refine ⟨28369145513459872025092811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18912763675639914683395207 28369145513459872025092811)
          ·
            refine ⟨42553718270189808037639217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28369145513459872025092811 42553718270189808037639217)
            ·
              refine ⟨31915288702642356028229413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42553718270189808037639217 31915288702642356028229413)
              ·
                refine ⟨5984116631745441755293015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31915288702642356028229413 5984116631745441755293015)
                ·
                  refine ⟨8976174947618162632939523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5984116631745441755293015 8976174947618162632939523)
                  ·
                    refine ⟨13464262421427243949409285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8976174947618162632939523 13464262421427243949409285)
                    ·
                      refine ⟨2524549204017608240514241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13464262421427243949409285 2524549204017608240514241)
                      ·
                        rfl

theorem cell23_4916542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_4916542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4916542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4916542 prefixEnd_4916542 := by exact prefixLift 4916542
  have htrace : WordTrace (prefixWord ++ tailWord_4916542) baseStart_4916542 baseEnd_4916542 := by
    simpa [prefixWord, tailWord_4916542, baseEnd_4916542] using wordTrace_append hprefix tailTrace_4916542
  have hstable : (prefixWord ++ tailWord_4916542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4916542).length < 2 ^ (prefixWord ++ tailWord_4916542).sum := by decide
  have hdescent : baseEnd_4916542 < baseStart_4916542 := by decide
  rcases family_descends (prefixWord ++ tailWord_4916542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4916576 : List Nat := [2, 1, 1, 3, 4, 1, 2, 4, 1, 2, 2]
def baseStart_4916576 : Nat := 118140960795 + 4916576 * 2 ^ 59
def prefixEnd_4916576 : Nat := 4983230072969 + 3 ^ 40 * 4916576 * 2
def baseEnd_4916576 : Nat := 2524566662359861107489085

theorem tailTrace_4916576 : CollatzResearch.WordTrace tailWord_4916576 prefixEnd_4916576 2524566662359861107489085 := by
  unfold tailWord_4916576
  simp only [CollatzResearch.WordTrace]
  refine ⟨89661129318046155587612791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119548172424061540783483721 89661129318046155587612791)
  ·
    refine ⟨134491693977069233381419187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89661129318046155587612791 134491693977069233381419187)
    ·
      refine ⟨201737540965603850072128781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134491693977069233381419187 201737540965603850072128781)
      ·
        refine ⟨75651577862101443777048293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201737540965603850072128781 75651577862101443777048293)
        ·
          refine ⟨14184670849144020708196555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75651577862101443777048293 14184670849144020708196555)
          ·
            refine ⟨21277006273716031062294833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14184670849144020708196555 21277006273716031062294833)
            ·
              refine ⟨15957754705287023296721125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21277006273716031062294833 15957754705287023296721125)
              ·
                refine ⟨2992079007241316868135211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15957754705287023296721125 2992079007241316868135211)
                ·
                  refine ⟨4488118510861975302202817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2992079007241316868135211 4488118510861975302202817)
                  ·
                    refine ⟨3366088883146481476652113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4488118510861975302202817 3366088883146481476652113)
                    ·
                      refine ⟨2524566662359861107489085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3366088883146481476652113 2524566662359861107489085)
                      ·
                        rfl

theorem cell23_4916576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 4, 1, 2, 2].length) (baseStart_4916576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4916576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4916576 prefixEnd_4916576 := by exact prefixLift 4916576
  have htrace : WordTrace (prefixWord ++ tailWord_4916576) baseStart_4916576 baseEnd_4916576 := by
    simpa [prefixWord, tailWord_4916576, baseEnd_4916576] using wordTrace_append hprefix tailTrace_4916576
  have hstable : (prefixWord ++ tailWord_4916576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4916576).length < 2 ^ (prefixWord ++ tailWord_4916576).sum := by decide
  have hdescent : baseEnd_4916576 < baseStart_4916576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4916576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4916585 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 2, 7, 2]
def baseStart_4916585 : Nat := 118140960795 + 4916585 * 2 ^ 59
def prefixEnd_4916585 : Nat := 4983230072969 + 3 ^ 40 * 4916585 * 2
def baseEnd_4916585 : Nat := 2524571283685751572276543

theorem tailTrace_4916585 : CollatzResearch.WordTrace tailWord_4916585 prefixEnd_4916585 2524571283685751572276543 := by
  unfold tailWord_4916585
  simp only [CollatzResearch.WordTrace]
  refine ⟨179322586893059705712303209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119548391262039803808202139 179322586893059705712303209)
  ·
    refine ⟨134491940169794779284227407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179322586893059705712303209 134491940169794779284227407)
    ·
      refine ⟨201737910254692168926341111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134491940169794779284227407 201737910254692168926341111)
      ·
        refine ⟨302606865382038253389511667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201737910254692168926341111 302606865382038253389511667)
        ·
          refine ⟨453910298073057380084267501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302606865382038253389511667 453910298073057380084267501)
          ·
            refine ⟨170216361777396517531600313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 453910298073057380084267501 170216361777396517531600313)
            ·
              refine ⟨127662271333047388148700235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170216361777396517531600313 127662271333047388148700235)
              ·
                refine ⟨191493406999571082223050353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127662271333047388148700235 191493406999571082223050353)
                ·
                  refine ⟨143620055249678311667287765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 191493406999571082223050353 143620055249678311667287765)
                  ·
                    refine ⟨3366095044914335429702057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 143620055249678311667287765 3366095044914335429702057)
                    ·
                      refine ⟨2524571283685751572276543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3366095044914335429702057 2524571283685751572276543)
                      ·
                        rfl

theorem cell23_4916585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 7, 2].length) (baseStart_4916585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4916585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4916585 prefixEnd_4916585 := by exact prefixLift 4916585
  have htrace : WordTrace (prefixWord ++ tailWord_4916585) baseStart_4916585 baseEnd_4916585 := by
    simpa [prefixWord, tailWord_4916585, baseEnd_4916585] using wordTrace_append hprefix tailTrace_4916585
  have hstable : (prefixWord ++ tailWord_4916585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4916585).length < 2 ^ (prefixWord ++ tailWord_4916585).sum := by decide
  have hdescent : baseEnd_4916585 < baseStart_4916585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4916585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4916586 : List Nat := [3, 1, 3, 3, 2, 1, 3, 1, 2, 4]
def baseStart_4916586 : Nat := 118140960795 + 4916586 * 2 ^ 59
def prefixEnd_4916586 : Nat := 4983230072969 + 3 ^ 40 * 4916586 * 2
def baseEnd_4916586 : Nat := 841523932388802022788013

theorem tailTrace_4916586 : CollatzResearch.WordTrace tailWord_4916586 prefixEnd_4916586 841523932388802022788013 := by
  unfold tailWord_4916586
  simp only [CollatzResearch.WordTrace]
  refine ⟨44830655841514020720772403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119548415577370721922059741 44830655841514020720772403)
  ·
    refine ⟨67245983762271031081158605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44830655841514020720772403 67245983762271031081158605)
    ·
      refine ⟨25217243910851636655434477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67245983762271031081158605 25217243910851636655434477)
      ·
        refine ⟨9456466466569363745787929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25217243910851636655434477 9456466466569363745787929)
        ·
          refine ⟨7092349849927022809340947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9456466466569363745787929 7092349849927022809340947)
          ·
            refine ⟨10638524774890534214011421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7092349849927022809340947 10638524774890534214011421)
            ·
              refine ⟨3989446790583950330254283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10638524774890534214011421 3989446790583950330254283)
              ·
                refine ⟨5984170185875925495381425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3989446790583950330254283 5984170185875925495381425)
                ·
                  refine ⟨4488127639406944121536069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5984170185875925495381425 4488127639406944121536069)
                  ·
                    refine ⟨841523932388802022788013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4488127639406944121536069 841523932388802022788013)
                    ·
                      rfl

theorem cell23_4916586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_4916586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4916586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4916586 prefixEnd_4916586 := by exact prefixLift 4916586
  have htrace : WordTrace (prefixWord ++ tailWord_4916586) baseStart_4916586 baseEnd_4916586 := by
    simpa [prefixWord, tailWord_4916586, baseEnd_4916586] using wordTrace_append hprefix tailTrace_4916586
  have hstable : (prefixWord ++ tailWord_4916586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4916586).length < 2 ^ (prefixWord ++ tailWord_4916586).sum := by decide
  have hdescent : baseEnd_4916586 < baseStart_4916586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4916586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4916608 : List Nat := [2, 1, 1, 2, 1, 2, 1, 4, 1, 8]
def baseStart_4916608 : Nat := 118140960795 + 4916608 * 2 ^ 59
def prefixEnd_4916608 : Nat := 4983230072969 + 3 ^ 40 * 4916608 * 2
def baseEnd_4916608 : Nat := 841527697913601660762979

theorem tailTrace_4916608 : CollatzResearch.WordTrace tailWord_4916608 prefixEnd_4916608 841527697913601660762979 := by
  unfold tailWord_4916608
  simp only [CollatzResearch.WordTrace]
  refine ⟨89661712885988190320195239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119548950514650920426926985 89661712885988190320195239)
  ·
    refine ⟨134492569328982285480292859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89661712885988190320195239 134492569328982285480292859)
    ·
      refine ⟨201738853993473428220439289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134492569328982285480292859 201738853993473428220439289)
      ·
        refine ⟨151304140495105071165329467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201738853993473428220439289 151304140495105071165329467)
        ·
          refine ⟨226956210742657606747994201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151304140495105071165329467 226956210742657606747994201)
          ·
            refine ⟨170217158056993205060995651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226956210742657606747994201 170217158056993205060995651)
            ·
              refine ⟨255325737085489807591493477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170217158056993205060995651 255325737085489807591493477)
              ·
                refine ⟨47873575703529338923405027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 255325737085489807591493477 47873575703529338923405027)
                ·
                  refine ⟨71810363555294008385107541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47873575703529338923405027 71810363555294008385107541)
                  ·
                    refine ⟨841527697913601660762979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 71810363555294008385107541 841527697913601660762979)
                    ·
                      rfl

theorem cell23_4916608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 1, 8].length) (baseStart_4916608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4916608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4916608 prefixEnd_4916608 := by exact prefixLift 4916608
  have htrace : WordTrace (prefixWord ++ tailWord_4916608) baseStart_4916608 baseEnd_4916608 := by
    simpa [prefixWord, tailWord_4916608, baseEnd_4916608] using wordTrace_append hprefix tailTrace_4916608
  have hstable : (prefixWord ++ tailWord_4916608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4916608).length < 2 ^ (prefixWord ++ tailWord_4916608).sum := by decide
  have hdescent : baseEnd_4916608 < baseStart_4916608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4916608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4916610 : List Nat := [3, 4, 2, 1, 1, 1, 3, 3, 1, 2, 2]
def baseStart_4916610 : Nat := 118140960795 + 4916610 * 2 ^ 59
def prefixEnd_4916610 : Nat := 4983230072969 + 3 ^ 40 * 4916610 * 2
def baseEnd_4916610 : Nat := 2524584120702113974463929

theorem tailTrace_4916610 : CollatzResearch.WordTrace tailWord_4916610 prefixEnd_4916610 2524584120702113974463929 := by
  unfold tailWord_4916610
  simp only [CollatzResearch.WordTrace]
  refine ⟨44830874679492283745490821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119548999145312756654642189 44830874679492283745490821)
  ·
    refine ⟨8405789002404803202279529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44830874679492283745490821 8405789002404803202279529)
    ·
      refine ⟨6304341751803602401709647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8405789002404803202279529 6304341751803602401709647)
      ·
        refine ⟨9456512627705403602564471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6304341751803602401709647 9456512627705403602564471)
        ·
          refine ⟨14184768941558105403846707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9456512627705403602564471 14184768941558105403846707)
          ·
            refine ⟨21277153412337158105770061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14184768941558105403846707 21277153412337158105770061)
            ·
              refine ⟨7978932529626434289663773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21277153412337158105770061 7978932529626434289663773)
              ·
                refine ⟨2992099698609912858623915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7978932529626434289663773 2992099698609912858623915)
                ·
                  refine ⟨4488149547914869287935873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2992099698609912858623915 4488149547914869287935873)
                  ·
                    refine ⟨3366112160936151965951905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4488149547914869287935873 3366112160936151965951905)
                    ·
                      refine ⟨2524584120702113974463929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3366112160936151965951905 2524584120702113974463929)
                      ·
                        rfl

theorem cell23_4916610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_4916610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4916610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4916610 prefixEnd_4916610 := by exact prefixLift 4916610
  have htrace : WordTrace (prefixWord ++ tailWord_4916610) baseStart_4916610 baseEnd_4916610 := by
    simpa [prefixWord, tailWord_4916610, baseEnd_4916610] using wordTrace_append hprefix tailTrace_4916610
  have hstable : (prefixWord ++ tailWord_4916610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4916610).length < 2 ^ (prefixWord ++ tailWord_4916610).sum := by decide
  have hdescent : baseEnd_4916610 < baseStart_4916610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4916610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4916653 : List Nat := [1, 5, 2, 2, 1, 3, 1, 2, 1, 3, 2]
def baseStart_4916653 : Nat := 118140960795 + 4916653 * 2 ^ 59
def prefixEnd_4916653 : Nat := 4983230072969 + 3 ^ 40 * 4916653 * 2
def baseEnd_4916653 : Nat := 2524606200370257306226231

theorem tailTrace_4916653 : CollatzResearch.WordTrace tailWord_4916653 prefixEnd_4916653 2524606200370257306226231 := by
  unfold tailWord_4916653
  simp only [CollatzResearch.WordTrace]
  refine ⟨179325067056813353325778613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119550044704542235550519075 179325067056813353325778613)
  ·
    refine ⟨16811725036576251874291745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 179325067056813353325778613 16811725036576251874291745)
    ·
      refine ⟨12608793777432188905718809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16811725036576251874291745 12608793777432188905718809)
      ·
        refine ⟨9456595333074141679289107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12608793777432188905718809 9456595333074141679289107)
        ·
          refine ⟨14184892999611212518933661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9456595333074141679289107 14184892999611212518933661)
          ·
            refine ⟨5319334874854204694600123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14184892999611212518933661 5319334874854204694600123)
            ·
              refine ⟨7979002312281307041900185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5319334874854204694600123 7979002312281307041900185)
              ·
                refine ⟨5984251734210980281425139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7979002312281307041900185 5984251734210980281425139)
                ·
                  refine ⟨8976377601316470422137709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5984251734210980281425139 8976377601316470422137709)
                  ·
                    refine ⟨3366141600493676408301641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8976377601316470422137709 3366141600493676408301641)
                    ·
                      refine ⟨2524606200370257306226231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3366141600493676408301641 2524606200370257306226231)
                      ·
                        rfl

theorem cell23_4916653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_4916653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4916653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4916653 prefixEnd_4916653 := by exact prefixLift 4916653
  have htrace : WordTrace (prefixWord ++ tailWord_4916653) baseStart_4916653 baseEnd_4916653 := by
    simpa [prefixWord, tailWord_4916653, baseEnd_4916653] using wordTrace_append hprefix tailTrace_4916653
  have hstable : (prefixWord ++ tailWord_4916653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4916653).length < 2 ^ (prefixWord ++ tailWord_4916653).sum := by decide
  have hdescent : baseEnd_4916653 < baseStart_4916653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4916653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4916745 : List Nat := [1, 2, 1, 1, 3, 1, 5, 1, 8]
def baseStart_4916745 : Nat := 118140960795 + 4916745 * 2 ^ 59
def prefixEnd_4916745 : Nat := 4983230072969 + 3 ^ 40 * 4916745 * 2
def baseEnd_4916745 : Nat := 280517048954496771808423

theorem tailTrace_4916745 : CollatzResearch.WordTrace tailWord_4916745 prefixEnd_4916745 280517048954496771808423 := by
  unfold tailWord_4916745
  simp only [CollatzResearch.WordTrace]
  refine ⟨179328422572480053038127689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119552281714986702025418459 179328422572480053038127689)
  ·
    refine ⟨134496316929360039778595767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179328422572480053038127689 134496316929360039778595767)
    ·
      refine ⟨201744475394040059667893651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134496316929360039778595767 201744475394040059667893651)
      ·
        refine ⟨302616713091060089501840477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201744475394040059667893651 302616713091060089501840477)
        ·
          refine ⟨113481267409147533563190179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 302616713091060089501840477 113481267409147533563190179)
          ·
            refine ⟨170221901113721300344785269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113481267409147533563190179 170221901113721300344785269)
            ·
              refine ⟨15958303229411371907323619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 170221901113721300344785269 15958303229411371907323619)
              ·
                refine ⟨23937454844117057860985429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15958303229411371907323619 23937454844117057860985429)
                ·
                  refine ⟨280517048954496771808423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23937454844117057860985429 280517048954496771808423)
                  ·
                    rfl

theorem cell23_4916745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 8].length) (baseStart_4916745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4916745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4916745 prefixEnd_4916745 := by exact prefixLift 4916745
  have htrace : WordTrace (prefixWord ++ tailWord_4916745) baseStart_4916745 baseEnd_4916745 := by
    simpa [prefixWord, tailWord_4916745, baseEnd_4916745] using wordTrace_append hprefix tailTrace_4916745
  have hstable : (prefixWord ++ tailWord_4916745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4916745).length < 2 ^ (prefixWord ++ tailWord_4916745).sum := by decide
  have hdescent : baseEnd_4916745 < baseStart_4916745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4916745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4916799 : List Nat := [1, 1, 2, 2, 3, 3, 1, 1, 4, 3, 2]
def baseStart_4916799 : Nat := 118140960795 + 4916799 * 2 ^ 59
def prefixEnd_4916799 : Nat := 4983230072969 + 3 ^ 40 * 4916799 * 2
def baseEnd_4916799 : Nat := 2524681168545813735000559

theorem tailTrace_4916799 : CollatzResearch.WordTrace tailWord_4916799 prefixEnd_4916799 2524681168545813735000559 := by
  unfold tailWord_4916799
  simp only [CollatzResearch.WordTrace]
  refine ⟨179330392114284420260593451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119553594742856280173728967 179330392114284420260593451)
  ·
    refine ⟨268995588171426630390890177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179330392114284420260593451 268995588171426630390890177)
    ·
      refine ⟨201746691128569972793167633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268995588171426630390890177 201746691128569972793167633)
      ·
        refine ⟨151310018346427479594875725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201746691128569972793167633 151310018346427479594875725)
        ·
          refine ⟨56741256879910304848078397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151310018346427479594875725 56741256879910304848078397)
          ·
            refine ⟨21277971329966364318029399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56741256879910304848078397 21277971329966364318029399)
            ·
              refine ⟨31916956994949546477044099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21277971329966364318029399 31916956994949546477044099)
              ·
                refine ⟨47875435492424319715566149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31916956994949546477044099 47875435492424319715566149)
                ·
                  refine ⟨8976644154829559946668653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47875435492424319715566149 8976644154829559946668653)
                  ·
                    refine ⟨3366241558061084980000745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8976644154829559946668653 3366241558061084980000745)
                    ·
                      refine ⟨2524681168545813735000559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3366241558061084980000745 2524681168545813735000559)
                      ·
                        rfl

theorem cell23_4916799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 4, 3, 2].length) (baseStart_4916799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4916799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4916799 prefixEnd_4916799 := by exact prefixLift 4916799
  have htrace : WordTrace (prefixWord ++ tailWord_4916799) baseStart_4916799 baseEnd_4916799 := by
    simpa [prefixWord, tailWord_4916799, baseEnd_4916799] using wordTrace_append hprefix tailTrace_4916799
  have hstable : (prefixWord ++ tailWord_4916799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4916799).length < 2 ^ (prefixWord ++ tailWord_4916799).sum := by decide
  have hdescent : baseEnd_4916799 < baseStart_4916799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4916799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4916813 : List Nat := [1, 6, 1, 1, 3, 2, 2, 1, 6]
def baseStart_4916813 : Nat := 118140960795 + 4916813 * 2 ^ 59
def prefixEnd_4916813 : Nat := 4983230072969 + 3 ^ 40 * 4916813 * 2
def baseEnd_4916813 : Nat := 280520928586108520025055

theorem tailTrace_4916813 : CollatzResearch.WordTrace tailWord_4916813 prefixEnd_4916813 280520928586108520025055 := by
  unfold tailWord_4916813
  simp only [CollatzResearch.WordTrace]
  refine ⟨179330902736233700651603093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119553935157489133767735395 179330902736233700651603093)
  ·
    refine ⟨8406136065760954718043895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 179330902736233700651603093 8406136065760954718043895)
    ·
      refine ⟨12609204098641432077065843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8406136065760954718043895 12609204098641432077065843)
      ·
        refine ⟨18913806147962148115598765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12609204098641432077065843 18913806147962148115598765)
        ·
          refine ⟨7092677305485805543349537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18913806147962148115598765 7092677305485805543349537)
          ·
            refine ⟨5319507979114354157512153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7092677305485805543349537 5319507979114354157512153)
            ·
              refine ⟨3989630984335765618134115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5319507979114354157512153 3989630984335765618134115)
              ·
                refine ⟨5984446476503648427201173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3989630984335765618134115 5984446476503648427201173)
                ·
                  refine ⟨280520928586108520025055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5984446476503648427201173 280520928586108520025055)
                  ·
                    rfl

theorem cell23_4916813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_4916813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4916813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4916813 prefixEnd_4916813 := by exact prefixLift 4916813
  have htrace : WordTrace (prefixWord ++ tailWord_4916813) baseStart_4916813 baseEnd_4916813 := by
    simpa [prefixWord, tailWord_4916813, baseEnd_4916813] using wordTrace_append hprefix tailTrace_4916813
  have hstable : (prefixWord ++ tailWord_4916813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4916813).length < 2 ^ (prefixWord ++ tailWord_4916813).sum := by decide
  have hdescent : baseEnd_4916813 < baseStart_4916813 := by decide
  rcases family_descends (prefixWord ++ tailWord_4916813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4916849 : List Nat := [1, 2, 2, 2, 1, 1, 1, 7, 1, 2, 3]
def baseStart_4916849 : Nat := 118140960795 + 4916849 * 2 ^ 59
def prefixEnd_4916849 : Nat := 4983230072969 + 3 ^ 40 * 4916849 * 2
def baseEnd_4916849 : Nat := 2524706842578538539375329

theorem tailTrace_4916849 : CollatzResearch.WordTrace tailWord_4916849 prefixEnd_4916849 2524706842578538539375329 := by
  unfold tailWord_4916849
  simp only [CollatzResearch.WordTrace]
  refine ⟨179332215764103278799913601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119554810509402185866609067 179332215764103278799913601)
  ·
    refine ⟨134499161823077459099935201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179332215764103278799913601 134499161823077459099935201)
    ·
      refine ⟨100874371367308094324951401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134499161823077459099935201 100874371367308094324951401)
      ·
        refine ⟨75655778525481070743713551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100874371367308094324951401 75655778525481070743713551)
        ·
          refine ⟨113483667788221606115570327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75655778525481070743713551 113483667788221606115570327)
          ·
            refine ⟨170225501682332409173355491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113483667788221606115570327 170225501682332409173355491)
            ·
              refine ⟨255338252523498613760033237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170225501682332409173355491 255338252523498613760033237)
              ·
                refine ⟨5984490293519498760000779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 255338252523498613760033237 5984490293519498760000779)
                ·
                  refine ⟨8976735440279248140001169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5984490293519498760000779 8976735440279248140001169)
                  ·
                    refine ⟨6732551580209436105000877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8976735440279248140001169 6732551580209436105000877)
                    ·
                      refine ⟨2524706842578538539375329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6732551580209436105000877 2524706842578538539375329)
                      ·
                        rfl

theorem cell23_4916849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 7, 1, 2, 3].length) (baseStart_4916849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4916849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4916849 prefixEnd_4916849 := by exact prefixLift 4916849
  have htrace : WordTrace (prefixWord ++ tailWord_4916849) baseStart_4916849 baseEnd_4916849 := by
    simpa [prefixWord, tailWord_4916849, baseEnd_4916849] using wordTrace_append hprefix tailTrace_4916849
  have hstable : (prefixWord ++ tailWord_4916849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4916849).length < 2 ^ (prefixWord ++ tailWord_4916849).sum := by decide
  have hdescent : baseEnd_4916849 < baseStart_4916849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4916849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4916912 : List Nat := [2, 1, 1, 1, 2, 1, 5, 2, 2, 6]
def baseStart_4916912 : Nat := 118140960795 + 4916912 * 2 ^ 59
def prefixEnd_4916912 : Nat := 4983230072969 + 3 ^ 40 * 4916912 * 2
def baseEnd_4916912 : Nat := 841579730619923930962513

theorem tailTrace_4916912 : CollatzResearch.WordTrace tailWord_4916912 prefixEnd_4916912 841579730619923930962513 := by
  unfold tailWord_4916912
  simp only [CollatzResearch.WordTrace]
  refine ⟨89667256781437520279728495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119556342375250027039637993 89667256781437520279728495)
  ·
    refine ⟨134500885172156280419592743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89667256781437520279728495 134500885172156280419592743)
    ·
      refine ⟨201751327758234420629389115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134500885172156280419592743 201751327758234420629389115)
      ·
        refine ⟨302626991637351630944083673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201751327758234420629389115 302626991637351630944083673)
        ·
          refine ⟨226970243728013723208062755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 302626991637351630944083673 226970243728013723208062755)
          ·
            refine ⟨340455365592020584812094133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226970243728013723208062755 340455365592020584812094133)
            ·
              refine ⟨31917690524251929826133825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 340455365592020584812094133 31917690524251929826133825)
              ·
                refine ⟨23938267893188947369600369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31917690524251929826133825 23938267893188947369600369)
                ·
                  refine ⟨17953700919891710527200277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23938267893188947369600369 17953700919891710527200277)
                  ·
                    refine ⟨841579730619923930962513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17953700919891710527200277 841579730619923930962513)
                    ·
                      rfl

theorem cell23_4916912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 2, 6].length) (baseStart_4916912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4916912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4916912 prefixEnd_4916912 := by exact prefixLift 4916912
  have htrace : WordTrace (prefixWord ++ tailWord_4916912) baseStart_4916912 baseEnd_4916912 := by
    simpa [prefixWord, tailWord_4916912, baseEnd_4916912] using wordTrace_append hprefix tailTrace_4916912
  have hstable : (prefixWord ++ tailWord_4916912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4916912).length < 2 ^ (prefixWord ++ tailWord_4916912).sum := by decide
  have hdescent : baseEnd_4916912 < baseStart_4916912 := by decide
  rcases family_descends (prefixWord ++ tailWord_4916912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4916940 : List Nat := [2, 2, 1, 5, 2, 1, 2, 2, 1, 3, 2]
def baseStart_4916940 : Nat := 118140960795 + 4916940 * 2 ^ 59
def prefixEnd_4916940 : Nat := 4983230072969 + 3 ^ 40 * 4916940 * 2
def baseEnd_4916940 : Nat := 2524753569318097683337411

theorem tailTrace_4916940 : CollatzResearch.WordTrace tailWord_4916940 prefixEnd_4916940 2524753569318097683337411 := by
  unfold tailWord_4916940
  simp only [CollatzResearch.WordTrace]
  refine ⟨89667767403386800670738137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119557023204515734227650849 89667767403386800670738137)
  ·
    refine ⟨67250825552540100503053603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89667767403386800670738137 67250825552540100503053603)
    ·
      refine ⟨100876238328810150754580405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67250825552540100503053603 100876238328810150754580405)
      ·
        refine ⟨9457147343325951633241913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 100876238328810150754580405 9457147343325951633241913)
        ·
          refine ⟨7092860507494463724931435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9457147343325951633241913 7092860507494463724931435)
          ·
            refine ⟨10639290761241695587397153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7092860507494463724931435 10639290761241695587397153)
            ·
              refine ⟨7979468070931271690547865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10639290761241695587397153 7979468070931271690547865)
              ·
                refine ⟨5984601053198453767910899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7979468070931271690547865 5984601053198453767910899)
                ·
                  refine ⟨8976901579797680651866349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5984601053198453767910899 8976901579797680651866349)
                  ·
                    refine ⟨3366338092424130244449881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8976901579797680651866349 3366338092424130244449881)
                    ·
                      refine ⟨2524753569318097683337411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3366338092424130244449881 2524753569318097683337411)
                      ·
                        rfl

theorem cell23_4916940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_4916940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4916940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4916940 prefixEnd_4916940 := by exact prefixLift 4916940
  have htrace : WordTrace (prefixWord ++ tailWord_4916940) baseStart_4916940 baseEnd_4916940 := by
    simpa [prefixWord, tailWord_4916940, baseEnd_4916940] using wordTrace_append hprefix tailTrace_4916940
  have hstable : (prefixWord ++ tailWord_4916940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4916940).length < 2 ^ (prefixWord ++ tailWord_4916940).sum := by decide
  have hdescent : baseEnd_4916940 < baseStart_4916940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4916940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917019 : List Nat := [1, 1, 1, 1, 1, 1, 4, 4, 5, 4]
def baseStart_4917019 : Nat := 118140960795 + 4917019 * 2 ^ 59
def prefixEnd_4917019 : Nat := 4983230072969 + 3 ^ 40 * 4917019 * 2
def baseEnd_4917019 : Nat := 841598044763267624749849

theorem tailTrace_4917019 : CollatzResearch.WordTrace tailWord_4917019 prefixEnd_4917019 841598044763267624749849 := by
  unfold tailWord_4917019
  simp only [CollatzResearch.WordTrace]
  refine ⟨179338416173487397833602111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119558944115658265222401407 179338416173487397833602111)
  ·
    refine ⟨269007624260231096750403167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179338416173487397833602111 269007624260231096750403167)
    ·
      refine ⟨403511436390346645125604751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269007624260231096750403167 403511436390346645125604751)
      ·
        refine ⟨605267154585519967688407127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 403511436390346645125604751 605267154585519967688407127)
        ·
          refine ⟨907900731878279951532610691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 605267154585519967688407127 907900731878279951532610691)
          ·
            refine ⟨1361851097817419927298916037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 907900731878279951532610691 1361851097817419927298916037)
            ·
              refine ⟨255347080840766236368546757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1361851097817419927298916037 255347080840766236368546757)
              ·
                refine ⟨47877577657643669319102517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 255347080840766236368546757 47877577657643669319102517)
                ·
                  refine ⟨4488522905404093998665861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47877577657643669319102517 4488522905404093998665861)
                  ·
                    refine ⟨841598044763267624749849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4488522905404093998665861 841598044763267624749849)
                    ·
                      rfl

theorem cell23_4917019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5, 4].length) (baseStart_4917019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917019 prefixEnd_4917019 := by exact prefixLift 4917019
  have htrace : WordTrace (prefixWord ++ tailWord_4917019) baseStart_4917019 baseEnd_4917019 := by
    simpa [prefixWord, tailWord_4917019, baseEnd_4917019] using wordTrace_append hprefix tailTrace_4917019
  have hstable : (prefixWord ++ tailWord_4917019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917019).length < 2 ^ (prefixWord ++ tailWord_4917019).sum := by decide
  have hdescent : baseEnd_4917019 < baseStart_4917019 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917026 : List Nat := [3, 3, 1, 1, 2, 1, 1, 4, 2, 1, 4]
def baseStart_4917026 : Nat := 118140960795 + 4917026 * 2 ^ 59
def prefixEnd_4917026 : Nat := 4983230072969 + 3 ^ 40 * 4917026 * 2
def baseEnd_4917026 : Nat := 2524797728654384346862015

theorem tailTrace_4917026 : CollatzResearch.WordTrace tailWord_4917026 prefixEnd_4917026 2524797728654384346862015 := by
  unfold tailWord_4917026
  simp only [CollatzResearch.WordTrace]
  refine ⟨44834667871115509507276733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119559114322974692019404621 44834667871115509507276733)
  ·
    refine ⟨16813000451668316065228775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44834667871115509507276733 16813000451668316065228775)
    ·
      refine ⟨25219500677502474097843163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16813000451668316065228775 25219500677502474097843163)
      ·
        refine ⟨37829251016253711146764745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25219500677502474097843163 37829251016253711146764745)
        ·
          refine ⟨28371938262190283360073559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37829251016253711146764745 28371938262190283360073559)
          ·
            refine ⟨42557907393285425040110339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28371938262190283360073559 42557907393285425040110339)
            ·
              refine ⟨63836861089928137560165509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42557907393285425040110339 63836861089928137560165509)
              ·
                refine ⟨11969411454361525792531033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63836861089928137560165509 11969411454361525792531033)
                ·
                  refine ⟨8977058590771144344398275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11969411454361525792531033 8977058590771144344398275)
                  ·
                    refine ⟨13465587886156716516597413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8977058590771144344398275 13465587886156716516597413)
                    ·
                      refine ⟨2524797728654384346862015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13465587886156716516597413 2524797728654384346862015)
                      ·
                        rfl

theorem cell23_4917026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_4917026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917026 prefixEnd_4917026 := by exact prefixLift 4917026
  have htrace : WordTrace (prefixWord ++ tailWord_4917026) baseStart_4917026 baseEnd_4917026 := by
    simpa [prefixWord, tailWord_4917026, baseEnd_4917026] using wordTrace_append hprefix tailTrace_4917026
  have hstable : (prefixWord ++ tailWord_4917026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917026).length < 2 ^ (prefixWord ++ tailWord_4917026).sum := by decide
  have hdescent : baseEnd_4917026 < baseStart_4917026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
